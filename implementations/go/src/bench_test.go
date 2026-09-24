package suimon

import (
	"context"
	"fmt"
	"iter"
	"testing"
)

// Benchmarks of long streams: the runtime runs a Stream of n elements through a call per element
// into a waitStream, and Check replays the journal it wrote. Run them with
//
//	go test -run '^$' -bench . -benchtime 1x ./src

// streamDefinition yields n numbers, doubles each in its own call, collects the doubles and sums them.
const streamDefinition = `{
  "main": "stream",
  "functions": [
    {"id": "numbers", "input": "Count", "output": {"stream": "Int"}},
    {"id": "double", "input": "Int", "output": {"single": "Int"}},
    {"id": "sum", "input": {"list": "Int"}, "output": {"single": "Int"}}
  ],
  "transforms": [
    {"id": "int", "input": "Int", "output": "Int"},
    {"id": "ints", "input": {"list": "Int"}, "output": {"list": "Int"}}
  ],
  "workflows": [
    {
      "id": "stream",
      "input": {"type": "Count", "placement": "numbers"},
      "placements": [
        {"name": "numbers", "node": {"type": "function", "function": "numbers"}, "policy": "stop"},
        {"name": "double", "node": {"type": "function", "function": "double"}, "policy": "stop"},
        {"name": "all", "node": {"type": "waitStream", "element": "Int"}, "policy": "stop"},
        {"name": "sum", "node": {"type": "function", "function": "sum"}, "policy": "stop"}
      ],
      "connections": [
        {"source": "numbers", "target": "double", "transform": "int"},
        {"source": "double", "target": "all", "transform": "int"},
        {"source": "all", "target": "sum", "transform": "ints"}
      ]
    }
  ]
}`

func streamEngine(tb testing.TB) (*Definition, *Engine) {
	tb.Helper()
	p, err := ParseDefinition([]byte(streamDefinition))
	if err != nil {
		tb.Fatal(err)
	}
	r := mustRegistry(tb,
		Stream("numbers", func(ctx context.Context, n int) iter.Seq2[int, error] {
			return func(yield func(int, error) bool) {
				for i := range n {
					if !yield(i, nil) {
						return
					}
				}
			}
		}),
		Func("double", func(ctx context.Context, n int) (int, error) { return 2 * n, nil }),
		Func("sum", func(ctx context.Context, ns []int) (int, error) {
			total := 0
			for _, n := range ns {
				total += n
			}
			return total, nil
		}),
		Passthrough("int"),
		Passthrough("ints"),
	)
	e, err := NewEngine(p, r)
	if err != nil {
		tb.Fatal(err)
	}
	return p, e
}

// runStream runs the stream definition for n elements and returns the journal and the report.
func runStream(tb testing.TB, e *Engine, n int) (string, *Report) {
	tb.Helper()
	j := &memJournal{}
	r, err := e.Run(context.Background(), n, WithJournal(j))
	if err != nil {
		tb.Fatal(err)
	}
	if r.Status != StatusSucceeded {
		tb.Fatalf("status %v", r.Status)
	}
	var sum int
	if err := r.Output("sum", &sum); err != nil {
		tb.Fatal(err)
	}
	if want := n * (n - 1); sum != want {
		tb.Fatalf("sum %d, want %d", sum, want)
	}
	return j.text(), r
}

func TestLongStream(t *testing.T) {
	p, e := streamEngine(t)
	journal, r := runStream(t, e, 300)
	c, err := Check(journal, sameDefinition(p))
	if err != nil {
		t.Fatal(err)
	}
	if !c.State.Equal(r.State) || c.Uncommitted || c.Length != len(journal) {
		t.Fatal("the journal does not replay to the final state")
	}
}

var benchSizes = []int{1000, 10000}

func BenchmarkRuntimeStream(b *testing.B) {
	_, e := streamEngine(b)
	for _, n := range benchSizes {
		b.Run(fmt.Sprint(n), func(b *testing.B) {
			for range b.N {
				runStream(b, e, n)
			}
		})
	}
}

func BenchmarkCheckStream(b *testing.B) {
	p, e := streamEngine(b)
	for _, n := range benchSizes {
		b.Run(fmt.Sprint(n), func(b *testing.B) {
			journal, r := runStream(b, e, n)
			b.SetBytes(int64(len(journal)))
			b.ResetTimer()
			for range b.N {
				c, err := Check(journal, sameDefinition(p))
				if err != nil {
					b.Fatal(err)
				}
				if c.Committed == 0 || !c.State.Equal(r.State) {
					b.Fatal("the journal does not replay to the final state")
				}
			}
		})
	}
}

// The users definition (Test/definitions) runs a concurrency with a sub-workflow per user: executions,
// tasks and child runs grow with the stream.
func runUsers(tb testing.TB, e *Engine, n int) (string, *Report) {
	tb.Helper()
	j := &memJournal{}
	r, err := e.Run(context.Background(), tenant{Name: "acme", Users: n}, WithJournal(j))
	if err != nil {
		tb.Fatal(err)
	}
	if r.Status != StatusSucceeded {
		tb.Fatalf("status %v", r.Status)
	}
	var perUser [][]summary
	if err := r.Output("all", &perUser); err != nil {
		tb.Fatal(err)
	}
	count := 0
	for _, summaries := range perUser {
		count += len(summaries)
	}
	if len(perUser) != n || count != 2*n {
		tb.Fatalf("%d users with %d summaries, want %d with %d", len(perUser), count, n, 2*n)
	}
	return j.text(), r
}

func usersEngine(tb testing.TB) (*Definition, *Engine) {
	tb.Helper()
	p := load(tb, "users")
	e, err := NewEngine(p, mustRegistry(tb, usersBindings(usersKnobs{})...))
	if err != nil {
		tb.Fatal(err)
	}
	return p, e
}

var usersSizes = []int{1000, 5000}

func BenchmarkRuntimeUsers(b *testing.B) {
	_, e := usersEngine(b)
	for _, n := range usersSizes {
		b.Run(fmt.Sprint(n), func(b *testing.B) {
			for range b.N {
				runUsers(b, e, n)
			}
		})
	}
}

func BenchmarkCheckUsers(b *testing.B) {
	p, e := usersEngine(b)
	for _, n := range usersSizes {
		b.Run(fmt.Sprint(n), func(b *testing.B) {
			journal, r := runUsers(b, e, n)
			b.SetBytes(int64(len(journal)))
			b.ResetTimer()
			for range b.N {
				c, err := Check(journal, sameDefinition(p))
				if err != nil {
					b.Fatal(err)
				}
				if !c.State.Equal(r.State) {
					b.Fatal("the journal does not replay to the final state")
				}
			}
		})
	}
}
