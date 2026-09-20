package suimon

import (
	"context"
	"encoding/json"
	"fmt"
	"strings"
	"testing"
	"time"
)

func TestWorkflowIDs(t *testing.T) {
	for _, count := range []int{10, 40} {
		t.Run(fmt.Sprint(count), func(t *testing.T) {
			w := newFixtureWorkflow(t, "streaming")
			bindingAt(&w, "emit").Leaf = func(_ context.Context, task *Task) (Values, error) {
				for n := 0; n < count; n++ {
					if err := task.Emit("out", fmt.Sprint(n), n); err != nil {
						return nil, err
					}
				}
				return Values{}, nil
			}
			// The full-model race run is intentionally heavier than tiny fixtures;
			// the assertion concerns ID growth, not a wall-clock performance bound.
			ctx, cancel := context.WithTimeout(context.Background(), time.Minute)
			defer cancel()
			r, err := w.Run(ctx)
			if err != nil {
				t.Fatal(err)
			}
			if len(r.State.Attempts) != count+1 {
				t.Fatal("missing attempts")
			}
			limit := len(fmt.Sprintf("a:%d", count+1))
			for _, a := range r.State.Attempts {
				if len(a.ID) > limit || len(a.Token) > limit {
					t.Fatalf("IDs grow with previous IDs: %q %q", a.ID, a.Token)
				}
			}
			assertRuntimeTrace(t, r)
		})
	}
	t.Run("restore-external-ids-and-uncommitted-tail", func(t *testing.T) {
		w := newFixtureWorkflow(t, "minimal")
		s := Initial(w.Graph)
		snapshot := Snapshot{Graph: w.Graph, Values: map[string]json.RawMessage{}}
		var inputs List[Input]
		for _, in := range w.Inputs {
			input := Input{Entry: in.Entry}
			for _, item := range in.Items {
				input.Items = append(input.Items, item.ID)
				snapshot.Values[item.ID], _ = encodeData(item.Value)
			}
			inputs = append(inputs, input)
		}
		id := InstanceID(nil, "work", nil)
		ops := []Op{{Kind: "start", Inputs: inputs}, {Kind: "activate", Node: "work"},
			{Kind: "claim", Auth: Credentials{id, "a:2", "l:2", N(990)}, Worker: "external"},
			{Kind: "expireLease", Inst: id, Now: N(993)}, {Kind: "promoteRetry", Inst: id, Now: N(994)}}
		for n, op := range ops {
			var events List[Event]
			var rejected *Reject
			// tx:6 collides with the next transaction counter after restoration.
			s, events, rejected = RecordTransaction(s, []Op{op}, natLen(snapshot.Events).Inc(), fmt.Sprintf("tx:%d", n+2), s.Now)
			if rejected != nil {
				t.Fatal(rejected)
			}
			snapshot.Events = append(snapshot.Events, events...)
		}
		_, tail, rejected := RecordTransaction(s, []Op{{Kind: "claim", Auth: Credentials{id, "a:3", "l:3", N(1000)}, Worker: "lost"}}, natLen(snapshot.Events).Inc(), "tx:7", N(994))
		if rejected != nil {
			t.Fatal(rejected)
		}
		snapshot.Events = append(snapshot.Events, tail[:len(tail)-1]...)
		r, err := w.Resume(testContext(t), snapshot)
		if err != nil {
			t.Fatal(err)
		}
		if len(r.State.Attempts) != 2 || r.State.Attempts[0].Status != "abandoned" || r.State.Attempts[1].ID != "a:3" || r.State.Attempts[1].Token != "l:3" {
			t.Fatalf("restored freshness: %+v", r.State.Attempts)
		}
		for _, event := range r.Snapshot.Events[len(snapshot.Events)-len(tail)+1:] {
			if event.Op != nil && event.Op.Kind == "claim" && (!strings.HasPrefix(event.Txn, "tx:") || event.Txn == "tx:6") {
				t.Fatal("committed transaction collision")
			}
		}
		assertRuntimeTrace(t, r)
	})
}
