package suimon

import (
	"context"
	"errors"
	"fmt"
	"iter"
	"strings"
	"sync"
	"sync/atomic"
	"testing"
	"time"
)

// Go implementations of the definitions of Test/definitions and testdata, for runtime tests. Every
// function is a function of its input, so equal runs accept equal values; knobs make functions
// fail, block, or report what happened.

var errBoom = errors.New("boom")

// memJournal is a RecoverableJournal in memory. failAt makes the failAt-th Append write half of
// its lines and fail; synced is what the last Sync covered.
type memJournal struct {
	mu      sync.Mutex
	data    []byte
	synced  int
	appends int
	failAt  int
}

func newMemJournal(text string) *memJournal {
	return &memJournal{data: []byte(text), synced: len(text)}
}

func (j *memJournal) Append(lines []byte) error {
	j.mu.Lock()
	defer j.mu.Unlock()
	j.appends++
	if j.failAt > 0 && j.appends >= j.failAt {
		j.data = append(j.data, lines[:len(lines)/2]...)
		return errors.New("disk full")
	}
	j.data = append(j.data, lines...)
	return nil
}

func (j *memJournal) Sync() error {
	j.mu.Lock()
	defer j.mu.Unlock()
	j.synced = len(j.data)
	return nil
}

func (j *memJournal) Contents() ([]byte, error) {
	j.mu.Lock()
	defer j.mu.Unlock()
	return []byte(string(j.data)), nil
}

func (j *memJournal) Truncate(size int64) error {
	j.mu.Lock()
	defer j.mu.Unlock()
	j.data = j.data[:size]
	j.synced = min(j.synced, len(j.data))
	return nil
}

func (j *memJournal) text() string {
	j.mu.Lock()
	defer j.mu.Unlock()
	return string(j.data)
}

// durable is the text the last Sync made durable.
func (j *memJournal) durable() string {
	j.mu.Lock()
	defer j.mu.Unlock()
	return string(j.data[:j.synced])
}

// waitCtx blocks until ctx is cancelled and returns its error, or fails the test after a while.
func waitCtx(ctx context.Context) error {
	select {
	case <-ctx.Done():
		return ctx.Err()
	case <-time.After(20 * time.Second):
		return errors.New("test: not cancelled in time")
	}
}

// gauge counts how many calls run at once and remembers the most.
type gauge struct {
	mu        sync.Mutex
	now, most int
}

func (g *gauge) enter() {
	g.mu.Lock()
	defer g.mu.Unlock()
	g.now++
	g.most = max(g.most, g.now)
}

func (g *gauge) leave() {
	g.mu.Lock()
	defer g.mu.Unlock()
	g.now--
}

func (g *gauge) max() int {
	g.mu.Lock()
	defer g.mu.Unlock()
	return g.most
}

// signal is a set of named events that tests wait for.
type signal struct {
	mu   sync.Mutex
	seen map[string]int
	cond *sync.Cond
}

func newSignal() *signal {
	s := &signal{seen: map[string]int{}}
	s.cond = sync.NewCond(&s.mu)
	return s
}

func (s *signal) fire(name string) {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.seen[name]++
	s.cond.Broadcast()
}

func (s *signal) count(name string) int {
	s.mu.Lock()
	defer s.mu.Unlock()
	return s.seen[name]
}

// await waits until name has fired n times, or fails after a while.
func (s *signal) await(name string, n int) error {
	deadline := time.Now().Add(20 * time.Second)
	done := make(chan struct{})
	defer close(done)
	go func() {
		select {
		case <-done:
		case <-time.After(time.Until(deadline)):
			s.mu.Lock()
			s.cond.Broadcast()
			s.mu.Unlock()
		}
	}()
	s.mu.Lock()
	defer s.mu.Unlock()
	for s.seen[name] < n {
		if time.Now().After(deadline) {
			return fmt.Errorf("test: %s fired %d times, want %d", name, s.seen[name], n)
		}
		s.cond.Wait()
	}
	return nil
}

func mustRegistry(t testing.TB, bindings ...Binding) *Registry {
	t.Helper()
	r, err := NewRegistry(bindings...)
	if err != nil {
		t.Fatal(err)
	}
	return r
}

// merge.json

type sales struct {
	Amount int `json:"amount"`
}

type stock struct {
	Items int `json:"items"`
}

type widget struct {
	Title string `json:"title"`
	Value int    `json:"value"`
}

type mergeKnobs struct {
	failSales bool
	// panicSalesWidget makes the transform salesWidget panic.
	panicSalesWidget bool
	// blockStock makes fetchStock wait until it is cancelled.
	blockStock bool
	// journal, when set, is checked by the functions: their invocation is durable when they run,
	// and so is what cancelled fetchStock when it sees the cancellation; early counts violations.
	journal *memJournal
	early   *atomic.Int32
}

func mergeBindings(k mergeKnobs) []Binding {
	durable := func(fragment string) error {
		if k.journal != nil && !strings.Contains(k.journal.durable(), fragment) {
			return fmt.Errorf("test: %s is not durable when its user code runs", fragment)
		}
		return nil
	}
	return []Binding{
		FuncNoInput("fetchSales", func(ctx context.Context) (sales, error) {
			if err := durable(`"placement":"sales"`); err != nil {
				return sales{}, err
			}
			if k.failSales {
				return sales{}, errBoom
			}
			return sales{Amount: 120}, nil
		}),
		FuncNoInput("fetchStock", func(ctx context.Context) (stock, error) {
			if k.blockStock {
				err := waitCtx(ctx)
				if k.journal != nil && !strings.Contains(k.journal.durable(), `"type":"failed"`) &&
					!strings.Contains(k.journal.durable(), `"type":"timedOut"`) {
					k.early.Add(1)
				}
				return stock{}, err
			}
			return stock{Items: 7}, nil
		}),
		Func("render", func(ctx context.Context, ws []widget) (string, error) {
			if err := durable(`"placement":"page"`); err != nil {
				return "", err
			}
			var parts []string
			for _, w := range ws {
				parts = append(parts, fmt.Sprintf("%s=%d", w.Title, w.Value))
			}
			return strings.Join(parts, ","), nil
		}),
		Func("archive", func(ctx context.Context, s sales) (string, error) {
			return fmt.Sprintf("archived %d", s.Amount), nil
		}),
		FuncNoInput("notifyDone", func(ctx context.Context) (string, error) { return "ack", nil }),
		Passthrough("sales"),
		Transform("salesWidget", func(s sales) (widget, error) {
			if k.panicSalesWidget {
				panic("salesWidget broke")
			}
			return widget{"sales", s.Amount}, nil
		}),
		Transform("stockWidget", func(s stock) (widget, error) { return widget{"stock", s.Items}, nil }),
		Passthrough("widgets"),
	}
}

// users.json

type tenant struct {
	Name  string `json:"name"`
	Users int    `json:"users"`
}

type user struct {
	ID int `json:"id"`
}

type summary struct {
	User int    `json:"user"`
	Kind string `json:"kind"`
	Text string `json:"text"`
}

type usersKnobs struct {
	// failOrdersOf fails fetchOrders for this user, failProfileOf fetchProfile, which runs in the
	// sub-workflow profileFlow; failUserIDOf fails the task input transform userId, and
	// failOrdersSummaryOf the task output transform ordersSummary. 0 for none.
	failOrdersOf, failProfileOf, failUserIDOf, failOrdersSummaryOf int
	// failAfter makes fetchAllUsers fail after yielding this many users, once blockOrders calls
	// of all of them have started; 0 for never.
	failAfter int
	// blockOrders makes fetchOrders wait until it is cancelled, and fire "orders" when it starts.
	blockOrders bool
	signal      *signal
}

func usersBindings(k usersKnobs) []Binding {
	return []Binding{
		Stream("fetchAllUsers", func(ctx context.Context, t tenant) iter.Seq2[user, error] {
			return func(yield func(user, error) bool) {
				for id := 1; id <= t.Users; id++ {
					if k.failAfter > 0 && id > k.failAfter {
						if err := k.signal.await("orders", k.failAfter); err != nil {
							yield(user{}, err)
							return
						}
						yield(user{}, errBoom)
						return
					}
					if !yield(user{ID: id}, nil) {
						return
					}
				}
			}
		}),
		Func("fetchProfile", func(ctx context.Context, id int) (string, error) {
			if id == k.failProfileOf {
				return "", errBoom
			}
			return fmt.Sprintf("raw-%d", id), nil
		}),
		Func("formatProfile", func(ctx context.Context, raw string) (string, error) {
			return "profile of " + raw, nil
		}),
		Func("fetchOrders", func(ctx context.Context, id int) (int, error) {
			if k.blockOrders {
				k.signal.fire("orders")
				return 0, waitCtx(ctx)
			}
			if id == k.failOrdersOf {
				return 0, errBoom
			}
			return id * 10, nil
		}),
		Passthrough("user"),
		Transform("userId", func(u user) (int, error) {
			if u.ID == k.failUserIDOf {
				return 0, errBoom
			}
			return u.ID, nil
		}),
		Passthrough("rawProfile"),
		Transform("profileSummary", func(p string) (summary, error) {
			var id int
			fmt.Sscanf(p, "profile of raw-%d", &id)
			return summary{User: id, Kind: "profile", Text: p}, nil
		}),
		Transform("ordersSummary", func(n int) (summary, error) {
			if n/10 == k.failOrdersSummaryOf {
				return summary{}, errBoom
			}
			return summary{User: n / 10, Kind: "orders", Text: fmt.Sprint(n)}, nil
		}),
		Passthrough("summaries"),
	}
}

// branch.json

type order struct {
	ID   int  `json:"id"`
	Paid bool `json:"paid"`
}

type branchKnobs struct {
	orders []order
	// failAfter makes listOrders fail after yielding this many orders; blockAfter makes it wait
	// for cancellation instead. -1 for never.
	failAfter, blockAfter int
	// failJudgeOf fails the judge for this order; unknownArmOf answers an arm that does not exist.
	failJudgeOf, unknownArmOf int
	// shipWaitsForAll makes ship wait until listOrders has yielded every order: without the
	// engine's reading ahead (§4.1.1) the run would never end.
	shipWaitsForAll bool
	signal          *signal
	journal         *memJournal
}

func branchBindings(k branchKnobs) []Binding {
	return []Binding{
		StreamNoInput("listOrders", func(ctx context.Context) iter.Seq2[order, error] {
			return func(yield func(order, error) bool) {
				for i, o := range k.orders {
					if k.journal != nil {
						// The fetch of this element is durable before the generator is asked for it.
						if got := strings.Count(k.journal.durable(), `"type":"fetch"`); got < i+1 {
							yield(order{}, fmt.Errorf("test: %d durable fetches before element %d", got, i))
							return
						}
					}
					if i == k.failAfter {
						yield(order{}, errBoom)
						return
					}
					if i == k.blockAfter {
						yield(order{}, waitCtx(ctx))
						return
					}
					if !yield(o, nil) {
						return
					}
				}
				if k.signal != nil {
					k.signal.fire("listed")
				}
			}
		}),
		Judge("isPaid", func(ctx context.Context, o order) (string, error) {
			switch {
			case o.ID == k.failJudgeOf:
				return "", errBoom
			case o.ID == k.unknownArmOf:
				return "refunded", nil
			case o.Paid:
				return "paid", nil
			}
			return "unpaid", nil
		}),
		Func("ship", func(ctx context.Context, o order) (string, error) {
			if k.shipWaitsForAll {
				if err := k.signal.await("listed", 1); err != nil {
					return "", err
				}
			}
			return fmt.Sprintf("receipt-%d", o.ID), nil
		}),
		Passthrough("order"),
		Passthrough("receipt"),
	}
}

func orders(paid ...bool) []order {
	out := make([]order, len(paid))
	for i, p := range paid {
		out[i] = order{ID: i + 1, Paid: p}
	}
	return out
}

// testdata/calls.json

type bigOrder struct {
	ID    int    `json:"id"`
	Size  string `json:"size"`
	Lines int    `json:"lines"`
}

type line struct {
	Order int `json:"order"`
	N     int `json:"n"`
}

type callsKnobs struct {
	size  string
	lines int
	// failAudit fails the audit, whose policy is stop.
	failAudit bool
}

func callsBindings(k callsKnobs) []Binding {
	return []Binding{
		FuncNoInput("loadOrder", func(ctx context.Context) (bigOrder, error) {
			return bigOrder{ID: 7, Size: k.size, Lines: k.lines}, nil
		}),
		Judge("isLarge", func(ctx context.Context, o bigOrder) (string, error) { return o.Size, nil }),
		Stream("lines", func(ctx context.Context, o bigOrder) iter.Seq2[line, error] {
			return func(yield func(line, error) bool) {
				for n := 1; n <= o.Lines; n++ {
					if !yield(line{Order: o.ID, N: n}, nil) {
						return
					}
				}
			}
		}),
		Func("price", func(ctx context.Context, l line) (int, error) { return l.N * 100, nil }),
		Func("audit", func(ctx context.Context, o bigOrder) (string, error) {
			if k.failAudit {
				return "", errBoom
			}
			return fmt.Sprintf("audited %d", o.ID), nil
		}),
		FuncNoInput("notify", func(ctx context.Context) (string, error) { return "notified", nil }),
		Passthrough("order"),
		Passthrough("line"),
		Passthrough("price"),
		Transform("pricesSummary", func(prices []int) (string, error) {
			total := 0
			for _, p := range prices {
				total += p
			}
			return fmt.Sprintf("total %d", total), nil
		}),
		Transform("auditSummary", func(a string) (string, error) { return a, nil }),
	}
}

// testdata/fanout.json

type fanoutKnobs struct {
	items int
}

func fanoutBindings(k fanoutKnobs) []Binding {
	return []Binding{
		FuncNoInput("seed", func(ctx context.Context) (int, error) { return k.items, nil }),
		Stream("gather", func(ctx context.Context, n int) iter.Seq2[string, error] {
			return func(yield func(string, error) bool) {
				for i := 1; i <= n; i++ {
					if !yield(fmt.Sprintf("item-%d", i), nil) {
						return
					}
				}
			}
		}),
		FuncNoInput("ping", func(ctx context.Context) (string, error) { return "pong", nil }),
		Passthrough("seed"),
		Passthrough("item"),
		Passthrough("pong"),
		Passthrough("out"),
	}
}

// testdata/limit.json: items yields 1..n; each runs the tasks a..d (work) and e (idle) for each
// item, at most 2 at once. The transforms slow and fast turn an item into -1 and 0, which work
// treats specially.

type limitKnobs struct {
	items int
	// barrier makes work wait until this many calls of work have started; 0 for none.
	barrier int
	gauge   gauge
	// perItem holds a gauge for the calls of work of each item.
	perItem sync.Map
	signal  *signal
	// linger is how long the slow call takes to return after it is cancelled.
	linger time.Duration
	// violations counts fast calls that started before the slow call returned.
	violations atomic.Int32
}

func limitBindings(k *limitKnobs) []Binding {
	return []Binding{
		StreamNoInput("items", func(ctx context.Context) iter.Seq2[int, error] {
			return func(yield func(int, error) bool) {
				for i := 1; i <= k.items; i++ {
					if !yield(i, nil) {
						return
					}
				}
			}
		}),
		Func("work", func(ctx context.Context, item int) (string, error) {
			switch item {
			case -1:
				k.signal.fire("slow started")
				err := waitCtx(ctx)
				time.Sleep(k.linger)
				k.signal.fire("slow returned")
				return "", err
			case 0:
				if k.signal.count("slow returned") == 0 {
					k.violations.Add(1)
				}
				return "fast", nil
			}
			k.gauge.enter()
			defer k.gauge.leave()
			g, _ := k.perItem.LoadOrStore(item, &gauge{})
			g.(*gauge).enter()
			defer g.(*gauge).leave()
			k.signal.fire("work")
			if k.barrier > 0 {
				if err := k.signal.await("work", k.barrier); err != nil {
					return "", err
				}
			}
			return fmt.Sprintf("done %d", item), nil
		}),
		FuncNoInput("idle", func(ctx context.Context) (string, error) { return "idle", nil }),
		Passthrough("item"),
		Passthrough("done"),
		Passthrough("dones"),
		Transform("slow", func(int) (int, error) { return -1, nil }),
		Transform("fast", func(int) (int, error) { return 0, nil }),
	}
}
