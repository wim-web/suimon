package main

import (
	"bytes"
	"context"
	"embed"
	"encoding/json"
	"errors"
	"fmt"
	"hash/fnv"
	"iter"
	"strings"
	"sync"
	"time"

	suimon "github.com/wim-web/suimon/implementations/go/src"
)

// The scenarios: each is a definition in definitions/ run with the functions bound below. Durations
// are counted in units of simulated I/O. The unit is chosen for each run and taken from the context
// of the execution, so that one registry and one engine per definition serve every run.

//go:embed definitions/*.json
var definitionFiles embed.FS

// A scenario is one definition with a default input.
type scenario struct {
	ID          string          `json:"id"`
	Title       string          `json:"title"`
	Description string          `json:"description"`
	Definition  json.RawMessage `json:"definition"`
	Input       json.RawMessage `json:"input,omitempty"`
	// Compare names the scenario that runs the same input with the same delays another way.
	Compare string `json:"compare,omitempty"`

	engine *suimon.Engine
}

// compareInput is the default input of stream and batch. By processUnits, its first item takes the
// longest to process (bravo, 2.8 units) and its last the shortest (lima, 0.5), so Stream, which
// processes bravo while it fetches the rest, finishes after 5.5 units and Batch after 7.8.
const compareInput = `{"names":["bravo","charlie","echo","hotel","lima"]}`

var scenarioList = []struct {
	id, title, description, input, compare string
}{
	{"stream", "Stream", "Fetching takes one unit per item, and produce yields each item as soon as it is fetched. Processing takes a random time per item, from 0.5 to 3 units; it depends only on the item's name, so it is the same in both scenarios. Stream starts processing each item as soon as it arrives, in parallel with fetching the rest.", compareInput, "batch"},
	{"batch", "Batch", "Fetching takes one unit per item, and produceAll returns the whole list once every item is fetched; split then hands the items to process. Processing takes a random time per item, from 0.5 to 3 units; it depends only on the item's name, so it is the same in both scenarios. Batch processes in parallel, but only after fetching everything.", compareInput, "stream"},
	{"branch", "Branch and Merge", "orderSize sends the order to review (amount of 1000 or more) or approve. The other arm is skipped, and decide merges whatever arrives without waiting for it.", `{"id":"A-100","amount":120}`, ""},
	{"merge", "Merge", "Three lookups with different latencies run in parallel after load; summary waits for all of them and returns one list.", `{"id":"u-1"}`, ""},
	{"limit", "Concurrency limit", "A concurrency with four lookup tasks and limit 2: at most two tasks run at a time, the others wait for a slot.", `{"id":"u-1"}`, ""},
	{"timeout", "Timeout", "lookup takes one unit, at most 1000ms, and has callMs 2000 and policy continue. The call for \"stuck\" hangs, times out after 2000ms and is recorded as a failure; the other items still reach collect.", `{"names":["alpha","stuck","charlie"]}`, ""},
	{"stop", "Stop policy", "charge fails and its policy is stop: the workflow stops, and the running ship call is cancelled.", `{"id":"A-200","amount":80}`, ""},
}

// loadScenarios parses and validates every definition (NewEngine) against one registry.
func loadScenarios() ([]*scenario, error) {
	registry, err := suimon.NewRegistry(bindings()...)
	if err != nil {
		return nil, err
	}
	var out []*scenario
	for _, s := range scenarioList {
		data, err := definitionFiles.ReadFile("definitions/" + s.id + ".json")
		if err != nil {
			return nil, err
		}
		p, err := suimon.ParseDefinition(data)
		if err != nil {
			return nil, fmt.Errorf("%s: %w", s.id, err)
		}
		engine, err := suimon.NewEngine(p, registry)
		if err != nil {
			return nil, fmt.Errorf("%s: %w", s.id, err)
		}
		var compact bytes.Buffer
		if err := json.Compact(&compact, data); err != nil {
			return nil, err
		}
		sc := &scenario{ID: s.id, Title: s.title, Description: s.description, Definition: json.RawMessage(compact.String()),
			Compare: s.compare, engine: engine}
		if s.input != "" {
			sc.Input = json.RawMessage(s.input)
		}
		out = append(out, sc)
	}
	return out, nil
}

// Values. The engine passes them as JSON between the functions below.

type request struct {
	Names []string `json:"names"`
}

type item struct {
	Index int    `json:"index"`
	Name  string `json:"name"`
}

type done struct {
	Index  int    `json:"index"`
	Result string `json:"result"`
}

type order struct {
	ID     string `json:"id"`
	Amount int    `json:"amount"`
}

type decision struct {
	Order string `json:"order"`
	By    string `json:"by"`
}

type userRef struct {
	ID string `json:"id"`
}

type user struct {
	ID   string `json:"id"`
	Name string `json:"name"`
}

type part struct {
	Source string `json:"source"`
	Value  string `json:"value"`
}

const maxItems = 20

func bindings() []suimon.Binding {
	return []suimon.Binding{
		suimon.Stream("produce", produce),
		suimon.Func("produceAll", produceAll),
		suimon.Stream("split", split),
		suimon.Func("process", process),
		suimon.Func("lookup", lookup),
		suimon.Judge("orderSize", orderSize),
		suimon.Func("review", decide("review", 3)),
		suimon.Func("approve", decide("approve", 1)),
		suimon.Func("loadUser", loadUser),
		suimon.Func("fetchProfile", fetch("profile", 2)),
		suimon.Func("fetchOrders", fetch("orders", 4)),
		suimon.Func("fetchPoints", fetch("points", 1)),
		suimon.Func("fetchCoupons", fetch("coupons", 3)),
		suimon.Func("accept", accept),
		suimon.Func("charge", charge),
		suimon.Func("ship", ship),
		suimon.Passthrough("item"),
		suimon.Passthrough("items"),
		suimon.Passthrough("done"),
		suimon.Passthrough("order"),
		suimon.Passthrough("decision"),
		suimon.Passthrough("user"),
		suimon.Passthrough("part"),
	}
}

func checkNames(r request) error {
	if len(r.Names) > maxItems {
		return fmt.Errorf("at most %d names", maxItems)
	}
	return nil
}

// produce fetches one item per unit and yields it at once: downstream work for an item can start
// while the rest are still being fetched.
func produce(ctx context.Context, r request) iter.Seq2[item, error] {
	return func(yield func(item, error) bool) {
		s := begin(ctx, "produce", fmt.Sprintf("%d items", len(r.Names)))
		var err error
		defer func() { s.end(ctx, err) }()
		if err = checkNames(r); err != nil {
			yield(item{}, err)
			return
		}
		for i, name := range r.Names {
			if err = pause(ctx, 1); err != nil {
				yield(item{}, err)
				return
			}
			s.mark()
			if !yield(item{i, name}, nil) {
				return
			}
		}
	}
}

// produceAll fetches the same items with the same delays, and returns them together.
func produceAll(ctx context.Context, r request) (items []item, err error) {
	s := begin(ctx, "produceAll", fmt.Sprintf("%d items", len(r.Names)))
	defer func() { s.end(ctx, err) }()
	if err := checkNames(r); err != nil {
		return nil, err
	}
	items = []item{}
	for i, name := range r.Names {
		if err := pause(ctx, 1); err != nil {
			return nil, err
		}
		items = append(items, item{i, name})
	}
	return items, nil
}

// split turns the list back into a stream without delay, so that the batch variant has the same
// per-item downstream as the stream variant.
func split(ctx context.Context, items []item) iter.Seq2[item, error] {
	return func(yield func(item, error) bool) {
		s := begin(ctx, "split", fmt.Sprintf("%d items", len(items)))
		defer s.end(ctx, nil)
		for _, it := range items {
			s.mark()
			if !yield(it, nil) {
				return
			}
		}
	}
}

// process waits processUnits of the item's name, like a call to a service whose latency depends on
// the item.
func process(ctx context.Context, it item) (d done, err error) {
	s := begin(ctx, "process", it.Name)
	defer func() { s.end(ctx, err) }()
	if err := pause(ctx, processUnits(it.Name)); err != nil {
		return done{}, err
	}
	return done{it.Index, strings.ToUpper(it.Name)}, nil
}

// processUnits is how long process takes for an item, in units: from 0.5 to 3 in steps of 0.1, drawn
// from the FNV-1a hash of the item's name. It depends on nothing else, so an item takes the same time
// in every run and in both stream and batch.
func processUnits(name string) float64 {
	h := fnv.New32a()
	_, _ = h.Write([]byte(name))
	return 0.5 + float64(h.Sum32()%26)/10
}

// lookup hangs for the item named stuck, like a call to an unresponsive service; only the
// timeout of the placement ends it.
func lookup(ctx context.Context, it item) (d done, err error) {
	s := begin(ctx, "lookup", it.Name)
	defer func() { s.end(ctx, err) }()
	if it.Name == "stuck" {
		<-ctx.Done()
		return done{}, ctx.Err()
	}
	if err := pause(ctx, 1); err != nil {
		return done{}, err
	}
	return done{it.Index, "found " + it.Name}, nil
}

func orderSize(ctx context.Context, o order) (arm string, err error) {
	s := begin(ctx, "orderSize", o.ID)
	defer func() { s.end(ctx, err) }()
	if err := pause(ctx, 0.5); err != nil {
		return "", err
	}
	if o.Amount >= 1000 {
		return "review", nil
	}
	return "auto", nil
}

func decide(by string, units float64) func(context.Context, order) (decision, error) {
	return func(ctx context.Context, o order) (d decision, err error) {
		s := begin(ctx, by, o.ID)
		defer func() { s.end(ctx, err) }()
		if err := pause(ctx, units); err != nil {
			return decision{}, err
		}
		return decision{o.ID, by}, nil
	}
}

func loadUser(ctx context.Context, r userRef) (u user, err error) {
	s := begin(ctx, "loadUser", r.ID)
	defer func() { s.end(ctx, err) }()
	if err := pause(ctx, 1); err != nil {
		return user{}, err
	}
	return user{r.ID, "User " + r.ID}, nil
}

func fetch(source string, units float64) func(context.Context, user) (part, error) {
	return func(ctx context.Context, u user) (p part, err error) {
		s := begin(ctx, "fetch "+source, u.ID)
		defer func() { s.end(ctx, err) }()
		if err := pause(ctx, units); err != nil {
			return part{}, err
		}
		return part{source, fmt.Sprintf("%s of %s", source, u.Name)}, nil
	}
}

func accept(ctx context.Context, o order) (_ order, err error) {
	s := begin(ctx, "accept", o.ID)
	defer func() { s.end(ctx, err) }()
	return o, pause(ctx, 1)
}

var errDeclined = errors.New("card declined")

func charge(ctx context.Context, o order) (_ struct{}, err error) {
	s := begin(ctx, "charge", o.ID)
	defer func() { s.end(ctx, err) }()
	if err := pause(ctx, 2); err != nil {
		return struct{}{}, err
	}
	return struct{}{}, errDeclined
}

func ship(ctx context.Context, o order) (_ struct{}, err error) {
	s := begin(ctx, "ship", o.ID)
	defer func() { s.end(ctx, err) }()
	return struct{}{}, pause(ctx, 10)
}

// The environment of one run: the unit of delay, and the spans of user code for the timeline.

// minUnit and maxUnit bound the unit of a run. The delays scale with the unit, but the timeouts of
// the definitions do not: at maxUnit, a lookup of the timeout scenario (one unit) still ends well
// within its callMs (2000).
const (
	minUnit = 10 * time.Millisecond
	maxUnit = time.Second
)

type envKey struct{}

type env struct {
	unit    time.Duration
	started time.Time
	// changed is called after each change of the spans.
	changed func()

	mu    sync.Mutex
	spans []span
}

// span is one call of user code, in milliseconds from the start of the run.
type span struct {
	Function string    `json:"function"`
	Detail   string    `json:"detail"`
	StartMs  float64   `json:"startMs"`
	EndMs    *float64  `json:"endMs"`
	Marks    []float64 `json:"marks,omitempty"`
	// Outcome is running, ok, error, or cancelled (the context was cancelled: a timeout, a stop,
	// or a cancellation).
	Outcome string `json:"outcome"`
}

func newEnv(unit time.Duration, changed func()) *env {
	if changed == nil {
		changed = func() {}
	}
	return &env{unit: unit, started: time.Now(), changed: changed}
}

func withEnv(ctx context.Context, e *env) context.Context { return context.WithValue(ctx, envKey{}, e) }

func envOf(ctx context.Context) *env {
	if e, ok := ctx.Value(envKey{}).(*env); ok {
		return e
	}
	return newEnv(defaultUnit, nil)
}

func (e *env) now() float64 { return float64(time.Since(e.started).Microseconds()) / 1000 }

func (e *env) snapshot() []span {
	e.mu.Lock()
	defer e.mu.Unlock()
	out := make([]span, len(e.spans))
	for i, s := range e.spans {
		s.Marks = append([]float64(nil), s.Marks...)
		out[i] = s
	}
	return out
}

type spanRef struct {
	env   *env
	index int
}

func begin(ctx context.Context, function, detail string) spanRef {
	e := envOf(ctx)
	e.mu.Lock()
	e.spans = append(e.spans, span{Function: function, Detail: detail, StartMs: e.now(), Outcome: "running"})
	ref := spanRef{e, len(e.spans) - 1}
	e.mu.Unlock()
	e.changed()
	return ref
}

func (s spanRef) mark() {
	s.env.mu.Lock()
	sp := &s.env.spans[s.index]
	sp.Marks = append(sp.Marks, s.env.now())
	s.env.mu.Unlock()
	s.env.changed()
}

func (s spanRef) end(ctx context.Context, err error) {
	outcome := "ok"
	switch {
	case ctx.Err() != nil:
		outcome = "cancelled"
	case err != nil:
		outcome = "error"
	}
	s.env.mu.Lock()
	sp := &s.env.spans[s.index]
	end := s.env.now()
	sp.EndMs, sp.Outcome = &end, outcome
	s.env.mu.Unlock()
	s.env.changed()
}

// pause simulates I/O for a number of units, and returns early when ctx is cancelled.
func pause(ctx context.Context, units float64) error {
	timer := time.NewTimer(time.Duration(units * float64(envOf(ctx).unit)))
	defer timer.Stop()
	select {
	case <-timer.C:
		return nil
	case <-ctx.Done():
		return ctx.Err()
	}
}
