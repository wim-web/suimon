package suimon

import (
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"slices"
	"sync"
	"sync/atomic"
	"time"
)

var (
	ErrBlocked    = errors.New("workflow is blocked")
	ErrStopped    = errors.New("workflow execution stopped")
	ErrCancelled  = errors.New("workflow cancelled")
	ErrTaskClosed = errors.New("task is no longer active")
)

// Values maps plain output ports to JSON-serializable application values.
type Values map[string]any

type InputItem struct {
	ID    string
	Value any
}
type ValueInput struct {
	Entry PortRef
	Items []InputItem
}
type DataItem struct {
	ID    string          `json:"id"`
	Value json.RawMessage `json:"value"`
}

func (i DataItem) Decode(out any) error { return json.Unmarshal(i.Value, out) }

type ResultPort struct {
	Port  PortRef        `json:"port"`
	Items List[DataItem] `json:"items"`
}

// Snapshot stores the model journal and application values at one commit boundary.
// Restore also accepts a valid uncommitted event suffix and discards that suffix.
type Snapshot struct {
	Graph  Graph                      `json:"graph"`
	Events List[Event]                `json:"events"`
	Values map[string]json.RawMessage `json:"values"`
}
type RunResult struct {
	State    State            `json:"state"`
	Outputs  List[ResultPort] `json:"outputs"`
	Snapshot Snapshot         `json:"snapshot"`
}

func (r RunResult) Output(node, port string) List[DataItem] {
	for _, p := range r.Outputs {
		if p.Port == (PortRef{node, port}) {
			return p.Items
		}
	}
	return nil
}

type Handler func(context.Context, *Task) (Values, error)

// DecisionTask identifies the logical invocation, independently of worker attempts.
type DecisionTask struct {
	Node       string
	Path       Path
	Definition Path
	Iteration  Nat
	Item       DataItem
}
type BranchHandler func(context.Context, DecisionTask) (string, error)
type FilterHandler func(context.Context, DecisionTask) (bool, error)
type LoopHandler func(context.Context, DecisionTask) (bool, error)

// Binding.Path names node definitions, e.g. {"each", "work"} for a ForEach body.
// Iterations and individual stream items use the same binding, but distinct Task IDs.
type Binding struct {
	Path   Path
	Leaf   Handler
	Branch BranchHandler
	Filter FilterHandler
	Loop   LoopHandler
}

type RunOptions struct {
	// Oracle optionally enforces prescribed results, including stream completeness.
	Oracle *ScopedOracle
	// Workers optionally caps simultaneous handler calls. Zero uses node limits only.
	Workers int
	// Now returns logical seconds. The default follows wall time monotonically.
	Now              func() Nat
	PollInterval     time.Duration
	DisableAutoRenew bool
	// StaleGraceSeconds is a logical-time grace period after cancelling a stale
	// handler. Zero selects the default of five logical seconds.
	StaleGraceSeconds Nat
	// Commit must atomically persist the complete snapshot before returning nil.
	// A failure stops execution without publishing the proposed state or payloads.
	Commit func(context.Context, Snapshot) error
	// Append persists only this transaction's events and newly introduced values.
	// It is mutually exclusive with Commit. Return nil only after durable commit.
	Append func(context.Context, CommitBatch) error
}

// Workflow binds the verified control model to application processing functions.
// Every accepted runtime operation is recorded through RecordTransaction / Step.
type Workflow struct {
	Graph    Graph
	Bindings []Binding
	Inputs   []ValueInput
	Options  RunOptions
}

func (w Workflow) Run(ctx context.Context) (RunResult, error) {
	e, err := w.Start(ctx)
	if err != nil {
		return RunResult{}, err
	}
	defer e.Stop()
	return e.Wait(context.Background())
}
func (w Workflow) Resume(ctx context.Context, snapshot Snapshot) (RunResult, error) {
	e, err := w.Restore(ctx, snapshot)
	if err != nil {
		return RunResult{}, err
	}
	defer e.Stop()
	return e.Wait(context.Background())
}
func (w Workflow) Start(ctx context.Context) (*Execution, error) { return w.start(ctx, nil) }
func (w Workflow) Restore(ctx context.Context, snapshot Snapshot) (*Execution, error) {
	return w.start(ctx, &snapshot)
}

// Task inputs are private JSON copies. Emit commits each stable occurrence key
// before returning, allowing downstream work while this handler is still running.
type Task struct {
	ID         string
	Node       string
	Path       Path
	Definition Path
	Attempt    Nat
	Inputs     map[string]json.RawMessage
	auth       Credentials
	node       string
	path       Path
	execution  *Execution
	ctx        context.Context
	closed     atomic.Bool
}

func (t *Task) DecodeInput(port string, out any) error {
	v, ok := t.Inputs[port]
	if !ok {
		return fmt.Errorf("unknown input port: %s", port)
	}
	return json.Unmarshal(v, out)
}
func (t *Task) Emit(port, key string, v any) error {
	if t.closed.Load() {
		return ErrTaskClosed
	}
	data, err := encodeData(v)
	if err != nil {
		return err
	}
	id := StreamItemID(t.path, t.node, port, key)
	return t.execution.request(t.ctx, runMessage{kind: "emit", job: t.auth.Attempt,
		op: Op{Kind: "emit", Auth: t.auth, Port: port, Item: id}, values: map[string]json.RawMessage{id: data}})
}

func PlainItemID(path Path, node, port string) string {
	return DerivedItem("plain", path, node, []string{port})
}
func StreamItemID(path Path, node, port, key string) string {
	return DerivedItem("stream", path, node, []string{port, key})
}
func (t *Task) Renew() error {
	if t.closed.Load() {
		return ErrTaskClosed
	}
	return t.execution.request(t.ctx, runMessage{kind: "renew", job: t.auth.Attempt, op: Op{Kind: "renew", Auth: t.auth}})
}

// TaskError is a leaf failure interpreted using the node's retry policy.
type TaskError struct {
	Code      string
	Retryable bool
	Cause     error
}

func (e *TaskError) Error() string {
	if e.Cause != nil {
		return e.Code + ": " + e.Cause.Error()
	}
	return e.Code
}
func (e *TaskError) Unwrap() error { return e.Cause }

// Execution owns a single state writer while handlers run concurrently.
// Stop suspends the driver; Cancel records a terminal cancellation.
type Execution struct {
	requests      chan runMessage
	done          chan struct{}
	stop          chan struct{}
	stopOnce      sync.Once
	mu            sync.Mutex
	view          *runtimeView
	metrics       runtimeMetrics
	settled       bool
	err           error
	changed       chan struct{}
	statusChanged chan struct{}
	revision      Nat
	reasonKey     string
	stopped       bool
}

func (e *Execution) request(ctx context.Context, m runMessage) error {
	if ctx == nil {
		return fmt.Errorf("nil request context")
	}
	if err := ctx.Err(); err != nil {
		return err
	}
	m.reply = make(chan error, 1)
	select {
	case <-ctx.Done():
		return ctx.Err()
	case <-e.done:
		return ErrStopped
	case e.requests <- m:
	}
	select {
	case err := <-m.reply:
		return err
	case <-ctx.Done():
		return ctx.Err()
	case <-e.done:
		select {
		case err := <-m.reply:
			return err
		default:
			return ErrStopped
		}
	}
}

// Apply exposes all model operations, including manual retry and external worker
// operations. Payloads are keyed by logical item ID and committed with the Op.
func (e *Execution) Apply(ctx context.Context, op Op, payloads Values) error {
	b, err := json.Marshal(op)
	if err != nil {
		return err
	}
	var copy Op
	if err = json.Unmarshal(b, &copy); err != nil {
		return err
	}
	vs := map[string]json.RawMessage{}
	for id, v := range payloads {
		data, err := encodeData(v)
		if err != nil {
			return err
		}
		vs[id] = data
	}
	return e.request(ctx, runMessage{kind: "op", op: copy, values: vs})
}
func (e *Execution) ManualRetry(ctx context.Context, instance string) error {
	return e.Apply(ctx, Op{Kind: "manualRetry", Inst: instance}, nil)
}
func (e *Execution) Cancel(ctx context.Context) error { return e.Apply(ctx, Op{Kind: "cancel"}, nil) }
func (e *Execution) Stop()                            { e.stopOnce.Do(func() { close(e.stop) }); <-e.done }

// Result returns an independent copy of the latest committed state and values.
func (e *Execution) Result() RunResult { r, _, _, _ := e.read(); return r }

// Wait returns the current settled outcome: success, cancellation, runtime
// error, blocked, or worker-stalled. Repeated calls may return the same outcome.
// Observe/WaitForChange waits for changes; a started execution remains available
// for ManualRetry and natural recovery from stale handlers.
func (e *Execution) Wait(ctx context.Context) (RunResult, error) {
	for {
		update, changed := e.observeUpdate()
		if update.Settled {
			return update.Result(), update.Err
		}
		select {
		case <-changed:
		case <-ctx.Done():
			return e.Result(), ctx.Err()
		}
	}
}
func (e *Execution) WaitFor(ctx context.Context, predicate func(State) bool) (RunResult, error) {
	for {
		v, _, err, changed := e.observe()
		if predicate(copyPublicState(v.state)) {
			return e.result(v), nil
		}
		if terminal(v.state.Status) {
			if err == nil {
				err = fmt.Errorf("%w: %s", ErrConditionNotMet, v.state.Status)
			}
			return e.result(v), copyExecutionError(err)
		}
		select {
		case <-e.done:
			latest, _, lastErr, _ := e.read()
			if predicate(latest.State) {
				return latest, nil
			}
			if lastErr == nil {
				if terminal(latest.State.Status) {
					lastErr = fmt.Errorf("%w: %s", ErrConditionNotMet, latest.State.Status)
				} else {
					lastErr = ErrStopped
				}
			}
			return latest, lastErr
		case <-changed:
		case <-ctx.Done():
			return e.Result(), ctx.Err()
		}
	}
}

func (w Workflow) start(ctx context.Context, from *Snapshot) (*Execution, error) {
	if ctx == nil {
		return nil, fmt.Errorf("nil execution context")
	}
	if w.Options.Commit != nil && w.Options.Append != nil {
		return nil, fmt.Errorf("Commit and Append cannot both be configured")
	}
	if err := w.Graph.Validate(); err != nil {
		return nil, err
	}
	if w.Options.Workers < 0 || w.Options.PollInterval < 0 {
		return nil, fmt.Errorf("negative runtime limit")
	}
	graph := cloneGraph(w.Graph)
	bindings, err := runtimeBindings(graph, w.Bindings)
	if err != nil {
		return nil, err
	}
	opts := w.Options
	if opts.Oracle != nil {
		oracle := *opts.Oracle
		opts.Oracle = &oracle
	}
	if opts.PollInterval == 0 {
		opts.PollInterval = 25 * time.Millisecond
	}
	if opts.StaleGraceSeconds == (Nat{}) {
		opts.StaleGraceSeconds = N(5)
	}
	if opts.Now == nil {
		start := time.Now()
		epoch := N(uint64(start.Unix()))
		opts.Now = func() Nat { return epoch.Add(N(uint64(time.Since(start) / time.Second))) }
	}
	e := &Execution{requests: make(chan runMessage), done: make(chan struct{}), stop: make(chan struct{}), changed: make(chan struct{})}
	r := &workflowRuntime{execution: e, ctx: ctx, graph: graph, bindings: bindings, options: opts, state: Initial(graph),
		values: map[string]json.RawMessage{}, jobs: map[string]*runtimeJob{}}
	if from != nil {
		copy, err := copySnapshot(*from)
		if err != nil {
			return nil, err
		}
		if !equal(copy.Graph, graph) {
			return nil, fmt.Errorf("checkpoint graph differs from workflow")
		}
		state, d := Recover(graph, copy.Events)
		if d != nil {
			return nil, d
		}
		r.state = state
		boundary := 0
		for j, event := range copy.Events {
			if event.Type == "transaction.committed" {
				boundary = j + 1
			}
		}
		r.events = copy.Events[:boundary]
		if boundary > 0 {
			r.time = r.events[boundary-1].RecordedAt
		}
		if opts.Oracle != nil {
			state := Initial(graph)
			for _, event := range r.events {
				if event.Op != nil {
					if !OracleConforms(*opts.Oracle, state, *event.Op) {
						return nil, reject("ORACLE_MISMATCH", "checkpoint command violates the oracle")
					}
					state, _ = Step(state, *event.Op)
				}
			}
		}
		for _, id := range stateItemIDs(state) {
			v, ok := copy.Values[id]
			if !ok {
				return nil, fmt.Errorf("checkpoint is missing value %s", id)
			}
			data, err := encodeData(v)
			if err != nil {
				return nil, err
			}
			r.values[id] = data
		}
		// Complete snapshots (including JournalFile recovery) identify every
		// committed value, even values supplied ahead of their first use.
		// A raw torn snapshot has no per-value commit metadata, so its uncertain
		// extra values are excluded along with the uncommitted event suffix.
		if boundary == len(copy.Events) {
			for id, v := range copy.Values {
				if _, present := r.values[id]; !present {
					data, err := encodeData(v)
					if err != nil {
						return nil, err
					}
					r.values[id] = data
				}
			}
		}
	}
	if !r.state.Started && !terminal(r.state.Status) {
		for _, in := range w.Inputs {
			entry := Input{Entry: in.Entry}
			for _, item := range in.Items {
				data, err := encodeData(item.Value)
				if err != nil {
					return nil, err
				}
				if old, ok := r.startValues[item.ID]; ok && !sameValues(old, data) {
					return nil, fmt.Errorf("conflicting input value: %s", item.ID)
				}
				if r.startValues == nil {
					r.startValues = map[string]json.RawMessage{}
				}
				r.startValues[item.ID] = data
				entry.Items = append(entry.Items, item.ID)
			}
			r.inputs = append(r.inputs, entry)
		}
		if _, rejected := Step(r.state, Op{Kind: "start", Inputs: r.inputs}); rejected != nil {
			return nil, rejected
		}
	}
	r.ids = newRuntimeIDs(r.state, r.events)
	r.publishProgress()
	go r.loop()
	return e, nil
}

func runtimeBindings(g Graph, bindings []Binding) (map[string]Binding, error) {
	result := map[string]Binding{}
	for _, b := range bindings {
		k := Identity(b.Path)
		if _, ok := result[k]; ok {
			return nil, fmt.Errorf("duplicate binding: %s", k)
		}
		b.Path = slices.Clone(b.Path)
		result[k] = b
	}
	used := map[string]bool{}
	var visit func(Graph, Path) error
	visit = func(g Graph, path Path) error {
		for _, n := range g.Nodes {
			p := append(slices.Clone(path), n.ID)
			key := Identity(p)
			b, ok := result[key]
			count := 0
			if b.Leaf != nil {
				count++
			}
			if b.Branch != nil {
				count++
			}
			if b.Filter != nil {
				count++
			}
			if b.Loop != nil {
				count++
			}
			required := false
			valid := true
			switch n.Kind.Type {
			case "leaf":
				required = true
				valid = b.Leaf != nil
			case "branch":
				required = true
				valid = b.Branch != nil
			case "filter":
				required = true
				valid = b.Filter != nil
			case "loop":
				required = true
				valid = b.Loop != nil
			}
			if required && (!ok || !valid || count != 1) {
				return fmt.Errorf("missing or mismatched %s binding: %s", n.Kind.Type, key)
			}
			if ok {
				if !required {
					return fmt.Errorf("node needs no callback: %s", key)
				}
				used[key] = true
			}
			if n.Kind.Body != nil {
				if err := visit(*n.Kind.Body, p); err != nil {
					return err
				}
			}
		}
		return nil
	}
	if err := visit(g, nil); err != nil {
		return nil, err
	}
	for key := range result {
		if !used[key] {
			return nil, fmt.Errorf("unknown node binding: %s", key)
		}
	}
	return result, nil
}

func encodeData(v any) (json.RawMessage, error) {
	b, err := json.Marshal(v)
	if err != nil {
		return nil, err
	}
	j, err := jsonValue(b)
	if err != nil {
		return nil, err
	}
	return json.RawMessage(compactValue(j)), nil
}
func copySnapshot(s Snapshot) (Snapshot, error) {
	b, err := json.Marshal(s)
	if err != nil {
		return Snapshot{}, err
	}
	var out Snapshot
	err = json.Unmarshal(b, &out)
	return out, err
}
func stateItemIDs(s State) []string {
	ids := []string{}
	add := func(id string) {
		if !contains(ids, id) {
			ids = append(ids, id)
		}
	}
	for _, c := range s.Channels {
		for _, id := range c.Items() {
			add(id)
		}
	}
	for _, i := range s.Instances {
		for _, in := range i.Inputs {
			add(in[1])
		}
	}
	for _, receipt := range s.Receipts {
		for _, out := range receipt.Outputs {
			for _, id := range out.Items {
				add(id)
			}
		}
	}
	return ids
}
