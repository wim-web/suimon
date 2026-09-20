package suimon

import (
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"maps"
	"slices"
	"strings"
	"time"
)

type runMessage struct {
	kind, job string
	op        Op
	values    map[string]json.RawMessage
	outputs   map[string]json.RawMessage
	arm       string
	choice    bool
	err       error
	reply     chan error
}
type runtimeJob struct {
	kind     string
	obsolete bool
	staleAt  *Nat
	scope    DecisionTask
	op       Op
	auth     Credentials
	instance Instance
	cancel   context.CancelFunc
}
type workflowRuntime struct {
	ids         runtimeIDs
	needsSlot   bool
	stall       *WorkerStalledError
	cursor      int
	execution   *Execution
	ctx         context.Context
	graph       Graph
	bindings    map[string]Binding
	options     RunOptions
	state       State
	events      List[Event]
	values      map[string]json.RawMessage
	startValues map[string]json.RawMessage
	inputs      List[Input]
	time        Nat
	jobs        map[string]*runtimeJob
}

type CommitError struct{ Cause error }

func (e *CommitError) Error() string { return "persist workflow: " + e.Cause.Error() }
func (e *CommitError) Unwrap() error { return e.Cause }

func (r *workflowRuntime) now() Nat { return maxNat(maxNat(r.options.Now(), r.state.Now), r.time) }
func (r *workflowRuntime) binding(path Path, node string) (Binding, Path) {
	f := r.state.Frame(path)
	definition := append(slices.Clone(f.Definition), node)
	return r.bindings[Identity(definition)], definition
}
func (r *workflowRuntime) publish(settled bool, err error) {
	r.execution.mu.Lock()
	defer r.execution.mu.Unlock()
	r.execution.view = &runtimeView{r.state, Snapshot{r.graph, r.events, r.values}}
	r.execution.settled = settled
	r.execution.err = err
	close(r.execution.changed)
	r.execution.changed = make(chan struct{})
}
func (r *workflowRuntime) loop() {
	var finalError error
	ticker := time.NewTicker(r.options.PollInterval)
	defer func() {
		ticker.Stop()
		if p := recover(); p != nil {
			finalError = fmt.Errorf("workflow runtime: %v", p)
		}
		for _, job := range r.jobs {
			job.cancel()
		}
		r.publish(true, finalError)
		close(r.execution.done)
	}()
	for {
		select {
		case <-r.ctx.Done():
			if terminal(r.state.Status) {
				if r.state.Status == "cancelled" {
					finalError = ErrCancelled
				}
				return
			}
			if err := r.apply(Op{Kind: "cancel"}, nil); err != nil {
				finalError = err
				return
			}
			finalError = errors.Join(ErrCancelled, r.ctx.Err())
			return
		case <-r.execution.stop:
			if !terminal(r.state.Status) {
				finalError = ErrStopped
			} else if r.state.Status == "cancelled" {
				finalError = ErrCancelled
			}
			return
		default:
		}
		// A ready worker message is handled before scheduling more model work.
		select {
		case m := <-r.execution.requests:
			if err := r.handle(m); err != nil {
				finalError = err
				return
			}
		default:
		}
		if terminal(r.state.Status) {
			var err error
			if r.state.Status == "cancelled" {
				err = ErrCancelled
			}
			r.publish(true, err)
			select {
			case <-r.ctx.Done():
			case <-r.execution.stop:
			case m := <-r.execution.requests:
				if e := r.handle(m); e != nil {
					finalError = e
					return
				}
			}
			continue
		}
		progress, err := r.advance()
		if err != nil {
			finalError = err
			return
		}
		if progress {
			continue
		}
		waitTick := ticker.C
		if stalled := r.stalledError(); stalled != nil {
			if r.stall == nil {
				r.stall = stalled
				r.publish(true, stalled)
			}
			waitTick = nil
		}
		if !r.hasTimedWork() && (len(r.jobs) == 0 || !r.hasActiveJobs() && !r.state.HasWork()) {
			next, rejected := r.probe(Op{Kind: "idle"})
			if rejected != nil {
				finalError = rejected
				return
			}
			if !equal(next, r.state) {
				if err := r.apply(Op{Kind: "idle"}, nil); err != nil {
					finalError = err
					return
				}
				continue
			}
			if r.state.Status == "blocked" {
				r.publish(true, fmt.Errorf("%w: %s", ErrBlocked, value(r.state.Reason, "DEPENDENCIES_UNRESOLVED")))
				waitTick = nil
			} else {
				finalError = fmt.Errorf("no executable operation for nonterminal state")
				return
			}
		}
		if err := r.wait(waitTick); err != nil {
			finalError = err
			return
		}
	}
}
func (r *workflowRuntime) hasTimedWork() bool {
	return anyOf(r.state.Instances, func(i Instance) bool {
		return i.Status == "running" && i.Lease != nil || i.Status == "retryWait" && i.RetryAt != nil
	})
}

func (r *workflowRuntime) hasActiveJobs() bool {
	for _, job := range r.jobs {
		if job.obsolete {
			continue
		}
		if job.kind == "decision" {
			return true
		}
		i := r.state.Instance(job.auth.Instance)
		if i != nil && i.Status == "running" && i.Lease != nil && i.Lease.Attempt == job.auth.Attempt {
			return true
		}
	}
	return false
}
func (r *workflowRuntime) slot() bool {
	return r.options.Workers == 0 || len(r.jobs) < r.options.Workers
}

func (r *workflowRuntime) abandon(job *runtimeJob) {
	job.obsolete = true
	if job.staleAt == nil {
		now := r.now()
		job.staleAt = &now
	}
	job.cancel()
}

func (r *workflowRuntime) stalledError() *WorkerStalledError {
	if !r.needsSlot || r.slot() || r.hasActiveJobs() {
		return nil
	}
	now := r.now()
	stalled := &WorkerStalledError{Workers: r.options.Workers}
	for _, job := range r.jobs {
		if job.staleAt == nil || now.Cmp(job.staleAt.Add(r.options.StaleGraceSeconds)) < 0 {
			return nil
		}
		stalled.Handlers = append(stalled.Handlers, StalledHandler{
			Node: job.scope.Node, Path: slices.Clone(job.scope.Path), Definition: slices.Clone(job.scope.Definition),
			Instance: job.auth.Instance, Attempt: job.auth.Attempt, Since: *job.staleAt, Deadline: job.staleAt.Add(r.options.StaleGraceSeconds),
		})
	}
	slices.SortFunc(stalled.Handlers, func(a, b StalledHandler) int {
		return strings.Compare(Identity(append(slices.Clone(a.Path), a.Node, a.Attempt)), Identity(append(slices.Clone(b.Path), b.Node, b.Attempt)))
	})
	return stalled
}

// apply prepares state and payloads, persists the transaction, then publishes.
// Workers never mutate State or the payload store directly.
func (r *workflowRuntime) apply(op Op, provided map[string]json.RawMessage) error {
	txn := r.ids.transaction.peek()
	recordedAt := r.time
	if opTime(op) == nil {
		recordedAt = r.now()
	}
	next, events, rejected := RecordTransaction(r.state, []Op{op}, natLen(r.events).Inc(), txn, recordedAt)
	if rejected != nil {
		return rejected
	}
	if r.options.Oracle != nil && !OracleConforms(*r.options.Oracle, r.state, op) {
		return reject("ORACLE_MISMATCH", op.Kind)
	}
	absorbed := r.state.duplicateComplete(op) || terminal(r.state.Status) && r.state.authorized(op)
	if absorbed {
		provided = nil
	}
	newValues := map[string]json.RawMessage{}
	put := func(id string, data json.RawMessage) error {
		old, ok := r.values[id]
		if !ok {
			old, ok = newValues[id]
		}
		if ok {
			if !sameValues(old, data) {
				return reject("NONDETERMINISTIC_VALUE", id)
			}
			return nil
		}
		newValues[id] = slices.Clone(data)
		return nil
	}
	for id, data := range provided {
		if err := put(id, data); err != nil {
			return err
		}
	}
	materialized := map[string]json.RawMessage{}
	if !absorbed {
		var err error
		materialized, err = r.materialize(op)
		if err != nil {
			return err
		}
	}
	for id, data := range materialized {
		if err := put(id, data); err != nil {
			return err
		}
	}
	for _, id := range stateItemIDs(next) {
		_, existing := r.values[id]
		if _, added := newValues[id]; !existing && !added {
			return reject("MISSING_VALUE", id)
		}
	}
	values := r.values
	if len(newValues) > 0 {
		values = maps.Clone(r.values)
		maps.Copy(values, newValues)
	}
	journal := append(r.events, events...)
	snapshot := Snapshot{r.graph, journal, values}
	ctx := r.ctx
	if op.Kind == "cancel" {
		ctx = context.WithoutCancel(ctx)
	}
	if r.options.Append != nil {
		if err := r.options.Append(ctx, CommitBatch{copyEvents(events), copyValues(newValues)}); err != nil {
			return &CommitError{err}
		}
	}
	if r.options.Commit != nil {
		copy, err := copySnapshot(snapshot)
		if err != nil {
			return err
		}
		if err := r.options.Commit(ctx, copy); err != nil {
			return &CommitError{err}
		}
	}
	r.state = next
	r.events = journal
	r.values = values
	r.stall = nil
	r.time = journal[len(journal)-1].RecordedAt
	r.ids.transaction.used[txn] = true
	if op.Kind == "claim" && !absorbed {
		r.ids.attempt.used[op.Auth.Attempt] = true
		r.ids.token.used[op.Auth.Token] = true
	}
	for _, j := range r.jobs {
		if terminal(r.state.Status) {
			r.abandon(j)
			continue
		}
		if j.kind == "decision" && !j.obsolete {
			next, rejected := r.probe(j.op)
			if rejected != nil || equal(next, r.state) {
				r.abandon(j)
			}
		}
		if j.kind == "leaf" {
			i := r.state.Instance(j.auth.Instance)
			if i == nil || i.Status != "running" || i.Lease == nil || i.Lease.Attempt != j.auth.Attempt {
				r.abandon(j)
			}
		}
	}
	r.publish(false, nil)
	return nil
}

func (r *workflowRuntime) materialize(op Op) (map[string]json.RawMessage, error) {
	result := map[string]json.RawMessage{}
	load := func(id string) (json.RawMessage, error) {
		v, ok := r.values[id]
		if !ok {
			return nil, reject("MISSING_VALUE", id)
		}
		return v, nil
	}
	switch op.Kind {
	case "fireWaitAll":
		n := r.state.Node(op.Path, op.Node)
		inputs, rejected := r.state.plainInputs(op.Path, *n)
		if rejected != nil {
			return nil, rejected
		}
		record := map[string]json.RawMessage{}
		keys := []string{}
		for _, in := range inputs {
			v, err := load(in[1])
			if err != nil {
				return nil, err
			}
			record[in[0]] = v
			keys = append(keys, Identity(in[:]))
		}
		data, err := encodeData(record)
		if err != nil {
			return nil, err
		}
		result[DerivedItem("record", op.Path, op.Node, keys)] = data
	case "fireCollect":
		items := r.state.Incoming(op.Path, op.Node)[0].Items()
		slices.Sort(items)
		vs := []json.RawMessage{}
		for _, id := range items {
			v, err := load(id)
			if err != nil {
				return nil, err
			}
			vs = append(vs, v)
		}
		data, err := encodeData(vs)
		if err != nil {
			return nil, err
		}
		result[DerivedItem("list", op.Path, op.Node, items)] = data
	case "fireMerge":
		v, err := load(op.Item)
		if err != nil {
			return nil, err
		}
		result[DerivedItem("merge", op.Path, op.Node, []string{op.Edge, op.Item})] = v
	}
	return result, nil
}

func (r *workflowRuntime) advance() (bool, error) {
	r.needsSlot = false
	if !r.state.Started {
		return true, r.apply(Op{Kind: "start", Inputs: r.inputs}, r.startValues)
	}
	now := r.now()
	for _, i := range r.state.Instances {
		if i.Status == "running" && i.Lease != nil && i.Lease.Until.Cmp(now) <= 0 {
			return true, r.apply(Op{Kind: "expireLease", Inst: i.ID, Now: now}, nil)
		}
		if i.Status == "retryWait" && i.RetryAt != nil && i.RetryAt.Cmp(now) <= 0 {
			return true, r.apply(Op{Kind: "promoteRetry", Inst: i.ID, Now: now}, nil)
		}
		if i.Status == "running" {
			if at := r.renewAt(i); at != nil && now.Cmp(*at) >= 0 {
				a := Credentials{i.ID, i.Lease.Attempt, i.Lease.Token, now}
				return true, r.apply(Op{Kind: "renew", Auth: a}, nil)
			}
		}
	}
	// Rotate through eligible controls and claims so a fast producer cannot
	// keep spawning at the expense of already-ready downstream work.
	candidates := List[Op]{}
	for _, f := range r.state.Frames {
		if !f.Closed {
			for _, n := range f.Graph.Nodes {
				candidates = append(candidates, nodeCandidates(r.state, f.Path, n)...)
			}
		}
	}
	for _, i := range r.state.Instances {
		if i.Status == "waitingInputs" {
			candidates = append(candidates, Op{Kind: "finishSubworkflow", Inst: i.ID}, Op{Kind: "loopIterate", Inst: i.ID, Done: true})
		}
		if i.Status == "ready" {
			auth := r.credentials(i)
			candidates = append(candidates, Op{Kind: "claim", Auth: auth, Worker: "local"})
		}
	}
	for offset := 0; offset < len(candidates); offset++ {
		idx := (r.cursor + offset) % len(candidates)
		op := candidates[idx]
		next, rejected := r.probe(op)
		if rejected != nil {
			if rejected.Code == "INVARIANT" {
				return false, rejected
			}
			continue
		}
		if equal(next, r.state) {
			continue
		}
		if (op.Kind == "claim" || op.Kind == "fireBranch" || op.Kind == "fireFilter" || op.Kind == "loopIterate") && !r.slot() {
			r.needsSlot = true
			continue
		}
		if op.Kind == "fireBranch" || op.Kind == "fireFilter" || op.Kind == "loopIterate" {
			if !r.startDecision(op) {
				continue
			}
			r.cursor = (idx + 1) % len(candidates)
			return true, nil
		}
		if err := r.apply(op, nil); err != nil {
			return false, err
		}
		r.cursor = (idx + 1) % len(candidates)
		if op.Kind == "claim" {
			return true, r.startLeaf(*r.state.Instance(op.Auth.Instance), op.Auth)
		}
		return true, nil
	}
	return false, nil
}

func (r *workflowRuntime) post(m runMessage) {
	select {
	case r.execution.requests <- m:
	case <-r.execution.done:
	}
}
func (r *workflowRuntime) startLeaf(i Instance, auth Credentials) error {
	current := auth
	current.Now = r.now()
	if !r.state.validLease(current) {
		return nil
	}
	binding, definition := r.binding(i.Path, i.Node)
	ctx, cancel := context.WithCancel(r.ctx)
	inputs := map[string]json.RawMessage{}
	for _, in := range i.Inputs {
		v, ok := r.values[in[1]]
		if !ok {
			cancel()
			return reject("MISSING_VALUE", in[1])
		}
		inputs[in[0]] = slices.Clone(v)
	}
	task := &Task{ID: i.ID, Node: i.Node, Path: slices.Clone(i.Path), Definition: definition, Attempt: i.AttemptCount, Inputs: inputs, auth: auth, node: i.Node, path: slices.Clone(i.Path), execution: r.execution, ctx: ctx}
	r.jobs[auth.Attempt] = &runtimeJob{kind: "leaf", auth: auth, instance: i, cancel: cancel, scope: DecisionTask{Node: i.Node, Path: slices.Clone(i.Path), Definition: slices.Clone(definition)}}
	go func() {
		m := runMessage{kind: "finish", job: auth.Attempt}
		defer func() {
			task.closed.Store(true)
			if p := recover(); p != nil {
				m.err = &TaskError{Code: "HANDLER_PANIC", Cause: fmt.Errorf("%v", p)}
			}
			r.post(m)
		}()
		outputs, err := binding.Leaf(ctx, task)
		if err != nil {
			m.err = err
			return
		}
		m.outputs = map[string]json.RawMessage{}
		for port, v := range outputs {
			data, err := encodeData(v)
			if err != nil {
				m.err = &TaskError{Code: "INVALID_VALUE", Cause: err}
				return
			}
			m.outputs[port] = data
		}
	}()
	return nil
}

func (r *workflowRuntime) startDecision(op Op) bool {
	if !r.slot() {
		return false
	}
	node, path, item, iteration := op.Node, op.Path, op.Item, Nat{}
	if op.Kind == "fireBranch" {
		inputs, _ := r.state.plainInputs(path, *r.state.Node(path, node))
		item = inputs[0][1]
	}
	if op.Kind == "loopIterate" {
		i := r.state.Instance(op.Inst)
		node, path, iteration = i.Node, i.Path, i.Iteration
		f, _ := r.state.CurrentFrame(*i)
		items, _ := r.state.bodyResults(f)
		item = items[0]
	}
	key := Identity([]string{"decision", op.Kind, Identity(path), node, item, iteration.String()})
	if _, pending := r.jobs[key]; pending {
		return false
	}
	binding, definition := r.binding(path, node)
	task := DecisionTask{node, slices.Clone(path), definition, iteration, DataItem{item, slices.Clone(r.values[item])}}
	ctx, cancel := context.WithCancel(r.ctx)
	scope := task
	scope.Path, scope.Definition, scope.Item.Value = slices.Clone(task.Path), slices.Clone(task.Definition), nil
	r.jobs[key] = &runtimeJob{kind: "decision", op: op, cancel: cancel, scope: scope}
	go func() {
		m := runMessage{kind: "decision", job: key}
		defer func() {
			if p := recover(); p != nil {
				m.err = fmt.Errorf("decision callback panic: %v", p)
			}
			r.post(m)
		}()
		switch op.Kind {
		case "fireBranch":
			m.arm, m.err = binding.Branch(ctx, task)
		case "fireFilter":
			m.choice, m.err = binding.Filter(ctx, task)
		case "loopIterate":
			m.choice, m.err = binding.Loop(ctx, task)
		}
	}()
	return true
}

func (r *workflowRuntime) handle(m runMessage) error {
	respond := func(err error) {
		if m.reply != nil {
			m.reply <- err
		}
	}
	if m.kind == "op" {
		err := r.apply(m.op, m.values)
		respond(err)
		var persistence *CommitError
		if errors.As(err, &persistence) {
			return err
		}
		return nil
	}
	job, ok := r.jobs[m.job]
	if !ok {
		respond(ErrTaskClosed)
		return nil
	}
	if m.kind == "emit" || m.kind == "renew" {
		m.op.Auth.Now = r.now()
		err := r.apply(m.op, m.values)
		respond(err)
		var persistence *CommitError
		if errors.As(err, &persistence) {
			return err
		}
		return nil
	}
	delete(r.jobs, m.job)
	defer job.cancel()
	if r.stall != nil {
		r.stall = nil
		r.publish(false, nil)
	}
	if job.obsolete || terminal(r.state.Status) {
		return nil
	}
	if m.kind == "decision" {
		wrap := func(err error) error {
			if err == nil {
				return nil
			}
			return &DecisionError{Node: job.scope.Node, Path: slices.Clone(job.scope.Path), Definition: slices.Clone(job.scope.Definition),
				Operation: job.op.Kind, Item: job.scope.Item.ID, Iteration: job.scope.Iteration, Cause: err}
		}
		if m.err != nil {
			return wrap(m.err)
		}
		op := job.op
		switch op.Kind {
		case "fireBranch":
			op.Arm = m.arm
		case "fireFilter":
			op.Keep = m.choice
		case "loopIterate":
			op.Done = m.choice
		}
		return wrap(r.apply(op, nil))
	}
	auth := job.auth
	auth.Now = r.now()
	if !r.state.validLease(auth) {
		return nil
	} // Abandoned or cancelled work cannot publish results.
	if m.err == nil {
		ports := make([]string, 0, len(m.outputs))
		for p := range m.outputs {
			ports = append(ports, p)
		}
		slices.Sort(ports)
		outputs := List[Output]{}
		values := map[string]json.RawMessage{}
		for _, port := range ports {
			id := PlainItemID(job.instance.Path, job.instance.Node, port)
			outputs = append(outputs, Output{port, List[string]{id}})
			values[id] = m.outputs[port]
		}
		err := r.apply(Op{Kind: "complete", Auth: auth, Outputs: outputs}, values)
		if err == nil {
			return nil
		}
		var rejected *Reject
		if !errors.As(err, &rejected) {
			return err
		}
		m.err = &TaskError{Code: rejected.Code, Cause: rejected}
	}
	failure := &TaskError{Code: "HANDLER_FAILED", Cause: m.err}
	var provided *TaskError
	if errors.As(m.err, &provided) {
		failure = provided
	}
	return r.apply(Op{Kind: "fail", Auth: auth, Code: failure.Code, Retryable: failure.Retryable}, nil)
}
