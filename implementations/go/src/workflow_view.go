package suimon

import (
	"encoding/json"
	"slices"
	"sync/atomic"
)

// Published state, event prefixes, and value maps are immutable. Result copies
// them only when requested; wait notifications carry no serialized history.
type runtimeView struct {
	state    State
	snapshot Snapshot
}

// Internal counters let tests observe actual idle polls and candidate probes.
type runtimeMetrics struct {
	candidates atomic.Uint64
	polls      atomic.Uint64
	waits      atomic.Uint64
	results    atomic.Uint64
}

func copyPointer[T any](p *T) *T {
	if p == nil {
		return nil
	}
	return ptr(*p)
}

func copyPublicState(s State) State {
	s = cloneState(s)
	s.Reason = copyPointer(s.Reason)
	for n := range s.Channels {
		s.Channels[n].Path = slices.Clone(s.Channels[n].Path)
	}
	for n := range s.Instances {
		i := &s.Instances[n]
		i.Path, i.Inputs = slices.Clone(i.Path), slices.Clone(i.Inputs)
		i.Trigger, i.Lease, i.RetryAt = copyPointer(i.Trigger), copyPointer(i.Lease), copyPointer(i.RetryAt)
	}
	for n := range s.Frames {
		f := &s.Frames[n]
		f.Path, f.Definition = slices.Clone(f.Path), slices.Clone(f.Definition)
		f.Graph, f.Owner = cloneGraph(f.Graph), copyPointer(f.Owner)
	}
	for n := range s.Receipts {
		s.Receipts[n].Outputs = cloneOutputs(s.Receipts[n].Outputs)
	}
	return s
}

func copyOp(op Op) Op {
	op.Path = slices.Clone(op.Path)
	op.Inputs = slices.Clone(op.Inputs)
	for n := range op.Inputs {
		op.Inputs[n].Items = slices.Clone(op.Inputs[n].Items)
	}
	op.Outputs = cloneOutputs(op.Outputs)
	return op
}

func copyEvents(events List[Event]) List[Event] {
	events = slices.Clone(events)
	for n := range events {
		e := &events[n]
		e.Data = slices.Clone(e.Data)
		if e.Op != nil {
			e.Op = ptr(copyOp(*e.Op))
		}
	}
	return events
}

func copyValues(values map[string]json.RawMessage) map[string]json.RawMessage {
	copy := make(map[string]json.RawMessage, len(values))
	for id, data := range values {
		copy[id] = slices.Clone(data)
	}
	return copy
}

func (e *Execution) result(v *runtimeView) RunResult {
	e.metrics.results.Add(1)
	snapshot := Snapshot{cloneGraph(v.snapshot.Graph), copyEvents(v.snapshot.Events), copyValues(v.snapshot.Values)}
	ports := List[ResultPort]{}
	for _, p := range v.snapshot.Graph.Exits {
		out := ResultPort{Port: p}
		for _, c := range v.state.Channels {
			if len(c.Path) == 0 && c.Exit && c.Edge.Src == p {
				for _, id := range c.Items() {
					out.Items = append(out.Items, DataItem{id, slices.Clone(v.snapshot.Values[id])})
				}
			}
		}
		ports = append(ports, out)
	}
	return RunResult{copyPublicState(v.state), ports, snapshot}
}

func (e *Execution) observe() (*runtimeView, bool, error, <-chan struct{}) {
	e.mu.Lock()
	defer e.mu.Unlock()
	return e.view, e.settled, e.err, e.changed
}

func (e *Execution) read() (RunResult, bool, error, <-chan struct{}) {
	v, settled, err, changed := e.observe()
	return e.result(v), settled, err, changed
}
