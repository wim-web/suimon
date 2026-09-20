package suimon

import (
	"encoding/json"
	"errors"
	"slices"
)

var ErrInvalidSnapshotCursor = errors.New("invalid snapshot cursor")

// SnapshotCursor identifies a committed data prefix in one Execution. It is
// independent of the scheduler-status ExecutionCursor and is not a checkpoint.
// Its zero value requests all data captured by an observation, including Graph.
type SnapshotCursor struct {
	execution *Execution
	events    int
	values    int
}

// EventCount is the length of the already received event prefix.
func (c SnapshotCursor) EventCount() int { return c.events }

// SnapshotDelta contains independent copies of the data after a SnapshotCursor.
// Append Events and merge Values into the previously received snapshot. Graph
// is only populated for a zero cursor. Empty Events and Values may be nil.
// Cursor advances only to this observation's immutable committed boundary.
type SnapshotDelta struct {
	Cursor SnapshotCursor
	Graph  *Graph
	Events List[Event]
	Values map[string]json.RawMessage
}

// EventCount reads the captured committed prefix length without copying data.
func (u ExecutionUpdate) EventCount() int {
	if u.view == nil {
		return 0
	}
	return len(u.view.snapshot.Events)
}

// SnapshotSince reads the committed suffix captured by Observe, not any commits
// published afterward. Work and allocation depend on the new events and values;
// an unchanged cursor takes O(1) with no allocation. The initial graph is copied
// once. SnapshotCursor belongs to this Execution; foreign/future cursors and a
// zero ExecutionUpdate return ErrInvalidSnapshotCursor. Restore starts a new
// cursor sequence, whose first delta includes the recovered committed baseline.
func (u ExecutionUpdate) SnapshotSince(after SnapshotCursor) (SnapshotDelta, error) {
	if u.view == nil || u.execution == nil ||
		after.events < 0 || after.values < 0 ||
		after.events > len(u.view.snapshot.Events) || after.values > len(u.view.valueIDs) ||
		(after.execution != nil && after.execution != u.execution) ||
		(after.execution == nil && (after.events != 0 || after.values != 0)) {
		return SnapshotDelta{}, ErrInvalidSnapshotCursor
	}
	v := u.view
	delta := SnapshotDelta{Cursor: SnapshotCursor{u.execution, len(v.snapshot.Events), len(v.valueIDs)}}
	if after.execution == nil {
		graph := cloneGraph(v.snapshot.Graph)
		delta.Graph = &graph
	}
	if after.events < len(v.snapshot.Events) {
		delta.Events = copyEvents(v.snapshot.Events[after.events:])
	}
	if after.values < len(v.valueIDs) {
		delta.Values = make(map[string]json.RawMessage, len(v.valueIDs)-after.values)
		for _, id := range v.valueIDs[after.values:] {
			delta.Values[id] = slices.Clone(v.snapshot.Values[id])
		}
	}
	return delta, nil
}

// Outputs copies only the exit-port results captured by this observation. It
// does not copy the graph, journal, value store or model state. Call it when an
// outcome is needed, rather than obtaining a full Result merely for its outputs.
func (u ExecutionUpdate) Outputs() List[ResultPort] {
	if u.view == nil {
		return nil
	}
	return copyResultPorts(u.view)
}
