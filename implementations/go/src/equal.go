package suimon

import "slices"

// Structural equality of states (Lean's derived DecidableEq). Explore uses it to drop operations
// that are accepted but change nothing; a nil list equals an empty one, as Lean has only [].

// Equal reports whether s and t are the same state.
func (s *State) Equal(t *State) bool {
	return s.Status == t.Status && s.Started == t.Started && s.Cancelled == t.Cancelled &&
		slices.EqualFunc(s.Runs, t.Runs, Run.equal) &&
		slices.EqualFunc(s.Invocations, t.Invocations, Invocation.equal) &&
		slices.EqualFunc(s.Calls, t.Calls, Call.equal) &&
		slices.EqualFunc(s.Executions, t.Executions, Execution.equal) &&
		slices.EqualFunc(s.Results, t.Results, Result.equal) &&
		slices.EqualFunc(s.TaskResults, t.TaskResults, TaskResult.equal) &&
		slices.EqualFunc(s.Deliveries, t.Deliveries, Delivery.equal) &&
		slices.EqualFunc(s.Settled, t.Settled, Settled.equal) &&
		slices.EqualFunc(s.Failures, t.Failures, Failure.equal)
}

func (r Run) equal(u Run) bool {
	return slices.Equal(r.Path, u.Path) && r.Workflow == u.Workflow && equalPtr(r.Input, u.Input) &&
		equalPtr(r.Owner, u.Owner) && equalPtr(r.Task, u.Task) && r.Complete == u.Complete
}

func (i Invocation) equal(j Invocation) bool {
	return i.ID == j.ID && slices.Equal(i.Run, j.Run) && i.Placement == j.Placement &&
		equalPtr(i.Trigger, j.Trigger) && equalPtr(i.Input, j.Input) && i.Status == j.Status &&
		equalPtr(i.Arm, j.Arm)
}

func (c Call) equal(d Call) bool {
	return c.ID == d.ID && c.Owner == d.Owner && equalPtr(c.Task, d.Task) && c.Target == d.Target &&
		equalPtr(c.Input, d.Input) && c.Stream == d.Stream && c.Status == d.Status && c.Yields == d.Yields &&
		c.Timeout.equal(d.Timeout) && c.Policy == d.Policy
}

func (t TaskState) equal(u TaskState) bool {
	return t.Name == u.Name && equalPtr(t.Input, u.Input) && t.Status == u.Status
}

func (e Execution) equal(f Execution) bool {
	return e.ID == f.ID && slices.Equal(e.Run, f.Run) && e.Placement == f.Placement &&
		equalPtr(e.Input, f.Input) && slices.EqualFunc(e.Tasks, f.Tasks, TaskState.equal) && e.Complete == f.Complete
}

func (r TaskResult) equal(u TaskResult) bool { return r == u }

func (r Result) equal(u Result) bool {
	return r.ID == u.ID && slices.Equal(r.Run, u.Run) && r.Placement == u.Placement && r.Producer == u.Producer &&
		equalPtr(r.Arm, u.Arm) && r.Value == u.Value
}

func (d Delivery) equal(e Delivery) bool {
	return slices.Equal(d.Run, e.Run) && d.Connection == e.Connection && d.Source == e.Source &&
		d.Outcome == e.Outcome
}

func (x Settled) equal(y Settled) bool {
	return slices.Equal(x.Run, y.Run) && x.Placement == y.Placement && x.Outcome == y.Outcome &&
		slices.Equal(x.Arms, y.Arms)
}

func (f Failure) equal(g Failure) bool {
	return slices.Equal(f.Run, g.Run) && f.Placement == g.Placement && equalPtr(f.Task, g.Task) &&
		f.Cause == g.Cause
}
