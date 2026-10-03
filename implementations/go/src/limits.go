package suimon

import (
	"errors"
	"fmt"
	"strings"
	"time"
)

// ErrQuotaExceeded identifies a host resource limit. For a running workflow, Wait returns
// both this error and a report after recording cancellation and waiting for callbacks to exit.
// The journal preserves the cancellation, not the host's error or limit configuration.
var ErrQuotaExceeded = errors.New("suimon: resource quota exceeded")

// Limits bounds one Engine and each Start/Resume on it. Zero fields use DefaultLimits;
// negative fields are invalid. Limits also apply without a journal and to unchecked engines.
// MaxWorkflows times the per-workflow budgets bounds aggregate engine work. Completed reports
// and journals retained by the host, callback allocations, and JSON encoding scratch space
// belong to the host; callbacks and synchronous transforms must return cooperatively.
type Limits struct {
	MaxWorkflows      int64         // Concurrent Start/Resume executions on this engine, including shutdown.
	MaxCalls          int64         // Active calls per workflow, including streams and cancelling calls.
	MaxExecutions     int64         // Total concurrency executions per workflow, including completed ones.
	MaxTasks          int64         // Total task entries across those executions, including waiting tasks.
	MaxStreamElements int64         // Accepted yields across all streams in a workflow.
	MaxPayloadBytes   int64         // Retained JSON and queued callback output bytes, including lists.
	MaxRecords        int64         // Journal lines after the header (operations and commits), even in memory.
	MaxJournalBytes   int64         // Encoded journal bytes including the header and shutdown records.
	MaxDuration       time.Duration // Time per Start/Resume session, excluding cooperative shutdown.
}

// DefaultLimits returns finite host defaults. Increase selected fields with WithLimits for
// workloads that need larger budgets. Record and byte budgets reserve room for cancellation,
// termination of every admitted call, and conclusion before accepting new work.
func DefaultLimits() Limits {
	return Limits{MaxWorkflows: 16, MaxCalls: 256, MaxExecutions: 4096, MaxTasks: 16384,
		MaxStreamElements: 10000, MaxPayloadBytes: 64 << 20, MaxRecords: 250000,
		MaxJournalBytes: 128 << 20, MaxDuration: 5 * time.Minute}
}

// EngineOption configures the host's execution policy, outside the workflow definition.
type EngineOption func(*Limits)

// WithLimits sets engine limits; each zero field keeps its default.
func WithLimits(l Limits) EngineOption { return func(dst *Limits) { *dst = l } }

func engineLimits(opts []EngineOption) (Limits, error) {
	l := DefaultLimits()
	for _, opt := range opts {
		opt(&l)
	}
	defaults := DefaultLimits()
	fields := []struct {
		p     *int64
		value int64
	}{
		{&l.MaxWorkflows, defaults.MaxWorkflows}, {&l.MaxCalls, defaults.MaxCalls},
		{&l.MaxExecutions, defaults.MaxExecutions}, {&l.MaxTasks, defaults.MaxTasks},
		{&l.MaxStreamElements, defaults.MaxStreamElements}, {&l.MaxPayloadBytes, defaults.MaxPayloadBytes},
		{&l.MaxRecords, defaults.MaxRecords}, {&l.MaxJournalBytes, defaults.MaxJournalBytes},
	}
	for _, f := range fields {
		if *f.p < 0 {
			return Limits{}, errors.New("suimon: resource limits must be positive")
		}
		if *f.p == 0 {
			*f.p = f.value
		}
	}
	if l.MaxDuration < 0 {
		return Limits{}, errors.New("suimon: MaxDuration must be positive")
	}
	if l.MaxDuration == 0 {
		l.MaxDuration = defaults.MaxDuration
	}
	return l, nil
}

func quota(resource string, limit int64) error {
	return fmt.Errorf("%w: %s (limit %d)", ErrQuotaExceeded, resource, limit)
}

func (e *Engine) acquire() error {
	e.mu.Lock()
	defer e.mu.Unlock()
	if e.active >= e.limits.MaxWorkflows {
		return quota("workflows", e.limits.MaxWorkflows)
	}
	e.active++
	return nil
}

func (e *Engine) release() { e.mu.Lock(); e.active--; e.mu.Unlock() }

const largestRecordSequence = int(^uint(0) >> 1)

// Engines use the default reader limits for both writing and Resume. A limit failure
// before admission uses the quota shutdown path, preserving a readable journal.
func checkJournalLine(line string) error {
	if err := (InputLimits{}).check(line); err != nil {
		return fmt.Errorf("%w: journal line: %w", ErrQuotaExceeded, err)
	}
	return nil
}

// shutdownBytes uses the largest sequence numbers, so the reserve remains sufficient even
// when normal work crosses a decimal digit boundary. All shutdown operations carry no values.
func shutdownBytes(op Op) int64 {
	return int64(len(EncodeRecord(Record{Seq: largestRecordSequence, Op: op})) +
		len(EncodeRecord(Record{Seq: largestRecordSequence, Commit: true})) + 2)
}

// A call must remain recordable when it is cancelled, even after sequence numbers
// grow. OpLost on Resume is shorter than this termination record.
func checkCallShutdown(call string) error {
	return checkJournalLine(EncodeRecord(Record{Seq: largestRecordSequence, Op: OpTerminated{Call: call}}))
}

func (d *driver) stopQuota(err error) {
	if d.quotaErr == nil {
		d.quotaErr = err
	}
	d.cancel()
}

// reservePayload is also called by callback goroutines before enqueueing an output. A full
// budget ends the producer; waiting here could deadlock streams and downstream calls.
func (d *driver) reservePayload(size int64) bool {
	for {
		used := d.payloadUsage.Load()
		if size > d.limits.MaxPayloadBytes-used {
			return false
		}
		if d.payloadUsage.CompareAndSwap(used, used+size) {
			return true
		}
	}
}

// payloadForAdmission builds a list only within the remaining payload budget. Nothing is
// retained until the operation and all resource checks succeed.
func (d *driver) payloadForAdmission(id string) (string, error) {
	if p, ok := d.payloads[id]; ok {
		return p, nil
	}
	remaining := d.limits.MaxPayloadBytes - d.payloadBytes
	if d.pending != nil && d.pending.Value == id {
		if int64(len(d.pending.Payload)) > remaining {
			return "", quota("payload bytes", d.limits.MaxPayloadBytes)
		}
		return d.pending.Payload, nil
	}
	parts, ok := DecodeIdentity(id)
	if !ok || len(parts) == 0 || parts[0] != "list" || Identity(parts...) != id {
		return "", fmt.Errorf("suimon: no payload for value %q", id)
	}
	var b strings.Builder
	if remaining < 2 {
		return "", quota("payload bytes", d.limits.MaxPayloadBytes)
	}
	b.WriteByte('[')
	for i, element := range parts[1:] {
		p, err := d.payloadForAdmission(element)
		if err != nil {
			return "", err
		}
		extra := int64(len(p))
		if i > 0 {
			extra++
		}
		if extra > remaining-int64(b.Len())-1 {
			return "", quota("payload bytes", d.limits.MaxPayloadBytes)
		}
		if i > 0 {
			b.WriteByte(',')
		}
		b.WriteString(p)
	}
	b.WriteByte(']')
	return b.String(), nil
}

// growth is called after Step has checked the operation and before it changes state.
func (d *driver) growth(op Op) (call string, executions, tasks int64) {
	switch op := op.(type) {
	case OpInvoke:
		pl := d.planOf(op.Run).placements[op.Placement].placement
		switch c := pl.Control.(type) {
		case CallControl:
			if !c.Body.Workflow {
				call = keyInvocation(op.Run, op.Placement, op.Trigger)
			}
		case BranchControl:
			call = keyInvocation(op.Run, op.Placement, op.Trigger)
		case ConcurrencyControl:
			executions, tasks = 1, int64(len(c.Spec.Tasks))
		}
	case OpBeginTask:
		e, _ := d.v.execution(op.Execution)
		spec, _ := d.v.taskSpec(d.definition, e, op.Task)
		if !spec.Body.Workflow {
			call = taskID(op.Execution, op.Task)
		}
	}
	return
}

func endingCall(op Op) string {
	switch op := op.(type) {
	case OpReturned:
		return op.Call
	case OpJudged:
		return op.Call
	case OpEnded:
		return op.Call
	case OpFailed:
		return op.Call
	case OpLost:
		return op.Call
	case OpTerminated:
		return op.Call
	}
	return ""
}

func (d *driver) admit(records []Record) error {
	op := records[0].Op
	call, executions, tasks := d.growth(op)
	calls, reserve := d.activeCalls, d.terminationBytes
	if call != "" {
		if err := checkCallShutdown(call); err != nil {
			return err
		}
		calls++
		reserve += shutdownBytes(OpTerminated{Call: call})
	}
	if id := endingCall(op); id != "" {
		calls--
		reserve -= shutdownBytes(OpTerminated{Call: id})
	}
	var payloadBytes int64
	for _, v := range records[0].Values {
		payloadBytes += int64(len(v.Payload))
	}
	var encoded []byte
	for _, r := range records {
		line := EncodeRecord(r)
		if err := checkJournalLine(line); err != nil {
			return err
		}
		encoded = append(encoded, line...)
		encoded = append(encoded, '\n')
	}
	_, cancel := op.(OpCancel)
	_, conclude := op.(OpConclude)
	if d.running() && !cancel && !conclude {
		checks := []struct {
			name               string
			used, added, limit int64
		}{
			{"active calls", calls, 0, d.limits.MaxCalls},
			{"executions", d.executions, executions, d.limits.MaxExecutions},
			{"tasks", d.taskCount, tasks, d.limits.MaxTasks},
			{"payload bytes", d.payloadBytes, payloadBytes, d.limits.MaxPayloadBytes},
			{"records", int64(d.recorder.seq - 1), 2 + 4 + 2*calls, d.limits.MaxRecords},
			{"journal bytes", d.journalBytes, int64(len(encoded)) + reserve + d.shutdownBytes, d.limits.MaxJournalBytes},
		}
		if _, yielded := op.(OpYielded); yielded {
			checks = append(checks, struct {
				name               string
				used, added, limit int64
			}{"stream elements", d.elements, 1, d.limits.MaxStreamElements})
		}
		for _, c := range checks {
			if c.used > c.limit || c.added > c.limit-c.used {
				return quota(c.name, c.limit)
			}
		}
		if !time.Now().Before(d.deadline) {
			return quota("duration nanoseconds", int64(d.limits.MaxDuration))
		}
	}
	if !d.reservePayload(payloadBytes) {
		return quota("payload bytes", d.limits.MaxPayloadBytes)
	}
	d.activeCalls, d.terminationBytes = calls, reserve
	d.executions += executions
	d.taskCount += tasks
	if _, yielded := op.(OpYielded); yielded {
		d.elements++
	}
	d.payloadBytes += payloadBytes
	d.journalBytes += int64(len(encoded))
	d.prepared = encoded
	return nil
}

// restoreBudget counts committed work too: restarting a workflow does not replenish its
// production, memory or journal allowance. Elapsed time starts a new session on Resume.
func (d *driver) restoreBudget(length int, values []Payload) error {
	d.journalBytes = int64(length)
	d.executions = int64(len(d.state.Executions))
	for _, e := range d.state.Executions {
		d.taskCount += int64(len(e.Tasks))
	}
	for _, c := range d.state.Calls {
		d.elements += int64(c.Yields)
		if !c.Status.ended() {
			if err := checkCallShutdown(c.ID); err != nil {
				return err
			}
			d.activeCalls++
			d.terminationBytes += shutdownBytes(OpTerminated{Call: c.ID})
		}
	}
	for _, v := range values {
		d.payloadBytes += int64(len(v.Payload))
	}
	d.payloadUsage.Store(d.payloadBytes)
	checks := []struct {
		name        string
		used, limit int64
	}{
		{"active calls", d.activeCalls, d.limits.MaxCalls},
		{"executions", d.executions, d.limits.MaxExecutions},
		{"tasks", d.taskCount, d.limits.MaxTasks},
		{"stream elements", d.elements, d.limits.MaxStreamElements},
		{"payload bytes", d.payloadBytes, d.limits.MaxPayloadBytes},
		{"records", int64(d.recorder.seq - 1), d.limits.MaxRecords},
		{"journal bytes", d.journalBytes, d.limits.MaxJournalBytes},
	}
	if !d.state.Status.Terminal() {
		checks[5].used += 4 + 2*d.activeCalls
		checks[6].used += d.shutdownBytes + d.terminationBytes
		if d.state.Cancelled {
			checks[5].used -= 2
			checks[6].used -= shutdownBytes(OpCancel{})
		}
	}
	for _, c := range checks {
		if c.used > c.limit {
			return quota(c.name, c.limit)
		}
	}
	return nil
}
