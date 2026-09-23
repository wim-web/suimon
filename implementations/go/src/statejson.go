package suimon

// The JSON form of a state, as Lean's derived ToJson renders it: structure fields under their
// Lean names, an absent Option as null, a constructor without arguments as its name, and a
// constructor with arguments as {"ctor": {"arg": value}}.

// MarshalJSON renders the state as (toJson state).compress does in Lean, byte for byte: the output
// of the Lean CLI's check --state.
func (s *State) MarshalJSON() ([]byte, error) {
	return []byte(stateWire(s).renderLean()), nil
}

func optionWire(v *string) wire {
	if v == nil {
		return wireNull()
	}
	return wireStr(*v)
}

func optionNatWire(v *uint64) wire {
	if v == nil {
		return wireNull()
	}
	return wireNat(*v)
}

func listWire[T any](xs []T, item func(T) wire) wire {
	items := make([]wire, len(xs))
	for i, x := range xs {
		items[i] = item(x)
	}
	return wireArr(items...)
}

func timeoutWire(t Timeout) wire {
	return wireObj(field("callMs", optionNatWire(t.CallMs)), field("elementMs", optionNatWire(t.ElementMs)))
}

func runWire(r Run) wire {
	return wireObj(field("path", pathWire(r.Path)), field("workflow", wireStr(r.Workflow)),
		field("input", optionWire(r.Input)), field("owner", optionWire(r.Owner)), field("task", optionWire(r.Task)),
		field("complete", wireBool(r.Complete)))
}

func invocationWire(i Invocation) wire {
	return wireObj(field("id", wireStr(i.ID)), field("run", pathWire(i.Run)), field("placement", wireStr(i.Placement)),
		field("trigger", optionWire(i.Trigger)), field("input", optionWire(i.Input)),
		field("status", wireStr(i.Status.String())), field("arm", optionWire(i.Arm)))
}

func callTargetWire(t CallTarget) wire {
	ctor := "function"
	if t.Judge {
		ctor = "judge"
	}
	return wireObj(field(ctor, wireObj(field("id", wireStr(t.ID)))))
}

func callWire(c Call) wire {
	return wireObj(field("id", wireStr(c.ID)), field("owner", wireStr(c.Owner)), field("task", optionWire(c.Task)),
		field("target", callTargetWire(c.Target)), field("input", optionWire(c.Input)), field("stream", wireBool(c.Stream)),
		field("status", wireStr(c.Status.String())), field("yields", wireInt(c.Yields)),
		field("timeout", timeoutWire(c.Timeout)), field("policy", wireStr(c.Policy.String())))
}

func taskStateWire(t TaskState) wire {
	return wireObj(field("name", wireStr(t.Name)), field("input", optionWire(t.Input)),
		field("status", wireStr(t.Status.String())))
}

func executionWire(e Execution) wire {
	return wireObj(field("id", wireStr(e.ID)), field("run", pathWire(e.Run)), field("placement", wireStr(e.Placement)),
		field("input", optionWire(e.Input)), field("tasks", listWire(e.Tasks, taskStateWire)),
		field("complete", wireBool(e.Complete)))
}

func taskOutputWire(o TaskOutput) wire {
	switch o.Kind {
	case TaskOutputValue:
		return wireObj(field("value", wireObj(field("v", wireStr(o.Value)))))
	case TaskOutputFailed:
		return wireStr("failed")
	}
	return wireStr("pending")
}

func taskResultWire(r TaskResult) wire {
	return wireObj(field("execution", wireStr(r.Execution)), field("task", wireStr(r.Task)),
		field("index", wireInt(r.Index)), field("value", wireStr(r.Value)), field("output", taskOutputWire(r.Output)))
}

func resultWire(r Result) wire {
	return wireObj(field("id", wireStr(r.ID)), field("run", pathWire(r.Run)), field("placement", wireStr(r.Placement)),
		field("producer", wireStr(r.Producer)), field("arm", optionWire(r.Arm)), field("value", wireStr(r.Value)))
}

func deliveredWire(d Delivered) wire {
	switch d.Kind {
	case DeliveredValue:
		return wireObj(field("value", wireObj(field("v", wireStr(d.Value)))))
	case DeliveredTrigger:
		return wireStr("trigger")
	}
	return wireStr("failed")
}

func deliveryWire(d Delivery) wire {
	return wireObj(field("run", pathWire(d.Run)), field("connection", wireInt(d.Connection)),
		field("source", wireStr(d.Source)), field("outcome", deliveredWire(d.Outcome)))
}

func settledWire(x Settled) wire {
	arms := listWire(x.Arms, func(a ArmOutcome) wire { return wireArr(wireStr(a.Arm), wireStr(a.Outcome.String())) })
	return wireObj(field("run", pathWire(x.Run)), field("placement", wireStr(x.Placement)),
		field("outcome", wireStr(x.Outcome.String())), field("arms", arms))
}

func failureWire(f Failure) wire {
	return wireObj(field("run", pathWire(f.Run)), field("placement", wireStr(f.Placement)),
		field("task", optionWire(f.Task)), field("cause", wireStr(f.Cause.String())))
}

func stateWire(s *State) wire {
	return wireObj(field("status", wireStr(s.Status.String())), field("started", wireBool(s.Started)),
		field("cancelled", wireBool(s.Cancelled)), field("runs", listWire(s.Runs, runWire)),
		field("invocations", listWire(s.Invocations, invocationWire)), field("calls", listWire(s.Calls, callWire)),
		field("executions", listWire(s.Executions, executionWire)), field("results", listWire(s.Results, resultWire)),
		field("taskResults", listWire(s.TaskResults, taskResultWire)),
		field("deliveries", listWire(s.Deliveries, deliveryWire)), field("settled", listWire(s.Settled, settledWire)),
		field("failures", listWire(s.Failures, failureWire)))
}
