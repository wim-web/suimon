package suimon

// Runtime IDs are independent of the explorer's longest-ID freshness witness.
// Peek does not reserve an ID: rejected candidate probes consume no numbers.
type idSequence struct {
	prefix string
	next   Nat
	used   map[string]bool
}

func (s *idSequence) peek() string {
	for s.used[s.prefix+s.next.String()] {
		s.next = s.next.Inc()
	}
	return s.prefix + s.next.String()
}

type runtimeIDs struct{ attempt, token, transaction idSequence }

func newRuntimeIDs(state State, events List[Event]) runtimeIDs {
	ids := runtimeIDs{
		attempt:     idSequence{"a:", natLen(state.Attempts).Inc(), map[string]bool{}},
		token:       idSequence{"l:", natLen(state.Attempts).Inc(), map[string]bool{}},
		transaction: idSequence{"tx:", N(1), map[string]bool{}},
	}
	for _, a := range state.Attempts {
		ids.attempt.used[a.ID] = true
		ids.token.used[a.Token] = true
	}
	for _, event := range events {
		if event.Type == "transaction.committed" {
			ids.transaction.used[event.Txn] = true
		}
	}
	ids.transaction.next = N(uint64(len(ids.transaction.used))).Inc()
	return ids
}

func (r *workflowRuntime) credentials(i Instance) Credentials {
	return Credentials{i.ID, r.ids.attempt.peek(), r.ids.token.peek(), r.now()}
}
