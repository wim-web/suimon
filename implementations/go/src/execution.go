package suimon

import (
	"encoding/json"
	"slices"
)

// ScopedOracle is the executable oracle contract from Suimon/Execution.lean.
// Functions must be total, deterministic, and free of external side effects.
type ScopedOracle struct {
	Leaf   func(Path, string, List[[2]string]) List[Output]
	Branch func(Path, string, string) string
	Filter func(Path, string, string) bool
	Loop   func(Path, string, Nat, string) bool
}

func permutation[T any](a, b []T) bool {
	if len(a) != len(b) {
		return false
	}
	counts := map[string]int{}
	for _, x := range a {
		counts[compact(x)]++
	}
	for _, x := range b {
		k := compact(x)
		if counts[k] == 0 {
			return false
		}
		counts[k]--
	}
	return true
}
func prescribedItems(outputs List[Output], port string) List[string] {
	for _, o := range outputs {
		if o.Port == port {
			return o.Items
		}
	}
	return nil
}

func OracleConforms(oracle ScopedOracle, s State, op Op) bool {
	if s.duplicateComplete(op) || terminal(s.Status) && s.authorized(op) {
		return true
	}
	switch op.Kind {
	case "emit":
		i := s.Instance(op.Auth.Instance)
		return i != nil && oracle.Leaf != nil && contains(prescribedItems(oracle.Leaf(slices.Clone(i.Path), i.Node, slices.Clone(i.Inputs)), op.Port), op.Item)
	case "complete":
		i := s.Instance(op.Auth.Instance)
		if i == nil || oracle.Leaf == nil {
			return false
		}
		n := s.Node(i.Path, i.Node)
		if n == nil {
			return false
		}
		expected := oracle.Leaf(slices.Clone(i.Path), i.Node, slices.Clone(i.Inputs))
		plain := filter(expected, func(o Output) bool {
			return anyOf(n.Outputs, func(p Port) bool { return p.Name == o.Port && p.Kind == "plain" })
		})
		return permutation(op.Outputs, plain) && all(filter(n.Outputs, func(p Port) bool { return p.Kind == "stream" }), func(p Port) bool {
			return all(s.Outgoing(i.Path, i.Node, p.Name), func(c Channel) bool { return permutation(c.Items(), prescribedItems(expected, p.Name)) })
		})
	case "fireBranch":
		cs := s.Incoming(op.Path, op.Node)
		return len(cs) > 0 && len(cs[0].PendingItems()) > 0 && oracle.Branch != nil && op.Arm == oracle.Branch(slices.Clone(op.Path), op.Node, cs[0].PendingItems()[0])
	case "fireFilter":
		return oracle.Filter != nil && op.Keep == oracle.Filter(slices.Clone(op.Path), op.Node, op.Item)
	case "loopIterate":
		i := s.Instance(op.Inst)
		if i == nil || oracle.Loop == nil {
			return false
		}
		f, r := s.CurrentFrame(*i)
		if r != nil {
			return false
		}
		items, r := s.frameOutputItems(f)
		return r == nil && len(items) > 0 && op.Done == oracle.Loop(slices.Clone(i.Path), i.Node, i.Iteration, items[0])
	}
	return true
}

type ChannelBag struct {
	Channel string
	Items   List[string]
}

func (b ChannelBag) MarshalJSON() ([]byte, error) { return json.Marshal([]any{b.Channel, b.Items}) }
func ChannelBags(s State) List[ChannelBag] {
	result := mapped(s.Channels, func(c Channel) ChannelBag { items := c.Items(); slices.Sort(items); return ChannelBag{c.ID, items} })
	slices.SortFunc(result, func(a, b ChannelBag) int {
		if a.Channel < b.Channel {
			return -1
		}
		if a.Channel > b.Channel {
			return 1
		}
		return 0
	})
	return result
}
func SucceededDrained(s State) bool {
	return s.Status == "succeeded" && all(s.Channels, func(c Channel) bool { return c.Closed() && (len(c.Path) == 0 && c.Exit || len(c.PendingItems()) == 0) }) && all(s.Frames, func(f Frame) bool { return len(f.Path) == 0 || f.Closed })
}
