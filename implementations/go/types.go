// Package suimon implements the executable Suimon Lean specification in pure Go.
// The correspondence to the Lean sources is checked by bin/test-go.
package suimon

import (
	"encoding/json"
	"fmt"
)

type Port struct {
	Name string `json:"name"`
	Kind string `json:"kind"`
}
type PortRef struct {
	Node string `json:"node"`
	Port string `json:"port"`
}
type RetryPolicy struct {
	MaxAttempts  Nat `json:"maxAttempts"`
	LeaseSeconds Nat `json:"leaseSeconds"`
	RetrySeconds Nat `json:"retrySeconds"`
}
type Edge struct {
	Src PortRef `json:"src"`
	Dst PortRef `json:"dst"`
}
type NodeKind struct {
	Type          string
	Retry         RetryPolicy
	Concurrency   Nat
	Arms          List[string]
	Body          *Graph
	MaxIterations Nat
}

func (k NodeKind) MarshalJSON() ([]byte, error) {
	v := map[string]any{"type": k.Type}
	switch k.Type {
	case "leaf":
		v["retry"] = k.Retry
		v["concurrency"] = k.Concurrency
	case "branch":
		v["arms"] = k.Arms
	case "loop":
		v["body"] = k.Body
		v["maxIterations"] = k.MaxIterations
	case "subworkflow", "forEach":
		v["body"] = k.Body
	case "waitAll", "coalesce", "collect", "filter", "merge":
	default:
		return nil, fmt.Errorf("unknown node kind: %s", k.Type)
	}
	return json.Marshal(v)
}
func (k *NodeKind) UnmarshalJSON(b []byte) error {
	var v struct {
		Type          string       `json:"type"`
		Retry         RetryPolicy  `json:"retry"`
		Concurrency   Nat          `json:"concurrency"`
		Arms          List[string] `json:"arms"`
		Body          *Graph       `json:"body"`
		MaxIterations Nat          `json:"maxIterations"`
	}
	if err := json.Unmarshal(b, &v); err != nil {
		return err
	}
	*k = NodeKind{v.Type, v.Retry, v.Concurrency, v.Arms, v.Body, v.MaxIterations}
	_, err := k.MarshalJSON()
	return err
}

type Node struct {
	ID      string     `json:"id"`
	Kind    NodeKind   `json:"kind"`
	Inputs  List[Port] `json:"inputs"`
	Outputs List[Port] `json:"outputs"`
}
type Graph struct {
	Nodes   List[Node]    `json:"nodes"`
	Edges   List[Edge]    `json:"edges"`
	Entries List[PortRef] `json:"entries"`
	Exits   List[PortRef] `json:"exits"`
}
type Path = List[string]

// Token has either an Item or EOS=true. Item's empty string is a valid ID.
type Token struct {
	Item string
	EOS  bool
}

func (t Token) MarshalJSON() ([]byte, error) {
	if t.EOS {
		return json.Marshal("eos")
	}
	return json.Marshal(map[string]any{"item": map[string]string{"id": t.Item}})
}
func (t *Token) UnmarshalJSON(b []byte) error {
	var tag string
	if json.Unmarshal(b, &tag) == nil && tag == "eos" {
		*t = Token{EOS: true}
		return nil
	}
	var v struct {
		Item *struct {
			ID string `json:"id"`
		} `json:"item"`
	}
	if err := json.Unmarshal(b, &v); err != nil {
		return err
	}
	if v.Item == nil {
		return fmt.Errorf("invalid token")
	}
	*t = Token{Item: v.Item.ID}
	return nil
}

type Channel struct {
	ID       string      `json:"id"`
	Edge     Edge        `json:"edge"`
	Path     Path        `json:"path"`
	Kind     string      `json:"kind"`
	Entry    bool        `json:"entry"`
	Exit     bool        `json:"exit"`
	Placed   List[Token] `json:"placed"`
	Consumed Nat         `json:"consumed"`
}
type Lease struct {
	Attempt string `json:"attempt"`
	Token   string `json:"token"`
	Until   Nat    `json:"until_"`
}
type Instance struct {
	ID              string          `json:"id"`
	Node            string          `json:"node"`
	Path            Path            `json:"path"`
	Trigger         *string         `json:"trigger"`
	Status          string          `json:"status"`
	AttemptCount    Nat             `json:"attemptCount"`
	Lease           *Lease          `json:"lease"`
	RetryAt         *Nat            `json:"retryAt"`
	Iteration       Nat             `json:"iteration"`
	ExtraAttempts   Nat             `json:"extraAttempts"`
	ExtraIterations Nat             `json:"extraIterations"`
	Inputs          List[[2]string] `json:"inputs"`
}
type Attempt struct {
	ID       string `json:"id"`
	Instance string `json:"instance"`
	No       Nat    `json:"no"`
	Status   string `json:"status"`
	Token    string `json:"token"`
	Worker   string `json:"worker"`
}
type Frame struct {
	Path       Path         `json:"path"`
	Graph      Graph        `json:"graph"`
	Definition List[string] `json:"definition"`
	Owner      *string      `json:"owner"`
	Closed     bool         `json:"closed"`
}
type Consumption struct {
	Channel    string `json:"channel"`
	Index      Nat    `json:"index"`
	Item       string `json:"item"`
	ByInstance string `json:"byInstance"`
}
type Output struct {
	Port  string       `json:"port"`
	Items List[string] `json:"items"`
}
type Receipt struct {
	Instance string       `json:"instance"`
	Attempt  string       `json:"attempt"`
	Token    string       `json:"token"`
	Outputs  List[Output] `json:"outputs"`
}
type Decision struct {
	Key   string `json:"key"`
	Value string `json:"value"`
}
type State struct {
	Status    string            `json:"status"`
	Channels  List[Channel]     `json:"channels"`
	Instances List[Instance]    `json:"instances"`
	Attempts  List[Attempt]     `json:"attempts"`
	Frames    List[Frame]       `json:"frames"`
	Consumed  List[Consumption] `json:"consumed"`
	Receipts  List[Receipt]     `json:"receipts"`
	Decisions List[Decision]    `json:"decisions"`
	Now       Nat               `json:"now"`
	Started   bool              `json:"started"`
	Reason    *string           `json:"reason"`
}
type Credentials struct {
	Instance string `json:"instance"`
	Attempt  string `json:"attempt"`
	Token    string `json:"token"`
	Now      Nat    `json:"now"`
}
type Input struct {
	Entry PortRef      `json:"entry"`
	Items List[string] `json:"items"`
}
type Reject struct {
	Code    string `json:"code"`
	Message string `json:"message"`
}

func (r *Reject) Error() string { return r.Code + ": " + r.Message }
func reject(code string, msg ...string) *Reject {
	text := code
	if len(msg) > 0 {
		text = msg[0]
	}
	return &Reject{code, text}
}

// Op represents the 23 constructors in Suimon/Op.lean. Only fields belonging
// to Kind are serialized; the JSON encoding matches Lean's derived codec.
type Op struct {
	Kind      string
	Inputs    List[Input]
	Path      Path
	Node      string
	Item      string
	Auth      Credentials
	Worker    string
	Inst      string
	Now       Nat
	Port      string
	Outputs   List[Output]
	Code      string
	Retryable bool
	Arm       string
	Edge      string
	Keep      bool
	Done      bool
}

func (o Op) MarshalJSON() ([]byte, error) {
	if o.Kind == "idle" || o.Kind == "cancel" {
		return json.Marshal(o.Kind)
	}
	v := map[string]any{}
	switch o.Kind {
	case "start":
		v["inputs"] = o.Inputs
	case "activate", "spawn", "fireWaitAll", "fireBranch", "fireCoalesce", "fireCollect", "fireFilter", "fireMerge", "propagateEos", "skip":
		v["path"] = o.Path
		v["node"] = o.Node
		switch o.Kind {
		case "spawn":
			v["item"] = o.Item
		case "fireBranch":
			v["arm"] = o.Arm
		case "fireCoalesce", "fireMerge":
			v["edge"] = o.Edge
			v["item"] = o.Item
		case "fireFilter":
			v["item"] = o.Item
			v["keep"] = o.Keep
		}
	case "claim", "renew", "emit", "complete", "fail":
		v["auth"] = o.Auth
		switch o.Kind {
		case "claim":
			v["worker"] = o.Worker
		case "emit":
			v["port"] = o.Port
			v["item"] = o.Item
		case "complete":
			v["outputs"] = o.Outputs
		case "fail":
			v["code"] = o.Code
			v["retryable"] = o.Retryable
		}
	case "expireLease", "promoteRetry", "finishSubworkflow", "loopIterate", "manualRetry":
		v["inst"] = o.Inst
		switch o.Kind {
		case "expireLease", "promoteRetry":
			v["now"] = o.Now
		case "loopIterate":
			v["done"] = o.Done
		}
	default:
		return nil, fmt.Errorf("unknown operation: %s", o.Kind)
	}
	return json.Marshal(map[string]any{o.Kind: v})
}
func (o *Op) UnmarshalJSON(b []byte) error {
	var tag string
	if json.Unmarshal(b, &tag) == nil {
		if tag != "idle" && tag != "cancel" {
			return fmt.Errorf("unknown operation: %s", tag)
		}
		*o = Op{Kind: tag}
		return nil
	}
	var variants map[string]json.RawMessage
	if err := json.Unmarshal(b, &variants); err != nil {
		return err
	}
	if len(variants) != 1 {
		return fmt.Errorf("expected one operation constructor")
	}
	for kind, raw := range variants {
		// Lowercase JSON field names match these exported fields case-insensitively.
		type fields Op
		var f fields
		if err := json.Unmarshal(raw, &f); err != nil {
			return err
		}
		*o = Op(f)
		o.Kind = kind
		if kind == "idle" || kind == "cancel" {
			return fmt.Errorf("expected operation string")
		}
		if _, err := o.MarshalJSON(); err != nil {
			return err
		}
	}
	return nil
}
func ParseOp(b []byte) (Op, error) { var o Op; err := decodeCanonical(b, &o); return o, err }
