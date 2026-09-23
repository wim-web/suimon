// Package suimon is the Go implementation of the suimon workflow engine. The control semantics
// are defined in Lean (Suimon/*.lean at the repository root). The model part of this package
// ports each Lean declaration under the same name, so that the two can be read side by side: the
// program and its validation, the state and Step, exploration, and the execution record (Recorder,
// Check).
//
// The runtime runs a program with Go functions: NewRegistry binds the functions, judges and
// transforms the program names, NewEngine checks the program and the bindings, and Engine.Start,
// Run and Resume drive executions with Step, recording each accepted operation in a Journal
// before publishing its effects.
package suimon

import "strings"

// ValueType is a type name wrapped in List zero or more times (Lean ValueType): the engine never
// looks inside values, so a type is compared only by its name and structure.
type ValueType struct {
	Name string
	// Lists is the number of List wrappers: List<List<T>> is {Name: "T", Lists: 2}.
	Lists int
}

// Named is the type with the given name.
func Named(name string) ValueType { return ValueType{Name: name} }

// ListOf is List<element>.
func ListOf(element ValueType) ValueType {
	return ValueType{Name: element.Name, Lists: element.Lists + 1}
}

// String renders the type as Lean's ValueType.render does, e.g. List<T>.
func (t ValueType) String() string {
	return strings.Repeat("List<", t.Lists) + t.Name + strings.Repeat(">", t.Lists)
}

// Kind is whether a connection carries one result (Single) or a sequence ended by EOS (Stream).
type Kind int

const (
	KindSingle Kind = iota
	KindStream
)

func (k Kind) String() string {
	if k == KindStream {
		return "stream"
	}
	return "single"
}

// Contract is the output contract of one call: a Single call returns one value of Type, a
// Stream call yields elements of Type.
type Contract struct {
	Kind Kind
	Type ValueType
}

// Element is the type of the call's results (Lean Contract.element).
func (c Contract) Element() ValueType { return c.Type }

// Policy is what an accepted failure does to the workflow: stop it, or record it and continue.
type Policy int

const (
	PolicyStop Policy = iota
	PolicyContinue
)

func (p Policy) String() string {
	if p == PolicyContinue {
		return "continue"
	}
	return "stop"
}

// Timeout holds the optional durations in milliseconds. The model only uses whether a timeout
// exists and that it is positive. JSON numbers above 2^64-1 are clamped to 2^64-1, which the
// model cannot tell apart from the exact value.
type Timeout struct {
	CallMs    *uint64
	ElementMs *uint64
}

// IsEmpty reports whether neither duration is set.
func (t Timeout) IsEmpty() bool { return t.CallMs == nil && t.ElementMs == nil }

func (t Timeout) equal(u Timeout) bool {
	return equalPtr(t.CallMs, u.CallMs) && equalPtr(t.ElementMs, u.ElementMs)
}

func equalPtr[T comparable](a, b *T) bool {
	if a == nil || b == nil {
		return a == nil && b == nil
	}
	return *a == *b
}

func ptr[T any](v T) *T { return &v }
