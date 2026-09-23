package suimon

import (
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"iter"
)

// A program names its functions, judges and transforms; a Registry supplies their Go
// implementations (§14). Values cross the engine boundary as JSON: the engine keeps and records
// each value as the encoding/json encoding of the Go value a function returned, yielded or a
// transform produced, and decodes that JSON into the parameter type of the function that receives
// it. Values must therefore survive a JSON round trip (§4.4); a value that does not encode, or an
// input that does not decode into the parameter type, fails the call or the transform.

type bindingKind int

const (
	bindFunction bindingKind = iota
	bindStream
	bindJudge
	bindTransform
)

func (k bindingKind) String() string {
	return [...]string{"Single function", "Stream function", "judge", "transform"}[k]
}

// A Binding binds one identifier of a program to its implementation. Make bindings with Func,
// FuncNoInput, Stream, StreamNoInput, Judge, Transform and Passthrough, and collect them with
// NewRegistry.
type Binding struct {
	id   string
	kind bindingKind
	// input is whether a function takes an input; judges and transforms always take one.
	input     bool
	function  func(ctx context.Context, input []byte) ([]byte, error)
	stream    func(ctx context.Context, input []byte) iter.Seq2[[]byte, error]
	judge     func(ctx context.Context, input []byte) (string, error)
	transform func(input []byte) ([]byte, error)
}

// Func binds a function that takes an input and returns one value (Single, §4.1). The engine
// calls f once per invocation and accepts what it returns; an error fails the call. f must return
// when ctx is cancelled (a timeout, a stop or a cancellation, §11.3); what it returns then is not
// accepted.
func Func[In, Out any](id string, f func(ctx context.Context, in In) (Out, error)) Binding {
	return Binding{id: id, kind: bindFunction, input: true,
		function: func(ctx context.Context, input []byte) ([]byte, error) {
			in, err := decodeValue[In](input)
			if err != nil {
				return nil, err
			}
			out, err := f(ctx, in)
			if err != nil {
				return nil, err
			}
			return encodeValue(out)
		}}
}

// FuncNoInput binds a function without input that returns one value, like Func.
func FuncNoInput[Out any](id string, f func(ctx context.Context) (Out, error)) Binding {
	return Binding{id: id, kind: bindFunction,
		function: func(ctx context.Context, _ []byte) ([]byte, error) {
			out, err := f(ctx)
			if err != nil {
				return nil, err
			}
			return encodeValue(out)
		}}
}

// Stream binds a function that takes an input and yields values (Stream, §4.1). The engine calls
// f once per invocation and reads the returned sequence one element at a time, never two at once,
// and without waiting for downstream work (§4.1.1): each element is accepted when it is yielded.
// An element with a non-nil error fails the call, and the elements accepted before it stay. When
// ctx is cancelled the sequence must end, even while an element is being produced; elements after
// that are not accepted. The value returned with an error is ignored, and a nil sequence is empty.
func Stream[In, Out any](id string, f func(ctx context.Context, in In) iter.Seq2[Out, error]) Binding {
	return Binding{id: id, kind: bindStream, input: true,
		stream: func(ctx context.Context, input []byte) iter.Seq2[[]byte, error] {
			return func(yield func([]byte, error) bool) {
				in, err := decodeValue[In](input)
				if err != nil {
					yield(nil, err)
					return
				}
				encodeAll(f(ctx, in), yield)
			}
		}}
}

// StreamNoInput binds a function without input that yields values, like Stream.
func StreamNoInput[Out any](id string, f func(ctx context.Context) iter.Seq2[Out, error]) Binding {
	return Binding{id: id, kind: bindStream,
		stream: func(ctx context.Context, _ []byte) iter.Seq2[[]byte, error] {
			return func(yield func([]byte, error) bool) { encodeAll(f(ctx), yield) }
		}}
}

// encodeAll yields the JSON of each element of seq, and stops at the first error. A nil sequence
// yields nothing.
func encodeAll[T any](seq iter.Seq2[T, error], yield func([]byte, error) bool) {
	if seq == nil {
		return
	}
	for v, err := range seq {
		if err != nil {
			yield(nil, err)
			return
		}
		data, err := encodeValue(v)
		if err != nil {
			yield(nil, err)
			return
		}
		if !yield(data, nil) {
			return
		}
	}
}

// Judge binds a branch judge (§7.1): it receives the branch input and returns the name of one arm
// of the branch. An error, or a name that is not an arm, fails the judgement.
func Judge[In any](id string, f func(ctx context.Context, in In) (arm string, err error)) Binding {
	return Binding{id: id, kind: bindJudge, input: true,
		judge: func(ctx context.Context, input []byte) (string, error) {
			in, err := decodeValue[In](input)
			if err != nil {
				return "", err
			}
			return f(ctx, in)
		}}
}

// Transform binds a connection or task transform (§4.2). A transform is pure: the engine calls it
// synchronously, once per value, while it holds the execution state, so it must be quick and must
// not block. An error fails the transform, under the policy of the target (§11.2).
func Transform[In, Out any](id string, f func(in In) (Out, error)) Binding {
	return Binding{id: id, kind: bindTransform, input: true,
		transform: func(input []byte) ([]byte, error) {
			in, err := decodeValue[In](input)
			if err != nil {
				return nil, err
			}
			out, err := f(in)
			if err != nil {
				return nil, err
			}
			return encodeValue(out)
		}}
}

// Passthrough binds a transform that passes each value on unchanged, for a connection whose
// source and target types are the same (§4.2). The discard transform needs no binding.
func Passthrough(id string) Binding {
	return Binding{id: id, kind: bindTransform, input: true,
		transform: func(input []byte) ([]byte, error) { return input, nil }}
}

// encodeValue is the JSON of v, without the HTML escaping of json.Marshal.
func encodeValue(v any) ([]byte, error) {
	var b bytes.Buffer
	enc := json.NewEncoder(&b)
	enc.SetEscapeHTML(false)
	if err := enc.Encode(v); err != nil {
		return nil, fmt.Errorf("suimon: encoding a value: %w", err)
	}
	return bytes.TrimSuffix(b.Bytes(), []byte("\n")), nil
}

func decodeValue[T any](data []byte) (T, error) {
	var v T
	if err := json.Unmarshal(data, &v); err != nil {
		return v, fmt.Errorf("suimon: decoding a value into %T: %w", v, err)
	}
	return v, nil
}

// Registry holds the implementations of the functions, judges and transforms of programs. It is
// immutable, and safe for concurrent use.
type Registry struct {
	// functions holds Single and Stream functions, which share the identifiers of a program's
	// functions; judges and transforms have their own identifiers.
	functions, judges, transforms map[string]Binding
}

// NewRegistry collects bindings. An identifier may be bound once in each of the three kinds, and
// discard, which the library provides, cannot be bound.
func NewRegistry(bindings ...Binding) (*Registry, error) {
	r := &Registry{functions: map[string]Binding{}, judges: map[string]Binding{}, transforms: map[string]Binding{}}
	var errs []error
	for _, b := range bindings {
		switch {
		case b.id == "":
			errs = append(errs, errors.New("suimon: a binding needs an identifier"))
			continue
		case b.kind == bindTransform && b.id == DiscardName:
			errs = append(errs, fmt.Errorf("suimon: %s is provided by the library and cannot be bound", DiscardName))
			continue
		}
		m := r.namespace(b.kind)
		if _, dup := m[b.id]; dup {
			errs = append(errs, fmt.Errorf("suimon: %s is bound twice", b.id))
			continue
		}
		m[b.id] = b
	}
	if err := errors.Join(errs...); err != nil {
		return nil, err
	}
	return r, nil
}

func (r *Registry) namespace(kind bindingKind) map[string]Binding {
	switch kind {
	case bindJudge:
		return r.judges
	case bindTransform:
		return r.transforms
	}
	return r.functions
}

// check reports the functions, judges and transforms that p uses but r does not bind, or binds
// with another shape than p declares: a Single or a Stream function, with or without input.
// Unknown declarations are left to validation.
func (r *Registry) check(p *Program) error {
	var errs []error
	seen := map[string]bool{}
	fail := func(key string, err error) {
		if !seen[key] {
			seen[key] = true
			errs = append(errs, err)
		}
	}
	function := func(id string) {
		decl, ok := p.function(id)
		if !ok {
			return
		}
		want := bindFunction
		if decl.Output.Kind == KindStream {
			want = bindStream
		}
		b, ok := r.functions[id]
		switch {
		case !ok:
			fail("function "+id, fmt.Errorf("suimon: function %s is not bound", id))
		case b.kind != want:
			fail("function "+id, fmt.Errorf("suimon: function %s is declared as a %s but bound to a %s", id, want, b.kind))
		case b.input != (decl.Input != nil):
			takes := map[bool]string{true: "takes an input", false: "takes no input"}
			fail("function "+id, fmt.Errorf("suimon: function %s %s, but its binding %s", id, takes[decl.Input != nil],
				takes[b.input]))
		}
	}
	judge := func(id string) {
		if _, ok := r.judges[id]; !ok {
			fail("judge "+id, fmt.Errorf("suimon: judge %s is not bound", id))
		}
	}
	transform := func(ref TransformRef) {
		if ref.Discard {
			return
		}
		if _, ok := r.transforms[ref.ID]; !ok {
			fail("transform "+ref.ID, fmt.Errorf("suimon: transform %s is not bound", ref.ID))
		}
	}
	for _, w := range p.Workflows {
		for _, pl := range w.Placements {
			switch c := pl.Control.(type) {
			case CallControl:
				if !c.Body.Workflow {
					function(c.Body.ID)
				}
			case BranchControl:
				judge(c.Judge)
			case ConcurrencyControl:
				for _, t := range c.Spec.Tasks {
					if !t.Body.Workflow {
						function(t.Body.ID)
					}
					if t.Input != nil {
						transform(*t.Input)
					}
					if t.Output != nil {
						transform(Declared(*t.Output))
					}
				}
			}
		}
		for _, c := range w.Connections {
			transform(c.Transform)
		}
	}
	return errors.Join(errs...)
}
