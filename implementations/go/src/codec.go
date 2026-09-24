package suimon

import (
	"errors"
	"fmt"
	"slices"
	"unicode/utf8"
)

// The definition JSON codec of Suimon/Json.lean (schema/definition.schema.json). Decoding is strict:
// unknown fields are rejected, an optional field is omitted only by leaving its key out, and the
// transform name discard refers to the library transform. Errors carry the messages of the Lean
// decoder, including the JSON syntax errors of Lean's parser.

// ParseDefinition decodes a definition from JSON text. It does not validate the definition.
func ParseDefinition(data []byte) (*Definition, error) {
	if !utf8.Valid(data) {
		return nil, errors.New("definition: invalid UTF-8")
	}
	json, err := parseLeanJSON(string(data))
	if err != nil {
		return nil, err
	}
	return decodeDefinition(json)
}

func strict(json ljValue, allowed []string, at string) error {
	if json.kind != ljObj {
		return fmt.Errorf("%s: expected an object", at)
	}
	for _, f := range json.fields {
		if !slices.Contains(allowed, f.key) {
			return fmt.Errorf("%s: unknown field %s", at, f.key)
		}
	}
	return nil
}

func requireField(json ljValue, key, at string) (ljValue, error) {
	v, ok := json.field(key)
	if !ok {
		return ljValue{}, fmt.Errorf("%s: missing field %s", at, key)
	}
	return v, nil
}

func text(json ljValue, at string) (string, error) {
	if json.kind != ljStr {
		return "", fmt.Errorf("%s: expected a string", at)
	}
	if json.str == "" {
		return "", fmt.Errorf("%s: empty string", at)
	}
	return json.str, nil
}

func textField(json ljValue, key, at string) (string, error) {
	v, err := requireField(json, key, at)
	if err != nil {
		return "", err
	}
	return text(v, at+"."+key)
}

func optionalTextField(json ljValue, key, at string) (*string, error) {
	v, ok := json.field(key)
	if !ok {
		return nil, nil
	}
	s, err := text(v, at+"."+key)
	if err != nil {
		return nil, err
	}
	return &s, nil
}

func optionalNatField(json ljValue, key, at string) (*uint64, error) {
	v, ok := json.field(key)
	if !ok {
		return nil, nil
	}
	if v.kind == ljNum {
		if n, ok := v.num.nat(); ok {
			return &n, nil
		}
	}
	return nil, fmt.Errorf("%s.%s: expected a natural number", at, key)
}

// list is an optional array field; an absent key is the empty list.
func list(json ljValue, key, at string) ([]ljValue, error) {
	v, ok := json.field(key)
	if !ok {
		return nil, nil
	}
	if v.kind != ljArr {
		return nil, fmt.Errorf("%s.%s: expected an array", at, key)
	}
	return v.items, nil
}

func decodeValueType(json ljValue, at string) (ValueType, error) {
	switch json.kind {
	case ljStr:
		if json.str == "" {
			return ValueType{}, fmt.Errorf("%s: empty type name", at)
		}
		return Named(json.str), nil
	case ljObj:
		if err := strict(json, []string{"list"}, at); err != nil {
			return ValueType{}, err
		}
		element, err := requireField(json, "list", at)
		if err != nil {
			return ValueType{}, err
		}
		t, err := decodeValueType(element, at)
		if err != nil {
			return ValueType{}, err
		}
		return ListOf(t), nil
	}
	return ValueType{}, fmt.Errorf(`%s: a type is a name or {"list": type}`, at)
}

func decodeContract(json ljValue, at string) (Contract, error) {
	if err := strict(json, []string{"single", "stream"}, at); err != nil {
		return Contract{}, err
	}
	single, hasSingle := json.field("single")
	stream, hasStream := json.field("stream")
	switch {
	case hasSingle && !hasStream:
		t, err := decodeValueType(single, at+".single")
		return Contract{Kind: KindSingle, Type: t}, err
	case hasStream && !hasSingle:
		t, err := decodeValueType(stream, at+".stream")
		return Contract{Kind: KindStream, Type: t}, err
	}
	return Contract{}, fmt.Errorf("%s: an output contract is either single or stream", at)
}

func decodePolicy(json ljValue, at string) (Policy, error) {
	if json.kind == ljStr {
		switch json.str {
		case "stop":
			return PolicyStop, nil
		case "continue":
			return PolicyContinue, nil
		}
	}
	return 0, fmt.Errorf("%s: policy is stop or continue", at)
}

func decodeTimeout(json ljValue, at string) (Timeout, error) {
	value, ok := json.field("timeout")
	if !ok {
		return Timeout{}, nil
	}
	at += ".timeout"
	if err := strict(value, []string{"callMs", "elementMs"}, at); err != nil {
		return Timeout{}, err
	}
	call, err := optionalNatField(value, "callMs", at)
	if err != nil {
		return Timeout{}, err
	}
	element, err := optionalNatField(value, "elementMs", at)
	if err != nil {
		return Timeout{}, err
	}
	return Timeout{CallMs: call, ElementMs: element}, nil
}

func decodeBody(json ljValue, at string) (Body, error) {
	kind, err := textField(json, "type", at)
	if err != nil {
		return Body{}, err
	}
	switch kind {
	case "function":
		if err := strict(json, []string{"type", "function"}, at); err != nil {
			return Body{}, err
		}
		id, err := textField(json, "function", at)
		return FunctionBody(id), err
	case "subworkflow":
		if err := strict(json, []string{"type", "workflow", "output"}, at); err != nil {
			return Body{}, err
		}
		id, err := textField(json, "workflow", at)
		if err != nil {
			return Body{}, err
		}
		output, err := textField(json, "output", at)
		return WorkflowBody(id, output), err
	}
	return Body{}, fmt.Errorf("%s: unknown body type %s", at, kind)
}

func transformRef(id string) TransformRef {
	if id == DiscardName {
		return Discard
	}
	return Declared(id)
}

func decodeTask(json ljValue, at string) (TaskSpec, error) {
	if err := strict(json, []string{"name", "body", "inputTransform", "outputTransform", "policy", "timeout"}, at); err != nil {
		return TaskSpec{}, err
	}
	name, err := textField(json, "name", at)
	if err != nil {
		return TaskSpec{}, err
	}
	at += "." + name
	t := TaskSpec{Name: name}
	body, err := requireField(json, "body", at)
	if err != nil {
		return TaskSpec{}, err
	}
	if t.Body, err = decodeBody(body, at+".body"); err != nil {
		return TaskSpec{}, err
	}
	input, err := optionalTextField(json, "inputTransform", at)
	if err != nil {
		return TaskSpec{}, err
	}
	if input != nil {
		t.Input = ptr(transformRef(*input))
	}
	if t.Output, err = optionalTextField(json, "outputTransform", at); err != nil {
		return TaskSpec{}, err
	}
	policy, err := requireField(json, "policy", at)
	if err != nil {
		return TaskSpec{}, err
	}
	if t.Policy, err = decodePolicy(policy, at+".policy"); err != nil {
		return TaskSpec{}, err
	}
	t.Timeout, err = decodeTimeout(json, at)
	return t, err
}

func decodeCollect(json ljValue, at string) (Collect, error) {
	if json.kind == ljStr {
		switch json.str {
		case "list":
			return CollectList, nil
		case "stream":
			return CollectStream, nil
		}
	}
	return 0, fmt.Errorf("%s: output is list or stream", at)
}

func decodeElement(json ljValue, at string) (ValueType, error) {
	element, err := requireField(json, "element", at)
	if err != nil {
		return ValueType{}, err
	}
	return decodeValueType(element, at+".element")
}

func decodeControl(json ljValue, at string) (Control, error) {
	kind, err := textField(json, "type", at)
	if err != nil {
		return nil, err
	}
	switch kind {
	case "function", "subworkflow":
		body, err := decodeBody(json, at)
		if err != nil {
			return nil, err
		}
		return CallControl{Body: body}, nil
	case "branch":
		if err := strict(json, []string{"type", "judge", "arms"}, at); err != nil {
			return nil, err
		}
		items, err := list(json, "arms", at)
		if err != nil {
			return nil, err
		}
		var arms []string
		for _, item := range items {
			arm, err := text(item, at+".arms")
			if err != nil {
				return nil, err
			}
			arms = append(arms, arm)
		}
		judge, err := textField(json, "judge", at)
		if err != nil {
			return nil, err
		}
		return BranchControl{Judge: judge, Arms: arms}, nil
	case "waitStream":
		if err := strict(json, []string{"type", "element"}, at); err != nil {
			return nil, err
		}
		element, err := decodeElement(json, at)
		if err != nil {
			return nil, err
		}
		return WaitStreamControl{Element: element}, nil
	case "merge":
		if err := strict(json, []string{"type", "element"}, at); err != nil {
			return nil, err
		}
		element, err := decodeElement(json, at)
		if err != nil {
			return nil, err
		}
		return MergeControl{Element: element}, nil
	case "concurrency":
		return decodeConcurrency(json, at)
	}
	return nil, fmt.Errorf("%s: unknown node type %s", at, kind)
}

func decodeConcurrency(json ljValue, at string) (Control, error) {
	if err := strict(json, []string{"type", "input", "limit", "tasks", "output", "element"}, at); err != nil {
		return nil, err
	}
	limit, err := optionalNatField(json, "limit", at)
	if err != nil {
		return nil, err
	}
	var c Concurrency
	if input, ok := json.field("input"); ok {
		t, err := decodeValueType(input, at+".input")
		if err != nil {
			return nil, err
		}
		c.Input = &t
	}
	if limit == nil {
		return nil, fmt.Errorf("%s: missing field limit", at)
	}
	c.Limit = *limit
	tasks, err := list(json, "tasks", at)
	if err != nil {
		return nil, err
	}
	for _, task := range tasks {
		t, err := decodeTask(task, at+".tasks")
		if err != nil {
			return nil, err
		}
		c.Tasks = append(c.Tasks, t)
	}
	output, err := requireField(json, "output", at)
	if err != nil {
		return nil, err
	}
	if c.Output, err = decodeCollect(output, at+".output"); err != nil {
		return nil, err
	}
	if c.Element, err = decodeElement(json, at); err != nil {
		return nil, err
	}
	return ConcurrencyControl{Spec: c}, nil
}

func decodePlacement(json ljValue, at string) (Placement, error) {
	if err := strict(json, []string{"name", "node", "policy", "timeout"}, at); err != nil {
		return Placement{}, err
	}
	name, err := textField(json, "name", at)
	if err != nil {
		return Placement{}, err
	}
	at += "." + name
	pl := Placement{Name: name}
	node, err := requireField(json, "node", at)
	if err != nil {
		return Placement{}, err
	}
	if pl.Control, err = decodeControl(node, at+".node"); err != nil {
		return Placement{}, err
	}
	policy, err := requireField(json, "policy", at)
	if err != nil {
		return Placement{}, err
	}
	if pl.Policy, err = decodePolicy(policy, at+".policy"); err != nil {
		return Placement{}, err
	}
	pl.Timeout, err = decodeTimeout(json, at)
	return pl, err
}

func decodeConnection(json ljValue, at string) (Connection, error) {
	if err := strict(json, []string{"source", "arm", "target", "transform"}, at); err != nil {
		return Connection{}, err
	}
	var c Connection
	var err error
	if c.Source, err = textField(json, "source", at); err != nil {
		return Connection{}, err
	}
	if c.Arm, err = optionalTextField(json, "arm", at); err != nil {
		return Connection{}, err
	}
	if c.Target, err = textField(json, "target", at); err != nil {
		return Connection{}, err
	}
	transform, err := textField(json, "transform", at)
	c.Transform = transformRef(transform)
	return c, err
}

func decodeWorkflow(json ljValue, at string) (Workflow, error) {
	if err := strict(json, []string{"id", "input", "placements", "connections"}, at); err != nil {
		return Workflow{}, err
	}
	id, err := textField(json, "id", at)
	if err != nil {
		return Workflow{}, err
	}
	at += "." + id
	w := Workflow{ID: id}
	if entry, ok := json.field("input"); ok {
		if err := strict(entry, []string{"type", "placement"}, at+".input"); err != nil {
			return Workflow{}, err
		}
		typeJSON, err := requireField(entry, "type", at+".input")
		if err != nil {
			return Workflow{}, err
		}
		t, err := decodeValueType(typeJSON, at+".input.type")
		if err != nil {
			return Workflow{}, err
		}
		placement, err := textField(entry, "placement", at+".input")
		if err != nil {
			return Workflow{}, err
		}
		w.Input = &Entry{Type: t, Placement: placement}
	}
	placements, err := list(json, "placements", at)
	if err != nil {
		return Workflow{}, err
	}
	for _, item := range placements {
		pl, err := decodePlacement(item, at+".placements")
		if err != nil {
			return Workflow{}, err
		}
		w.Placements = append(w.Placements, pl)
	}
	connections, err := list(json, "connections", at)
	if err != nil {
		return Workflow{}, err
	}
	for _, item := range connections {
		c, err := decodeConnection(item, at+".connections")
		if err != nil {
			return Workflow{}, err
		}
		w.Connections = append(w.Connections, c)
	}
	return w, nil
}

func decodeFunction(json ljValue, at string) (FunctionDecl, error) {
	if err := strict(json, []string{"id", "input", "output"}, at); err != nil {
		return FunctionDecl{}, err
	}
	id, err := textField(json, "id", at)
	if err != nil {
		return FunctionDecl{}, err
	}
	at += "." + id
	f := FunctionDecl{ID: id}
	if input, ok := json.field("input"); ok {
		t, err := decodeValueType(input, at+".input")
		if err != nil {
			return FunctionDecl{}, err
		}
		f.Input = &t
	}
	output, err := requireField(json, "output", at)
	if err != nil {
		return FunctionDecl{}, err
	}
	f.Output, err = decodeContract(output, at+".output")
	return f, err
}

func decodeJudge(json ljValue, at string) (JudgeDecl, error) {
	if err := strict(json, []string{"id", "input"}, at); err != nil {
		return JudgeDecl{}, err
	}
	id, err := textField(json, "id", at)
	if err != nil {
		return JudgeDecl{}, err
	}
	input, err := requireField(json, "input", at)
	if err != nil {
		return JudgeDecl{}, err
	}
	t, err := decodeValueType(input, at+"."+id+".input")
	return JudgeDecl{ID: id, Input: t}, err
}

func decodeTransform(json ljValue, at string) (TransformDecl, error) {
	if err := strict(json, []string{"id", "input", "output"}, at); err != nil {
		return TransformDecl{}, err
	}
	id, err := textField(json, "id", at)
	if err != nil {
		return TransformDecl{}, err
	}
	input, err := requireField(json, "input", at)
	if err != nil {
		return TransformDecl{}, err
	}
	in, err := decodeValueType(input, at+"."+id+".input")
	if err != nil {
		return TransformDecl{}, err
	}
	output, err := requireField(json, "output", at)
	if err != nil {
		return TransformDecl{}, err
	}
	out, err := decodeValueType(output, at+"."+id+".output")
	return TransformDecl{ID: id, Input: in, Output: out}, err
}

func decodeDefinition(json ljValue) (*Definition, error) {
	if err := strict(json, []string{"main", "functions", "judges", "transforms", "workflows"}, "definition"); err != nil {
		return nil, err
	}
	p := &Definition{}
	var err error
	if p.Main, err = textField(json, "main", "definition"); err != nil {
		return nil, err
	}
	if err := decodeList(json, "functions", decodeFunction, &p.Functions); err != nil {
		return nil, err
	}
	if err := decodeList(json, "judges", decodeJudge, &p.Judges); err != nil {
		return nil, err
	}
	if err := decodeList(json, "transforms", decodeTransform, &p.Transforms); err != nil {
		return nil, err
	}
	if err := decodeList(json, "workflows", decodeWorkflow, &p.Workflows); err != nil {
		return nil, err
	}
	return p, nil
}

// decodeList decodes the items of the array field key of the definition; each item is located by the
// field name alone, like the Lean decoder does.
func decodeList[T any](json ljValue, key string, decode func(ljValue, string) (T, error), out *[]T) error {
	items, err := list(json, key, "definition")
	if err != nil {
		return err
	}
	for _, item := range items {
		v, err := decode(item, key)
		if err != nil {
			return err
		}
		*out = append(*out, v)
	}
	return nil
}

// MarshalJSON renders the definition in its canonical form, which ParseDefinition reads (Lean
// Codec.definitionWire).
func (p *Definition) MarshalJSON() ([]byte, error) {
	return []byte(definitionWire(p).render()), nil
}

func valueTypeWire(t ValueType) wire {
	w := wireStr(t.Name)
	for range t.Lists {
		w = wireObj(field("list", w))
	}
	return w
}

func contractWire(c Contract) wire {
	key := "single"
	if c.Kind == KindStream {
		key = "stream"
	}
	return wireObj(field(key, valueTypeWire(c.Type)))
}

func timeoutFields(t Timeout) []wireField {
	if t.IsEmpty() {
		return nil
	}
	var fields []wireField
	if t.CallMs != nil {
		fields = append(fields, field("callMs", wireNat(*t.CallMs)))
	}
	if t.ElementMs != nil {
		fields = append(fields, field("elementMs", wireNat(*t.ElementMs)))
	}
	return []wireField{field("timeout", wireObj(fields...))}
}

func bodyWire(b Body) wire {
	if b.Workflow {
		return wireObj(field("type", wireStr("subworkflow")), field("workflow", wireStr(b.ID)),
			field("output", wireStr(b.Output)))
	}
	return wireObj(field("type", wireStr("function")), field("function", wireStr(b.ID)))
}

func transformRefName(t TransformRef) string {
	if t.Discard {
		return DiscardName
	}
	return t.ID
}

func taskWire(t TaskSpec) wire {
	fields := []wireField{field("name", wireStr(t.Name)), field("body", bodyWire(t.Body))}
	if t.Input != nil {
		fields = append(fields, field("inputTransform", wireStr(transformRefName(*t.Input))))
	}
	if t.Output != nil {
		fields = append(fields, field("outputTransform", wireStr(*t.Output)))
	}
	fields = append(fields, field("policy", wireStr(t.Policy.String())))
	return wireObj(append(fields, timeoutFields(t.Timeout)...)...)
}

func controlWire(c Control) wire {
	switch c := c.(type) {
	case CallControl:
		return bodyWire(c.Body)
	case BranchControl:
		arms := make([]wire, len(c.Arms))
		for i, arm := range c.Arms {
			arms[i] = wireStr(arm)
		}
		return wireObj(field("type", wireStr("branch")), field("judge", wireStr(c.Judge)), field("arms", wireArr(arms...)))
	case WaitStreamControl:
		return wireObj(field("type", wireStr("waitStream")), field("element", valueTypeWire(c.Element)))
	case MergeControl:
		return wireObj(field("type", wireStr("merge")), field("element", valueTypeWire(c.Element)))
	case ConcurrencyControl:
		fields := []wireField{field("type", wireStr("concurrency"))}
		if c.Spec.Input != nil {
			fields = append(fields, field("input", valueTypeWire(*c.Spec.Input)))
		}
		tasks := make([]wire, len(c.Spec.Tasks))
		for i, t := range c.Spec.Tasks {
			tasks[i] = taskWire(t)
		}
		return wireObj(append(fields, field("limit", wireNat(c.Spec.Limit)), field("tasks", wireArr(tasks...)),
			field("output", wireStr(c.Spec.Output.String())), field("element", valueTypeWire(c.Spec.Element)))...)
	}
	return wireNull()
}

func workflowWire(w *Workflow) wire {
	fields := []wireField{field("id", wireStr(w.ID))}
	if w.Input != nil {
		fields = append(fields, field("input", wireObj(field("type", valueTypeWire(w.Input.Type)),
			field("placement", wireStr(w.Input.Placement)))))
	}
	placements := make([]wire, len(w.Placements))
	for i, pl := range w.Placements {
		pf := []wireField{field("name", wireStr(pl.Name)), field("node", controlWire(pl.Control)),
			field("policy", wireStr(pl.Policy.String()))}
		placements[i] = wireObj(append(pf, timeoutFields(pl.Timeout)...)...)
	}
	connections := make([]wire, len(w.Connections))
	for i, c := range w.Connections {
		cf := []wireField{field("source", wireStr(c.Source))}
		if c.Arm != nil {
			cf = append(cf, field("arm", wireStr(*c.Arm)))
		}
		connections[i] = wireObj(append(cf, field("target", wireStr(c.Target)),
			field("transform", wireStr(transformRefName(c.Transform))))...)
	}
	return wireObj(append(fields, field("placements", wireArr(placements...)), field("connections", wireArr(connections...)))...)
}

// definitionWire is the canonical form of a definition (Lean Codec.definitionWire): the definition
// file with its fields in a fixed order and the absent optional fields left out. The header of an
// execution record holds it, so that equal definitions are recorded alike (§12.1).
func definitionWire(p *Definition) wire {
	functions := make([]wire, len(p.Functions))
	for i, f := range p.Functions {
		fields := []wireField{field("id", wireStr(f.ID))}
		if f.Input != nil {
			fields = append(fields, field("input", valueTypeWire(*f.Input)))
		}
		functions[i] = wireObj(append(fields, field("output", contractWire(f.Output)))...)
	}
	judges := make([]wire, len(p.Judges))
	for i, j := range p.Judges {
		judges[i] = wireObj(field("id", wireStr(j.ID)), field("input", valueTypeWire(j.Input)))
	}
	transforms := make([]wire, len(p.Transforms))
	for i, t := range p.Transforms {
		transforms[i] = wireObj(field("id", wireStr(t.ID)), field("input", valueTypeWire(t.Input)),
			field("output", valueTypeWire(t.Output)))
	}
	workflows := make([]wire, len(p.Workflows))
	for i := range p.Workflows {
		workflows[i] = workflowWire(&p.Workflows[i])
	}
	return wireObj(field("main", wireStr(p.Main)), field("functions", wireArr(functions...)),
		field("judges", wireArr(judges...)), field("transforms", wireArr(transforms...)),
		field("workflows", wireArr(workflows...)))
}
