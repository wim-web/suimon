package suimon

import (
	"encoding/json"
	"reflect"
	"testing"
)

func TestIdentity(t *testing.T) {
	cases := []struct {
		parts []string
		want  string
	}{
		{nil, ""},
		{[]string{""}, "0:"},
		{[]string{"", "sales", ""}, "0:5:sales0:"},
		{[]string{"a:b", "3:x"}, "3:a:b3:3:x"},
		{[]string{"日本語", "é"}, "3:日本語1:é"},
		{[]string{"0123456789"}, "10:0123456789"},
		{[]string{Identity("x", "y"), "z"}, "6:1:x1:y1:z"},
	}
	for _, c := range cases {
		if got := Identity(c.parts...); got != c.want {
			t.Errorf("Identity(%q) = %q, want %q", c.parts, got, c.want)
		}
		parts, ok := DecodeIdentity(c.want)
		if !ok || len(parts) != len(c.parts) || (len(parts) > 0 && !reflect.DeepEqual(parts, c.parts)) {
			t.Errorf("DecodeIdentity(%q) = %q %v, want %q", c.want, parts, ok, c.parts)
		}
	}
	for _, id := range []string{"5", "a", "2:a", "1:a1", "99999999999999999999999:x", "3:日本"} {
		if parts, ok := DecodeIdentity(id); ok {
			t.Errorf("DecodeIdentity(%q) = %q, want none", id, parts)
		}
	}
	// Like Lean's decodeIdentity, lengths are read as the digits that are there.
	for id, want := range map[string][]string{":": {""}, "01:a": {"a"}, ":1:b": {"", "b"}} {
		if parts, ok := DecodeIdentity(id); !ok || !reflect.DeepEqual(parts, want) {
			t.Errorf("DecodeIdentity(%q) = %q %v, want %q", id, parts, ok, want)
		}
	}
}

func TestListValue(t *testing.T) {
	// Sorted by code points, which is the byte order of UTF-8.
	got := listValue([]string{"b", "é", "a", "B", "a"})
	if want := Identity("list", "B", "a", "a", "b", "é"); got != want {
		t.Errorf("listValue = %q, want %q", got, want)
	}
	if listValue(nil) != Identity("list") {
		t.Error("the empty list")
	}
}

func TestExploreValues(t *testing.T) {
	if got := ExploreValue("input"); got != "5:value5:input" {
		t.Errorf("ExploreValue = %q", got)
	}
	seeds := []uint64{NextSeed(1), NextSeed(NextSeed(1)), NextSeed(1 << 40)}
	if seeds[0] != 1015568748 || seeds[1] != 1586005467 || seeds[2] != NextSeed(0) {
		t.Errorf("NextSeed: %v", seeds)
	}
	merge := load(t, "merge")
	s := mustStep(t, merge, &State{}, OpStart{})
	choices := Accepted(merge, DefaultConfig(), s)
	cfg := DefaultConfig()
	cfg.Disruption = 0
	// With disruption 0, Lean's n % 0 = n and n / 0 = 0: seed 0 picks the first disruptive choice.
	if c, ok := Pick(cfg, s, 0, choices); !ok || !disruptive(cfg, s, c.Op) {
		t.Errorf("disruption 0, seed 0: %v", c.Op)
	}
	firstGood := -1
	for i, c := range choices {
		if !disruptive(cfg, s, c.Op) && firstGood < 0 {
			firstGood = i
		}
	}
	if c, ok := Pick(cfg, s, 7, choices); !ok || firstGood < 0 || EncodeOp(c.Op) != EncodeOp(choices[firstGood].Op) {
		t.Errorf("disruption 0, seed 7: %v", c.Op)
	}
	if _, ok := Pick(DefaultConfig(), s, 1, nil); ok {
		t.Error("no choice")
	}
	a, opsA := Walk(merge, DefaultConfig(), 5, 10000)
	b, opsB := Walk(merge, DefaultConfig(), 5, 10000)
	if !a.Equal(b) || len(opsA) != len(opsB) || !a.Status.Terminal() {
		t.Error("a walk is reproducible and ends in a final state")
	}
	if _, ops := Walk(merge, DefaultConfig(), 5, 3); len(ops) != 3 {
		t.Errorf("limit: %d ops", len(ops))
	}
}

// The JSON form of a state follows Lean's derived ToJson.
func TestStateJSON(t *testing.T) {
	users := load(t, "users")
	var s *State
	for seed := uint64(1); seed < 40; seed++ {
		final, _ := Walk(users, DefaultConfig(), seed, 10000)
		if final.Status == StatusSucceeded {
			s = final
			break
		}
	}
	if s == nil {
		t.Fatal("no succeeded walk")
	}
	data, err := s.MarshalJSON()
	if err != nil {
		t.Fatal(err)
	}
	var doc map[string]any
	if err := json.Unmarshal(data, &doc); err != nil {
		t.Fatalf("%v: %s", err, data)
	}
	if doc["status"] != "succeeded" || doc["started"] != true || doc["cancelled"] != false {
		t.Errorf("status fields: %v %v %v", doc["status"], doc["started"], doc["cancelled"])
	}
	root := doc["runs"].([]any)[0].(map[string]any)
	if len(root["path"].([]any)) != 0 || root["owner"] != nil || root["input"] != ExploreValue("input") {
		t.Errorf("root run: %v", root)
	}
	call := doc["calls"].([]any)[0].(map[string]any)
	target := call["target"].(map[string]any)["function"].(map[string]any)
	if target["id"] != "fetchAllUsers" || call["status"] != "returned" || call["policy"] != "stop" {
		t.Errorf("call: %v", call)
	}
	timeout := call["timeout"].(map[string]any)
	if len(timeout) != 2 || timeout["callMs"] != nil || timeout["elementMs"] != nil {
		t.Errorf("timeout: %v", timeout)
	}
	delivery := doc["deliveries"].([]any)[0].(map[string]any)
	if _, ok := delivery["outcome"].(map[string]any)["value"].(map[string]any)["v"].(string); !ok {
		t.Errorf("delivered value: %v", delivery["outcome"])
	}
	for _, key := range []string{"runs", "invocations", "calls", "executions", "results", "taskResults",
		"deliveries", "settled", "failures"} {
		if _, ok := doc[key].([]any); !ok {
			t.Errorf("%s is not an array", key)
		}
	}
	for _, x := range doc["taskResults"].([]any) {
		output, _ := x.(map[string]any)["output"].(map[string]any)
		if _, ok := output["value"].(map[string]any)["v"].(string); !ok {
			t.Errorf("a transformed task result has an output value: %v", x)
		}
	}
	for _, x := range doc["results"].([]any) {
		if producer, _ := x.(map[string]any)["producer"].(string); producer == "" {
			t.Errorf("a result has a producer: %v", x)
		}
	}
	// A branch settles its arms as [arm, outcome] pairs; a discard delivery is "trigger".
	branch := load(t, "branch")
	b := drive(branch, succeed(2, func(*State, *Call) string { return "unpaid" }))
	data, _ = b.MarshalJSON()
	var bdoc struct {
		Settled []struct {
			Placement string
			Arms      [][]string
		}
	}
	if err := json.Unmarshal(data, &bdoc); err != nil {
		t.Fatal(err)
	}
	found := false
	for _, x := range bdoc.Settled {
		if x.Placement == "paid" {
			found = reflect.DeepEqual(x.Arms, [][]string{{"paid", "skipped"}, {"unpaid", "normal"}})
		}
	}
	if !found {
		t.Errorf("branch arms: %s", data)
	}
	merge := load(t, "merge")
	m := drive(merge, succeed(0, none))
	data, _ = m.MarshalJSON()
	if !hasFragment(string(data), `"outcome":"trigger"`) {
		t.Errorf("trigger: %s", data)
	}
}
