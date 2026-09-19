package main

import (
	"bytes"
	"encoding/json"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func TestCLI(t *testing.T) {
	graph := "../../../Test/graphs/minimal.json"
	for _, tc := range []struct {
		args []string
		code int
	}{
		{[]string{"--help"}, 0}, {nil, 2}, {[]string{"check"}, 2},
		{[]string{"check", "../../../Test/traces/minimal.jsonl", "--graph", graph}, 0},
		{[]string{"check", "../../../Test/traces/after-eos.jsonl", "--graph", graph}, 1},
		{[]string{"explore", "--graph", graph, "--max-states", "1"}, 1},
		{[]string{"explore", "--graph", graph, "--depth", "-1"}, 2},
		{[]string{"explore", "--graph", graph, "--workers", "0"}, 2},
		{[]string{"gen", "--seed", "1", "--seed", "2"}, 2},
		{[]string{"gen", "--typo", "1"}, 2},
		{[]string{"gen", "--seed"}, 2},
	} {
		var out, stderr bytes.Buffer
		code, _ := run(tc.args, &out, &stderr)
		if code != tc.code {
			t.Errorf("%v: exit %d, want %d\n%s\n%s", tc.args, code, tc.code, &out, &stderr)
		}
	}
}

func TestGeneratedTraceAndLongLine(t *testing.T) {
	var out, stderr bytes.Buffer
	code, err := run([]string{"gen", "--seed", "17", "--count", "30"}, &out, &stderr)
	if err != nil || code != 0 {
		t.Fatalf("gen: %d %v %s", code, err, &stderr)
	}
	lines := strings.Split(strings.TrimSpace(out.String()), "\n")
	// Increase the transaction ID beyond Scanner's default token limit.
	var first map[string]any
	if err := json.Unmarshal([]byte(lines[0]), &first); err != nil {
		t.Fatal(err)
	}
	txn := first["txn"]
	for i, line := range lines {
		var event map[string]json.RawMessage
		if err := json.Unmarshal([]byte(line), &event); err != nil {
			t.Fatal(err)
		}
		var id string
		_ = json.Unmarshal(event["txn"], &id)
		if id == txn {
			event["txn"], _ = json.Marshal(strings.Repeat("x", 100000))
		}
		b, _ := json.Marshal(event)
		lines[i] = string(b)
	}
	path := filepath.Join(t.TempDir(), "generated.jsonl")
	if err := os.WriteFile(path, []byte(strings.Join(lines, "\n")+"\n"), 0600); err != nil {
		t.Fatal(err)
	}
	out.Reset()
	stderr.Reset()
	code, err = run([]string{"check", path, "--graph", "../../../Test/graphs/minimal.json"}, &out, &stderr)
	if err != nil || code != 0 {
		t.Fatalf("check: %d %v %s", code, err, &stderr)
	}
}
