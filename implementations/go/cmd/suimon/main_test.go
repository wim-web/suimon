package main

import (
	"bytes"
	"encoding/json"
	"errors"
	"io"
	"os"
	"path/filepath"
	"strings"
	"testing"

	suimon "github.com/wim-web/suimon/implementations/go/src"
)

func TestNatOptionDigitSeparators(t *testing.T) {
	for _, key := range []string{"--depth", "--workers", "--tick", "--max-states", "--seed", "--count"} {
		t.Run(key, func(t *testing.T) {
			for _, tc := range []struct{ input, want string }{
				{"0", "0"}, {"00", "0"}, {"0_0", "0"}, {"1_0", "10"},
				{"01_0", "10"}, {"1_2_3", "123"},
				{"18_446_744_073_709_551_616", "18446744073709551616"},
			} {
				got, err := natOpt(map[string]string{key: tc.input}, key, suimon.N(7))
				if err != nil || got.String() != tc.want {
					t.Errorf("%s: got %s, %v; want %s", tc.input, got, err, tc.want)
				}
			}
			for _, input := range []string{"", "_", "_10", "10_", "1__0", "1_0_", "+10", "-1", " 10", "10 ", "1 0", "1.0", "1e1", "0x10", "１_０", "١_٠"} {
				_, err := natOpt(map[string]string{key: input}, key, suimon.N(7))
				if err == nil || err.Error() != "invalid nonnegative integer for "+key {
					t.Errorf("%q: expected option error, got %v", input, err)
				}
			}
			got, err := natOpt(nil, key, suimon.N(7))
			if err != nil || got != suimon.N(7) {
				t.Fatalf("missing option: %s, %v", got, err)
			}
		})
	}
	if _, err := suimon.ParseNat("1_0"); err == nil {
		t.Fatal("CLI syntax leaked into the decimal Nat parser")
	}
	var n suimon.Nat
	if err := json.Unmarshal([]byte("1_0"), &n); err == nil {
		t.Fatal("CLI syntax leaked into the JSON codec")
	}
}

func TestCLI(t *testing.T) {
	graph := "../../../../Test/graphs/minimal.json"
	for _, tc := range []struct {
		args []string
		code int
	}{
		{[]string{"--help"}, 0}, {nil, 2}, {[]string{"check"}, 2},
		{[]string{"check", "../../../../Test/traces/minimal.jsonl", "--graph", graph}, 0},
		{[]string{"check", "../../../../Test/traces/after-eos.jsonl", "--graph", graph}, 1},
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

type failingWriter struct {
	failAfter, writes int
	err               error
}

func (w *failingWriter) Write(p []byte) (int, error) {
	w.writes++
	if w.writes > w.failAfter {
		return 0, w.err
	}
	return len(p), nil
}

func TestCLIOutputErrors(t *testing.T) {
	graph := "../../../../Test/graphs/minimal.json"
	trace := "../../../../Test/traces/minimal.jsonl"
	data, err := os.ReadFile(trace)
	if err != nil {
		t.Fatal(err)
	}
	first, _, _ := strings.Cut(string(data), "\n")
	truncated := filepath.Join(t.TempDir(), "truncated.jsonl")
	if err := os.WriteFile(truncated, []byte(first+"\n"), 0600); err != nil {
		t.Fatal(err)
	}
	for _, tc := range []struct {
		name      string
		args      []string
		stderr    bool
		failAfter int
	}{
		{"gen", []string{"gen", "--seed", "1", "--count", "3"}, false, 0},
		{"gen-partial-output", []string{"gen", "--seed", "1", "--count", "3"}, false, 2},
		{"check-result", []string{"check", trace, "--graph", graph}, false, 0},
		{"check-diagnostic", []string{"check", "../../../../Test/traces/after-eos.jsonl", "--graph", graph}, true, 0},
		{"check-truncated", []string{"check", truncated, "--graph", graph}, true, 0},
		{"explore-result", []string{"explore", "--graph", graph, "--depth", "1"}, false, 0},
		{"explore-incomplete", []string{"explore", "--graph", graph, "--max-states", "1"}, false, 0},
		{"help", []string{"--help"}, false, 0},
		{"missing-command", nil, true, 0},
		{"missing-trace", []string{"check"}, true, 0},
		{"unknown-command", []string{"unknown"}, true, 0},
	} {
		t.Run(tc.name, func(t *testing.T) {
			cause := errors.New("output unavailable")
			writer := &failingWriter{failAfter: tc.failAfter, err: cause}
			var stdout, stderr io.Writer = writer, io.Discard
			if tc.stderr {
				stdout, stderr = stderr, stdout
			}
			code, err := run(tc.args, stdout, stderr)
			if code != 2 || !errors.Is(err, cause) {
				t.Errorf("exit %d, error %v; want exit 2 and %v", code, err, cause)
			}
			if writer.writes != tc.failAfter+1 {
				t.Errorf("got %d writes; want to stop on write %d", writer.writes, tc.failAfter+1)
			}
		})
	}
}

func TestGenArgumentErrorOrder(t *testing.T) {
	for _, tc := range []struct {
		args []string
		want string
	}{
		{[]string{"--seed", "bad", "--workers", "0"}, "invalid nonnegative integer for --seed"},
		{[]string{"--count", "bad", "--tick", "0"}, "invalid nonnegative integer for --count"},
		{[]string{"--count", "bad", "--seed", "bad"}, "invalid nonnegative integer for --seed"},
		{[]string{"--seed", "1", "--count", "1", "--workers", "0"}, "workers, tick and max-states must be positive"},
	} {
		var stdout, stderr bytes.Buffer
		code, err := run(append([]string{"gen"}, tc.args...), &stdout, &stderr)
		if code != 2 || err == nil || err.Error() != tc.want {
			t.Errorf("%q: got exit %d, %v; want %q", tc.args, code, err, tc.want)
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
	code, err = run([]string{"check", path, "--graph", "../../../../Test/graphs/minimal.json"}, &out, &stderr)
	if err != nil || code != 0 {
		t.Fatalf("check: %d %v %s", code, err, &stderr)
	}
}
