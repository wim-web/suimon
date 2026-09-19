package main

import (
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"math/big"
	"os"
	"os/exec"
	"path/filepath"
	"reflect"
	"strings"
	"testing"
	"time"
)

type cliResult struct {
	code           int
	stdout, stderr []byte
}

type cliPair struct{ lean, goCLI, root string }

func comparisonCLIs(t *testing.T) cliPair {
	t.Helper()
	lean, goCLI := os.Getenv("SUIMON_LEAN_CLI"), os.Getenv("SUIMON_GO_CLI")
	if lean == "" && goCLI == "" {
		t.Skip("run bin/test-go for comparisons of the compiled Lean and Go CLIs")
	}
	if lean == "" || goCLI == "" {
		t.Fatal("both SUIMON_LEAN_CLI and SUIMON_GO_CLI are required")
	}
	root, err := filepath.Abs("../../../..")
	if err != nil {
		t.Fatal(err)
	}
	return cliPair{lean, goCLI, root}
}

func runBinary(t *testing.T, root, binary string, args []string) cliResult {
	t.Helper()
	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()
	cmd := exec.CommandContext(ctx, binary, args...)
	cmd.Dir = root
	var stdout, stderr bytes.Buffer
	cmd.Stdout, cmd.Stderr = &stdout, &stderr
	err := cmd.Run()
	if ctx.Err() != nil {
		t.Fatalf("CLI timed out: %s %q", binary, args)
	}
	code := 0
	if err != nil {
		var exit *exec.ExitError
		if !errors.As(err, &exit) {
			t.Fatal(err)
		}
		code = exit.ExitCode()
	}
	return cliResult{code, stdout.Bytes(), stderr.Bytes()}
}

// Normalize only the numeric spelling of CLI output, without float64 rounding.
// This comparison is independent of the runtime's JSON and Nat implementations.
type exactJSONNumber string

func normalizeCLIJSON(t *testing.T, v any) any {
	t.Helper()
	switch v := v.(type) {
	case json.Number:
		n, ok := new(big.Rat).SetString(string(v))
		if !ok {
			t.Fatalf("invalid JSON number: %s", v)
		}
		return exactJSONNumber(n.RatString())
	case []any:
		for i := range v {
			v[i] = normalizeCLIJSON(t, v[i])
		}
	case map[string]any:
		for k := range v {
			v[k] = normalizeCLIJSON(t, v[k])
		}
	}
	return v
}

func jsonRecords(t *testing.T, data []byte, parserMessage bool) []any {
	t.Helper()
	d := json.NewDecoder(bytes.NewReader(data))
	d.UseNumber()
	var records []any
	for {
		var v any
		err := d.Decode(&v)
		if err == io.EOF {
			break
		}
		if err != nil {
			t.Fatalf("invalid CLI JSON output: %v\n%s", err, data)
		}
		if parserMessage {
			if object, ok := v.(map[string]any); ok {
				if reason, ok := object["reason"].(map[string]any); ok && reason["code"] == "INVALID_JSON" {
					if message, ok := reason["message"].(string); !ok || message == "" {
						t.Fatal("missing parser diagnostic")
					}
					// Parser wording is documented as implementation dependent.
					reason["message"] = "<parser diagnostic>"
				}
			}
		}
		records = append(records, normalizeCLIJSON(t, v))
	}
	return records
}

func (p cliPair) compare(t *testing.T, args []string, wantCode int, jsonOutput, parserMessage bool) (cliResult, cliResult) {
	t.Helper()
	lean := runBinary(t, p.root, p.lean, args)
	goCLI := runBinary(t, p.root, p.goCLI, args)
	if lean.code != wantCode || goCLI.code != wantCode {
		t.Fatalf("%q: want exit %d; Lean=%d Go=%d\nLean: %s%s\nGo: %s%s", args, wantCode, lean.code, goCLI.code, lean.stdout, lean.stderr, goCLI.stdout, goCLI.stderr)
	}
	for _, stream := range []struct {
		name        string
		lean, goCLI []byte
	}{{"stdout", lean.stdout, goCLI.stdout}, {"stderr", lean.stderr, goCLI.stderr}} {
		if jsonOutput {
			if !reflect.DeepEqual(jsonRecords(t, stream.lean, parserMessage), jsonRecords(t, stream.goCLI, parserMessage)) {
				t.Fatalf("%q %s differs\nLean: %s\nGo: %s", args, stream.name, stream.lean, stream.goCLI)
			}
		} else if !bytes.Equal(stream.lean, stream.goCLI) {
			t.Fatalf("%q %s differs\nLean: %s\nGo: %s", args, stream.name, stream.lean, stream.goCLI)
		}
	}
	return lean, goCLI
}

func TestCLICompatibilityFixtures(t *testing.T) {
	p := comparisonCLIs(t)
	for _, tc := range []struct {
		trace, graph string
		code         int
	}{
		{"minimal", "minimal", 0}, {"coalesce", "coalesce", 0}, {"loop-retry", "loop", 0},
		{"missing-attempt", "minimal", 1}, {"after-eos", "minimal", 1},
	} {
		t.Run(tc.trace, func(t *testing.T) {
			p.compare(t, []string{"check", "Test/traces/" + tc.trace + ".jsonl", "--graph", "Test/graphs/" + tc.graph + ".json"}, tc.code, true, false)
		})
	}
}

func TestCLICompatibilityExploreAndGenerate(t *testing.T) {
	p := comparisonCLIs(t)
	graphs, err := filepath.Glob(filepath.Join(p.root, "Test/graphs/*.json"))
	if err != nil {
		t.Fatal(err)
	}
	if len(graphs) == 0 {
		t.Fatal("no graph fixtures found")
	}
	for _, graph := range graphs {
		t.Run(filepath.Base(graph), func(t *testing.T) {
			p.compare(t, []string{"explore", "--graph", graph, "--depth", "5", "--workers", "2"}, 0, true, false)
			for _, seed := range []string{"1", "3", "17"} {
				t.Run("seed-"+seed, func(t *testing.T) {
					lean, goCLI := p.compare(t, []string{"gen", "--graph", graph, "--seed", seed, "--count", "30"}, 0, true, false)
					if len(lean.stdout) == 0 || len(goCLI.stdout) == 0 {
						t.Fatal("empty generated trace")
					}
					for name, trace := range map[string][]byte{"lean": lean.stdout, "go": goCLI.stdout} {
						path := filepath.Join(t.TempDir(), name+".jsonl")
						if err := os.WriteFile(path, trace, 0600); err != nil {
							t.Fatal(err)
						}
						// Both CLIs must accept both generated spellings and report
						// the same event count, status and committed transactions.
						p.compare(t, []string{"check", path, "--graph", graph}, 0, true, false)
					}
				})
			}
		})
	}
	t.Run("default-graph", func(t *testing.T) { p.compare(t, []string{"gen", "--seed", "17", "--count", "30"}, 0, true, false) })
}

func TestCLICompatibilityNumericOptions(t *testing.T) {
	p := comparisonCLIs(t)
	for _, key := range []string{"--depth", "--workers", "--tick", "--max-states", "--seed", "--count"} {
		t.Run(key, func(t *testing.T) {
			for _, value := range []string{"1_0", "01_0", "0_0", "_10", "10_", "1__0", "1_0_", "", "+1", "1.0", "１_０"} {
				t.Run(fmt.Sprintf("%q", value), func(t *testing.T) {
					var args []string
					if key == "--seed" {
						args = []string{"gen", "--count", "2"}
					} else if key == "--count" {
						args = []string{"gen", "--seed", "17"}
					} else if key == "--depth" {
						args = []string{"explore", "--graph", "Test/graphs/minimal.json", "--max-states", "1"}
					} else {
						args = []string{"explore", "--graph", "Test/graphs/minimal.json", "--depth", "0"}
					}
					args = append(args, key, value)
					code := 2
					if value == "1_0" || value == "01_0" || value == "0_0" {
						code = 0
						if key == "--depth" && value != "0_0" {
							code = 1
						}
						if value == "0_0" && (key == "--workers" || key == "--tick" || key == "--max-states") {
							code = 2
						}
					}
					p.compare(t, args, code, code != 2, false)
				})
			}
		})
	}
	t.Run("large-seed", func(t *testing.T) {
		p.compare(t, []string{"gen", "--seed", "18_446_744_073_709_551_616", "--count", "3"}, 0, true, false)
	})
	for _, args := range [][]string{
		{"gen", "--seed", "bad", "--workers", "0"},
		{"gen", "--count", "bad", "--tick", "0"},
		{"gen", "--seed", "bad", "--count", "bad"},
		{"gen", "--seed", "1", "--seed", "2"},
		{"gen", "--typo", "1"},
		{"gen", "--seed"},
	} {
		t.Run(strings.Join(args, " "), func(t *testing.T) { p.compare(t, args, 2, false, false) })
	}
}

func TestCLICompatibilityInvalidRecords(t *testing.T) {
	p := comparisonCLIs(t)
	b, err := os.ReadFile(filepath.Join(p.root, "Test/traces/minimal.jsonl"))
	if err != nil {
		t.Fatal(err)
	}
	base := string(b)
	lines := strings.Split(strings.TrimSuffix(base, "\n"), "\n")
	mutateFirst := func(key string, v json.RawMessage) string {
		var event map[string]json.RawMessage
		if err := json.Unmarshal([]byte(lines[0]), &event); err != nil {
			t.Fatal(err)
		}
		if v == nil {
			delete(event, key)
		} else {
			event[key] = v
		}
		first, err := json.Marshal(event)
		if err != nil {
			t.Fatal(err)
		}
		return string(first) + "\n" + strings.Join(lines[1:], "\n") + "\n"
	}
	for _, tc := range []struct {
		name, text, reason string
		code               int
	}{
		{"extra-key", mutateFirst("extra", json.RawMessage("true")), "INVALID_JSON", 1},
		{"missing-key", mutateFirst("op", nil), "INVALID_JSON", 1},
		{"decimal-version", mutateFirst("schema_version", json.RawMessage("2.0")), "INVALID_JSON", 1},
		{"decimal-exponent", mutateFirst("schema_version", json.RawMessage("20e-1")), "INVALID_JSON", 1},
		{"integer-exponent", mutateFirst("schema_version", json.RawMessage("2e-0")), "", 0},
		{"blank-line", "\n" + base, "INVALID_JSON", 1},
		{"crlf", strings.ReplaceAll(base, "\n", "\r\n"), "", 0},
		{"no-final-newline", strings.TrimSuffix(base, "\n"), "", 0},
		{"torn-line", base[:len(base)-5], "INVALID_JSON", 1},
		{"uncommitted", strings.Join(lines[:len(lines)-1], "\n") + "\n", "TRUNCATED_TRANSACTION", 1},
		{"sequence-gap", mutateFirst("sequence", json.RawMessage("2")), "SEQUENCE", 1},
		{"wrong-command", mutateFirst("type", json.RawMessage(`"wrong"`)), "COMMAND_MISMATCH", 1},
	} {
		t.Run(tc.name, func(t *testing.T) {
			path := filepath.Join(t.TempDir(), tc.name+".jsonl")
			if err := os.WriteFile(path, []byte(tc.text), 0600); err != nil {
				t.Fatal(err)
			}
			_, got := p.compare(t, []string{"check", path, "--graph", "Test/graphs/minimal.json"}, tc.code, true, tc.reason == "INVALID_JSON")
			if tc.reason != "" {
				var diagnostic struct {
					Reason struct {
						Code string `json:"code"`
					} `json:"reason"`
				}
				if err := json.Unmarshal(got.stderr, &diagnostic); err != nil {
					t.Fatal(err)
				}
				if diagnostic.Reason.Code != tc.reason {
					t.Fatalf("want %s, got %s", tc.reason, diagnostic.Reason.Code)
				}
			}
		})
	}
}
