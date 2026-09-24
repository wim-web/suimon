package main

import (
	"bytes"
	"encoding/json"
	"errors"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"reflect"
	"sort"
	"strings"
	"testing"

	suimon "github.com/wim-web/suimon/implementations/go/src"
)

// Conformance tests compare this CLI with the Lean CLI named by SUIMON_LEAN_CLI (a relative path is
// resolved from the repository root); they are skipped when it is not set.

func leanCLI(t *testing.T) string {
	t.Helper()
	path := os.Getenv("SUIMON_LEAN_CLI")
	if path == "" {
		t.Skip("SUIMON_LEAN_CLI is not set")
	}
	if !filepath.IsAbs(path) {
		path = filepath.Join(repoRoot(t), path)
	}
	if _, err := os.Stat(path); err != nil {
		t.Fatalf("SUIMON_LEAN_CLI: %v", err)
	}
	return path
}

func runLean(t *testing.T, cli string, args ...string) result {
	t.Helper()
	cmd := exec.Command(cli, args...)
	cmd.Dir = repoRoot(t)
	var stdout, stderr bytes.Buffer
	cmd.Stdout, cmd.Stderr = &stdout, &stderr
	err := cmd.Run()
	var exit *exec.ExitError
	if err != nil && !errors.As(err, &exit) {
		t.Fatalf("%s %v: %v", cli, args, err)
	}
	return result{cmd.ProcessState.ExitCode(), stdout.String(), stderr.String()}
}

// conformanceDefinitions are the definitions of the Lean tests and the extra ones of the Go tests.
func conformanceDefinitions(t *testing.T) []string {
	t.Helper()
	var paths []string
	for _, pattern := range []string{filepath.Join(repoRoot(t), "Test", "definitions", "*.json"),
		filepath.Join("..", "..", "src", "testdata", "*.json")} {
		matches, err := filepath.Glob(pattern)
		if err != nil {
			t.Fatal(err)
		}
		for _, match := range matches {
			abs, err := filepath.Abs(match)
			if err != nil {
				t.Fatal(err)
			}
			paths = append(paths, abs)
		}
	}
	if len(paths) < 5 {
		t.Fatalf("definitions not found: %v", paths)
	}
	return paths
}

func baseName(path string) string { return strings.TrimSuffix(filepath.Base(path), ".json") }

func sameResult(t *testing.T, label string, lean, goResult result) {
	t.Helper()
	if lean != goResult {
		t.Errorf("%s:\n  Lean: exit %d, stdout %q, stderr %q\n  Go:   exit %d, stdout %q, stderr %q", label,
			lean.code, lean.stdout, lean.stderr, goResult.code, goResult.stdout, goResult.stderr)
	}
}

// A definition as a generic JSON document, so that mutations do not go through the Go codec.

type doc = map[string]any

func loadDoc(t *testing.T, name string) doc {
	t.Helper()
	data, err := os.ReadFile(definition(t, name))
	if err != nil {
		t.Fatal(err)
	}
	var d doc
	if err := json.Unmarshal(data, &d); err != nil {
		t.Fatal(err)
	}
	return d
}

func items(v any) []any { return v.([]any) }

func find(list any, key, value string) doc {
	for _, item := range items(list) {
		if item.(doc)[key] == value {
			return item.(doc)
		}
	}
	panic(fmt.Sprintf("no item with %s %s", key, value))
}

func workflow(d doc, id string) doc { return find(d["workflows"], "id", id) }

func placement(w doc, name string) doc { return find(w["placements"], "name", name) }

func connection(w doc, source, target string) doc {
	for _, item := range items(w["connections"]) {
		if c := item.(doc); c["source"] == source && c["target"] == target {
			return c
		}
	}
	panic("no connection")
}

func drop(list any, keep func(doc) bool) []any {
	var out []any
	for _, item := range items(list) {
		if keep(item.(doc)) {
			out = append(out, item)
		}
	}
	return out
}

func task(pl doc, name string) doc { return find(pl["node"].(doc)["tasks"], "name", name) }

// mutations mirror the rejected definitions of Test/Validate.lean, and a few more.
func mutations() map[string]func(t *testing.T) any {
	with := func(name string, f func(d doc)) func(t *testing.T) any {
		return func(t *testing.T) any {
			d := loadDoc(t, name)
			f(d)
			return d
		}
	}
	return map[string]func(t *testing.T) any{
		"duplicate placement": with("merge", func(d doc) {
			w := workflow(d, "dashboard")
			w["placements"] = append(items(w["placements"]), items(w["placements"])[0])
		}),
		"unknown main": with("merge", func(d doc) { d["main"] = "nope" }),
		"unknown transform": with("merge", func(d doc) {
			connection(workflow(d, "dashboard"), "sales", "archive")["transform"] = "nope"
		}),
		"unknown output endpoint": with("users", func(d doc) {
			task(placement(workflow(d, "users"), "perUser"), "profile")["body"].(doc)["output"] = "fetch"
		}),
		"transform input": with("merge", func(d doc) {
			connection(workflow(d, "dashboard"), "sales", "archive")["transform"] = "stockWidget"
		}),
		"transform output": with("merge", func(d doc) {
			connection(workflow(d, "dashboard"), "sales", "archive")["transform"] = "salesWidget"
		}),
		"entry type": with("users", func(d doc) {
			workflow(d, "users")["input"] = doc{"type": doc{"list": "Org"}, "placement": "fetchAllUsers"}
		}),
		"task input transform": with("users", func(d doc) {
			delete(task(placement(workflow(d, "users"), "perUser"), "orders"), "inputTransform")
		}),
		"task output transform": with("users", func(d doc) {
			task(placement(workflow(d, "users"), "perUser"), "orders")["outputTransform"] = "profileSummary"
		}),
		"two inputs": with("merge", func(d doc) {
			w := workflow(d, "dashboard")
			w["connections"] = append(items(w["connections"]), connection(w, "sales", "archive"))
		}),
		"missing input": with("merge", func(d doc) {
			w := workflow(d, "dashboard")
			w["connections"] = drop(w["connections"], func(c doc) bool { return c["target"] != "archive" })
		}),
		"input to a node without input": with("merge", func(d doc) {
			w := workflow(d, "dashboard")
			w["connections"] = append(items(w["connections"]), doc{"source": "sales", "target": "stock", "transform": "sales"})
		}),
		"Merge entry": with("merge", func(d doc) {
			workflow(d, "dashboard")["input"] = doc{"type": "Widget", "placement": "widgets"}
		}),
		"discard to a node with input": with("merge", func(d doc) {
			connection(workflow(d, "dashboard"), "sales", "archive")["transform"] = "discard"
		}),
		"two discard connections": with("merge", func(d doc) {
			w := workflow(d, "dashboard")
			w["connections"] = append(items(w["connections"]), doc{"source": "stock", "target": "notify", "transform": "discard"})
		}),
		"declared discard": with("merge", func(d doc) {
			d["transforms"] = append(items(d["transforms"]), doc{"id": "discard", "input": "A", "output": "A"})
		}),
		"recursive call": with("users", func(d doc) {
			placement(workflow(d, "profileFlow"), "format")["node"] = doc{"type": "subworkflow", "workflow": "profileFlow", "output": "format"}
		}),
		"cycle": with("merge", func(d doc) {
			w := workflow(d, "dashboard")
			w["connections"] = append(items(w["connections"]), doc{"source": "archive", "target": "sales", "transform": "discard"})
		}),
		"waitStream on Single": with("merge", func(d doc) {
			placement(workflow(d, "dashboard"), "page")["node"] = doc{"type": "waitStream", "element": doc{"list": "Widget"}}
		}),
		"Merge of Stream": with("branch", func(d doc) {
			placement(workflow(d, "shipping"), "receipts")["node"] = doc{"type": "merge", "element": "Receipt"}
		}),
		"Stream endpoint": with("branch", func(d doc) {
			w := workflow(d, "shipping")
			w["connections"] = drop(w["connections"], func(c doc) bool { return c["target"] != "receipts" })
			w["placements"] = drop(w["placements"], func(pl doc) bool { return pl["name"] != "receipts" })
		}),
		"no connected arm": with("branch", func(d doc) {
			w := workflow(d, "shipping")
			w["connections"] = drop(w["connections"], func(c doc) bool { return c["target"] != "ship" })
		}),
		"unknown arm": with("branch", func(d doc) { connection(workflow(d, "shipping"), "paid", "ship")["arm"] = "refunded" }),
		"missing arm": with("branch", func(d doc) { delete(connection(workflow(d, "shipping"), "paid", "ship"), "arm") }),
		"arm outside a branch": with("merge", func(d doc) {
			connection(workflow(d, "dashboard"), "sales", "archive")["arm"] = "x"
		}),
		"zero limit": with("users", func(d doc) { placement(workflow(d, "users"), "perUser")["node"].(doc)["limit"] = 0 }),
		"no task in the output": with("users", func(d doc) {
			for _, item := range items(placement(workflow(d, "users"), "perUser")["node"].(doc)["tasks"]) {
				delete(item.(doc), "outputTransform")
			}
		}),
		"timeout on waitStream": with("users", func(d doc) { placement(workflow(d, "users"), "all")["timeout"] = doc{"callMs": 10} }),
		"element timeout on Single": with("merge", func(d doc) {
			placement(workflow(d, "dashboard"), "sales")["timeout"] = doc{"elementMs": 10}
		}),
		"zero timeout": with("branch", func(d doc) { placement(workflow(d, "shipping"), "paid")["timeout"] = doc{"callMs": 0} }),
		"task timeout on a sub-workflow": with("users", func(d doc) {
			task(placement(workflow(d, "users"), "perUser"), "profile")["timeout"] = doc{"callMs": 5}
		}),
		"unknown judge": with("branch", func(d doc) { placement(workflow(d, "shipping"), "paid")["node"].(doc)["judge"] = "isFree" }),
		// Without connections and not the entry, the branch reaches the check of its placement.
		"unknown judge of a placement": with("branch", func(d doc) {
			w := workflow(d, "shipping")
			w["placements"] = append(items(w["placements"]),
				doc{"name": "orphan", "node": doc{"type": "branch", "judge": "nope", "arms": []any{"a"}}, "policy": "stop"})
		}),
		"duplicate arms": with("branch", func(d doc) {
			placement(workflow(d, "shipping"), "paid")["node"].(doc)["arms"] = []any{"paid", "paid"}
		}),
		"duplicate task": with("users", func(d doc) {
			node := placement(workflow(d, "users"), "perUser")["node"].(doc)
			node["tasks"] = append(items(node["tasks"]), items(node["tasks"])[0])
		}),
		"unknown source":     with("merge", func(d doc) { connection(workflow(d, "dashboard"), "sales", "archive")["source"] = "x" }),
		"empty workflow":     with("merge", func(d doc) { workflow(d, "dashboard")["placements"] = []any{} }),
		"duplicate workflow": with("users", func(d doc) { d["workflows"] = append(items(d["workflows"]), workflow(d, "profileFlow")) }),
		"list type mismatch": with("users", func(d doc) {
			placement(workflow(d, "users"), "all")["node"] = doc{"type": "waitStream", "element": doc{"list": doc{"list": "Summary"}}}
		}),
	}
}

// texts are definitions written as text: JSON syntax, strict decoding and numbers.
var texts = map[string]string{
	"empty":           "",
	"syntax":          `{"main":"w",}`,
	"trailing":        `{"main":"w","workflows":[]} x`,
	"bad escape":      `{"main":"\q"}`,
	"bad hex":         `{"main":"é\u00zz"}`,
	"control char":    "{\"main\":\"a\x01\"}",
	"lone surrogates": `{"main":"\ud83d","workflows":[{"id":"\ude00","placements":[]}]}`,
	"surrogate pair":  `{"main":"\ud83d\ude00","workflows":[]}`,
	"unknown field":   `{"main":"w","workflows":[{"id":"w","placements":[{"name":"a","node":{"type":"merge","element":"T"},"policy":"stop","retries":1}]}]}`,
	"sorted unknown":  `{"z":1,"main":"w","b":2}`,
	"missing policy":  `{"main":"w","workflows":[{"id":"w","placements":[{"name":"a","node":{"type":"merge","element":"T"}}]}]}`,
	"unknown policy":  `{"main":"w","workflows":[{"id":"w","placements":[{"name":"a","node":{"type":"merge","element":"T"},"policy":"retry"}]}]}`,
	"null optional":   `{"main":"w","functions":[{"id":"f","input":null,"output":{"single":"A"}}]}`,
	"empty name":      `{"main":"w","workflows":[{"id":"","placements":[]}]}`,
	"arms":            `{"main":"w","workflows":[{"id":"w","placements":[{"name":"b","node":{"type":"branch","judge":"j","arms":["a",1]},"policy":"stop"}]}]}`,
	"limit 2.0":       limitDefinition("2.0"),
	"limit 20e-1":     limitDefinition("20e-1"),
	"limit 0.2e1":     limitDefinition("0.2e1"),
	"limit 0.0":       limitDefinition("0.0"),
	"limit 2.5":       limitDefinition("2.5"),
	"limit -1":        limitDefinition("-1"),
	"limit 1e-1":      limitDefinition("1e-1"),
	"limit 1e-10^9":   limitDefinition("1e-1000000000"),
	"limit 2^64-1":    limitDefinition("18446744073709551615"),
	"limit 2^64":      limitDefinition("18446744073709551616"),
	"limit 1e20":      limitDefinition("1e20"),
	"limit 1e10^9":    limitDefinition("1e1000000000"),
	"limit 0e10^9":    limitDefinition("0e1000000000"),
	"callMs 2^64":     callMsDefinition("1.8446744073709551616e19"),
	"callMs 1.5e3":    callMsDefinition("1.5e3"),
	"callMs 0.0":      callMsDefinition("0.0"),
	"callMs 25e-1":    callMsDefinition("25e-1"),
	"limit -0":        `{"main":"w","workflows":[{"id":"w","placements":[{"name":"c","node":{"type":"concurrency","limit":-0,"tasks":[],"output":"list","element":"T"},"policy":"stop"}]}]}`,
	"limit 1e1":       `{"main":"w","workflows":[{"id":"w","placements":[{"name":"c","node":{"type":"concurrency","limit":1e1,"tasks":[],"output":"list","element":"T"},"policy":"stop"}]}]}`,
	"exp too large":   `{"main":"w","limit":1e99999999999999999999}`,
	"duplicate key":   `{"main":"x","main":"w","workflows":[{"id":"w","placements":[{"name":"a","node":{"type":"function","function":"f"},"policy":"stop"}]}],"functions":[{"id":"f","output":{"single":"A"}}]}`,
	// A key repeated deep inside, one that only its escapes reveal, and one that quoting must escape.
	"duplicate nested key":  `{"main":"w","workflows":[{"id":"w","placements":[{"name":"a","node":{"type":"merge","element":"T","type":"merge"},"policy":"stop"}]}]}`,
	"duplicate escaped key": `{"main":"x","workflows":[],"\u006d\u0061in":"w"}`,
	"duplicate quoted key":  `{"main":"w","workflows":[{"id":"w","placements":[],"\n'\u0001\u007f\"é":1,"\n'\u0001\u007f\"\u00e9":2}]}`,
	"nested list":           `{"main":"w","functions":[{"id":"f","output":{"single":{"list":{"list":{"lst":"A"}}}}}]}`,
	"body type":             `{"main":"w","workflows":[{"id":"w","placements":[{"name":"a","node":{"type":"function"},"policy":"stop"}]}]}`,
	"subworkflow body":      `{"main":"w","workflows":[{"id":"w","placements":[{"name":"a","node":{"type":"subworkflow","workflow":"v","output":"o","x":1},"policy":"stop"}]}]}`,
	"not an object":         `[1,2]`,
	// Empty identifiers and type names, which validation also rejects in a definition built in code.
	"empty function id":  `{"main":"w","functions":[{"id":"","output":{"single":"A"}}]}`,
	"empty judge id":     `{"main":"w","judges":[{"id":"","input":"A"}]}`,
	"empty transform id": `{"main":"w","transforms":[{"id":"","input":"A","output":"A"}]}`,
	"empty list type":    `{"main":"w","transforms":[{"id":"t","input":"A","output":{"list":""}}]}`,
	"empty entry type":   `{"main":"w","workflows":[{"id":"w","input":{"type":"","placement":"a"},"placements":[]}]}`,
	"empty element type": `{"main":"w","workflows":[{"id":"w","placements":[{"name":"a","node":{"type":"waitStream","element":""},"policy":"stop"}]}]}`,
}

// limitDefinition is a valid definition whose concurrency limit is the JSON number limit.
func limitDefinition(limit string) string {
	return `{"main":"w","functions":[{"id":"f","output":{"single":"T"}}],"transforms":[{"id":"t","input":"T","output":"T"}],` +
		`"workflows":[{"id":"w","placements":[{"name":"c","policy":"stop","node":{"type":"concurrency","limit":` + limit +
		`,"tasks":[{"name":"a","body":{"type":"function","function":"f"},"outputTransform":"t","policy":"stop"}],` +
		`"output":"list","element":"T"}}]}]}`
}

// callMsDefinition is a valid definition whose call timeout is the JSON number callMs.
func callMsDefinition(callMs string) string {
	return `{"main":"w","functions":[{"id":"f","output":{"single":"T"}}],"workflows":[{"id":"w","placements":[` +
		`{"name":"a","policy":"stop","timeout":{"callMs":` + callMs + `},"node":{"type":"function","function":"f"}}]}]}`
}

// mergeChainDefinition is a function followed by n Merges, each with two connections from the one
// before; diamondsDefinition is a function followed by n diamonds, two calls after the end of the
// previous diamond whose results a Merge collects. Lean's Workflow.kind? derives their kinds in time
// exponential in n, which compiled code avoids (Workflow.kindFast).
func mergeChainDefinition(t *testing.T, n int) string {
	t.Helper()
	placements := []any{doc{"name": "p0", "node": doc{"type": "function", "function": "f"}, "policy": "stop"}}
	var connections []any
	for i := 1; i <= n; i++ {
		transforms := []string{"l1", "l2"}
		if i == 1 {
			transforms = []string{"t1", "t2"}
		}
		placements = append(placements, doc{"name": fmt.Sprintf("p%d", i), "node": doc{"type": "merge", "element": "T"}, "policy": "stop"})
		for _, transform := range transforms {
			connections = append(connections, doc{"source": fmt.Sprintf("p%d", i-1), "target": fmt.Sprintf("p%d", i), "transform": transform})
		}
	}
	return chainDefinition(t, doc{"main": "w", "functions": []any{doc{"id": "f", "output": doc{"single": "T"}}},
		"transforms": []any{doc{"id": "t1", "input": "T", "output": "T"}, doc{"id": "t2", "input": "T", "output": "T"},
			doc{"id": "l1", "input": doc{"list": "T"}, "output": "T"}, doc{"id": "l2", "input": doc{"list": "T"}, "output": "T"}},
		"workflows": []any{doc{"id": "w", "placements": placements, "connections": connections}}})
}

func diamondsDefinition(t *testing.T, n int) string {
	t.Helper()
	placements := []any{doc{"name": "s0", "node": doc{"type": "function", "function": "f"}, "policy": "stop"}}
	var connections []any
	for i := 1; i <= n; i++ {
		into := "l"
		if i == 1 {
			into = "t"
		}
		for _, side := range []string{"b", "c"} {
			name := fmt.Sprintf("%s%d", side, i)
			placements = append(placements, doc{"name": name, "node": doc{"type": "function", "function": "g"}, "policy": "stop"})
			connections = append(connections, doc{"source": fmt.Sprintf("s%d", i-1), "target": name, "transform": into},
				doc{"source": name, "target": fmt.Sprintf("s%d", i), "transform": "t"})
		}
		placements = append(placements, doc{"name": fmt.Sprintf("s%d", i), "node": doc{"type": "merge", "element": "T"}, "policy": "stop"})
	}
	return chainDefinition(t, doc{"main": "w",
		"functions":  []any{doc{"id": "f", "output": doc{"single": "T"}}, doc{"id": "g", "input": "T", "output": doc{"single": "T"}}},
		"transforms": []any{doc{"id": "t", "input": "T", "output": "T"}, doc{"id": "l", "input": doc{"list": "T"}, "output": "T"}},
		"workflows":  []any{doc{"id": "w", "placements": placements, "connections": connections}}})
}

func chainDefinition(t *testing.T, d doc) string {
	t.Helper()
	data, err := json.Marshal(d)
	if err != nil {
		t.Fatal(err)
	}
	return string(data)
}

func TestConformanceValidate(t *testing.T) {
	cli := leanCLI(t)
	dir := t.TempDir()
	check := func(label, path string) result {
		lean := runLean(t, cli, "validate", path)
		t.Logf("%s: exit %d %s", label, lean.code, strings.TrimSpace(lean.stdout+lean.stderr))
		sameResult(t, "validate "+label, lean, runGo("validate", path))
		return lean
	}
	for _, path := range conformanceDefinitions(t) {
		check(filepath.Base(path), path)
	}
	for label, mutate := range mutations() {
		data, err := json.Marshal(mutate(t))
		if err != nil {
			t.Fatal(err)
		}
		path := filepath.Join(dir, strings.ReplaceAll(label, " ", "-")+".json")
		if err := os.WriteFile(path, data, 0o644); err != nil {
			t.Fatal(err)
		}
		lean := check(label, path)
		if label == "unknown judge of a placement" && lean.stderr != "shipping.orphan: unknown judge nope\n" {
			t.Errorf("%s: not the error of the placement: %q", label, lean.stderr)
		}
	}
	for label, text := range texts {
		path := filepath.Join(dir, strings.ReplaceAll(label, " ", "-")+".txt")
		if err := os.WriteFile(path, []byte(text), 0o644); err != nil {
			t.Fatal(err)
		}
		check(label, path)
	}
	for label, text := range map[string]string{"merge chain 20": mergeChainDefinition(t, 20),
		"merge chain 40": mergeChainDefinition(t, 40), "30 diamonds": diamondsDefinition(t, 30)} {
		path := filepath.Join(dir, strings.ReplaceAll(label, " ", "-")+".json")
		if err := os.WriteFile(path, []byte(text), 0o644); err != nil {
			t.Fatal(err)
		}
		if lean := check(label, path); lean.code != 0 {
			t.Errorf("%s: rejected: %s", label, lean.stderr)
		}
	}
	nonUTF8 := filepath.Join(dir, "latin1.json")
	if err := os.WriteFile(nonUTF8, []byte("{\"main\":\"\xe9\"}"), 0o644); err != nil {
		t.Fatal(err)
	}
	check("non UTF-8", nonUTF8)
	check("missing file", filepath.Join(dir, "missing.json"))
}

func TestConformanceArguments(t *testing.T) {
	cli := leanCLI(t)
	merge := definition(t, "merge")
	for _, args := range [][]string{
		{}, {"--help"}, {"help"}, {"--help", "x"}, {"validate"}, {"validate", "a", "b"}, {"frobnicate"},
		{"check", merge}, {"check", "x.jsonl", "--definition", merge}, {"explore", merge, "--seeds"}, {"explore", merge, "--bogus", "1"},
		{"explore", merge, "--seeds", "x"}, {"explore", merge, "--seeds", "1_0", "--steps", "5"},
		{"explore", merge, "--seeds", "0"}, {"explore", merge, "--seeds", "3", "--seeds", "5"},
		{"gen", merge, "--seed", "3", "--steps", "0"}, {"gen", merge, "--seed", "-1"}, {"gen", merge, "--steps", "1_"},
		{"check", "x.jsonl", "--state"}, {"check", "x.jsonl", "--state", "--definition"}, {"check", "x.jsonl", "--definition"},
		{"check", "x.jsonl", "--state", "1", "--definition", merge}, {"explore", merge, "--state"},
	} {
		sameResult(t, fmt.Sprint(args), runLean(t, cli, args...), runGo(args...))
	}
}

func TestConformanceExplore(t *testing.T) {
	cli := leanCLI(t)
	for _, path := range conformanceDefinitions(t) {
		for _, args := range [][]string{{"--seeds", "200"}, {"--seeds", "20", "--steps", "40"}, {"--seeds", "5", "--steps", "3"}} {
			args = append([]string{"explore", path}, args...)
			sameResult(t, fmt.Sprint(baseName(path), args[2:]), runLean(t, cli, args...), runGo(args...))
		}
	}
	// Every settle derives kinds, which the Go engine derives once per workflow.
	dir := t.TempDir()
	for label, text := range map[string]string{"merge chain 20": mergeChainDefinition(t, 20), "10 diamonds": diamondsDefinition(t, 10)} {
		path := filepath.Join(dir, strings.ReplaceAll(label, " ", "-")+".json")
		if err := os.WriteFile(path, []byte(text), 0o644); err != nil {
			t.Fatal(err)
		}
		for _, args := range [][]string{{"--seeds", "20"}, {"--seeds", "20", "--steps", "40"}} {
			args = append([]string{"explore", path}, args...)
			sameResult(t, fmt.Sprint(label, args[2:]), runLean(t, cli, args...), runGo(args...))
		}
	}
}

// conformanceSeeds include seeds beyond 2^32 and 2^64: a walk uses the seed modulo 2^64.
var conformanceSeeds = []string{"1", "2", "3", "4", "5", "7", "11", "42", "4294967299", "18446744073709551619"}

// header is the header line of the records of the definition at path, as Lean gen writes it.
func header(t *testing.T, cli, path string) string {
	t.Helper()
	generated := runLean(t, cli, "gen", path, "--steps", "0")
	if generated.code != 0 || strings.Count(generated.stdout, "\n") != 1 {
		t.Fatalf("Lean gen %s --steps 0: %q %s", path, generated.stdout, generated.stderr)
	}
	return generated.stdout
}

// Lean gen writes records that the Go checker accepts with the summary of Lean check.
func TestConformanceCheck(t *testing.T) {
	cli := leanCLI(t)
	dir := t.TempDir()
	for _, path := range conformanceDefinitions(t) {
		name := baseName(path)
		for _, seed := range conformanceSeeds {
			generated := runLean(t, cli, "gen", path, "--seed", seed)
			if generated.code != 0 {
				t.Fatalf("Lean gen %s %s: %s", name, seed, generated.stderr)
			}
			trace := filepath.Join(dir, name+"-"+seed+".jsonl")
			if err := os.WriteFile(trace, []byte(generated.stdout), 0o644); err != nil {
				t.Fatal(err)
			}
			args := []string{"check", trace}
			sameResult(t, fmt.Sprintf("check Lean records %s seed %s", name, seed), runLean(t, cli, args...), runGo(args...))
			// The replayed states are the same, compared as the JSON of Lean's ToJson State.
			args = append(args, "--state")
			sameResult(t, fmt.Sprintf("check --state Lean records %s seed %s", name, seed), runLean(t, cli, args...), runGo(args...))
			// And the other way: Lean check accepts the records Go gen writes.
			goGenerated := runGo("gen", path, "--seed", seed)
			goTrace := filepath.Join(dir, name+"-"+seed+"-go.jsonl")
			if err := os.WriteFile(goTrace, []byte(goGenerated.stdout), 0o644); err != nil {
				t.Fatal(err)
			}
			args = []string{"check", goTrace}
			sameResult(t, fmt.Sprintf("check Go records %s seed %s", name, seed), runLean(t, cli, args...), runGo(args...))
			args = append(args, "--state")
			sameResult(t, fmt.Sprintf("check --state Go records %s seed %s", name, seed), runLean(t, cli, args...), runGo(args...))
		}
	}
}

// A record cut at any line, or inside a line, the header included, is recovered to the same summary
// by both checkers; a corrupted record is rejected by both with the same message.
func TestConformanceTorn(t *testing.T) {
	cli := leanCLI(t)
	dir := t.TempDir()
	for _, path := range conformanceDefinitions(t) {
		generated := runGo("gen", path, "--seed", "3")
		lines := strings.SplitAfter(generated.stdout, "\n")
		lines = lines[:len(lines)-1]
		check := func(label, text string) {
			trace := filepath.Join(dir, "torn.jsonl")
			if err := os.WriteFile(trace, []byte(text), 0o644); err != nil {
				t.Fatal(err)
			}
			args := []string{"check", trace}
			sameResult(t, label, runLean(t, cli, args...), runGo(args...))
		}
		for cut := 0; cut <= len(lines); cut++ {
			prefix := strings.Join(lines[:cut], "")
			label := fmt.Sprintf("%s cut %d", baseName(path), cut)
			check(label, prefix)
			if cut < len(lines) {
				runes := []rune(lines[cut])
				check(label+" half", prefix+string(runes[:len(runes)/2]))
			}
		}
		if len(lines) >= 7 {
			corrupt := append([]string(nil), lines...)
			corrupt[4] = "{\"seq\":4,\"commit\":tru\n"
			check(baseName(path)+" corrupt", strings.Join(corrupt, ""))
			check(baseName(path)+" reordered", lines[0]+lines[2]+lines[1]+strings.Join(lines[3:], ""))
			check(baseName(path)+" commit twice", strings.Join(lines[:3], "")+strings.Replace(lines[2], "2", "3", 1))
			check(baseName(path)+" no header", strings.Join(lines[1:], ""))
			check(baseName(path)+" header twice", lines[0]+strings.Join(lines, ""))
		}
	}
}

// recordTexts are records that are malformed, out of order, rejected by the rules or missing
// payloads, or that stress the parser; both checkers must give the same output for each. They
// follow the header of the definition.
var recordTexts = map[string]string{
	"nothing":               "",
	"empty line":            "\n",
	"crlf":                  "{\"seq\":1,\"op\":{\"type\":\"start\"}}\r\n{\"seq\":2,\"commit\":true}\r\n",
	"spaces":                " { \"op\" : { \"type\" : \"start\" } , \"seq\" : 1 } \n{\"commit\":true,\"seq\":2}\n",
	"unterminated":          "{\"seq\":1,\n",
	"trailing":              "{\"seq\":1,\"op\":{\"type\":\"start\"}} x\n",
	"leading zero":          "{\"seq\":01,\"commit\":true}\n",
	"negative":              "{\"seq\":-1,\"commit\":true}\n",
	"fraction":              "{\"seq\":1.0,\"commit\":true}\n",
	"single quotes":         "{'seq':1}\n",
	"bad escape":            "{\"seq\":1,\"op\":{\"type\":\"st\\art\"}}\n",
	"truncated escape":      "{\"seq\":1,\"op\":{\"type\":\"\\u12\"}}\n",
	"lone surrogate":        "{\"seq\":1,\"op\":{\"type\":\"start\",\"input\":\"\\ud800\"}}\n",
	"surrogate pair":        "{\"seq\":1,\"op\":{\"type\":\"returned\",\"call\":\"\\ud83d\\ude00\",\"value\":\"v\"}}\n{\"seq\":2,\"commit\":true}\n",
	"control character":     "{\"seq\":1,\"op\":{\"type\":\"a\tb\"}}\n",
	"literal":               "{\"seq\":1,\"commit\":tru}\n",
	"missing comma":         "{\"seq\":1 \"commit\":true}\n",
	"trailing comma":        "{\"seq\":1,\"commit\":true,}\n",
	"number key":            "{1:2}\n",
	"not an object":         "[]\n",
	"no seq":                "{\"commit\":true}\n",
	"string seq":            "{\"seq\":\"1\",\"commit\":true}\n",
	"neither":               "{\"seq\":1}\n",
	"commit false":          "{\"seq\":1,\"commit\":false}\n",
	"both":                  "{\"seq\":1,\"op\":{\"type\":\"start\"},\"commit\":true}\n",
	"unknown field":         "{\"seq\":1,\"commit\":true,\"x\":1}\n",
	"op string":             "{\"seq\":1,\"op\":\"start\"}\n",
	"op without type":       "{\"seq\":1,\"op\":{}}\n",
	"type number":           "{\"seq\":1,\"op\":{\"type\":5}}\n",
	"unknown op":            "{\"seq\":1,\"op\":{\"type\":\"retry\"}}\n",
	"null input":            "{\"seq\":1,\"op\":{\"type\":\"start\",\"input\":null}}\n",
	"run string":            "{\"seq\":1,\"op\":{\"type\":\"invoke\",\"run\":\"x\",\"placement\":\"a\"}}\n",
	"run numbers":           "{\"seq\":1,\"op\":{\"type\":\"invoke\",\"run\":[1],\"placement\":\"a\"}}\n",
	"element string":        "{\"seq\":1,\"op\":{\"type\":\"timedOut\",\"call\":\"c\",\"element\":\"no\"}}\n",
	"connection string":     "{\"seq\":1,\"op\":{\"type\":\"deliver\",\"run\":[],\"connection\":\"1\",\"source\":\"s\"}}\n",
	"values array":          "{\"seq\":1,\"op\":{\"type\":\"start\"},\"values\":[]}\n",
	"payload number":        "{\"seq\":1,\"op\":{\"type\":\"start\"},\"values\":{\"v\":1}}\n",
	"op unknown field":      "{\"seq\":1,\"op\":{\"type\":\"fetch\",\"call\":\"c\",\"x\":1}}\n",
	"op missing field":      "{\"seq\":1,\"op\":{\"type\":\"fetch\"}}\n",
	"starts at 2":           "{\"seq\":2,\"op\":{\"type\":\"start\"}}\n",
	"commit first":          "{\"seq\":1,\"commit\":true}\n",
	"op twice":              "{\"seq\":1,\"op\":{\"type\":\"start\"}}\n{\"seq\":2,\"op\":{\"type\":\"cancel\"}}\n",
	"commit twice":          "{\"seq\":1,\"op\":{\"type\":\"start\"}}\n{\"seq\":2,\"commit\":true}\n{\"seq\":3,\"commit\":true}\n",
	"rejected":              "{\"seq\":1,\"op\":{\"type\":\"judged\",\"call\":\"a\\\"b\\\\c\\n\\u0001é\",\"arm\":\"x\"}}\n{\"seq\":2,\"commit\":true}\n",
	"rejected deliver":      "{\"seq\":1,\"op\":{\"type\":\"start\"}}\n{\"seq\":2,\"commit\":true}\n{\"seq\":3,\"op\":{\"value\":\"v\",\"type\":\"deliver\",\"source\":\"s\",\"connection\":3,\"run\":[\"a\",\"b\"]}}\n{\"seq\":4,\"commit\":true}\n",
	"duplicate fields":      "{\"seq\":1,\"seq\":7,\"op\":{\"type\":\"start\"},\"op\":{\"type\":\"cancel\"}}\n{\"seq\":2,\"commit\":true}\n",
	"duplicate payload":     "{\"seq\":1,\"op\":{\"type\":\"start\"},\"values\":{\"v\":\"a\",\"v\":\"b\"}}\n{\"seq\":2,\"commit\":true}\n",
	"duplicate op key":      "{\"seq\":1,\"op\":{\"type\":\"start\"}}\n{\"seq\":2,\"commit\":true}\n{\"seq\":3,\"op\":{\"type\":\"invoke\",\"run\":[],\"placement\":\"sales\",\"placement\":\"stock\"}}\n{\"seq\":4,\"commit\":true}\n",
	"duplicate escaped":     "{\"seq\":1,\"\\u0073eq\":1,\"op\":{\"type\":\"start\"}}\n{\"seq\":2,\"commit\":true}\n",
	"duplicate commit":      "{\"seq\":1,\"op\":{\"type\":\"start\"}}\n{\"seq\":2,\"commit\":true,\"commit\":true}\n",
	"duplicate uncommitted": "{\"seq\":1,\"op\":{\"type\":\"start\"}}\n{\"seq\":2,\"commit\":true}\n{\"seq\":3,\"seq\":3,\"op\":{\"type\":\"cancel\"}}\n",
	"duplicate torn":        "{\"seq\":1,\"op\":{\"type\":\"start\"}}\n{\"seq\":2,\"commit\":true}\n{\"seq\":3,\"seq\":3",
	"huge seq":              "{\"seq\":123456789012345678901234567890,\"commit\":true}\n",
	"torn op":               "{\"seq\":1,\"op\":{\"type\":\"start\"}}\n{\"seq\":2,\"commit\":true}\n{\"seq\":3,\"op\":{\"type\":\"invoke\",\"run\":[],\"placement\":\"sales\"}}\n",
	"torn line":             "{\"seq\":1,\"op\":{\"type\":\"start\"}}\n{\"seq\":2,\"com",
	"header again":          "{\"seq\":1,\"op\":{\"type\":\"start\"}}\n{\"seq\":2,\"commit\":true}\n{\"definition\":{\"main\":\"x\"}}\n",
}

// headerTexts are whole records whose header is missing, torn, malformed, or holds a definition that
// does not decode or validate, or is written in another form; both checkers must give the same
// output for each.
var headerTexts = map[string]string{
	"empty":                "",
	"torn header":          "{\"definition\":{\"main\":\"da",
	"torn character":       "{\"definition\":{\"main\":\"\xe3\x81",
	"no header":            "{\"seq\":1,\"op\":{\"type\":\"start\"}}\n{\"seq\":2,\"commit\":true}\n",
	"empty first line":     "\n",
	"not an object":        "[]\n",
	"without definition":   "{}\n",
	"unknown field":        "{\"definition\":{},\"seq\":0}\n",
	"null definition":      "{\"definition\":null}\n",
	"empty definition":     "{\"definition\":{}}\n",
	"invalid definition":   "{\"definition\":{\"main\":\"w\",\"workflows\":[]}}\n",
	"escaped name":         "{\"definition\":{\"main\":\"a\\nb\\u0001\\u00e9\\ud83d\\ude00\",\"workflows\":[]}}\n",
	"duplicate definition": "{\"definition\":{\"main\":\"w\",\"workflows\":[]},\"definition\":{}}\n",
	"duplicate main":       "{\"definition\":{\"main\":\"x\",\"main\":\"w\",\"workflows\":[]}}\n",
	"duplicate nested key": "{\"definition\":" + strings.TrimSuffix(limitDefinition("2"), "}]}]}") + ",\"policy\":\"stop\"}]}]}}\n" +
		"{\"seq\":1,\"op\":{\"type\":\"start\"}}\n{\"seq\":2,\"commit\":true}\n",
	"duplicate escaped key":  "{\"definition\":{\"main\":\"w\",\"workflows\":[],\"m\\u0061in\":\"w\"}}\n",
	"unknown definition key": "{\"definition\":{\"z\":1,\"main\":\"w\",\"b\":2}}\n",
	"huge limit": "{\"definition\":" + limitDefinition("99999999999999999999999") + "}\n" +
		"{\"seq\":1,\"op\":{\"type\":\"start\"}}\n{\"seq\":2,\"commit\":true}\n",
	"spaced header": " { \"definition\" : " + limitDefinition("2") + " } \n" +
		"{\"seq\":1,\"op\":{\"type\":\"start\"}}\n{\"seq\":2,\"commit\":true}\n",
}

func TestConformanceRecords(t *testing.T) {
	cli := leanCLI(t)
	dir := t.TempDir()
	headers := map[string]string{"merge": header(t, cli, definition(t, "merge")), "users": header(t, cli, definition(t, "users"))}
	texts := map[string]string{}
	for label, text := range recordTexts {
		texts["merge "+label] = headers["merge"] + text
	}
	// users takes an input, whose payload the commit of the start needs.
	users := map[string]string{
		"missing payload": "{\"seq\":1,\"op\":{\"type\":\"start\",\"input\":\"t\"}}\n{\"seq\":2,\"commit\":true}\n",
		"pending op":      "{\"seq\":1,\"op\":{\"type\":\"start\",\"input\":\"t\"}}\n",
		"payload":         "{\"seq\":1,\"op\":{\"type\":\"start\",\"input\":\"t\"},\"values\":{\"t\":\"x\"}}\n{\"seq\":2,\"commit\":true}\n",
	}
	users["huge connection"] = users["payload"] + "{\"seq\":3,\"op\":{\"type\":\"deliver\",\"run\":[],\"connection\":99999999999999999999,\"source\":\"s\"}}\n"
	// An op record carries payloads only for values its transition introduces: not again for a value
	// that is already known, and not for one the state does not mention.
	users["known payload"] = users["payload"] + "{\"seq\":3,\"op\":{\"type\":\"invoke\",\"run\":[],\"placement\":\"fetchAllUsers\"}," +
		"\"values\":{\"t\":\"y\"}}\n{\"seq\":4,\"commit\":true}\n"
	users["stray payload"] = "{\"seq\":1,\"op\":{\"type\":\"start\",\"input\":\"t\"},\"values\":{\"t\":\"x\",\"z\":\"w\",\"y\":\"v\"}}\n" +
		"{\"seq\":2,\"commit\":true}\n"
	for label, text := range users {
		texts["users "+label] = headers["users"] + text
		// The records replay against the definition of the header, not the one they were meant for.
		texts["merge header, users "+label] = headers["merge"] + text
	}
	for label, text := range headerTexts {
		texts["header "+label] = text
	}
	for label, text := range texts {
		trace := filepath.Join(dir, strings.ReplaceAll(label, " ", "-")+".jsonl")
		if err := os.WriteFile(trace, []byte(text), 0o644); err != nil {
			t.Fatal(err)
		}
		args := []string{"check", trace}
		lean := runLean(t, cli, args...)
		t.Logf("%s: exit %d %s", label, lean.code, strings.TrimSpace(lean.stdout+lean.stderr))
		sameResult(t, label, lean, runGo(args...))
	}
}

// Go gen and Lean gen write the same records for a seed, compared as parsed JSON.
func TestConformanceGen(t *testing.T) {
	cli := leanCLI(t)
	for _, path := range conformanceDefinitions(t) {
		name := baseName(path)
		for _, seed := range conformanceSeeds {
			lean := runLean(t, cli, "gen", path, "--seed", seed)
			goResult := runGo("gen", path, "--seed", seed)
			if lean.code != 0 || goResult.code != 0 {
				t.Fatalf("gen %s %s: Lean %q, Go %q", name, seed, lean.stderr, goResult.stderr)
			}
			leanRecords, goRecords := parseLines(t, lean.stdout), parseLines(t, goResult.stdout)
			label := fmt.Sprintf("gen %s seed %s", name, seed)
			if reflect.DeepEqual(leanRecords, goRecords) {
				// Both write the canonical rendering, so the texts are the same too.
				if lean.stdout != goResult.stdout {
					t.Errorf("%s: the same records are rendered differently:\n%s", label,
						firstDifference(lean.stdout, goResult.stdout, splitText(lean.stdout), splitText(goResult.stdout)))
				}
				continue
			}
			// Diagnose: compare with identities decoded into their parts, whichever encoding each side uses.
			leanNorm, goNorm := normalize(leanRecords, decodeAny), normalize(goRecords, decodeAny)
			if reflect.DeepEqual(leanNorm, goNorm) {
				t.Errorf("%s: the records differ only in how identities are encoded (Lean writes %s)", label,
					firstString(leanRecords))
				continue
			}
			if leanOps, goOps := withoutValues(leanNorm), withoutValues(goNorm); reflect.DeepEqual(leanOps, goOps) {
				t.Errorf("%s: the ops are the same, but the payloads differ:\n%s", label,
					firstDifference(lean.stdout, goResult.stdout, leanNorm, goNorm))
				continue
			}
			t.Errorf("%s: the records differ:\n%s", label, firstDifference(lean.stdout, goResult.stdout, leanNorm, goNorm))
		}
	}
}

// Go gen and Lean gen write the same records for the chains of Test/definitions/chains, 16 and 8 runs
// deep, including a walk that runs every level.
func TestConformanceChains(t *testing.T) {
	cli := leanCLI(t)
	for _, name := range chainNames {
		for _, start := range []string{"w0", "w8"} {
			path := chainPath(t, name, start)
			_, succeeded := succeededGen(t, path)
			for _, seed := range append([]string{succeeded}, conformanceSeeds...) {
				args := []string{"gen", path, "--seed", seed}
				sameResult(t, fmt.Sprintf("gen %s from %s seed %s", name, start, seed), runLean(t, cli, args...),
					runGo(args...))
			}
		}
	}
}

func parseLines(t *testing.T, text string) []any {
	t.Helper()
	var records []any
	for _, line := range strings.Split(strings.TrimSuffix(text, "\n"), "\n") {
		if line == "" {
			continue
		}
		var v any
		if err := json.Unmarshal([]byte(line), &v); err != nil {
			t.Fatalf("%v: %s", err, line)
		}
		records = append(records, v)
	}
	return records
}

// decodeLegacy decodes the escape-based identities the Lean model wrote before the length-prefixed
// encoding: each part is escaped with \ and ended by ;.
func decodeLegacy(id string) ([]string, bool) {
	var parts []string
	var current []rune
	runes := []rune(id)
	for i := 0; i < len(runes); i++ {
		switch runes[i] {
		case '\\':
			if i+1 == len(runes) {
				return nil, false
			}
			i++
			current = append(current, runes[i])
		case ';':
			parts = append(parts, string(current))
			current = nil
		default:
			current = append(current, runes[i])
		}
	}
	return parts, len(current) == 0
}

// decodeAny decodes an identity in the current encoding, or else in the legacy one.
func decodeAny(id string) ([]string, bool) {
	if id == "" {
		return nil, true
	}
	if parts, ok := suimon.DecodeIdentity(id); ok && suimon.Identity(parts...) == id {
		return parts, true
	}
	return decodeLegacy(id)
}

// normalize replaces identities by their decoded parts, sorts the elements of list values, and
// turns objects into sorted pairs, so that encodings and key orders compare equal.
func normalize(v any, decode func(string) ([]string, bool)) any {
	switch v := v.(type) {
	case string:
		parts, ok := decode(v)
		if !ok {
			return v
		}
		out := []any{"#id"}
		for _, part := range parts {
			out = append(out, normalize(part, decode))
		}
		if len(parts) > 0 && parts[0] == "list" {
			rest := out[2:]
			sort.Slice(rest, func(i, j int) bool { return fmt.Sprint(rest[i]) < fmt.Sprint(rest[j]) })
		}
		return out
	case []any:
		out := make([]any, len(v))
		for i, item := range v {
			out[i] = normalize(item, decode)
		}
		return out
	case map[string]any:
		var pairs []any
		for key, value := range v {
			pairs = append(pairs, []any{normalize(key, decode), normalize(value, decode)})
		}
		sort.Slice(pairs, func(i, j int) bool { return fmt.Sprint(pairs[i]) < fmt.Sprint(pairs[j]) })
		return pairs
	}
	return v
}

func splitText(text string) []any {
	var lines []any
	for _, line := range strings.Split(text, "\n") {
		lines = append(lines, line)
	}
	return lines
}

// withoutValues drops the payloads from normalized records, leaving seq and op.
func withoutValues(records any) []any {
	var out []any
	for _, r := range records.([]any) {
		var kept []any
		for _, pair := range r.([]any) {
			if pair.([]any)[0] != "values" {
				kept = append(kept, pair)
			}
		}
		out = append(out, kept)
	}
	return out
}

func firstString(records []any) string {
	for _, r := range records {
		if op, ok := r.(map[string]any)["op"].(map[string]any); ok {
			if call, ok := op["call"].(string); ok {
				return fmt.Sprintf("call %q", call)
			}
		}
	}
	return "identities in another form"
}

func firstDifference(leanText, goText string, leanNorm, goNorm any) string {
	leanLines, goLines := strings.Split(leanText, "\n"), strings.Split(goText, "\n")
	ln, gn := leanNorm.([]any), goNorm.([]any)
	for i := 0; i < len(ln) || i < len(gn); i++ {
		if i >= len(ln) || i >= len(gn) || !reflect.DeepEqual(ln[i], gn[i]) {
			line := func(lines []string) string {
				if i < len(lines) {
					return lines[i]
				}
				return "(none)"
			}
			return fmt.Sprintf("  line %d\n  Lean: %s\n  Go:   %s", i+1, line(leanLines), line(goLines))
		}
	}
	return "  (no difference after normalization)"
}
