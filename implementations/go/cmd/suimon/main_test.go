package main

import (
	"bytes"
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"

	suimon "github.com/wim-web/suimon/implementations/go/src"
)

// Ported from Test/Cli.lean, run in process.

type result struct {
	code           int
	stdout, stderr string
}

func runGo(args ...string) result {
	var stdout, stderr bytes.Buffer
	code := run(args, &stdout, &stderr)
	return result{code, stdout.String(), stderr.String()}
}

func repoRoot(t testing.TB) string {
	t.Helper()
	dir, err := os.Getwd()
	if err != nil {
		t.Fatal(err)
	}
	for {
		if _, err := os.Stat(filepath.Join(dir, "lakefile.lean")); err == nil {
			return dir
		}
		parent := filepath.Dir(dir)
		if parent == dir {
			t.Fatal("repository root not found")
		}
		dir = parent
	}
}

func definition(t testing.TB, name string) string {
	return filepath.Join(repoRoot(t), "Test", "definitions", name+".json")
}

func writeTemp(t testing.TB, name, content string) string {
	t.Helper()
	path := filepath.Join(t.TempDir(), name)
	if err := os.WriteFile(path, []byte(content), 0o644); err != nil {
		t.Fatal(err)
	}
	return path
}

func mustRead(t testing.TB, path string) []byte {
	t.Helper()
	data, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	return data
}

func expectCode(t *testing.T, r result, code int, args ...string) {
	t.Helper()
	if r.code != code {
		t.Errorf("CLI %v: expected exit %d, got %d\n%s\n%s", args, code, r.code, r.stdout, r.stderr)
	}
}

func cli(t *testing.T, code int, args ...string) result {
	t.Helper()
	r := runGo(args...)
	expectCode(t, r, code, args...)
	return r
}

func TestCLI(t *testing.T) {
	for _, name := range []string{"users", "branch", "merge"} {
		if r := cli(t, 0, "validate", definition(t, name)); r.stdout != "ok\n" {
			t.Errorf("validate %s: unexpected output %q", name, r.stdout)
		}
	}
	invalid := writeTemp(t, "invalid.json", `{"main":"w","workflows":[]}`)
	if r := cli(t, 1, "validate", invalid); !strings.Contains(r.stderr, "unknown main workflow w") {
		t.Errorf("invalid definition: %s", r.stderr)
	}
	for _, name := range []string{"users", "branch", "merge"} {
		generated := cli(t, 0, "gen", definition(t, name), "--seed", "3")
		// The record starts with the header, which holds the definition.
		p, err := suimon.ParseDefinition(mustRead(t, definition(t, name)))
		if err != nil {
			t.Fatal(err)
		}
		lines := strings.SplitAfter(generated.stdout, "\n")
		lines = lines[:len(lines)-1]
		if header := suimon.EncodeHeader(p) + "\n"; lines[0] != header {
			t.Errorf("gen %s: the first line is not the header", name)
		}
		trace := writeTemp(t, name+".jsonl", generated.stdout)
		if r := cli(t, 0, "check", trace); !strings.Contains(r.stdout, `"uncommitted":false`) {
			t.Errorf("check %s: %s", name, r.stdout)
		}
		// A record cut in the middle of its last line is recovered, and the cut is reported.
		torn := writeTemp(t, name+"-torn.jsonl", strings.Join(lines[:len(lines)-1], "")+`{"seq"`)
		r := cli(t, 0, "check", torn)
		if !strings.Contains(r.stdout, fmt.Sprintf(`"committed":%d,`, (len(lines)-2)/2)) || !strings.Contains(r.stdout, `"uncommitted":true`) {
			t.Errorf("check torn %s: %s", name, r.stdout)
		}
		// A record cut inside its header has committed nothing; a header alone neither.
		for text, torn := range map[string]bool{lines[0][:20]: true, lines[0]: false} {
			r := cli(t, 0, "check", writeTemp(t, name+"-header.jsonl", text))
			if want := fmt.Sprintf(`{"committed":0,"status":"running","uncommitted":%t}`+"\n", torn); r.stdout != want {
				t.Errorf("check header %s: %s", name, r.stdout)
			}
		}
		// --state prints the replayed state as JSON.
		expected, err := suimon.Check(generated.stdout, loadDefinition)
		if err != nil {
			t.Fatal(err)
		}
		want, _ := expected.State.MarshalJSON()
		state := cli(t, 0, "check", trace, "--state")
		var doc map[string]any
		if err := json.Unmarshal([]byte(state.stdout), &doc); err != nil || doc["started"] != true || state.stdout != string(want)+"\n" {
			t.Errorf("check --state %s: %v %.80s", name, err, state.stdout)
		}
		if r := cli(t, 0, "explore", definition(t, name), "--seeds", "20"); !strings.HasPrefix(r.stdout, "{") {
			t.Errorf("explore %s: %s", name, r.stdout)
		}
	}
	cli(t, 1, "check", definition(t, "users"))
	cli(t, 2, "check", definition(t, "users"), "--states")
	cli(t, 2, "check", "x.jsonl", "--definition", definition(t, "users"))
	cli(t, 2, "explore", definition(t, "users"), "--seeds")
	// The definition of the header is read like a definition file: decoded, then validated.
	invalidHeader := writeTemp(t, "invalid.jsonl", "{\"definition\":{\"main\":\"w\",\"workflows\":[]}}\n")
	if r := cli(t, 1, "check", invalidHeader); r.stderr != "line 1: unknown main workflow w\n" {
		t.Errorf("invalid header: %q", r.stderr)
	}
	cli(t, 1, "validate", filepath.Join(repoRoot(t), "Test", "definitions", "missing.json"))
	cli(t, 2)
	cli(t, 0, "--help")
}

func TestCLIOutputs(t *testing.T) {
	merge := definition(t, "merge")
	p, err := suimon.ParseDefinition(mustRead(t, merge))
	if err != nil {
		t.Fatal(err)
	}
	cases := []struct {
		args           []string
		code           int
		stdout, stderr string
	}{
		{[]string{"help"}, 0, usage, ""},
		{[]string{"--help", "x"}, 2, "", usage},
		{[]string{"validate", "a", "b"}, 2, "", usage},
		{[]string{"explore", merge, "--seeds", "0"}, 0, "{}\n", ""},
		{[]string{"explore", merge, "--seeds", "1_0", "--steps", "5"}, 1, "", "seed 1: no accepted operation in status running\n"},
		{[]string{"explore", merge, "--seeds", "3", "--seeds", "5"}, 0, `{"cancelled":2,"succeeded":1}` + "\n", ""},
		{[]string{"explore", merge, "--seeds", "x"}, 1, "", "--seeds expects a natural number\n"},
		{[]string{"explore", merge, "--seeds", "1__0"}, 1, "", "--seeds expects a natural number\n"},
		{[]string{"explore", merge, "--bogus", "1"}, 2, "", "unknown option --bogus\n"},
		{[]string{"explore", merge, "--seeds", "1", "--bogus"}, 2, "", "missing value for --bogus\n"},
		{[]string{"gen", merge, "--steps", "0"}, 0, suimon.EncodeHeader(p) + "\n", ""},
		{[]string{"check", "x.jsonl"}, 1, "", "no such file or directory (error code: 2)\n  file: x.jsonl\n"},
		{[]string{"check", "x.jsonl", "--definition", merge}, 2, "", "unknown option --definition\n"},
		{[]string{"check", "x.jsonl", "--state", "--definition"}, 2, "", "missing value for --definition\n"},
		{[]string{"explore", merge, "--state"}, 2, "", "missing value for --state\n"},
		{[]string{"explore", merge, "--state", "1"}, 2, "", "unknown option --state\n"},
	}
	for _, c := range cases {
		r := runGo(c.args...)
		if r.code != c.code || r.stdout != c.stdout || r.stderr != c.stderr {
			t.Errorf("%v: got %d %q %q, want %d %q %q", c.args, r.code, r.stdout, r.stderr, c.code, c.stdout, c.stderr)
		}
	}
	missing := filepath.Join(t.TempDir(), "missing.json")
	r := runGo("validate", missing)
	if want := "no such file or directory (error code: 2)\n  file: " + missing + "\n"; r.stderr != want {
		t.Errorf("missing file: %q", r.stderr)
	}
	bad := writeTemp(t, "bad.json", "\xff")
	if r := runGo("validate", bad); r.stderr != "Tried to read file '"+bad+"' containing non UTF-8 data.\n" {
		t.Errorf("non UTF-8: %q", r.stderr)
	}
}

func TestCLICheck(t *testing.T) {
	merge, err := suimon.ParseDefinition(mustRead(t, definition(t, "merge")))
	if err != nil {
		t.Fatal(err)
	}
	header := suimon.EncodeHeader(merge) + "\n"
	start := header + "{\"seq\":1,\"op\":{\"type\":\"start\"}}\n{\"seq\":2,\"commit\":true}\n"
	cases := []struct {
		trace          string
		code           int
		stdout, stderr string
	}{
		{start, 0, `{"committed":1,"status":"running","uncommitted":false}` + "\n", ""},
		{start + `{"seq":3,"op":{"type":"cancel"}}` + "\n", 0, `{"committed":1,"status":"running","uncommitted":true}` + "\n", ""},
		{start + `{"seq":3,"op":{"ty`, 0, `{"committed":1,"status":"running","uncommitted":true}` + "\n", ""},
		{start + "{\"seq\":3,\"op\":{\"type\":\"invoke\",\"run\":[],\"placement\":\"\xe3", 0,
			`{"committed":1,"status":"running","uncommitted":true}` + "\n", ""},
		{start + "{\"seq\":3,\"commit\":true}\n", 1, "", "line 4: a commit without an op\n"},
		{"", 0, `{"committed":0,"status":"running","uncommitted":false}` + "\n", ""},
		{header[:40] + "\xe3", 0, `{"committed":0,"status":"running","uncommitted":true}` + "\n", ""},
		{start[len(header):], 1, "", "line 1: header: unknown field seq\n"},
		{start + header, 1, "", "line 4: record: missing field seq\n"},
		{"{\"definition\":{\"main\":\"w\"}}\n", 1, "", "line 1: unknown main workflow w\n"},
	}
	for _, c := range cases {
		r := runGo("check", writeTemp(t, "trace.jsonl", c.trace))
		if r.code != c.code || r.stdout != c.stdout || r.stderr != c.stderr {
			t.Errorf("%q: got %d %q %q", c.trace, r.code, r.stdout, r.stderr)
		}
	}
	bad := writeTemp(t, "bad.jsonl", "\xff\n")
	if r := runGo("check", bad); r.code != 1 ||
		r.stderr != "Tried to read file '"+bad+"' containing non UTF-8 data.\n" {
		t.Errorf("non UTF-8 line: %d %q", r.code, r.stderr)
	}
}
