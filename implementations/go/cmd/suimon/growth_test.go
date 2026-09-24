package main

import (
	"encoding/json"
	"path/filepath"
	"strconv"
	"strings"
	"testing"
)

// Identities grow linearly with the nesting of runs (Test/Trace.lean): a run path holds one label per
// level, and an identity holds its run path once. The chains of Test/definitions/chains nest 16 runs,
// sub-workflow calls or concurrency tasks and sub-workflow calls in turn, and 8 when started at w8.

// chainNames are the chains of Test/definitions/chains.
var chainNames = []string{"nested", "alternating"}

// chainPath is Test/definitions/chains/<name>.json, run from the workflow start: a copy with that
// main workflow when start is not w0.
func chainPath(t *testing.T, name, start string) string {
	t.Helper()
	path := filepath.Join(repoRoot(t), "Test", "definitions", "chains", name+".json")
	if start == "w0" {
		return path
	}
	var doc map[string]any
	if err := json.Unmarshal(mustRead(t, path), &doc); err != nil {
		t.Fatal(err)
	}
	doc["main"] = start
	data, err := json.Marshal(doc)
	if err != nil {
		t.Fatal(err)
	}
	return writeTemp(t, name+"-"+start+".json", string(data))
}

// succeededGen is what gen writes for the first seed whose walk succeeds, which runs every level of
// a chain, and that seed.
func succeededGen(t *testing.T, path string) (string, string) {
	t.Helper()
	for seed := 1; seed <= 200; seed++ {
		s := strconv.Itoa(seed)
		generated := cli(t, 0, "gen", path, "--seed", s)
		checked := cli(t, 0, "check", writeTemp(t, "chain.jsonl", generated.stdout))
		if strings.Contains(checked.stdout, `"status":"succeeded"`) {
			return generated.stdout, s
		}
	}
	t.Fatalf("%s: no walk succeeds", path)
	return "", ""
}

// longestRecordLine is the length in bytes of the longest line of a record, the header aside.
func longestRecordLine(record string) int {
	lines := strings.Split(strings.TrimSuffix(record, "\n"), "\n")
	longest := 0
	for _, line := range lines[1:] {
		longest = max(longest, len(line))
	}
	return longest
}

// gen writes lines for 16 levels within 2.5 times those of 8 levels, and under 8 KiB; identities that
// embed their run path at every level grow exponentially instead.
func TestGenIdentifierGrowth(t *testing.T) {
	for _, name := range chainNames {
		deep, _ := succeededGen(t, chainPath(t, name, "w0"))
		shallow, _ := succeededGen(t, chainPath(t, name, "w8"))
		l16, l8 := longestRecordLine(deep), longestRecordLine(shallow)
		t.Logf("%s: the longest line has %d bytes at depth 16 and %d at depth 8", name, l16, l8)
		if 2*l16 > 5*l8 || l16 > 8192 {
			t.Errorf("%s: the longest line has %d bytes at depth 16 and %d at depth 8", name, l16, l8)
		}
	}
}
