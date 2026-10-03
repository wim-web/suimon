package main

import (
	"fmt"
	"strings"
	"testing"

	suimon "github.com/wim-web/suimon/implementations/go/src"
)

// Both CLIs run this corpus so input limits and rejection precedence stay identical.
func inputLimitCases(t *testing.T, check func(string, []string, string)) {
	t.Helper()
	depthErr := "input exceeds maximum nesting depth of 64\n"
	sizeErr := "input exceeds maximum size of 1048576 bytes\n"
	header := `{"definition":{"main":"w"},"validated":false}` + "\n"
	for _, tc := range []struct{ name, text, error string }{
		{"arrays", strings.Repeat("[", 65) + "null" + strings.Repeat("]", 65), depthErr},
		{"objects", strings.Repeat(`{"list":`, 65) + `"T"` + strings.Repeat("}", 65), depthErr},
		{"hostile", strings.Repeat("[", 20000) + "0" + strings.Repeat("]", 20000), depthErr},
		{"bytes", strings.Repeat(" ", suimon.DefaultMaxInputBytes) + "0", sizeErr},
		{"unicode bytes", `"` + strings.Repeat("界", suimon.DefaultMaxInputBytes/3) + `"`, sizeErr},
	} {
		path := writeTemp(t, "input.json", tc.text)
		for _, action := range []string{"validate", "explore", "gen"} {
			check(tc.name+" "+action, []string{action, path}, tc.error)
		}
		path = writeTemp(t, "header.jsonl", tc.text+"\n")
		check(tc.name+" check header", []string{"check", path}, "line 1: "+tc.error)
		path = writeTemp(t, "record.jsonl", header+tc.text+"\n")
		check(tc.name+" check record", []string{"check", path}, "line 2: "+tc.error)
	}
	// The canonical form expands short control escapes before header loading.
	expanded := `{"definition":{"main":"` + strings.Repeat(`\n`, 200000) + `"},"validated":false}` + "\n"
	check("expanded header", []string{"check", writeTemp(t, "expanded.jsonl", expanded)}, "line 1: "+sizeErr)

	for _, n := range []int{64, 65} {
		text := strings.Repeat("[", n) + "null" + strings.Repeat("]", n)
		want := "definition: expected an object\n"
		if n == 65 {
			want = depthErr
		}
		check(fmt.Sprintf("depth %d", n), []string{"validate", writeTemp(t, "depth.json", text)}, want)
	}
	// Exactly the byte budget reaches semantic validation; limit + 1 fails first.
	for _, n := range []int{suimon.DefaultMaxInputBytes, suimon.DefaultMaxInputBytes + 1} {
		text := "0" + strings.Repeat(" ", n-1)
		want := "definition: expected an object\n"
		if n > suimon.DefaultMaxInputBytes {
			want = sizeErr
		}
		check(fmt.Sprintf("bytes %d", n), []string{"validate", writeTemp(t, "size.json", text)}, want)
	}
}

func TestCLIInputLimits(t *testing.T) {
	inputLimitCases(t, func(name string, args []string, stderr string) {
		t.Helper()
		got := runGo(args...)
		if got != (result{1, "", stderr}) {
			t.Errorf("%s: %+v; expected %q", name, got, stderr)
		}
	})
}

func TestConformanceInputLimits(t *testing.T) {
	lean := leanCLI(t)
	inputLimitCases(t, func(name string, args []string, stderr string) {
		t.Helper()
		goResult, leanResult := runGo(args...), runLean(t, lean, args...)
		sameResult(t, name, leanResult, goResult)
		if goResult != (result{1, "", stderr}) {
			t.Errorf("%s: %+v; expected %q", name, goResult, stderr)
		}
	})
}
