package suimon

import (
	"bytes"
	"errors"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"sync/atomic"
	"testing"
)

// Conformance of the runtime with the Lean model: the Lean CLI named by SUIMON_LEAN_CLI (a
// relative path is resolved from the repository root) accepts every journal the runtime writes,
// and replays it to the runtime's final state. The tests are skipped when it is not set.

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

var leanFiles atomic.Int64

// leanRun runs the Lean CLI and returns its exit code and output.
func leanRun(t *testing.T, cli string, args ...string) (int, string, string) {
	t.Helper()
	cmd := exec.Command(cli, args...)
	var stdout, stderr bytes.Buffer
	cmd.Stdout, cmd.Stderr = &stdout, &stderr
	err := cmd.Run()
	var exit *exec.ExitError
	if err != nil && !errors.As(err, &exit) {
		t.Fatalf("%s %v: %v", cli, args, err)
	}
	return cmd.ProcessState.ExitCode(), stdout.String(), stderr.String()
}

// writeTemp writes data to a new file of the test's temporary directory.
func writeTemp(t *testing.T, dir, name string, data []byte) string {
	t.Helper()
	path := filepath.Join(dir, fmt.Sprintf("%d-%s", leanFiles.Add(1), name))
	if err := os.WriteFile(path, data, 0o644); err != nil {
		t.Fatal(err)
	}
	return path
}

// leanAgrees has Lean check a journal of p, against the definition of its header: Lean's summary is
// the Go checker's, and, when the journal replays, Lean's state is state, the JSON of the Go state.
func leanAgrees(t *testing.T, cli, dir string, p *Definition, journal string, state *State) {
	t.Helper()
	journalPath := writeTemp(t, dir, "journal.jsonl", []byte(journal))
	c, err := Check(journal, sameDefinition(p))
	if err != nil {
		t.Fatalf("Go check: %v", err)
	}
	code, stdout, stderr := leanRun(t, cli, "check", journalPath)
	want := fmt.Sprintf(`{"committed":%d,"status":"%s","uncommitted":%t}`+"\n", c.Committed, c.State.Status, c.Uncommitted)
	if code != 0 || stdout != want {
		t.Fatalf("Lean check: exit %d, %q%s, want %q\n%s", code, stdout, stderr, want, journal)
	}
	if state == nil {
		return
	}
	code, stdout, stderr = leanRun(t, cli, "check", journalPath, "--state")
	goState, err := state.MarshalJSON()
	if err != nil {
		t.Fatal(err)
	}
	if code != 0 || strings.TrimSuffix(stdout, "\n") != string(goState) {
		t.Fatalf("Lean check --state: exit %d %s\nLean: %s\nGo:   %s", code, stderr, stdout, goState)
	}
}

// Every scenario's journal is accepted by Lean, which replays it to the runtime's final state.
func TestConformanceRuntime(t *testing.T) {
	cli := leanCLI(t)
	for _, sc := range scenarios() {
		t.Run(sc.name, func(t *testing.T) {
			t.Parallel()
			p, journal, r := runOnce(t, sc)
			leanAgrees(t, cli, t.TempDir(), p, journal, r.State)
		})
	}
}

// The journals of the chains of Test/definitions/chains, 16 runs deep, conform too.
func TestConformanceChains(t *testing.T) {
	cli := leanCLI(t)
	for _, name := range chainNames {
		t.Run(name, func(t *testing.T) {
			t.Parallel()
			p := loadChain(t, name, "w0")
			journal, r := runChain(t, p, nil)
			leanAgrees(t, cli, t.TempDir(), p, journal, r.State)
		})
	}
}

// Recovered executions conform too: Lean summarizes a cut journal as Go does, and accepts the
// journal of the resumed execution, lost calls included, with the same final state.
func TestConformanceRecovery(t *testing.T) {
	cli := leanCLI(t)
	for _, name := range []string{"merge", "users", "branch", "calls large", "fanout", "limit"} {
		sc := scenarioNamed(t, name)
		t.Run(sc.name, func(t *testing.T) {
			t.Parallel()
			p, journal, _ := runOnce(t, sc)
			dir := t.TempDir()
			for i, cut := range cutPoints(journal) {
				if i%3 != 0 {
					continue
				}
				prefix := journal[:cut]
				leanAgrees(t, cli, dir, p, prefix, nil)
				r, j, c, err := resumeAt(t, sc, p, prefix)
				if c.Committed == 0 {
					continue
				}
				if err != nil {
					t.Fatal(err)
				}
				leanAgrees(t, cli, dir, p, j.text(), r.State)
			}
		})
	}
}

// Longer streams conform too: the runtime changes its state in place and reads it through indexes.
// The sizes are small because Lean's checker takes time that grows faster than the journal.
func TestConformanceLongStreams(t *testing.T) {
	cli := leanCLI(t)
	t.Run("stream", func(t *testing.T) {
		t.Parallel()
		p, e := streamEngine(t)
		journal, r := runStream(t, e, 60)
		leanAgrees(t, cli, t.TempDir(), p, journal, r.State)
	})
	t.Run("users", func(t *testing.T) {
		t.Parallel()
		p, e := usersEngine(t)
		journal, r := runUsers(t, e, 20)
		leanAgrees(t, cli, t.TempDir(), p, journal, r.State)
	})
}
