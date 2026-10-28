package suimon

import (
	"bufio"
	"bytes"
	"context"
	"errors"
	"fmt"
	"io"
	"os"
	"os/exec"
	"runtime"
	"testing"
	"time"
)

const journalProcessRole = "SUIMON_TEST_JOURNAL_PROCESS_ROLE"
const journalProcessPath = "SUIMON_TEST_JOURNAL_PROCESS_PATH"

func journalProcessCommand(t *testing.T, test, role, path string) *exec.Cmd {
	t.Helper()
	executable, err := os.Executable()
	if err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	t.Cleanup(cancel)
	cmd := exec.CommandContext(ctx, executable, "-test.run=^"+test+"$")
	cmd.Env = append(os.Environ(), journalProcessRole+"="+role, journalProcessPath+"="+path)
	return cmd
}

// startJournalProcess waits for a child to reach its explicit durable/locked checkpoint.
// Its stdin stays open until cleanup so a child also exits if the parent goes away.
func startJournalProcess(t *testing.T, test, role, path string) (*exec.Cmd, func() error) {
	t.Helper()
	cmd := journalProcessCommand(t, test, role, path)
	stdout, err := cmd.StdoutPipe()
	if err != nil {
		t.Fatal(err)
	}
	stdin, err := cmd.StdinPipe()
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = stdin.Close() })
	var stderr bytes.Buffer
	cmd.Stderr = &stderr
	if err := cmd.Start(); err != nil {
		t.Fatal(err)
	}
	waited := false
	wait := func() error {
		waited = true
		return cmd.Wait()
	}
	t.Cleanup(func() {
		if !waited {
			_ = cmd.Process.Kill()
			_ = wait()
		}
	})
	ready, err := bufio.NewReader(stdout).ReadString('\n')
	if err != nil || ready != "journal-ready\n" {
		_ = cmd.Process.Kill()
		processErr := wait()
		t.Fatalf("journal subprocess did not reach its checkpoint: %q, %v, %v\n%s", ready, err, processErr, stderr.String())
	}
	return cmd, wait
}

func holdJournalProcess() error {
	fmt.Fprintln(os.Stdout, "journal-ready")
	_, _ = io.Copy(io.Discard, os.Stdin)
	return fmt.Errorf("journal subprocess stdin closed before it was killed")
}

// A killed process cannot explicitly unlock its handles. Windows may release those locks
// after Wait returns (unlike FileJournal.Close, which calls UnlockFileEx first).
func openJournalAfterProcessExit(t *testing.T, path string) *FileJournal {
	t.Helper()
	deadline := time.Now().Add(5 * time.Second)
	for {
		j, err := OpenJournal(path)
		if err == nil {
			return j
		}
		if runtime.GOOS != "windows" || !errors.Is(err, ErrJournalLocked) || !time.Now().Before(deadline) {
			t.Fatalf("OpenJournal after process exit: %v", err)
		}
		time.Sleep(10 * time.Millisecond)
	}
}
