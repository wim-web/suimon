//go:build unix

package suimon

import (
	"os"
	"os/exec"
	"path/filepath"
	"syscall"
	"testing"
)

func TestCreateJournalPermissions(t *testing.T) {
	// Umask is process-wide, so change it only in a dedicated subprocess.
	const childEnv = "SUIMON_TEST_JOURNAL_PERMISSIONS"
	if os.Getenv(childEnv) != "1" {
		executable, err := os.Executable()
		if err != nil {
			t.Fatal(err)
		}
		cmd := exec.Command(executable, "-test.run=^TestCreateJournalPermissions$")
		cmd.Env = append(os.Environ(), childEnv+"=1")
		if output, err := cmd.CombinedOutput(); err != nil {
			t.Fatalf("journal permissions subprocess: %v\n%s", err, output)
		}
		return
	}

	oldMask := syscall.Umask(0)
	defer syscall.Umask(oldMask)
	path := filepath.Join(t.TempDir(), "private.jsonl")
	j, err := CreateJournal(path)
	if err != nil {
		t.Fatal(err)
	}
	defer j.Close()
	info, err := os.Stat(path)
	if err != nil {
		t.Fatal(err)
	}
	if got := info.Mode().Perm(); got != 0o600 {
		t.Errorf("journal permissions with umask 000: got %04o, want 0600", got)
	}
}
