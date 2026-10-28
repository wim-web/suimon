//go:build darwin || dragonfly || freebsd || linux || netbsd || openbsd || windows

package suimon

import (
	"errors"
	"os"
	"path/filepath"
	"testing"
)

// While a FileJournal is open, no other FileJournal opens its file, even in the same process.
func TestFileJournalLock(t *testing.T) {
	if role := os.Getenv(journalProcessRole); role != "" {
		j, err := OpenJournal(os.Getenv(journalProcessPath))
		if role == "lock-probe" {
			if j != nil {
				_ = j.Close()
			}
			if !errors.Is(err, ErrJournalLocked) {
				t.Fatalf("opening the parent's locked journal: %v", err)
			}
			return
		}
		if role != "lock-holder" || err != nil {
			t.Fatalf("opening the child-held journal (%s): %v", role, err)
		}
		defer j.Close()
		t.Fatal(holdJournalProcess())
		return
	}
	path := filepath.Join(t.TempDir(), "locked.jsonl")
	created, err := CreateJournal(path)
	if err != nil {
		t.Fatal(err)
	}
	if _, err := OpenJournal(path); !errors.Is(err, ErrJournalLocked) {
		t.Errorf("OpenJournal while created: %v", err)
	}
	probe := journalProcessCommand(t, "TestFileJournalLock", "lock-probe", path)
	if output, err := probe.CombinedOutput(); err != nil {
		t.Fatalf("another process opened the locked journal: %v\n%s", err, output)
	}
	if err := created.Close(); err != nil {
		t.Fatal(err)
	}
	opened, err := OpenJournal(path)
	if err != nil {
		t.Fatalf("OpenJournal after Close: %v", err)
	}
	if _, err := OpenJournal(path); !errors.Is(err, ErrJournalLocked) {
		t.Errorf("OpenJournal while opened: %v", err)
	}
	if err := opened.Close(); err != nil {
		t.Fatal(err)
	}
	reopened, err := OpenJournal(path)
	if err != nil {
		t.Fatalf("OpenJournal after the second Close: %v", err)
	}
	if err := reopened.Close(); err != nil {
		t.Fatal(err)
	}
	// A separate process holds the OS lock, then dies without calling Close.
	child, wait := startJournalProcess(t, "TestFileJournalLock", "lock-holder", path)
	if other, err := OpenJournal(path); !errors.Is(err, ErrJournalLocked) {
		if other != nil {
			_ = other.Close()
		}
		t.Fatalf("OpenJournal while another process holds it: %v", err)
	}
	if err := child.Process.Kill(); err != nil {
		t.Fatal(err)
	}
	if err := wait(); err == nil {
		t.Fatal("the lock holder was not terminated")
	}
	afterExit := openJournalAfterProcessExit(t, path)
	if err := afterExit.Close(); err != nil {
		t.Fatal(err)
	}
}
