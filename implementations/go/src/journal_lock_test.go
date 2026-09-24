//go:build darwin || dragonfly || freebsd || linux || netbsd || openbsd || windows

package suimon

import (
	"errors"
	"path/filepath"
	"testing"
)

// While a FileJournal is open, no other FileJournal opens its file, even in the same process.
func TestFileJournalLock(t *testing.T) {
	path := filepath.Join(t.TempDir(), "locked.jsonl")
	created, err := CreateJournal(path)
	if err != nil {
		t.Fatal(err)
	}
	if _, err := OpenJournal(path); !errors.Is(err, ErrJournalLocked) {
		t.Errorf("OpenJournal while created: %v", err)
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
}
