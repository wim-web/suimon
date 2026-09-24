package suimon

import (
	"errors"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"runtime"
)

// Journal receives the execution record of one workflow execution (§12.1, the lines of
// schema/trace.schema.json): for each accepted transition, an op line carrying the payloads of the
// values the transition introduces, then a commit line.
//
// The engine calls Append with complete lines, then Sync. It publishes the effects of the
// transitions it appended (starting a call, asking a Stream for its next element, cancelling calls,
// the final report) only after Sync returns, so every transition that anyone could observe is
// durable. An error from Append or Sync ends the execution (Wait returns the error); whatever
// part of the failed Append reached the record, the record stays readable for Resume, which
// discards an uncommitted tail.
type Journal interface {
	// Append writes lines at the end of the record.
	Append(lines []byte) error
	// Sync makes everything appended so far durable.
	Sync() error
}

// A RecoverableJournal is a Journal that Resume can read back and cut.
type RecoverableJournal interface {
	Journal
	// Contents returns the whole record written so far.
	Contents() ([]byte, error)
	// Truncate cuts the record to its first size bytes and makes that durable. Resume calls it
	// to discard an uncommitted tail before it appends.
	Truncate(size int64) error
}

// ErrJournalLocked is wrapped by the error of CreateJournal and OpenJournal when another
// FileJournal, in this process or another, has the file open.
var ErrJournalLocked = errors.New("suimon: the journal is locked")

// FileJournal is a RecoverableJournal in a file. Its methods must not be called concurrently; the
// engine calls them from one goroutine.
//
// A FileJournal holds an exclusive lock on its file until Close: flock on Linux, macOS and the
// BSDs, LockFileEx on Windows. Other platforms have no lock. The file is not opened for appending,
// which on Windows would deny Truncate; the lock makes the journal the only writer of its file, so
// Append writes at the end it finds.
type FileJournal struct {
	file *os.File
}

// CreateJournal creates a journal in a new file; it fails if the file exists.
func CreateJournal(path string) (*FileJournal, error) {
	j, err := openJournal(path, os.O_RDWR|os.O_CREATE|os.O_EXCL, 0o644)
	if err != nil {
		return nil, err
	}
	// The new directory entry must survive a crash as well as the lines.
	if err := syncDir(filepath.Dir(path)); err != nil {
		j.Close()
		return nil, err
	}
	return j, nil
}

// OpenJournal opens the journal in an existing file, to resume the execution it records.
func OpenJournal(path string) (*FileJournal, error) {
	return openJournal(path, os.O_RDWR, 0)
}

func openJournal(path string, flag int, perm os.FileMode) (*FileJournal, error) {
	f, err := os.OpenFile(path, flag, perm)
	if err != nil {
		return nil, err
	}
	if err := lockFile(f); err != nil {
		f.Close()
		return nil, &os.PathError{Op: "lock", Path: path, Err: err}
	}
	return &FileJournal{file: f}, nil
}

func syncDir(dir string) error {
	if runtime.GOOS == "windows" {
		return nil // directories cannot be opened for syncing there
	}
	d, err := os.Open(dir)
	if err != nil {
		return err
	}
	defer d.Close()
	return d.Sync()
}

// Append writes lines at the end of the file.
func (j *FileJournal) Append(lines []byte) error {
	if _, err := j.file.Seek(0, io.SeekEnd); err != nil {
		return err
	}
	_, err := j.file.Write(lines)
	return err
}

// Sync flushes the file to stable storage.
func (j *FileJournal) Sync() error { return j.file.Sync() }

// Contents reads the whole file.
func (j *FileJournal) Contents() ([]byte, error) {
	info, err := j.file.Stat()
	if err != nil {
		return nil, err
	}
	data := make([]byte, info.Size())
	n, err := j.file.ReadAt(data, 0)
	if err != nil && err != io.EOF {
		return nil, err
	}
	if n != len(data) {
		return nil, fmt.Errorf("suimon: read %d of %d bytes of %s", n, len(data), j.file.Name())
	}
	return data, nil
}

// Truncate cuts the file to size bytes and syncs it.
func (j *FileJournal) Truncate(size int64) error {
	if err := j.file.Truncate(size); err != nil {
		return err
	}
	return j.file.Sync()
}

// Name is the name of the file.
func (j *FileJournal) Name() string { return j.file.Name() }

// Close releases the lock and closes the file. Close it after the execution that writes it has
// ended.
func (j *FileJournal) Close() error {
	err := unlockFile(j.file)
	if cerr := j.file.Close(); cerr != nil {
		return cerr
	}
	return err
}
