package suimon

import (
	"context"
	"crypto/sha256"
	"encoding/binary"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"sync"
)

// CommitBatch is one complete model transaction and its new immutable values.
// Existing values are omitted, including identical redeliveries.
type CommitBatch struct {
	Events List[Event]                `json:"events"`
	Values map[string]json.RawMessage `json:"values"`
}

const journalMagic = "suimon-journal-v1\n"
const journalFrameHeader = 48 // length, complemented length, SHA-256(payload)

// JournalFile appends durable batches. Use one writer per path and Close it
// after stopping its execution. On append errors, reopen and recover the file.
type JournalFile struct {
	mu       sync.Mutex
	file     *os.File
	next     Nat
	used     map[string]bool
	failed   error
	closed   bool
	write    func([]byte) (int, error)
	syncFile func() error
}

// OpenJournalFile creates or recovers a journal for this exact graph. It checks
// all readable events with Recover, then truncates only the uncommitted suffix.
// The returned snapshot can be passed to Workflow.Resume or Workflow.Restore.
func OpenJournalFile(ctx context.Context, path string, graph Graph) (*JournalFile, Snapshot, error) {
	if err := ctx.Err(); err != nil {
		return nil, Snapshot{}, err
	}
	if err := graph.Validate(); err != nil {
		return nil, Snapshot{}, err
	}
	file, err := os.OpenFile(path, os.O_RDWR|os.O_CREATE|os.O_EXCL, 0600)
	created := err == nil
	if errors.Is(err, os.ErrExist) {
		file, err = os.OpenFile(path, os.O_RDWR, 0)
	}
	if err != nil {
		return nil, Snapshot{}, err
	}
	ok := false
	defer func() {
		if !ok {
			file.Close()
			if created {
				os.Remove(path)
			}
		}
	}()
	if created {
		header, err := json.Marshal(graph)
		if err != nil {
			return nil, Snapshot{}, err
		}
		if _, err := io.WriteString(file, journalMagic); err != nil {
			return nil, Snapshot{}, err
		}
		if err := writeJournalFrame(file.Write, header); err != nil {
			return nil, Snapshot{}, err
		}
		if err := file.Sync(); err != nil {
			return nil, Snapshot{}, err
		}
		dir, err := os.Open(filepath.Dir(path))
		if err != nil {
			return nil, Snapshot{}, err
		}
		err = dir.Sync()
		dir.Close()
		if err != nil {
			return nil, Snapshot{}, err
		}
	}
	if _, err := file.Seek(0, io.SeekStart); err != nil {
		return nil, Snapshot{}, err
	}
	snapshot, boundary, err := readJournal(ctx, file, graph)
	if err != nil {
		return nil, Snapshot{}, err
	}
	if err := ctx.Err(); err != nil {
		return nil, Snapshot{}, err
	}
	info, err := file.Stat()
	if err != nil {
		return nil, Snapshot{}, err
	}
	if info.Size() != boundary {
		if err := file.Truncate(boundary); err != nil {
			return nil, Snapshot{}, err
		}
		if err := file.Sync(); err != nil {
			return nil, Snapshot{}, err
		}
	}
	if _, err := file.Seek(boundary, io.SeekStart); err != nil {
		return nil, Snapshot{}, err
	}
	journal := &JournalFile{file: file, next: natLen(snapshot.Events).Inc(), used: map[string]bool{}, write: file.Write, syncFile: file.Sync}
	for _, e := range snapshot.Events {
		if e.Type == "transaction.committed" {
			journal.used[e.Txn] = true
		}
	}
	ok = true
	return journal, snapshot, nil
}

func (j *JournalFile) Close() error {
	j.mu.Lock()
	defer j.mu.Unlock()
	if j.closed {
		return nil
	}
	j.closed = true
	return j.file.Close()
}

func (j *JournalFile) Append(ctx context.Context, batch CommitBatch) error {
	j.mu.Lock()
	defer j.mu.Unlock()
	if j.closed {
		return os.ErrClosed
	}
	if j.failed != nil {
		return fmt.Errorf("reopen journal after failed append: %w", j.failed)
	}
	if err := ctx.Err(); err != nil {
		return err
	}
	if len(batch.Events) == 0 || batch.Events[len(batch.Events)-1].Type != "transaction.committed" {
		return fmt.Errorf("append requires a complete transaction")
	}
	txn, seq := batch.Events[0].Txn, j.next
	if txn == "" || j.used[txn] {
		return fmt.Errorf("duplicate or empty journal transaction: %s", txn)
	}
	for n, e := range batch.Events {
		if e.Sequence != seq || e.Txn != txn || n < len(batch.Events)-1 && e.Type == "transaction.committed" {
			return fmt.Errorf("journal transaction or sequence mismatch")
		}
		seq = seq.Inc()
	}
	data, err := json.Marshal(batch)
	if err != nil {
		return err
	}
	if err := writeJournalFrame(j.write, data); err != nil {
		j.failed = err
		return err
	}
	if err := j.syncFile(); err != nil {
		j.failed = err
		return err
	}
	j.next, j.used[txn] = seq, true
	return nil
}

func writeJournalFrame(write func([]byte) (int, error), data []byte) error {
	var header [journalFrameHeader]byte
	length := uint64(len(data))
	binary.BigEndian.PutUint64(header[:8], length)
	binary.BigEndian.PutUint64(header[8:16], ^length)
	digest := sha256.Sum256(data)
	copy(header[16:], digest[:])
	for _, part := range [][]byte{header[:], data} {
		n, err := write(part)
		if err != nil {
			return err
		}
		if n != len(part) {
			return io.ErrShortWrite
		}
	}
	return nil
}

// A short final header/body is a physical torn suffix. A complete header with
// a damaged length or a complete body with a bad checksum is corruption.
func readJournalFrame(file *os.File, size int64) ([]byte, bool, error) {
	var header [journalFrameHeader]byte
	if _, err := io.ReadFull(file, header[:]); err != nil {
		if errors.Is(err, io.EOF) || errors.Is(err, io.ErrUnexpectedEOF) {
			return nil, false, nil
		}
		return nil, false, err
	}
	length := binary.BigEndian.Uint64(header[:8])
	if length != ^binary.BigEndian.Uint64(header[8:16]) {
		return nil, false, fmt.Errorf("corrupt journal frame length")
	}
	position, err := file.Seek(0, io.SeekCurrent)
	if err != nil {
		return nil, false, err
	}
	if length > uint64(size-position) {
		return nil, false, nil
	}
	if length > uint64(int(^uint(0)>>1)) {
		return nil, false, fmt.Errorf("journal frame too large")
	}
	data := make([]byte, int(length))
	if _, err := io.ReadFull(file, data); err != nil {
		return nil, false, err
	}
	digest := sha256.Sum256(data)
	if digest != ([32]byte)(header[16:]) {
		return nil, false, fmt.Errorf("corrupt journal frame checksum")
	}
	return data, true, nil
}

func readJournal(ctx context.Context, file *os.File, graph Graph) (Snapshot, int64, error) {
	fail := func(err error) (Snapshot, int64, error) { return Snapshot{}, 0, err }
	info, err := file.Stat()
	if err != nil {
		return fail(err)
	}
	magic := make([]byte, len(journalMagic))
	if _, err := io.ReadFull(file, magic); err != nil || string(magic) != journalMagic {
		return fail(fmt.Errorf("invalid journal header"))
	}
	data, complete, err := readJournalFrame(file, info.Size())
	if err != nil {
		return fail(err)
	}
	if !complete {
		return fail(fmt.Errorf("incomplete journal graph"))
	}
	savedGraph, err := ParseGraph(data)
	if err != nil {
		return fail(err)
	}
	if !equal(savedGraph, graph) {
		return fail(fmt.Errorf("journal graph differs from workflow"))
	}
	boundary, err := file.Seek(0, io.SeekCurrent)
	if err != nil {
		return fail(err)
	}
	snapshot := Snapshot{Graph: savedGraph, Values: map[string]json.RawMessage{}}
	pending := map[string]json.RawMessage{}
	committed := 0
	for {
		if err := ctx.Err(); err != nil {
			return fail(err)
		}
		data, complete, err := readJournalFrame(file, info.Size())
		if err != nil {
			return fail(err)
		}
		if !complete {
			break
		}
		var batch CommitBatch
		if err := decodeCanonical(data, &batch); err != nil {
			return fail(fmt.Errorf("decode journal batch: %w", err))
		}
		if len(batch.Events) == 0 {
			return fail(fmt.Errorf("empty journal batch"))
		}
		for id, v := range batch.Values {
			old, ok := snapshot.Values[id]
			if !ok {
				old, ok = pending[id]
			}
			if ok && !sameValues(old, v) {
				return fail(reject("NONDETERMINISTIC_VALUE", id))
			}
			pending[id] = v
		}
		for n, e := range batch.Events {
			if e.Txn != batch.Events[0].Txn || e.Type == "transaction.committed" && n != len(batch.Events)-1 {
				return fail(fmt.Errorf("journal batch crosses transaction boundaries"))
			}
		}
		snapshot.Events = append(snapshot.Events, batch.Events...)
		if batch.Events[len(batch.Events)-1].Type == "transaction.committed" {
			for id, v := range pending {
				snapshot.Values[id] = v
			}
			pending = map[string]json.RawMessage{}
			committed = len(snapshot.Events)
			boundary, err = file.Seek(0, io.SeekCurrent)
			if err != nil {
				return fail(err)
			}
		}
	}
	state, diagnostic := Recover(graph, snapshot.Events)
	if diagnostic != nil {
		return fail(diagnostic)
	}
	for _, id := range stateItemIDs(state) {
		if _, ok := snapshot.Values[id]; !ok {
			return fail(reject("MISSING_VALUE", id))
		}
	}
	snapshot.Events = snapshot.Events[:committed]
	return snapshot, boundary, nil
}
