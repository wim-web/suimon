package suimon

import (
	"context"
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
)

// SnapshotFile persists a complete journal/value snapshot by atomic replacement.
// Use one execution writer per path. The parent directory must already exist.
type SnapshotFile struct{ Path string }

func (f SnapshotFile) Save(ctx context.Context, snapshot Snapshot) error {
	if err := ctx.Err(); err != nil {
		return err
	}
	data, err := json.Marshal(snapshot)
	if err != nil {
		return err
	}
	dir := filepath.Dir(f.Path)
	temp, err := os.CreateTemp(dir, ".suimon-checkpoint-*")
	if err != nil {
		return err
	}
	name := temp.Name()
	defer os.Remove(name)
	defer temp.Close()
	if _, err := temp.Write(data); err != nil {
		return err
	}
	if err := temp.Sync(); err != nil {
		return err
	}
	if err := temp.Close(); err != nil {
		return err
	}
	if err := ctx.Err(); err != nil {
		return err
	}
	if err := os.Rename(name, f.Path); err != nil {
		return err
	}
	directory, err := os.Open(dir)
	if err != nil {
		return err
	}
	defer directory.Close()
	return directory.Sync()
}
func (f SnapshotFile) Load(ctx context.Context) (Snapshot, error) {
	if err := ctx.Err(); err != nil {
		return Snapshot{}, err
	}
	data, err := os.ReadFile(f.Path)
	if err != nil {
		return Snapshot{}, err
	}
	var snapshot Snapshot
	if err := json.Unmarshal(data, &snapshot); err != nil {
		return Snapshot{}, fmt.Errorf("decode checkpoint: %w", err)
	}
	return snapshot, nil
}
