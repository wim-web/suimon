package suimon

import (
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"os"
	"path/filepath"
	"testing"
)

func TestLeanSourceSnapshot(t *testing.T) {
	b, err := os.ReadFile(filepath.Join("..", "lean-sources.json"))
	if err != nil {
		t.Fatal(err)
	}
	var sources map[string]string
	if err := json.Unmarshal(b, &sources); err != nil {
		t.Fatal(err)
	}
	for path, want := range sources {
		b, err := os.ReadFile(filepath.Join("..", "..", "..", path))
		if err != nil {
			t.Fatal(err)
		}
		sum := sha256.Sum256(b)
		if hex.EncodeToString(sum[:]) != want {
			t.Errorf("%s changed: update its Go translation and rerun bin/test-go before updating lean-sources.json", path)
		}
	}
}
