//go:build !(darwin || dragonfly || freebsd || linux || netbsd || openbsd || windows)

package suimon

import "os"

// Other platforms have no journal lock (see FileJournal).

func lockFile(*os.File) error { return nil }

func unlockFile(*os.File) error { return nil }
