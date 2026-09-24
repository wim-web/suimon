//go:build darwin || dragonfly || freebsd || linux || netbsd || openbsd

package suimon

import (
	"os"
	"syscall"
)

// lockFile takes an exclusive flock on f without waiting. The lock belongs to the open file
// description, so another opening of the file conflicts with it even in this process, and closing
// f releases it.
func lockFile(f *os.File) error {
	for {
		err := syscall.Flock(int(f.Fd()), syscall.LOCK_EX|syscall.LOCK_NB)
		switch err {
		case syscall.EINTR:
			continue
		case syscall.EWOULDBLOCK:
			return ErrJournalLocked
		}
		return err
	}
}

func unlockFile(*os.File) error { return nil }
