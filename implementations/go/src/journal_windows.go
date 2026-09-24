//go:build windows

package suimon

import (
	"os"
	"syscall"
	"unsafe"
)

var (
	kernel32         = syscall.NewLazyDLL("kernel32.dll")
	procLockFileEx   = kernel32.NewProc("LockFileEx")
	procUnlockFileEx = kernel32.NewProc("UnlockFileEx")
)

const (
	lockfileFailImmediately = 0x1
	lockfileExclusiveLock   = 0x2
	errorLockViolation      = syscall.Errno(33) // ERROR_LOCK_VIOLATION
)

// lockedByte is what the lock covers: the last byte a file could have. Windows locks are mandatory,
// so a lock on the contents would keep other processes from reading the record.
func lockedByte() *syscall.Overlapped {
	return &syscall.Overlapped{Offset: ^uint32(0), OffsetHigh: ^uint32(0)}
}

// lockFile takes an exclusive lock on f without waiting. The lock belongs to the handle, so another
// opening of the file conflicts with it even in this process.
func lockFile(f *os.File) error {
	r, _, err := procLockFileEx.Call(f.Fd(), lockfileExclusiveLock|lockfileFailImmediately, 0, 1, 0,
		uintptr(unsafe.Pointer(lockedByte())))
	switch {
	case r != 0:
		return nil
	case err == errorLockViolation:
		return ErrJournalLocked
	}
	return err
}

// unlockFile releases the lock before f is closed: Windows may release the lock of a closed handle
// only some time later.
func unlockFile(f *os.File) error {
	r, _, err := procUnlockFileEx.Call(f.Fd(), 0, 1, 0, uintptr(unsafe.Pointer(lockedByte())))
	if r == 0 {
		return err
	}
	return nil
}
