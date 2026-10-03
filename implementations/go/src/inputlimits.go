package suimon

import "fmt"

const (
	// DefaultMaxInputBytes limits each definition or execution-record line to 1 MiB.
	DefaultMaxInputBytes = 1 << 20
	// MaxInputDepth counts open arrays and objects, including empty containers.
	MaxInputDepth = 64
)

// InputLimits controls the byte budget of a definition or record line. Zero uses
// DefaultMaxInputBytes. The nesting ceiling is fixed, independent of input size.
type InputLimits struct {
	MaxBytes int
}

func (l InputLimits) maxBytes() int {
	if l.MaxBytes <= 0 {
		return DefaultMaxInputBytes
	}
	return l.MaxBytes
}

func (l InputLimits) checkSize(n int) error {
	if n > l.maxBytes() {
		return fmt.Errorf("input exceeds maximum size of %d bytes", l.maxBytes())
	}
	return nil
}

// check scans before recursive parsing or rune allocation. Quotes and escapes
// are tracked so brackets in strings do not consume the nesting budget. Syntax
// validation and its existing diagnostics remain the parser's responsibility.
func (l InputLimits) check(s string) error {
	if err := l.checkSize(len(s)); err != nil {
		return err
	}
	depth, quoted, escaped := 0, false, false
	for i := 0; i < len(s); i++ {
		c := s[i]
		if quoted {
			if escaped {
				escaped = false
			} else if c == '\\' {
				escaped = true
			} else if c == '"' {
				quoted = false
			}
			continue
		}
		switch c {
		case '"':
			quoted = true
		case '[', '{':
			depth++
			if depth > MaxInputDepth {
				return fmt.Errorf("input exceeds maximum nesting depth of %d", MaxInputDepth)
			}
		case ']', '}':
			if depth > 0 {
				depth--
			}
		}
	}
	return nil
}
