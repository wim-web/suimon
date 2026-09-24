package suimon

import (
	"slices"
	"strconv"
	"strings"
	"unicode/utf8"
)

// Identity encodes structured parts as one string: each part is its length in code points in
// decimal, a colon, and the part itself (Lean identity). The encoding is injective; DecodeIdentity
// inverts it.
func Identity(parts ...string) string {
	var b strings.Builder
	for _, part := range parts {
		b.WriteString(strconv.Itoa(utf8.RuneCountInString(part)))
		b.WriteByte(':')
		b.WriteString(part)
	}
	return b.String()
}

// DecodeIdentity returns the parts of an identity, and false for a string that is not one. Like
// Lean's decodeIdentity, it reads each length as the digits that are there, so it also accepts
// forms that Identity never writes, such as a length with leading zeros or none at all (":" is
// one empty part); DecodeIdentity(Identity(parts...)) is always parts.
func DecodeIdentity(id string) ([]string, bool) {
	parts := []string{}
	for id != "" {
		digits := 0
		for digits < len(id) && '0' <= id[digits] && id[digits] <= '9' {
			digits++
		}
		if digits == len(id) || id[digits] != ':' {
			return nil, false
		}
		length := 0
		for _, d := range id[:digits] {
			if length > (len(id)-int(d-'0'))/10 {
				return nil, false // longer than the whole identity
			}
			length = length*10 + int(d-'0')
		}
		rest := id[digits+1:]
		end := 0
		for range length {
			if end == len(rest) {
				return nil, false
			}
			_, size := utf8.DecodeRuneInString(rest[end:])
			end += size
		}
		parts = append(parts, rest[:end])
		id = rest[end:]
	}
	return parts, true
}

// listValue identifies a list value by the multiset of its elements (§15.4): the elements are
// sorted, so the identity does not depend on the order in which results arrived.
func listValue(values []string) string {
	sorted := slices.Clone(values)
	slices.Sort(sorted)
	return Identity(append([]string{"list"}, sorted...)...)
}
