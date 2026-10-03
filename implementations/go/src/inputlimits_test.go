package suimon

import (
	"fmt"
	"strings"
	"testing"
)

func nestedInput(open, close, leaf string, depth int) string {
	return strings.Repeat(open, depth) + leaf + strings.Repeat(close, depth)
}

func TestInputLimits(t *testing.T) {
	parsers := map[string]func(string) error{
		"definition JSON": func(s string) error { _, err := parseLeanJSON(s); return err },
		"record JSON":     func(s string) error { _, err := parseWire(s); return err },
	}
	for name, parse := range parsers {
		t.Run(name, func(t *testing.T) {
			for _, brackets := range [][2]string{{"[", "]"}, {`{"x":`, "}"}, {`[{"x":`, "}]"}} {
				step := strings.Count(brackets[0], "[") + strings.Count(brackets[0], "{")
				for _, leaf := range []string{"null", "[]", "{}"} {
					leafDepth := 0
					if leaf != "null" {
						leafDepth = 1
					}
					n := (MaxInputDepth - leafDepth) / step
					if err := parse(nestedInput(brackets[0], brackets[1], leaf, n)); err != nil {
						t.Fatalf("at limit: %v", err)
					}
					err := parse(nestedInput(brackets[0], brackets[1], leaf, n+1))
					if err == nil || err.Error() != "input exceeds maximum nesting depth of 64" {
						t.Fatalf("past limit: %v", err)
					}
				}
			}
			// Wide arrays consume bytes, not nesting fuel. Strings may contain brackets,
			// escaped quotes, escaped backslashes, and Unicode escapes for brackets.
			for _, s := range []string{
				"[" + strings.Repeat("0,", 10000) + "0]",
				`"` + strings.Repeat(`\"\\[{}]\u005b`, 100) + `"`,
				`"` + strings.Repeat("x", DefaultMaxInputBytes-2) + `"`,
			} {
				if err := parse(s); err != nil {
					t.Fatal(err)
				}
			}
			for _, s := range []string{
				strings.Repeat(" ", DefaultMaxInputBytes) + "0",
				`"` + strings.Repeat("界", DefaultMaxInputBytes/3) + `"`,
				"[" + strings.Repeat("0,", DefaultMaxInputBytes/2) + "0]",
			} {
				err := parse(s)
				if err == nil || err.Error() != "input exceeds maximum size of 1048576 bytes" {
					t.Fatalf("size limit: %v", err)
				}
			}
		})
	}
}

func TestInputLimitEntryPoints(t *testing.T) {
	header := `{"definition":{"main":"w"},"validated":false}` + "\n"
	entries := map[string]func(string) error{
		"ParseDefinition": func(s string) error { _, e := ParseDefinition([]byte(s)); return e },
		"LoadHeader":      func(s string) error { _, e := LoadHeader([]byte(s), true); return e },
		"unchecked header": func(s string) error {
			_, e := LoadHeader([]byte(s), false)
			return e
		},
		"DecodeOp":     func(s string) error { _, e := DecodeOp(s); return e },
		"DecodeRecord": func(s string) error { _, e := DecodeRecord(s); return e },
		"Check header": func(s string) error { _, e := Check(s+"\n", LoadHeader); return e },
		"Check record": func(s string) error { _, e := Check(header+s+"\n", LoadHeader); return e },
		"Recover":      func(s string) error { _, e := Recover(s+"\n", LoadHeader); return e },
	}
	for name, parse := range entries {
		t.Run(name, func(t *testing.T) {
			for _, s := range []string{
				nestedInput("[", "]", "null", 20000),
				strings.Repeat(" ", DefaultMaxInputBytes) + "0",
			} {
				err := parse(s)
				if err == nil || !strings.Contains(err.Error(), "input exceeds maximum") {
					t.Fatalf("got %v", err)
				}
			}
		})
	}
	// The type decoder is also guarded when an alternate decoder builds the AST.
	v := ljValue{kind: ljStr, str: "T"}
	for i := 0; i < MaxInputDepth; i++ {
		v = ljValue{kind: ljObj, fields: []ljField{{"list", v}}}
	}
	if typ, err := decodeValueType(v, "type"); err != nil || typ.Lists != MaxInputDepth {
		t.Fatalf("type at limit: %v, %v", typ, err)
	}
	v = ljValue{kind: ljObj, fields: []ljField{{"list", v}}}
	if _, err := decodeValueType(v, "type"); err == nil {
		t.Fatal("alternate type decoder bypassed depth limit")
	}
	// Check the whole definition's depth, including its enclosing schema fields.
	for _, n := range []int{MaxInputDepth - 4, MaxInputDepth - 3} {
		s := `{"main":"w","functions":[{"id":"f","output":{"single":` +
			nestedInput(`{"list":`, "}", `"T"`, n) + `}}]}`
		_, err := ParseDefinition([]byte(s))
		if (err == nil) != (n == MaxInputDepth-4) {
			t.Fatalf("definition depth %d: %v", n+4, err)
		}
	}
}

func TestConfiguredInputSize(t *testing.T) {
	large := []byte(`{"main":"w"}` + strings.Repeat(" ", DefaultMaxInputBytes))
	if _, err := ParseDefinition(large); err == nil {
		t.Fatal("default size limit ignored")
	}
	if _, err := ParseDefinitionWithLimits(large, InputLimits{MaxBytes: len(large)}); err != nil {
		t.Fatalf("raised definition budget: %v", err)
	}
	definition := []byte(`{"main":"界"}`)
	for _, delta := range []int{-1, 0, 1} {
		_, err := ParseDefinitionWithLimits(definition, InputLimits{MaxBytes: len(definition) + delta})
		if (err == nil) != (delta >= 0) {
			t.Fatalf("size delta %d: %v", delta, err)
		}
	}
	record := `{"seq":1,"commit":true}`
	if _, err := DecodeRecordWithLimits(record, InputLimits{MaxBytes: len(record)}); err != nil {
		t.Fatal(err)
	}
	if _, err := DecodeRecordWithLimits(record, InputLimits{MaxBytes: len(record) - 1}); err == nil {
		t.Fatal("record byte limit ignored")
	}
	if _, err := ParseDefinitionWithLimits([]byte(nestedInput("[", "]", "0", 65)), InputLimits{MaxBytes: 2 << 20}); err == nil {
		t.Fatal("increased byte limit bypassed depth limit")
	}
	header := `{"definition":{"main":"w"},"validated":false}`
	_, err := CheckWithLimits(header+"\n", LoadHeader, InputLimits{MaxBytes: len(header) - 1})
	if err == nil || err.Error() != fmt.Sprintf("line 1: input exceeds maximum size of %d bytes", len(header)-1) {
		t.Fatalf("check byte limit: %v", err)
	}
}

func FuzzInputDepth(f *testing.F) {
	f.Add(uint16(64), true)
	f.Add(uint16(65), false)
	f.Add(uint16(20000), true)
	f.Fuzz(func(t *testing.T, depth uint16, arrays bool) {
		open, close := `{"list":`, "}"
		if arrays {
			open, close = "[", "]"
		}
		s := nestedInput(open, close, "null", int(depth))
		_, jsonErr := parseLeanJSON(s)
		_, wireErr := parseWire(s)
		wantOK := depth <= MaxInputDepth
		if (jsonErr == nil) != wantOK || (wireErr == nil) != wantOK {
			t.Fatalf("depth %d: definition %v, record %v", depth, jsonErr, wireErr)
		}
	})
}
