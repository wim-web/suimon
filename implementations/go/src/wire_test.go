package suimon

import (
	"encoding/json"
	"testing"
)

// Ported from Test/WireText.lean. A backslash in an expected text is written \x5c.

func renders(t *testing.T, label string, w wire, expected string) {
	t.Helper()
	if got := w.render(); got != expected {
		t.Errorf("%s: rendered %s, expected %s", label, got, expected)
	}
}

func roundTrip(t *testing.T, label string, w wire) {
	t.Helper()
	text := w.render()
	back, err := parseWire(text)
	if err != nil {
		t.Errorf("%s: %s did not parse: %v", label, text, err)
	} else if back.render() != text {
		t.Errorf("%s: round trip changed %s to %s", label, text, back.render())
	}
	for _, c := range text {
		if c == '\n' {
			t.Errorf("%s: raw newline in %s", label, text)
		}
	}
}

func parses(t *testing.T, label, text string, expected wire) {
	t.Helper()
	w, err := parseWire(text)
	if err != nil {
		t.Errorf("%s: %v", label, err)
	} else if w.render() != expected.render() {
		t.Errorf("%s: parsed %s, expected %s", label, w.render(), expected.render())
	}
}

var sample = wireObj(
	field("name", wireStr("suimon")),
	field("quote", wireStr("say \"hi\" \\ back\\slash")),
	field("control", wireStr("a\nb\tc\r\x00\x1f")),
	field("unicode", wireStr("日本語 é \U0001F600 \x7f")),
	field("nums", wireArr(wireNat(0), wireNat(7), wireNat(10), wireNat(^uint64(0)))),
	field("flags", wireArr(wireBool(true), wireBool(false), wireNull())),
	field("nested", wireArr(wireArr(), wireObj(), wireArr(wireArr(wireObj(field("", wireArr())))))),
	field("dup", wireNat(1)),
	field("dup", wireNat(2)))

func TestWireText(t *testing.T) {
	renders(t, "scalars", wireArr(wireNull(), wireBool(true), wireBool(false), wireNat(0), wireNat(42)),
		"[null,true,false,0,42]")
	renders(t, "empty", wireObj(field("a", wireArr()), field("b", wireObj())), `{"a":[],"b":{}}`)
	renders(t, "escapes", wireStr("\"\\\n\x1f/é"), "\"\x5c\"\x5c\x5c\x5cu000a\x5cu001f/é\"")
	renders(t, "field order", wireObj(field("z", wireNat(1)), field("a", wireNat(2)), field("z", wireNat(3))),
		`{"z":1,"a":2,"z":3}`)
	deep := wireNull()
	for range 200 {
		deep = wireArr(deep)
	}
	for label, w := range map[string]wire{"null": wireNull(), "empty string": wireStr(""), "empty array": wireArr(),
		"empty object": wireObj(), "sample": sample, "deep": deep} {
		roundTrip(t, label, w)
	}
	parses(t, "whitespace", " { \"a\" :\n[ 1 ,\t2 ] ,\r\"b\" : { } } ",
		wireObj(field("a", wireArr(wireNat(1), wireNat(2))), field("b", wireObj())))
	parses(t, "standard escapes", "\"\x5cn\x5ct\x5cr\x5cb\x5cf\x5c/\x5cu00e9\x5cu00C9\"", wireStr("\n\t\r\x08\x0c/éÉ"))
	parses(t, "surrogate pair", "\"\x5cud83d\x5cude00\"", wireStr("\U0001F600"))
	for label, text := range map[string]string{"trailing content": "{} {}", "leading zero": "01", "negative": "-1",
		"fraction": "1.5", "trailing comma": "[1,]", "raw control character": "\"a\nb\"",
		"lone surrogate": "\"\x5cude00\"", "unterminated": "[\"a\"", "empty": ""} {
		if w, err := parseWire(text); err == nil {
			t.Errorf("%s: accepted %s as %s", label, text, w.render())
		}
	}
	// A natural number beyond 2^64-1 parses, and is flagged.
	if w, err := parseWire("1234567890123456789012345678901234567890"); err != nil || !w.overflow {
		t.Errorf("large natural number: %+v %v", w, err)
	}
	// Go's encoding/json reads the same strings from a rendering.
	var doc map[string]any
	if err := json.Unmarshal([]byte(sample.render()), &doc); err != nil {
		t.Fatal(err)
	}
	if doc["unicode"] != "日本語 é \U0001F600 \x7f" || doc["control"] != "a\nb\tc\r\x00\x1f" || doc["quote"] != "say \"hi\" \\ back\\slash" {
		t.Errorf("encoding/json reads %v", doc)
	}
}
