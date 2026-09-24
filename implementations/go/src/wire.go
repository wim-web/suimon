package suimon

import (
	"fmt"
	"slices"
	"strconv"
	"strings"
	"unicode/utf8"
)

// The JSON values an execution record is made of (Lean Wire) and their text form (Lean WireText):
// compact JSON with one rendering, and a parser that accepts standard JSON formatting. Objects
// keep their fields in order and repeat no key, and numbers are natural numbers.

type wireKind int

const (
	wireNullKind wireKind = iota
	wireBoolKind
	wireNatKind
	wireStrKind
	wireArrKind
	wireObjKind
)

type wire struct {
	kind wireKind
	b    bool
	n    uint64
	// overflow marks a parsed natural number above 2^64-1, which n cannot hold; s then holds its
	// digits.
	overflow bool
	s        string
	items    []wire
	fields   []wireField
}

type wireField struct {
	key   string
	value wire
}

func wireNull() wire             { return wire{kind: wireNullKind} }
func wireBool(b bool) wire       { return wire{kind: wireBoolKind, b: b} }
func wireNat(n uint64) wire      { return wire{kind: wireNatKind, n: n} }
func wireInt(n int) wire         { return wireNat(uint64(n)) }
func wireStr(s string) wire      { return wire{kind: wireStrKind, s: s} }
func wireArr(items ...wire) wire { return wire{kind: wireArrKind, items: items} }

func wireObj(fields ...wireField) wire { return wire{kind: wireObjKind, fields: fields} }

func field(key string, value wire) wireField { return wireField{key, value} }

// lookup is the value of the first field named key, like Lean's List.lookup.
func (w wire) lookup(key string) (wire, bool) {
	for _, f := range w.fields {
		if f.key == key {
			return f.value, true
		}
	}
	return wire{}, false
}

// render is the compact JSON text of w: no whitespace, fields in order, and strings escaped with
// \" and \\ and with \u00xx (lowercase hexadecimal) for the characters below U+0020; every other
// character is written as it is. Invalid UTF-8 is written as U+FFFD. A natural number read beyond
// 2^64-1 is written with the digits it was read with.
func (w wire) render() string {
	var b strings.Builder
	w.renderTo(&b)
	return b.String()
}

func (w wire) renderTo(b *strings.Builder) {
	switch w.kind {
	case wireNullKind:
		b.WriteString("null")
	case wireBoolKind:
		b.WriteString(strconv.FormatBool(w.b))
	case wireNatKind:
		b.WriteString(natText(w))
	case wireStrKind:
		renderString(b, w.s)
	case wireArrKind:
		b.WriteByte('[')
		for i, item := range w.items {
			if i > 0 {
				b.WriteByte(',')
			}
			item.renderTo(b)
		}
		b.WriteByte(']')
	case wireObjKind:
		b.WriteByte('{')
		for i, f := range w.fields {
			if i > 0 {
				b.WriteByte(',')
			}
			renderString(b, f.key)
			b.WriteByte(':')
			f.value.renderTo(b)
		}
		b.WriteByte('}')
	}
}

// natText is the decimal text of a natural number as it was written.
func natText(w wire) string {
	if w.overflow {
		return w.s
	}
	return strconv.FormatUint(w.n, 10)
}

const hexDigits = "0123456789abcdef"

func renderString(b *strings.Builder, s string) {
	b.WriteByte('"')
	for _, c := range s {
		switch {
		case c == '"':
			b.WriteString(`\"`)
		case c == '\\':
			b.WriteString(`\\`)
		case c < 0x20:
			b.WriteString(`\u00`)
			b.WriteByte(hexDigits[c/16])
			b.WriteByte(hexDigits[c%16])
		default:
			b.WriteRune(c)
		}
	}
	b.WriteByte('"')
}

// renderLean is the text Lean's Json.compress gives for the same JSON value: object fields sorted
// by key, and strings escaped with \", \\, \n, \r and \u00xx for the other characters below U+0020.
// It matches the output of the Lean CLI byte for byte.
func (w wire) renderLean() string {
	var b strings.Builder
	w.renderLeanTo(&b)
	return b.String()
}

func (w wire) renderLeanTo(b *strings.Builder) {
	switch w.kind {
	case wireStrKind:
		renderLeanString(b, w.s)
	case wireArrKind:
		b.WriteByte('[')
		for i, item := range w.items {
			if i > 0 {
				b.WriteByte(',')
			}
			item.renderLeanTo(b)
		}
		b.WriteByte(']')
	case wireObjKind:
		fields := slices.Clone(w.fields)
		slices.SortStableFunc(fields, func(x, y wireField) int { return strings.Compare(x.key, y.key) })
		b.WriteByte('{')
		for i, f := range fields {
			if i > 0 {
				b.WriteByte(',')
			}
			renderLeanString(b, f.key)
			b.WriteByte(':')
			f.value.renderLeanTo(b)
		}
		b.WriteByte('}')
	default:
		w.renderTo(b)
	}
}

func renderLeanString(b *strings.Builder, s string) {
	b.WriteByte('"')
	for _, c := range s {
		switch {
		case c == '"':
			b.WriteString(`\"`)
		case c == '\\':
			b.WriteString(`\\`)
		case c == '\n':
			b.WriteString(`\n`)
		case c == '\r':
			b.WriteString(`\r`)
		case c < 0x20:
			b.WriteString(`\u00`)
			b.WriteByte(hexDigits[c/16])
			b.WriteByte(hexDigits[c%16])
		default:
			b.WriteRune(c)
		}
	}
	b.WriteByte('"')
}

// wireError is a parse error; offset counts characters (code points), as Lean does.
type wireError struct {
	msg    string
	offset int
}

func (e *wireError) Error() string { return fmt.Sprintf("%s at offset %d", e.msg, e.offset) }

type wireParser struct{ cs []rune }

func (p *wireParser) fail(msg string, at int) error { return &wireError{msg: msg, offset: at} }

// parseWire parses JSON text into a wire value: whitespace between tokens and the standard escapes
// are accepted, numbers must be natural numbers, no object may repeat a key, and nothing may follow
// the value.
func parseWire(s string) (wire, error) {
	p := &wireParser{cs: []rune(s)}
	w, rest, err := p.value(len(p.cs)+1, 0)
	if err != nil {
		return wire{}, err
	}
	if rest = p.skipWs(rest); rest < len(p.cs) {
		return wire{}, p.fail("unexpected trailing character "+quoteChar(p.cs[rest]), rest)
	}
	return w, nil
}

func isWireSpace(c rune) bool { return c == ' ' || c == '\t' || c == '\n' || c == '\r' }

func (p *wireParser) skipWs(i int) int {
	for i < len(p.cs) && isWireSpace(p.cs[i]) {
		i++
	}
	return i
}

// value reads one value after optional whitespace. The fuel bounds the call depth; the input
// length plus one is enough, because every call consumes input or is followed by one that does.
func (p *wireParser) value(fuel, i int) (wire, int, error) {
	if fuel == 0 {
		return wire{}, 0, p.fail("input too deeply nested", i)
	}
	j := p.skipWs(i)
	if j == len(p.cs) {
		return wire{}, 0, p.fail("unexpected end of input", j)
	}
	c := p.cs[j]
	switch {
	case c == '{':
		k := p.skipWs(j + 1)
		if k == len(p.cs) {
			return wire{}, 0, p.fail("unterminated object", k)
		}
		if p.cs[k] == '}' {
			return wireObj(), k + 1, nil
		}
		return p.fields(fuel-1, k, nil)
	case c == '[':
		k := p.skipWs(j + 1)
		if k == len(p.cs) {
			return wire{}, 0, p.fail("unterminated array", k)
		}
		if p.cs[k] == ']' {
			return wireArr(), k + 1, nil
		}
		return p.items(fuel-1, k, nil)
	case c == '"':
		s, rest, err := p.stringBody(j + 1)
		return wireStr(s), rest, err
	case c == 't':
		return p.literal("rue", wireBool(true), j+1)
	case c == 'f':
		return p.literal("alse", wireBool(false), j+1)
	case c == 'n':
		return p.literal("ull", wireNull(), j+1)
	case c == '0':
		if j+1 < len(p.cs) && isDigit(p.cs[j+1]) {
			return wire{}, 0, p.fail("leading zero in number", j+1)
		}
		return wireNat(0), j + 1, nil
	case isDigit(c):
		w := wire{kind: wireNatKind}
		k := j
		for ; k < len(p.cs) && isDigit(p.cs[k]); k++ {
			d := uint64(p.cs[k] - '0')
			if w.n > (^uint64(0)-d)/10 {
				w.overflow = true
			}
			w.n = w.n*10 + d
		}
		if w.overflow {
			w.s = string(p.cs[j:k])
		}
		return w, k, nil
	}
	return wire{}, 0, p.fail("unexpected character "+quoteChar(c), j)
}

func (p *wireParser) items(fuel, i int, acc []wire) (wire, int, error) {
	for {
		if fuel == 0 {
			return wire{}, 0, p.fail("input too deeply nested", i)
		}
		w, rest, err := p.value(fuel-1, i)
		if err != nil {
			return wire{}, 0, err
		}
		acc = append(acc, w)
		k := p.skipWs(rest)
		if k == len(p.cs) {
			return wire{}, 0, p.fail("unterminated array", k)
		}
		switch p.cs[k] {
		case ',':
			fuel, i = fuel-1, k+1
		case ']':
			return wireArr(acc...), k + 1, nil
		default:
			return wire{}, 0, p.fail("expected ',' or ']'", k)
		}
	}
}

// fields reads object fields from the first key on, through the closing brace. A key the object
// already has, compared after its escapes are decoded, is rejected right after its closing quote.
func (p *wireParser) fields(fuel, i int, acc []wireField) (wire, int, error) {
	keys := keySet{}
	for {
		if fuel == 0 {
			return wire{}, 0, p.fail("input too deeply nested", i)
		}
		k := p.skipWs(i)
		if k == len(p.cs) {
			return wire{}, 0, p.fail("unterminated object", k)
		}
		if p.cs[k] != '"' {
			return wire{}, 0, p.fail("expected a string key", k)
		}
		key, rest, err := p.stringBody(k + 1)
		if err != nil {
			return wire{}, 0, err
		}
		if !keys.add(key) {
			return wire{}, 0, p.fail("duplicate key "+quoteString(key), rest)
		}
		m := p.skipWs(rest)
		if m == len(p.cs) {
			return wire{}, 0, p.fail("unterminated object", m)
		}
		if p.cs[m] != ':' {
			return wire{}, 0, p.fail("expected ':'", m)
		}
		v, rest, err := p.value(fuel-1, m+1)
		if err != nil {
			return wire{}, 0, err
		}
		acc = append(acc, wireField{key, v})
		q := p.skipWs(rest)
		if q == len(p.cs) {
			return wire{}, 0, p.fail("unterminated object", q)
		}
		switch p.cs[q] {
		case ',':
			fuel, i = fuel-1, q+1
		case '}':
			return wireObj(acc...), q + 1, nil
		default:
			return wire{}, 0, p.fail("expected ',' or '}'", q)
		}
	}
}

// keySet holds the keys of an object read so far: a list while the object is small, and also a
// map once it is not, so that reading an object takes linear time.
type keySet struct {
	list  []string
	index map[string]struct{}
}

// add adds key and reports whether it is new.
func (s *keySet) add(key string) bool {
	if s.index != nil {
		if _, found := s.index[key]; found {
			return false
		}
		s.index[key] = struct{}{}
		return true
	}
	if slices.Contains(s.list, key) {
		return false
	}
	s.list = append(s.list, key)
	if len(s.list) > 16 {
		s.index = make(map[string]struct{}, 2*len(s.list))
		for _, k := range s.list {
			s.index[k] = struct{}{}
		}
	}
	return true
}

func (p *wireParser) literal(word string, value wire, i int) (wire, int, error) {
	rest := []rune(word)
	if len(p.cs)-i >= len(rest) && string(p.cs[i:i+len(rest)]) == word {
		return value, i + len(rest), nil
	}
	return wire{}, 0, p.fail("invalid literal", i)
}

func hexValue(c rune) (rune, bool) {
	switch {
	case '0' <= c && c <= '9':
		return c - '0', true
	case 'a' <= c && c <= 'f':
		return c - 'a' + 10, true
	case 'A' <= c && c <= 'F':
		return c - 'A' + 10, true
	}
	return 0, false
}

func hex4(cs []rune) (rune, bool) {
	var v rune
	for _, c := range cs {
		d, ok := hexValue(c)
		if !ok {
			return 0, false
		}
		v = v*16 + d
	}
	return v, true
}

var simpleEscapes = map[rune]rune{'"': '"', '\\': '\\', '/': '/', 'b': '\b', 'f': '\f', 'n': '\n', 'r': '\r', 't': '\t'}

// stringBody reads a string body after the opening quote, up to and including the closing quote.
func (p *wireParser) stringBody(i int) (string, int, error) {
	var b []byte
	for {
		if i == len(p.cs) {
			return "", 0, p.fail("unterminated string", i)
		}
		c := p.cs[i]
		switch {
		case c == '"':
			return string(b), i + 1, nil
		case c == '\\':
			if i+1 == len(p.cs) {
				return "", 0, p.fail("unterminated escape", i+1)
			}
			e := p.cs[i+1]
			if d, ok := simpleEscapes[e]; ok {
				b = utf8.AppendRune(b, d)
				i += 2
				continue
			}
			if e != 'u' {
				return "", 0, p.fail("invalid escape "+quoteChar(e), i+2)
			}
			if i+6 > len(p.cs) {
				return "", 0, p.fail(`truncated \u escape`, i+2)
			}
			v, ok := hex4(p.cs[i+2 : i+6])
			if !ok {
				return "", 0, p.fail(`invalid \u escape`, i+6)
			}
			switch {
			case v < 0xD800 || 0xDFFF < v:
				b = utf8.AppendRune(b, v)
				i += 6
			case v < 0xDC00:
				if i+12 > len(p.cs) {
					return "", 0, p.fail("unpaired high surrogate", i+6)
				}
				if p.cs[i+6] != '\\' || p.cs[i+7] != 'u' {
					return "", 0, p.fail("unpaired high surrogate", i+12)
				}
				lo, ok := hex4(p.cs[i+8 : i+12])
				if !ok {
					return "", 0, p.fail(`invalid \u escape`, i+12)
				}
				if lo < 0xDC00 || 0xDFFF < lo {
					return "", 0, p.fail("invalid low surrogate", i+12)
				}
				b = utf8.AppendRune(b, 0x10000+(v-0xD800)*0x400+(lo-0xDC00))
				i += 12
			default:
				return "", 0, p.fail("unpaired low surrogate", i+6)
			}
		case c < 0x20:
			return "", 0, p.fail("control character in string", i)
		default:
			b = utf8.AppendRune(b, c)
			i++
		}
	}
}

// quoteChar is Lean's repr of a character, used in parse errors.
func quoteChar(c rune) string { return "'" + quoteCore(c, false) + "'" }

// quoteString is Lean's repr of a string (String.quote), used for keys in parse errors.
func quoteString(s string) string {
	var b strings.Builder
	b.WriteByte('"')
	for _, c := range s {
		b.WriteString(quoteCore(c, true))
	}
	b.WriteByte('"')
	return b.String()
}

// quoteCore is Lean's Char.quoteCore: a character as a Lean literal writes it; ' is escaped only
// outside a string.
func quoteCore(c rune, inString bool) string {
	switch {
	case c == '\n':
		return `\n`
	case c == '\t':
		return `\t`
	case c == '\\':
		return `\\`
	case c == '"':
		return `\"`
	case !inString && c == '\'':
		return `\'`
	case c <= 31 || c == 0x7f:
		return `\x` + string(hexDigits[c/16]) + string(hexDigits[c%16])
	}
	return string(c)
}
