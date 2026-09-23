package suimon

import (
	"fmt"
	"math"
	"math/big"
	"sort"
	"unicode/utf8"
)

// A port of Lean's Json.parse (Lean/Data/Json/Parser.lean), which reads program files. Porting it
// keeps the accepted inputs and the error messages of the Lean CLI: objects keep one field per key
// (the last one) in key order, numbers are a mantissa and a decimal exponent, a lone surrogate
// escape becomes U+FFFD, and errors report the byte offset.

type ljKind int

const (
	ljNull ljKind = iota
	ljBool
	ljNum
	ljStr
	ljArr
	ljObj
)

type ljValue struct {
	kind  ljKind
	b     bool
	num   ljNumber
	str   string
	items []ljValue
	// fields are sorted by key, one per key, like Lean's Std.TreeMap.
	fields []ljField
}

type ljField struct {
	key   string
	value ljValue
}

// ljNumber is Lean's JsonNumber: (-1)^neg * mantissa / 10^exponent, with neg false for zero.
type ljNumber struct {
	neg      bool
	mantissa *big.Int
	exponent *big.Int
}

// nat is Lean's Json.getNat?: a number with exponent 0 and a non-negative mantissa. Values above
// 2^64-1 are clamped (see Timeout).
func (n ljNumber) nat() (uint64, bool) {
	if n.exponent.Sign() != 0 || n.neg {
		return 0, false
	}
	if !n.mantissa.IsUint64() {
		return math.MaxUint64, true
	}
	return n.mantissa.Uint64(), true
}

func (v ljValue) field(key string) (ljValue, bool) {
	if v.kind != ljObj {
		return ljValue{}, false
	}
	i := sort.Search(len(v.fields), func(i int) bool { return v.fields[i].key >= key })
	if i < len(v.fields) && v.fields[i].key == key {
		return v.fields[i].value, true
	}
	return ljValue{}, false
}

type ljError struct {
	offset int
	msg    string
}

func (e *ljError) Error() string { return fmt.Sprintf("offset %d: %s", e.offset, e.msg) }

type ljParser struct {
	s   string
	pos int
}

// parseLeanJSON parses valid UTF-8 text as Lean's Json.parse does.
func parseLeanJSON(s string) (ljValue, error) {
	p := &ljParser{s: s}
	p.ws()
	v, err := p.anyCore()
	if err != nil {
		return ljValue{}, err
	}
	if p.pos < len(p.s) {
		return ljValue{}, p.fail("expected end of input")
	}
	return v, nil
}

func (p *ljParser) fail(msg string) error { return &ljError{offset: p.pos, msg: msg} }

func (p *ljParser) eof() error { return p.fail("unexpected end of input") }

func (p *ljParser) peek() (rune, bool) {
	if p.pos >= len(p.s) {
		return 0, false
	}
	r, _ := utf8.DecodeRuneInString(p.s[p.pos:])
	return r, true
}

func (p *ljParser) skip() {
	_, size := utf8.DecodeRuneInString(p.s[p.pos:])
	p.pos += size
}

// next is Parsec's any: the next character, consumed.
func (p *ljParser) next() (rune, error) {
	c, ok := p.peek()
	if !ok {
		return 0, p.eof()
	}
	p.skip()
	return c, nil
}

func (p *ljParser) ws() {
	for p.pos < len(p.s) {
		switch p.s[p.pos] {
		case ' ', '\t', '\n', '\r':
			p.pos++
		default:
			return
		}
	}
}

// lookahead fails with "expected desc" unless the next character satisfies ok; it consumes nothing.
func (p *ljParser) lookahead(ok func(rune) bool, desc string) error {
	c, found := p.peek()
	if !found {
		return p.eof()
	}
	if !ok(c) {
		return p.fail("expected " + desc)
	}
	return nil
}

func isDigit(c rune) bool { return '0' <= c && c <= '9' }

func (p *ljParser) skipString(word string) error {
	if len(p.s)-p.pos >= len(word) && p.s[p.pos:p.pos+len(word)] == word {
		p.pos += len(word)
		return nil
	}
	return p.fail("expected: " + word)
}

func (p *ljParser) anyCore() (ljValue, error) {
	c, ok := p.peek()
	if !ok {
		return ljValue{}, p.eof()
	}
	switch {
	case c == '[':
		p.skip()
		p.ws()
		c, ok := p.peek()
		if !ok {
			return ljValue{}, p.eof()
		}
		if c == ']' {
			p.skip()
			p.ws()
			return ljValue{kind: ljArr}, nil
		}
		items, err := p.arrayCore()
		return ljValue{kind: ljArr, items: items}, err
	case c == '{':
		p.skip()
		p.ws()
		c, ok := p.peek()
		if !ok {
			return ljValue{}, p.eof()
		}
		if c == '}' {
			p.skip()
			p.ws()
			return ljValue{kind: ljObj}, nil
		}
		fields, err := p.objectCore()
		return ljValue{kind: ljObj, fields: fields}, err
	case c == '"':
		p.skip()
		s, err := p.str()
		if err != nil {
			return ljValue{}, err
		}
		p.ws()
		return ljValue{kind: ljStr, str: s}, nil
	case c == 'f':
		if err := p.skipString("false"); err != nil {
			return ljValue{}, err
		}
		p.ws()
		return ljValue{kind: ljBool, b: false}, nil
	case c == 't':
		if err := p.skipString("true"); err != nil {
			return ljValue{}, err
		}
		p.ws()
		return ljValue{kind: ljBool, b: true}, nil
	case c == 'n':
		if err := p.skipString("null"); err != nil {
			return ljValue{}, err
		}
		p.ws()
		return ljValue{kind: ljNull}, nil
	case c == '-' || isDigit(c):
		n, err := p.num()
		if err != nil {
			return ljValue{}, err
		}
		p.ws()
		return ljValue{kind: ljNum, num: n}, nil
	}
	return ljValue{}, p.fail("unexpected input")
}

func (p *ljParser) arrayCore() ([]ljValue, error) {
	var items []ljValue
	for {
		item, err := p.anyCore()
		if err != nil {
			return nil, err
		}
		items = append(items, item)
		c, err := p.next()
		if err != nil {
			return nil, err
		}
		switch c {
		case ']':
			p.ws()
			return items, nil
		case ',':
			p.ws()
		default:
			return nil, p.fail("unexpected character in array")
		}
	}
}

func (p *ljParser) objectCore() ([]ljField, error) {
	var fields []ljField
	for {
		if err := p.lookahead(func(c rune) bool { return c == '"' }, `"`); err != nil {
			return nil, err
		}
		p.skip()
		key, err := p.str()
		if err != nil {
			return nil, err
		}
		p.ws()
		if err := p.lookahead(func(c rune) bool { return c == ':' }, ":"); err != nil {
			return nil, err
		}
		p.skip()
		p.ws()
		value, err := p.anyCore()
		if err != nil {
			return nil, err
		}
		fields = append(fields, ljField{key, value})
		c, err := p.next()
		if err != nil {
			return nil, err
		}
		switch c {
		case '}':
			p.ws()
			return treeMap(fields), nil
		case ',':
			p.ws()
		default:
			return nil, p.fail("unexpected character in object")
		}
	}
}

// treeMap keeps the last field of each key and sorts the fields by key.
func treeMap(fields []ljField) []ljField {
	last := make(map[string]int, len(fields))
	for i, f := range fields {
		last[f.key] = i
	}
	out := make([]ljField, 0, len(last))
	for i, f := range fields {
		if last[f.key] == i {
			out = append(out, f)
		}
	}
	sort.Slice(out, func(i, j int) bool { return out[i].key < out[j].key })
	return out
}

func (p *ljParser) str() (string, error) {
	var acc []byte
	for {
		c, ok := p.peek()
		if !ok {
			return "", p.eof()
		}
		if c == '"' {
			p.skip()
			return string(acc), nil
		}
		p.skip()
		if c == '\\' {
			e, err := p.escapedChar()
			if err != nil {
				return "", err
			}
			acc = utf8.AppendRune(acc, e)
		} else if c >= 0x20 {
			acc = utf8.AppendRune(acc, c)
		} else {
			return "", p.fail("unexpected character in string")
		}
	}
}

func (p *ljParser) hexChar() (uint32, error) {
	c, err := p.next()
	if err != nil {
		return 0, err
	}
	switch {
	case '0' <= c && c <= '9':
		return uint32(c - '0'), nil
	case 'a' <= c && c <= 'f':
		return uint32(c-'a') + 10, nil
	case 'A' <= c && c <= 'F':
		return uint32(c-'A') + 10, nil
	}
	return 0, p.fail("invalid hex character")
}

func (p *ljParser) escapedChar() (rune, error) {
	c, err := p.next()
	if err != nil {
		return 0, err
	}
	switch c {
	case '\\', '"', '/':
		return c, nil
	case 'b':
		return '\b', nil
	case 'f':
		return '\f', nil
	case 'n':
		return '\n', nil
	case 'r':
		return '\r', nil
	case 't':
		return '\t', nil
	case 'u':
		var val uint32
		for range 4 {
			h, err := p.hexChar()
			if err != nil {
				return 0, err
			}
			val = val<<4 | h
		}
		switch {
		case val < 0xD800 || val >= 0xE000:
			return rune(val), nil
		case val < 0xDC00:
			start := p.pos
			if r, ok := p.finishSurrogatePair(val); ok {
				return r, nil
			}
			p.pos = start
			return utf8.RuneError, nil
		default:
			return utf8.RuneError, nil
		}
	}
	return 0, p.fail(`illegal \u escape`)
}

// finishSurrogatePair reads the low half of a surrogate pair; on failure the caller backtracks.
func (p *ljParser) finishSurrogatePair(high uint32) (rune, bool) {
	for _, want := range []string{`\`, "u", "dD"} {
		c, err := p.next()
		if err != nil || (c != rune(want[0]) && (len(want) == 1 || c != rune(want[1]))) {
			return 0, false
		}
	}
	var val uint32
	for range 3 {
		h, err := p.hexChar()
		if err != nil {
			return 0, false
		}
		val = val<<4 | h
	}
	if val < 0xC00 {
		return 0, false
	}
	return rune(((high&0x3FF)<<10 | (val & 0x3FF)) + 0x10000), true
}

// digits reads decimal digits as far as they go and returns their value and count.
func (p *ljParser) digits() (*big.Int, int) {
	start := p.pos
	for p.pos < len(p.s) && isDigit(rune(p.s[p.pos])) {
		p.pos++
	}
	n, _ := new(big.Int).SetString(p.s[start:p.pos], 10)
	if n == nil {
		n = new(big.Int)
	}
	return n, p.pos - start
}

var (
	bigTen    = big.NewInt(10)
	usizeSize = new(big.Int).Lsh(big.NewInt(1), 64)
	// hugeShift is a shift beyond which any non-zero mantissa exceeds 2^64, so the exact value no
	// longer matters (see ljNumber.nat).
	hugeShift = big.NewInt(64)
)

func (p *ljParser) num() (ljNumber, error) {
	neg := false
	if c, _ := p.peek(); c == '-' {
		p.skip()
		neg = true
	}
	c, ok := p.peek()
	if !ok {
		return ljNumber{}, p.eof()
	}
	whole := new(big.Int)
	if c == '0' {
		p.skip()
	} else {
		if err := p.lookahead(func(c rune) bool { return '1' <= c && c <= '9' }, "1-9"); err != nil {
			return ljNumber{}, err
		}
		whole, _ = p.digits()
	}
	n := ljNumber{mantissa: whole, exponent: new(big.Int)}
	if c, ok := p.peek(); ok && c == '.' {
		p.skip()
		if err := p.lookahead(isDigit, "digit"); err != nil {
			return ljNumber{}, err
		}
		fraction, count := p.digits()
		scale := new(big.Int).Exp(bigTen, big.NewInt(int64(count)), nil)
		n.mantissa = new(big.Int).Add(new(big.Int).Mul(whole, scale), fraction)
		n.exponent = big.NewInt(int64(count))
	}
	n.neg = neg && n.mantissa.Sign() != 0
	c, ok = p.peek()
	if !ok || (c != 'e' && c != 'E') {
		return n, nil
	}
	p.skip()
	c, ok = p.peek()
	if !ok {
		return ljNumber{}, p.eof()
	}
	if c == '-' {
		p.skip()
		if err := p.lookahead(isDigit, "0-9"); err != nil {
			return ljNumber{}, err
		}
		shift, _ := p.digits()
		n.exponent = new(big.Int).Add(n.exponent, shift)
		return n, nil
	}
	if c == '+' {
		p.skip()
	}
	if err := p.lookahead(isDigit, "0-9"); err != nil {
		return ljNumber{}, err
	}
	shift, _ := p.digits()
	if shift.Cmp(usizeSize) > 0 {
		return ljNumber{}, p.fail("exp too large")
	}
	// JsonNumber.shiftl: ⟨m * 10 ^ (s - e), e - s⟩ with truncated subtraction.
	if shift.Cmp(n.exponent) <= 0 {
		n.exponent = new(big.Int).Sub(n.exponent, shift)
		return n, nil
	}
	pad := new(big.Int).Sub(shift, n.exponent)
	n.exponent = new(big.Int)
	if n.mantissa.Sign() != 0 {
		if pad.Cmp(hugeShift) > 0 {
			pad = hugeShift
		}
		n.mantissa = new(big.Int).Mul(n.mantissa, new(big.Int).Exp(bigTen, pad, nil))
	}
	return n, nil
}
