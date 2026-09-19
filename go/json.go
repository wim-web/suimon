package suimon

import (
	"bytes"
	"encoding/json"
	"fmt"
	"io"
	"math/big"
	"reflect"
	"sort"
	"strings"
)

// List encodes an empty Go slice as [], as Lean lists do.
type List[T any] []T

func (xs List[T]) MarshalJSON() ([]byte, error) {
	if xs == nil {
		return []byte("[]"), nil
	}
	return json.Marshal([]T(xs))
}
func (xs *List[T]) UnmarshalJSON(b []byte) error {
	if bytes.Equal(bytes.TrimSpace(b), []byte("null")) {
		return fmt.Errorf("expected array")
	}
	var v []T
	if err := json.Unmarshal(b, &v); err != nil {
		return err
	}
	*xs = v
	return nil
}
func ptr[T any](v T) *T { return &v }
func value[T any](p *T, fallback T) T {
	if p == nil {
		return fallback
	}
	return *p
}
func anyOf[T any](xs []T, f func(T) bool) bool {
	for _, x := range xs {
		if f(x) {
			return true
		}
	}
	return false
}
func all[T any](xs []T, f func(T) bool) bool {
	for _, x := range xs {
		if !f(x) {
			return false
		}
	}
	return true
}
func filter[T any](xs []T, f func(T) bool) List[T] {
	out := List[T]{}
	for _, x := range xs {
		if f(x) {
			out = append(out, x)
		}
	}
	return out
}
func mapped[A, B any](xs []A, f func(A) B) List[B] {
	out := make(List[B], 0, len(xs))
	for _, x := range xs {
		out = append(out, f(x))
	}
	return out
}
func find[T any](xs []T, f func(T) bool) *T {
	for _, x := range xs {
		if f(x) {
			return &x
		}
	}
	return nil
}
func contains[T comparable](xs []T, x T) bool { return anyOf(xs, func(y T) bool { return x == y }) }
func unique[T comparable](xs []T) bool {
	seen := map[T]bool{}
	for _, x := range xs {
		if seen[x] {
			return false
		}
		seen[x] = true
	}
	return true
}
func equal[T any](a, b T) bool { return compact(a) == compact(b) }

func jsonValue(data []byte) (any, error) {
	d := json.NewDecoder(bytes.NewReader(data))
	d.UseNumber()
	var v any
	if err := d.Decode(&v); err != nil {
		return nil, err
	}
	var extra any
	if err := d.Decode(&extra); err != io.EOF {
		return nil, fmt.Errorf("trailing JSON input")
	}
	return v, nil
}

// Lean's Json.compress spelling is also used inside logical identifiers.
func quote(s string) string {
	var b strings.Builder
	b.WriteByte('"')
	for _, r := range s {
		switch r {
		case '"', '\\':
			b.WriteByte('\\')
			b.WriteRune(r)
		case '\n':
			b.WriteString("\\n")
		case '\r':
			b.WriteString("\\r")
		default:
			if r < 32 {
				fmt.Fprintf(&b, "\\u%04x", r)
			} else {
				b.WriteRune(r)
			}
		}
	}
	b.WriteByte('"')
	return b.String()
}
func compactValue(v any) string {
	switch v := v.(type) {
	case nil:
		return "null"
	case bool:
		if v {
			return "true"
		}
		return "false"
	case string:
		return quote(v)
	case json.Number:
		return v.String()
	case []any:
		items := make([]string, len(v))
		for i, x := range v {
			items[i] = compactValue(x)
		}
		return "[" + strings.Join(items, ",") + "]"
	case map[string]any:
		keys := make([]string, 0, len(v))
		for k := range v {
			keys = append(keys, k)
		}
		sort.Strings(keys)
		items := make([]string, len(keys))
		for i, k := range keys {
			items[i] = quote(k) + ":" + compactValue(v[k])
		}
		return "{" + strings.Join(items, ",") + "}"
	default:
		panic(fmt.Sprintf("unexpected JSON value %T", v))
	}
}
func compact(v any) string {
	b, err := json.Marshal(v)
	if err != nil {
		panic(err)
	}
	j, err := jsonValue(b)
	if err != nil {
		panic(err)
	}
	return compactValue(j)
}
func numbersEqual(a, b json.Number) bool {
	x, xe := numberParts(a)
	y, ye := numberParts(b)
	return x.Cmp(y) == 0 && xe.Cmp(ye) == 0
}

// JsonNumber preserves decimal scale. 1e-0 is a Nat, but 1.0 is not.
func numberParts(n json.Number) (*big.Int, *big.Int) {
	parts := strings.SplitN(strings.ToLower(string(n)), "e", 2)
	exponent := new(big.Int)
	if len(parts) == 2 {
		exponent.SetString(strings.TrimPrefix(parts[1], "+"), 10)
	}
	s := parts[0]
	scale := new(big.Int)
	if pos := strings.IndexByte(s, '.'); pos >= 0 {
		scale.SetInt64(int64(len(s) - pos - 1))
		s = s[:pos] + s[pos+1:]
	}
	mantissa, _ := new(big.Int).SetString(s, 10)
	scale.Sub(scale, exponent)
	if scale.Sign() < 0 {
		power := new(big.Int).Exp(big.NewInt(10), new(big.Int).Neg(scale), nil)
		mantissa.Mul(mantissa, power)
		scale.SetInt64(0)
	}
	return mantissa, scale
}
func sameJSON(a, b any) bool {
	switch a := a.(type) {
	case json.Number:
		b, ok := b.(json.Number)
		return ok && numbersEqual(a, b)
	case []any:
		b, ok := b.([]any)
		if !ok || len(a) != len(b) {
			return false
		}
		for i := range a {
			if !sameJSON(a[i], b[i]) {
				return false
			}
		}
		return true
	case map[string]any:
		b, ok := b.(map[string]any)
		if !ok || len(a) != len(b) {
			return false
		}
		for k, x := range a {
			y, ok := b[k]
			if !ok || !sameJSON(x, y) {
				return false
			}
		}
		return true
	default:
		return reflect.DeepEqual(a, b)
	}
}
func sameValues(a, b any) bool {
	x, e := json.Marshal(a)
	if e != nil {
		return false
	}
	y, e := json.Marshal(b)
	if e != nil {
		return false
	}
	xj, e := jsonValue(x)
	if e != nil {
		return false
	}
	yj, e := jsonValue(y)
	return e == nil && sameJSON(xj, yj)
}
func decodeCanonical(data []byte, out any) error {
	j, err := jsonValue(data)
	if err != nil {
		return err
	}
	if err := json.Unmarshal(data, out); err != nil {
		return err
	}
	b, err := json.Marshal(out)
	if err != nil {
		return err
	}
	normalized, err := jsonValue(b)
	if err != nil {
		return err
	}
	if !sameJSON(j, normalized) {
		return fmt.Errorf("fields do not match the canonical schema")
	}
	return nil
}
