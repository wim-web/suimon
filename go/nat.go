package suimon

import (
	"bytes"
	"encoding/json"
	"fmt"
	"math/big"
	"strconv"
)

// Nat is an immutable, arbitrary precision natural number, matching Lean Nat.
// Its zero value is zero. Use N or ParseNat to construct a value.
type Nat struct{ digits string }

func N(n uint64) Nat {
	if n == 0 {
		return Nat{}
	}
	return Nat{strconv.FormatUint(n, 10)}
}
func natLen[T any](xs []T) Nat { return N(uint64(len(xs))) }
func ParseNat(s string) (Nat, error) {
	if s == "" {
		return Nat{}, fmt.Errorf("empty natural number")
	}
	for _, c := range s {
		if c < '0' || c > '9' {
			return Nat{}, fmt.Errorf("invalid natural number: %s", s)
		}
	}
	n, ok := new(big.Int).SetString(s, 10)
	if !ok {
		return Nat{}, fmt.Errorf("invalid natural number")
	}
	return fromBig(n), nil
}
func fromBig(n *big.Int) Nat {
	if n.Sign() <= 0 {
		return Nat{}
	}
	return Nat{n.String()}
}
func (n Nat) String() string {
	if n.digits == "" {
		return "0"
	}
	return n.digits
}
func (n Nat) big() *big.Int { v, _ := new(big.Int).SetString(n.String(), 10); return v }
func (n Nat) Cmp(m Nat) int {
	a, b := n.String(), m.String()
	if len(a) < len(b) {
		return -1
	}
	if len(a) > len(b) {
		return 1
	}
	if a < b {
		return -1
	}
	if a > b {
		return 1
	}
	return 0
}
func (n Nat) Add(m Nat) Nat { return fromBig(new(big.Int).Add(n.big(), m.big())) }
func (n Nat) Sub(m Nat) Nat { return fromBig(new(big.Int).Sub(n.big(), m.big())) }
func (n Nat) Mul(m Nat) Nat { return fromBig(new(big.Int).Mul(n.big(), m.big())) }
func (n Nat) Inc() Nat      { return n.Add(N(1)) }
func (n Nat) IsZero() bool  { return n.digits == "" }
func maxNat(a, b Nat) Nat {
	if a.Cmp(b) >= 0 {
		return a
	}
	return b
}
func (n Nat) mod(m Nat) Nat { return fromBig(new(big.Int).Mod(n.big(), m.big())) }
func (n Nat) index(limit int) int {
	if n.Cmp(N(uint64(limit))) >= 0 {
		return limit
	}
	v, _ := strconv.Atoi(n.String())
	return v
}
func (n Nat) MarshalJSON() ([]byte, error) { return []byte(n.String()), nil }
func (n *Nat) UnmarshalJSON(data []byte) error {
	data = bytes.TrimSpace(data)
	if !json.Valid(data) || len(data) == 0 || (data[0] != '-' && (data[0] < '0' || data[0] > '9')) {
		return fmt.Errorf("expected a natural number")
	}
	mantissa, scale := numberParts(json.Number(data))
	if mantissa.Sign() < 0 || scale.Sign() != 0 {
		return fmt.Errorf("expected a natural number")
	}
	*n = fromBig(mantissa)
	return nil
}
