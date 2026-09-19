package main

import (
	"bufio"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"os"
	"strings"

	suimon "github.com/wim-web/suimon/go"
)

const usage = `suimon check <trace.jsonl> --graph <graph.json>
suimon explore --graph <graph.json> [--depth N] [--workers N] [--tick N] [--max-states N]
suimon gen [--graph <graph.json>] --seed S --count N [--workers N] [--tick N]
`

func options(args, allowed []string) (map[string]string, error) {
	out := map[string]string{}
	for len(args) >= 2 {
		key, val := args[0], args[1]
		valid := false
		for _, a := range allowed {
			valid = valid || a == key
		}
		if _, exists := out[key]; !valid || exists {
			return nil, fmt.Errorf("unknown or repeated option: %s", key)
		}
		out[key] = val
		args = args[2:]
	}
	if len(args) > 0 {
		return nil, fmt.Errorf("option requires a value")
	}
	return out, nil
}
func natOpt(opts map[string]string, key string, def suimon.Nat) (suimon.Nat, error) {
	s, ok := opts[key]
	if !ok {
		return def, nil
	}
	// Match Lean String.toNat?: a single underscore may separate digit runs.
	// Keep this CLI spelling separate from Nat's decimal and JSON codecs.
	var digits strings.Builder
	lastWasDigit := false
	for _, c := range s {
		switch {
		case c >= '0' && c <= '9':
			digits.WriteByte(byte(c))
			lastWasDigit = true
		case c == '_' && lastWasDigit:
			lastWasDigit = false
		default:
			return suimon.Nat{}, fmt.Errorf("invalid nonnegative integer for %s", key)
		}
	}
	if !lastWasDigit {
		return suimon.Nat{}, fmt.Errorf("invalid nonnegative integer for %s", key)
	}
	n, err := suimon.ParseNat(digits.String())
	if err != nil {
		return n, fmt.Errorf("invalid nonnegative integer for %s", key)
	}
	return n, nil
}
func config(opts map[string]string) (suimon.Config, error) {
	c := suimon.DefaultConfig()
	for _, p := range []struct {
		key string
		dst *suimon.Nat
	}{{"--depth", &c.Depth}, {"--workers", &c.Workers}, {"--tick", &c.Tick}, {"--max-states", &c.MaxStates}} {
		v, err := natOpt(opts, p.key, *p.dst)
		if err != nil {
			return c, err
		}
		*p.dst = v
	}
	if c.Workers.IsZero() || c.Tick.IsZero() || c.MaxStates.IsZero() {
		return c, fmt.Errorf("workers, tick and max-states must be positive")
	}
	return c, nil
}
func getGraph(opts map[string]string, defaultGraph bool) (suimon.Graph, error) {
	path, ok := opts["--graph"]
	if !ok {
		if defaultGraph {
			return suimon.Graph{Nodes: suimon.List[suimon.Node]{{ID: "work", Kind: suimon.NodeKind{Type: "leaf", Retry: suimon.RetryPolicy{MaxAttempts: suimon.N(2), LeaseSeconds: suimon.N(3), RetrySeconds: suimon.N(1)}, Concurrency: suimon.N(2)}, Inputs: suimon.List[suimon.Port]{{Name: "in", Kind: "plain"}}, Outputs: suimon.List[suimon.Port]{{Name: "out", Kind: "plain"}}}}, Entries: suimon.List[suimon.PortRef]{{Node: "work", Port: "in"}}, Exits: suimon.List[suimon.PortRef]{{Node: "work", Port: "out"}}}, nil
		}
		return suimon.Graph{}, fmt.Errorf("--graph is required")
	}
	b, err := os.ReadFile(path)
	if err != nil {
		return suimon.Graph{}, err
	}
	g, err := suimon.ParseGraph(b)
	if err != nil {
		return g, fmt.Errorf("invalid graph: %w", err)
	}
	return g, nil
}
func writeJSON(w io.Writer, v any) { _ = json.NewEncoder(w).Encode(v) }
func checkFile(g suimon.Graph, path string, stdout, stderr io.Writer) (int, error) {
	f, err := os.Open(path)
	if err != nil {
		return 2, err
	}
	defer f.Close()
	r := bufio.NewReader(f)
	c := suimon.NewCursor(g)
	for {
		line, err := r.ReadString('\n')
		if err != nil && !errors.Is(err, io.EOF) {
			return 2, err
		}
		if line != "" {
			next, d := suimon.CheckTextLine(c, line)
			if d != nil {
				writeJSON(stderr, d)
				return 1, nil
			}
			c = next
		}
		if err == io.EOF {
			break
		}
	}
	s, d := suimon.Finish(c)
	if d != nil {
		writeJSON(stderr, d)
		return 1, nil
	}
	writeJSON(stdout, map[string]any{"valid": true, "events": c.Sequence.Sub(suimon.N(1)), "status": s.Status, "transactions": len(c.Completed)})
	return 0, nil
}
func run(args []string, stdout, stderr io.Writer) (int, error) {
	if len(args) == 1 && (args[0] == "help" || args[0] == "--help") {
		fmt.Fprint(stdout, usage)
		return 0, nil
	}
	if len(args) == 0 {
		fmt.Fprint(stderr, usage)
		return 2, nil
	}
	switch args[0] {
	case "check":
		if len(args) < 2 {
			fmt.Fprint(stderr, usage)
			return 2, nil
		}
		opts, err := options(args[2:], []string{"--graph"})
		if err != nil {
			return 2, err
		}
		g, err := getGraph(opts, false)
		if err != nil {
			return 2, err
		}
		return checkFile(g, args[1], stdout, stderr)
	case "explore", "gen":
		allowed := []string{"--graph", "--depth", "--workers", "--tick", "--max-states"}
		if args[0] == "gen" {
			allowed = []string{"--graph", "--seed", "--count", "--workers", "--tick"}
		}
		opts, err := options(args[1:], allowed)
		if err != nil {
			return 2, err
		}
		g, err := getGraph(opts, args[0] == "gen")
		if err != nil {
			return 2, err
		}
		if args[0] == "explore" {
			cfg, err := config(opts)
			if err != nil {
				return 2, err
			}
			report := suimon.Search(g, cfg)
			writeJSON(stdout, report)
			if report.Failure != nil || !report.Complete {
				return 1, nil
			}
			return 0, nil
		}
		seed, err := natOpt(opts, "--seed", suimon.N(1))
		if err != nil {
			return 2, err
		}
		count, err := natOpt(opts, "--count", suimon.N(20))
		if err != nil {
			return 2, err
		}
		cfg, err := config(opts)
		if err != nil {
			return 2, err
		}
		_, events, reject := suimon.Generate(g, cfg, seed, count)
		if reject != nil {
			writeJSON(stderr, reject)
			return 1, nil
		}
		for _, e := range events {
			fmt.Fprintln(stdout, suimon.EncodeEvent(e))
		}
		return 0, nil
	default:
		fmt.Fprint(stderr, usage)
		return 2, nil
	}
}
func main() {
	code, err := run(os.Args[1:], os.Stdout, os.Stderr)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
	}
	os.Exit(code)
}
