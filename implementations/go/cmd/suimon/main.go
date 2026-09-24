// Command suimon mirrors the Lean CLI (Main.lean at the repository root): it validates definitions,
// checks execution records, explores random walks and generates records, with the same arguments,
// output and exit codes.
package main

import (
	"bufio"
	"errors"
	"fmt"
	"io"
	"io/fs"
	"os"
	"slices"
	"sort"
	"strings"
	"syscall"
	"unicode/utf8"

	suimon "github.com/wim-web/suimon/implementations/go/src"
)

const usage = "suimon validate <definition.json>\n" +
	"suimon check <trace.jsonl> [--state]\n" +
	"suimon explore <definition.json> [--seeds N] [--steps N]\n" +
	"suimon gen <definition.json> [--seed N] [--steps N]\n"

func main() {
	os.Exit(run(os.Args[1:], os.Stdout, os.Stderr))
}

// run executes the CLI and returns its exit code: 0 on success, 1 when the command fails, and 2
// for invalid arguments.
func run(args []string, stdout, stderr io.Writer) int {
	out := bufio.NewWriter(stdout)
	defer out.Flush()
	command := func(allowed, flags []string, action func([]option) error) int {
		opts, err := options(args[2:], allowed, flags)
		if err != nil {
			fmt.Fprintln(stderr, err)
			return 2
		}
		if err := action(opts); err != nil {
			out.Flush()
			fmt.Fprintln(stderr, err)
			return 1
		}
		return 0
	}
	switch {
	case len(args) == 1 && (args[0] == "--help" || args[0] == "help"):
		fmt.Fprint(out, usage)
		return 0
	case len(args) == 2 && args[0] == "validate":
		return command(nil, nil, func([]option) error { return validate(out, args[1]) })
	case len(args) >= 2 && args[0] == "check":
		return command(nil, []string{"--state"}, func(opts []option) error { return check(out, args[1], opts) })
	case len(args) >= 2 && args[0] == "explore":
		return command([]string{"--seeds", "--steps"}, nil, func(opts []option) error { return explore(out, args[1], opts) })
	case len(args) >= 2 && args[0] == "gen":
		return command([]string{"--seed", "--steps"}, nil, func(opts []option) error { return gen(out, args[1], opts) })
	}
	fmt.Fprint(stderr, usage)
	return 2
}

type option struct{ key, value string }

// options reads options from the front, like Main.lean: a flag stands alone and has the value "",
// any other option takes the next argument as its value.
func options(args, allowed, flags []string) ([]option, error) {
	var opts []option
	for len(args) > 0 {
		key := args[0]
		switch {
		case slices.Contains(flags, key):
			opts = append(opts, option{key, ""})
			args = args[1:]
		case len(args) == 1:
			return nil, fmt.Errorf("missing value for %s", key)
		case !slices.Contains(allowed, key):
			return nil, fmt.Errorf("unknown option %s", key)
		default:
			opts = append(opts, option{key, args[1]})
			args = args[2:]
		}
	}
	return opts, nil
}

// lookup is the value of the first option named key.
func lookup(opts []option, key string) (string, bool) {
	for _, o := range opts {
		if o.key == key {
			return o.value, true
		}
	}
	return "", false
}

// natDigits accepts what Lean's String.toNat? accepts: decimal digits, with single underscores
// between them, and returns the digits.
func natDigits(text string) (string, bool) {
	var digits strings.Builder
	lastWasDigit := false
	for _, c := range text {
		switch {
		case c == '_' && lastWasDigit:
			lastWasDigit = false
		case '0' <= c && c <= '9':
			digits.WriteRune(c)
			lastWasDigit = true
		default:
			return "", false
		}
	}
	return digits.String(), lastWasDigit
}

// natOption reads a natural number option with a default, reduced by reduce as the digits are
// read, so that numbers of any length fit.
func natOption(opts []option, key string, def uint64, reduce func(uint64) uint64) (uint64, error) {
	text, ok := lookup(opts, key)
	if !ok {
		return def, nil
	}
	digits, ok := natDigits(text)
	if !ok {
		return 0, fmt.Errorf("%s expects a natural number", key)
	}
	var n uint64
	for _, d := range digits {
		n = reduce(n*10 + uint64(d-'0'))
	}
	return n, nil
}

// clampCount bounds a count at 2^40, which no walk or loop reaches.
func clampCount(n uint64) uint64 { return min(n, 1<<40) }

// seedModulus keeps a seed modulo 2^32, which is all that suimon.NextSeed uses of it.
func seedModulus(n uint64) uint64 { return n % (1 << 32) }

// readFile reads a file and reports errors as Lean's IO.FS.readFile does.
func readFile(path string) ([]byte, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		return nil, leanIOError(path, err)
	}
	return data, nil
}

// leanIOError words the common errors of reading a file as Lean's IO.Error does.
func leanIOError(path string, err error) error {
	var errno syscall.Errno
	if !errors.As(err, &errno) {
		return err
	}
	switch {
	case errors.Is(err, fs.ErrNotExist):
		return fmt.Errorf("no such file or directory (error code: %d)\n  file: %s", int(errno), path)
	case errors.Is(err, fs.ErrPermission):
		return fmt.Errorf("permission denied (error code: %d)\n  file: %s", int(errno), path)
	case errno == syscall.EISDIR:
		return fmt.Errorf("inappropriate type (error code: %d, illegal operation on a directory)", int(errno))
	}
	return err
}

// nonUTF8 is the error of Lean's IO.FS.readFile for a file that is not UTF-8, word for word.
func nonUTF8(path string) error {
	return fmt.Errorf("Tried to read file '%s' containing non UTF-8 data.", path)
}

// readDefinition reads, decodes and validates a definition.
func readDefinition(path string) (*suimon.Definition, error) {
	data, err := readFile(path)
	if err != nil {
		return nil, err
	}
	if !utf8.Valid(data) {
		return nil, nonUTF8(path)
	}
	return loadDefinition(data)
}

// loadDefinition decodes and validates a definition, from a file or from the header of a record.
func loadDefinition(data []byte) (*suimon.Definition, error) {
	p, err := suimon.ParseDefinition(data)
	if err != nil {
		return nil, err
	}
	if err := p.Validate(); err != nil {
		return nil, err
	}
	return p, nil
}

func validate(out io.Writer, path string) error {
	if _, err := readDefinition(path); err != nil {
		return err
	}
	fmt.Fprintln(out, "ok")
	return nil
}

// check replays a record against the definition of its header, which is read like a definition
// file. Like Lean, a file that is not UTF-8 is rejected, except that a partial last line may end
// inside a character: a crash can cut the file there, and recovery discards it.
func check(out io.Writer, trace string, opts []option) error {
	data, err := readFile(trace)
	if err != nil {
		return err
	}
	text := string(data)
	if !utf8.ValidString(text[:strings.LastIndexByte(text, '\n')+1]) {
		return nonUTF8(trace)
	}
	checked, err := suimon.Check(text, loadDefinition)
	if err != nil {
		return err
	}
	if _, ok := lookup(opts, "--state"); ok {
		// The whole state, for comparing another implementation's state with Lean's.
		state, err := checked.State.MarshalJSON()
		if err != nil {
			return err
		}
		fmt.Fprintf(out, "%s\n", state)
		return nil
	}
	fmt.Fprintf(out, `{"committed":%d,"status":"%s","uncommitted":%t}`+"\n", checked.Committed,
		checked.State.Status, checked.Uncommitted)
	return nil
}

func explore(out io.Writer, path string, opts []option) error {
	p, err := readDefinition(path)
	if err != nil {
		return err
	}
	seeds, err := natOption(opts, "--seeds", 100, clampCount)
	if err != nil {
		return err
	}
	steps, err := natOption(opts, "--steps", 10000, clampCount)
	if err != nil {
		return err
	}
	counts := map[string]int{}
	for seed := uint64(0); seed < seeds; seed++ {
		s, _ := suimon.Walk(p, suimon.DefaultConfig(), seed+1, int(steps))
		if !s.Status.Terminal() {
			return fmt.Errorf("seed %d: no accepted operation in status %s", seed+1, s.Status)
		}
		counts[s.Status.String()]++
	}
	names := make([]string, 0, len(counts))
	for name := range counts {
		names = append(names, name)
	}
	sort.Strings(names)
	fields := make([]string, len(names))
	for i, name := range names {
		fields[i] = fmt.Sprintf(`"%s":%d`, name, counts[name])
	}
	fmt.Fprintf(out, "{%s}\n", strings.Join(fields, ","))
	return nil
}

// gen writes a random walk as an execution record: the header with the definition, then the records.
// Payloads repeat the value identities.
func gen(out io.Writer, path string, opts []option) error {
	p, err := readDefinition(path)
	if err != nil {
		return err
	}
	seed, err := natOption(opts, "--seed", 1, seedModulus)
	if err != nil {
		return err
	}
	steps, err := natOption(opts, "--steps", 10000, clampCount)
	if err != nil {
		return err
	}
	_, ops := suimon.Walk(p, suimon.DefaultConfig(), seed, int(steps))
	if _, err := io.WriteString(out, suimon.EncodeHeader(p)+"\n"); err != nil {
		return err
	}
	recorder := suimon.NewRecorder(p)
	for _, op := range ops {
		needs, err := recorder.Needs(op)
		if err != nil {
			return err
		}
		values := make([]suimon.Payload, len(needs))
		for i, v := range needs {
			values[i] = suimon.Payload{Value: v, Payload: v}
		}
		records, err := recorder.Record(op, values)
		if err != nil {
			return err
		}
		if _, err := io.WriteString(out, suimon.RecordsText(records)); err != nil {
			return err
		}
	}
	return nil
}
