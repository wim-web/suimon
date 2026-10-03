package main

import (
	"encoding/json"
	"fmt"
	"strings"
	"testing"

	suimon "github.com/wim-web/suimon/implementations/go/src"
)

// Both CLIs receive the same adversarial text, including the validated and
// unchecked headers used by check. This catches limit and error-order drift.
func TestConformanceResourceLimits(t *testing.T) {
	lean := leanCLI(t)
	base := func() *suimon.Definition {
		return &suimon.Definition{Main: "w", Functions: []suimon.FunctionDecl{{ID: "f", Output: suimon.Contract{Kind: suimon.KindSingle, Type: suimon.Named("T")}}},
			Workflows: []suimon.Workflow{{ID: "w", Placements: []suimon.Placement{{Name: "p", Policy: suimon.PolicyStop, Control: suimon.CallControl{Body: suimon.FunctionBody("f")}}}}}}
	}
	cases := map[string]func(*suimon.Definition){
		"workflows": func(p *suimon.Definition) {
			for range suimon.MaxDefinitionWorkflows {
				p.Workflows = append(p.Workflows, p.Workflows[0])
			}
		},
		"declarations": func(p *suimon.Definition) {
			for range suimon.MaxDefinitionDeclarations {
				p.Functions = append(p.Functions, p.Functions[0])
			}
		},
		"placements": func(p *suimon.Definition) {
			w := &p.Workflows[0]
			for range suimon.MaxDefinitionPlacements {
				w.Placements = append(w.Placements, w.Placements[0])
			}
		},
		"connections": func(p *suimon.Definition) {
			w := &p.Workflows[0]
			for range suimon.MaxDefinitionConnections + 1 {
				w.Connections = append(w.Connections, suimon.Connection{Source: "p", Target: "p", Transform: suimon.Discard})
			}
		},
		"tasks": func(p *suimon.Definition) {
			tasks := make([]suimon.TaskSpec, suimon.MaxDefinitionTasks+1)
			for i := range tasks {
				tasks[i] = suimon.TaskSpec{Name: "t", Body: suimon.FunctionBody("f"), Policy: suimon.PolicyStop}
			}
			p.Workflows[0].Placements[0].Control = suimon.ConcurrencyControl{Spec: suimon.Concurrency{Limit: 1, Tasks: tasks, Element: suimon.Named("T")}}
		},
		"arms": func(p *suimon.Definition) {
			arms := make([]string, suimon.MaxDefinitionArms+1)
			for i := range arms {
				arms[i] = "a"
			}
			p.Workflows[0].Placements[0].Control = suimon.BranchControl{Judge: "j", Arms: arms}
		},
		"name":                   func(p *suimon.Definition) { p.Main = strings.Repeat("あ", 86) },
		"name without workflows": func(p *suimon.Definition) { p.Main = strings.Repeat("あ", 86); p.Workflows = nil },
		"type without workflows": func(p *suimon.Definition) {
			p.Functions[0].Output.Type.Lists = suimon.MaxDefinitionTypeDepth + 1
			p.Workflows = nil
		},
		"type": func(p *suimon.Definition) { p.Functions[0].Output.Type.Lists = suimon.MaxDefinitionTypeDepth + 1 },
	}
	for _, shape := range []string{"line", "fan-in", "dense"} {
		cases[shape] = func(p *suimon.Definition) {
			n := 150
			if shape == "dense" {
				n = 64
			}
			w := &p.Workflows[0]
			pl := w.Placements[0]
			w.Placements = nil
			for i := 0; i < n; i++ {
				pl.Name = fmt.Sprint(i)
				w.Placements = append(w.Placements, pl)
			}
			for i := 0; i < n; i++ {
				for j := i + 1; j < n; j++ {
					if shape == "dense" || (shape == "line" && j == i+1) || (shape == "fan-in" && j == n-1) {
						w.Connections = append(w.Connections, suimon.Connection{Source: fmt.Sprint(i), Target: fmt.Sprint(j), Transform: suimon.Discard})
					}
				}
			}
		}
	}
	for name, edit := range cases {
		t.Run(name, func(t *testing.T) {
			p := base()
			edit(p)
			data, err := json.Marshal(p)
			if err != nil {
				t.Fatal(err)
			}
			path := writeTemp(t, name+".json", string(data))
			got := cli(t, 1, "validate", path)
			if !strings.Contains(got.stderr, "limit exceeded") {
				t.Fatalf("expected resource rejection: %s", got.stderr)
			}
			sameResult(t, name, runLean(t, lean, "validate", path), got)
			for _, validated := range []bool{true, false} {
				header := fmt.Sprintf("{\"definition\":%s,\"validated\":%t}\n", data, validated)
				path := writeTemp(t, name+".jsonl", header)
				sameResult(t, name+" header", runLean(t, lean, "check", path), cli(t, 1, "check", path))
			}
		})
	}
	for name, data := range map[string]string{
		"bytes":   strings.Repeat(" ", suimon.MaxDefinitionBytes+1),
		"nesting": strings.Repeat("[", suimon.MaxDefinitionJSONDepth+1),
	} {
		t.Run(name, func(t *testing.T) {
			path := writeTemp(t, name+".json", data)
			sameResult(t, name, runLean(t, lean, "validate", path), cli(t, 1, "validate", path))
		})
	}
}
