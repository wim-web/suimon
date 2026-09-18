import Suimon.Trace.Check
namespace Suimon.Test

-- User-facing names follow design §3; constructor and fixture IDs follow §4.
-- Concurrency uses fan-out + waitAll; Sub uses subworkflow.
-- A yielding node is a leaf with stream outputs; AllWait uses collect.

def plain (name : String) : Port := ⟨name, .plain⟩
def stream (name : String) : Port := ⟨name, .stream⟩
def ref (node port : String) : PortRef := ⟨node, port⟩
def edge (a ap b bp : String) : Edge := ⟨ref a ap, ref b bp⟩
def leaf (id : String) (inputs outputs : List String) : Node :=
  { id, kind := .leaf { maxAttempts := 2, leaseSeconds := 3, retrySeconds := 1 } 2, inputs := inputs.map plain, outputs := outputs.map plain }
def emitter (id : String) : Node :=
  { leaf id ["in"] [] with outputs := [stream "out"] }
def body : Graph :=
  { nodes := [leaf "work" ["in"] ["out"]], edges := [], entries := [ref "work" "in"], exits := [ref "work" "out"] }
def minimal : Graph := body

def diamond : Graph := {
  nodes := [leaf "a" ["in"] ["out"], leaf "b" ["in"] ["out"], leaf "c" ["in"] ["out"], { id := "join", kind := .waitAll, inputs := [plain "b", plain "c"], outputs := [plain "out"] }]
  edges := [edge "a" "out" "b" "in", edge "a" "out" "c" "in", edge "b" "out" "join" "b", edge "c" "out" "join" "c"]
  entries := [ref "a" "in"]
  exits := [ref "join" "out"] }

def nShape : Graph := {
  nodes := [leaf "a" ["in"] ["out"], leaf "b" ["in"] ["out"], leaf "c" ["a", "b"] ["out"]]
  edges := [edge "a" "out" "b" "in", edge "a" "out" "c" "a", edge "b" "out" "c" "b"]
  entries := [ref "a" "in"]
  exits := [ref "c" "out"] }

def branch : Graph := {
  nodes := [{ id := "choose", kind := .branch ["left", "right"], inputs := [plain "in"], outputs := [plain "left", plain "right"] }, leaf "left" ["in"] ["out"], leaf "right" ["in"] ["out"]]
  edges := [edge "choose" "left" "left" "in", edge "choose" "right" "right" "in"]
  entries := [ref "choose" "in"]
  exits := [ref "left" "out", ref "right" "out"] }

def loop : Graph := {
  nodes := [{ id := "loop", kind := .loop body 2, inputs := [plain "in"], outputs := [plain "out"] }]
  edges := []
  entries := [ref "loop" "in"]
  exits := [ref "loop" "out"] }

def streaming : Graph := {
  nodes := [emitter "emit", { id := "each", kind := .forEach body, inputs := [stream "in"], outputs := [stream "out"] }, { id := "collect", kind := .collect, inputs := [stream "in"], outputs := [plain "out"] }]
  edges := [edge "emit" "out" "each" "in", edge "each" "out" "collect" "in"]
  entries := [ref "emit" "in"]
  exits := [ref "collect" "out"] }

def merging : Graph := {
  nodes := [emitter "a", emitter "b", { id := "merge", kind := .merge, inputs := [stream "a", stream "b"], outputs := [stream "out"] }, { id := "collect", kind := .collect, inputs := [stream "in"], outputs := [plain "out"] }]
  edges := [edge "a" "out" "merge" "a", edge "b" "out" "merge" "b", edge "merge" "out" "collect" "in"]
  entries := [ref "a" "in", ref "b" "in"]
  exits := [ref "collect" "out"] }

def filtering : Graph := {
  nodes := [emitter "emit", { id := "filter", kind := .filter, inputs := [stream "in"], outputs := [stream "out"] }, { id := "collect", kind := .collect, inputs := [stream "in"], outputs := [plain "out"] }]
  edges := [edge "emit" "out" "filter" "in", edge "filter" "out" "collect" "in"]
  entries := [ref "emit" "in"]
  exits := [ref "collect" "out"] }

def nested : Graph := {
  nodes := [{ id := "sub", kind := .subworkflow loop, inputs := [plain "in"], outputs := [plain "out"] }]
  edges := []
  entries := [ref "sub" "in"]
  exits := [ref "sub" "out"] }

def coalescedBranch : Graph := {
  nodes := branch.nodes ++ [{ id := "join", kind := .coalesce, inputs := [plain "left", plain "right"], outputs := [plain "out"] }]
  edges := branch.edges ++ [edge "left" "out" "join" "left", edge "right" "out" "join" "right"]
  entries := branch.entries
  exits := [ref "join" "out"] }

/-- A Sub containing a Loop whose body rejoins both Branch arms through Coalesce. --/
def coalesceLoop : Graph :=
  let loopGraph : Graph := { loop with nodes := loop.nodes.map fun n => { n with kind := .loop coalescedBranch 2 } }
  { nested with nodes := nested.nodes.map fun n => { n with kind := .subworkflow loopGraph } }

def independentCoalesce : Graph := {
  nodes := [leaf "a" ["in"] ["out"], leaf "b" ["in"] ["out"],
    { id := "join", kind := .coalesce, inputs := [plain "a", plain "b"], outputs := [plain "out"] }]
  edges := [edge "a" "out" "join" "a", edge "b" "out" "join" "b"]
  entries := [ref "a" "in", ref "b" "in"]
  exits := [ref "join" "out"] }

def sharedCoalesce : Graph := {
  coalescedBranch with
  nodes := coalescedBranch.nodes.map (fun n =>
    if n.id == "left" || n.id == "right" then { n with inputs := [plain "in", plain "context"] } else n) ++
    [leaf "context" ["in"] ["out"]]
  edges := coalescedBranch.edges ++ [edge "context" "out" "left" "context", edge "context" "out" "right" "context"]
  entries := coalescedBranch.entries ++ [ref "context" "in"] }

def nestedCoalesce : Graph := {
  coalescedBranch with
  nodes := coalescedBranch.nodes.map (fun n =>
    if n.id == "left" then { n with kind := .branch ["up", "down"], outputs := [plain "up", plain "down"] } else n) ++
    [leaf "up" ["in"] ["out"], leaf "down" ["in"] ["out"],
      { id := "innerJoin", kind := .coalesce, inputs := [plain "up", plain "down"], outputs := [plain "out"] }]
  edges := coalescedBranch.edges.filter (·.src.node != "left") ++
    [edge "left" "up" "up" "in", edge "left" "down" "down" "in",
      edge "up" "out" "innerJoin" "up", edge "down" "out" "innerJoin" "down", edge "innerJoin" "out" "join" "left"] }

/-- Two successive exclusive joins; both stages finish within the depth-eight search. --/
def stagedCoalesce : Graph := {
  nodes := [
    { id := "firstChoice", kind := .branch ["left", "right"], inputs := [plain "in"], outputs := [plain "left", plain "right"] },
    { id := "firstJoin", kind := .coalesce, inputs := [plain "left", plain "right"], outputs := [plain "out"] },
    { id := "secondChoice", kind := .branch ["left", "right"], inputs := [plain "in"], outputs := [plain "left", plain "right"] },
    { id := "secondJoin", kind := .coalesce, inputs := [plain "left", plain "right"], outputs := [plain "out"] }]
  edges := [edge "firstChoice" "left" "firstJoin" "left", edge "firstChoice" "right" "firstJoin" "right",
    edge "firstJoin" "out" "secondChoice" "in", edge "secondChoice" "left" "secondJoin" "left", edge "secondChoice" "right" "secondJoin" "right"]
  entries := [ref "firstChoice" "in"]
  exits := [ref "secondJoin" "out"] }

def examples : List (String × Graph) := [
  ("minimal", minimal), ("diamond", diamond), ("n-shape", nShape), ("branch", branch), ("loop", loop), ("streaming", streaming), ("merge", merging), ("filter", filtering), ("nested", nested), ("coalesce", coalescedBranch), ("coalesce-loop", coalesceLoop), ("coalesce-stages", stagedCoalesce)]
end Suimon.Test
