import Suimon.Trace.Check
import Std.Data.HashSet
namespace Suimon.Explore
open Lean

structure Failure where
  reason : String
  trace : List Op
  state : Json
  deriving ToJson
structure Report where
  states : Nat
  transitions : Nat
  depth : Nat
  complete : Bool
  failure : Option Failure := none
  deriving ToJson
structure SearchState where
  state : State
  trace : List Op

/-- Invariant guard rejections are counterexamples too; they are never silently discarded. --/
def search (g : Graph) (cfg : Config) : Report := Id.run do
  let initial := State.initial g
  let mut visited : Std.HashSet String := ({} : Std.HashSet String).insert (toJson initial).compress
  let mut frontier := [{ state := initial, trace := [] : SearchState }]
  let mut transitions := 0
  for depth in List.range cfg.depth do
    let mut nextFrontier := []
    for current in frontier do
      for op in candidates cfg current.state do
        match step current.state op with
        | .error r =>
          if r.code == "INVARIANT" then
            return { states := visited.size, transitions, depth, complete := false, failure := some { reason := r.message, trace := current.trace ++ [op], state := toJson current.state } }
        | .ok next =>
          transitions := transitions + 1
          let key := (toJson next).compress
          if !visited.contains key then
            if visited.size ≥ cfg.maxStates then
              return { states := visited.size, transitions, depth, complete := false }
            visited := visited.insert key
            nextFrontier := { state := next, trace := current.trace ++ [op] } :: nextFrontier
    frontier := nextFrontier.reverse
  return { states := visited.size, transitions, depth := cfg.depth, complete := true }

/-- Reproducible random walk, with a fixed portable generator. --/
def nextSeed (seed : Nat) : Nat := (1664525 * seed + 1013904223) % 4294967296

def generate (g : Graph) (cfg : Config) (seed count : Nat) : Result (State × List Trace.Event) := do
  let mut state := State.initial g
  let mut seed := seed
  let mut events := []
  for idx in List.range count do
    let mut choices := []
    for op in candidates cfg state do
      match step state op with
      | .ok next => if next != state then choices := choices ++ [op]
      | .error r => if r.code == "INVARIANT" then throw r
    if choices.isEmpty then break
    seed := nextSeed seed
    let op := choices[seed % choices.length]?.getD .idle
    let (next, records) ← Trace.recordTransaction state [op] (events.length + 1) (s!"txn-{idx + 1}") state.now
    events := events ++ records
    state := next
  return (state, events)
end Suimon.Explore
