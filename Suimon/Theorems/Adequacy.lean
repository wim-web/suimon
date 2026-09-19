import Suimon.Theorems.ChannelAssembly

namespace Suimon
open Semantics

theorem child_graph_smaller (g : Graph) (n : Node) (memberN : n ∈ g.nodes) (body : Graph)
    (kind : n.kind = .subworkflow body ∨ n.kind = .forEach body ∨ ∃ limit, n.kind = .loop body limit) :
    sizeOf body < sizeOf g := by
  have smaller := List.sizeOf_lt_of_mem memberN
  rcases kind with sub | each | ⟨limit, loop⟩ <;> cases g <;> cases n <;> simp_all <;> omega

/-- Operational adequacy for any validated nested DAG. Each node equation is
    obtained from accepted transitions; recursive calls descend into a strictly
    smaller body graph. No scheduler bound or final-output agreement is assumed. --/
theorem frame_adequacy (oracle : ScopedOracle) (g : Graph) : FrameAdequacy oracle g := by
  intro start last ops P inputs fs ancestors run complete finished
  let values := frameValues oracle last g P
  have sc := fs.scope.persist run
  obtain ⟨isBody, valid⟩ := fs.scope.valid
  obtain ⟨topology⟩ := topology_of_validate g isBody valid
  have nodes : ∀ n ∈ g.nodes, NodeEval oracle g P n (inputData g inputs values n) (values n.id) := by
    intro n memberN
    have children : ∀ body, (n.kind = .subworkflow body ∨ n.kind = .forEach body ∨ ∃ limit, n.kind = .loop body limit) →
        FrameAdequacy oracle body := by
      intro body kind
      exact frame_adequacy oracle body
    have evaluated := completed_node_eval oracle fs ancestors run complete finished n memberN children
    have inputsEq := frame_input_equations oracle run fs finished n memberN
    simpa only [values, inputsEq, frameValues_node oracle sc n memberN] using evaluated
  have result : assemble g P inputs values = observedResult last P g := by
    have outputs := frame_exit_equations oracle run fs finished
    have channels := frame_channels_equations oracle fs ancestors run complete finished
    cases assembled : assemble g P inputs values with
    | mk out chans =>
      change (assemble g P inputs values).outputs = _ at outputs
      change (assemble g P inputs values).channels = _ at channels
      rw [assembled] at outputs channels
      simp only [Semantics.Result.outputs, Semantics.Result.channels] at outputs channels
      simp only [observedResult, outputs, channels]
  rw [← result]
  exact GraphEval.graph topology nodes
termination_by sizeOf g
decreasing_by exact child_graph_smaller g n memberN body kind

/-- T9: all channels, including nested frame entries and exits, have the same
    item multisets in any two successful drained executions conforming to the
    same scoped oracle. Retries and lease expiry remain ordinary run steps. --/
theorem schedule_determinism : ScheduleDeterminism :=
  schedule_determinism_of_adequacy frame_adequacy

end Suimon
