import Suimon.Theorems.Start

namespace Suimon
open Semantics

/-- A frame-completion boundary in an actual execution. Child calls supply the
    boundary checked by bodyResults; the root supplies its successful idle. --/
def FrameCompletes (oracle : ScopedOracle) (start last : State) (P : Path) (g : Graph) : Prop :=
  ∃ before pre post f,
    ConformingSteps (fun s op => oracleConforms oracle s op = true) start pre before ∧
    ConformingSteps (fun s op => oracleConforms oracle s op = true) before post last ∧
    f ∈ before.frames ∧ f.path = P ∧ f.graph = g ∧ frameDone before f = true

theorem FrameCompletes.nodes {oracle : ScopedOracle} {start last : State} {P : Path} {g : Graph}
    (complete : FrameCompletes oracle start last P g) (safe : Invariants start) :
    ∀ n ∈ g.nodes, ∃ i ∈ last.instances, i.path = P ∧ i.node = n.id ∧ i.trigger = none ∧
      (i.status = .succeeded ∨ i.status = .cancelled) := by
  obtain ⟨before, pre, post, f, head, tail, _, pathF, graphF, done⟩ := complete
  have safeBefore := head.invariants safe
  simp only [frameDone, Bool.and_eq_true] at done
  intro n memberN
  have ready := List.all_eq_true.mp done.2 n (by simpa only [graphF] using memberN)
  obtain ⟨i, found, status⟩ := (Option.any_eq_true _ _).mp ready
  obtain ⟨memberI, pathI, nodeI, triggerI⟩ := nodeInstance?_mem found
  have terminal : i.status = .succeeded ∨ i.status = .cancelled := by simpa using status
  obtain ⟨j, memberJ, idJ, statusJ⟩ := tail.retains_status safeBefore i memberI terminal
  obtain ⟨nodeJ, pathJ, triggerJ, _⟩ := tail.input_snapshot safeBefore i j memberI memberJ idJ.symm
  exact ⟨j, memberJ, pathJ.trans (pathI.trans pathF), nodeJ.trans nodeI, triggerJ.trans triggerI,
    by rw [statusJ]; exact terminal⟩

theorem FrameCompletes.root (oracle : ScopedOracle) {start last : State} {ops : List Op} {g : Graph} {inputs : List Input}
    (fs : FrameStart start [] g inputs)
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) start ops last)
    (notFinished : start.status ≠ .succeeded) (finished : last.status = .succeeded) :
    FrameCompletes oracle start last [] g := by
  obtain ⟨pre, post, before, f, _, head, accepted, _, _, found, done⟩ := run.completion notFinished finished
  have scopeBefore := fs.scope.persist head
  obtain ⟨known, foundKnown, pathKnown, graphKnown⟩ := scopeBefore.frame?
  rw [foundKnown] at found
  have same := Option.some.inj found
  subst f
  have allowed : oracleConforms oracle before .idle = true := by unfold oracleConforms; split <;> rfl
  exact ⟨before, pre, [.idle], known, head, .cons allowed accepted (.nil last), List.mem_of_find?_eq_some foundKnown,
    pathKnown, graphKnown, done⟩

def observedResult (s : State) (P : Path) (g : Graph) : Semantics.Result :=
  {outputs := exitItems s P g, channels := subtreeBags s P}

/-- The local operational-to-denotational statement required for assembling
    nested calls. It is a proof obligation, not a new run guard. --/
def FrameAdequacy (oracle : ScopedOracle) (g : Graph) : Prop :=
  ∀ (start last : State) (ops : List Op) (P : Path) (inputs : List Input),
    FrameStart start P g inputs → FrameAncestors start →
    ConformingSteps (fun s op => oracleConforms oracle s op = true) start ops last →
    FrameCompletes oracle start last P g → succeededDrained last = true →
    GraphEval oracle g P inputs (observedResult last P g)

theorem subtreeBags_root (s : State) : subtreeBags s [] = channelBags s := by
  have all : s.channels.filter (fun _ => true) = s.channels := List.filter_eq_self.mpr (by simp)
  simpa [subtreeBags, channelBags, bag] using congrArg
    (fun channels => (channels.map fun c => (c.id, sortedItems c.items)).mergeSort (fun a b => a.1 ≤ b.1)) all

/-- Closing lemma for the original unrestricted T9 target. The substantive
    obligation is FrameAdequacy, supplied separately for every graph. --/
theorem schedule_determinism_of_adequacy
    (adequacy : ∀ oracle graph, FrameAdequacy oracle graph) : ScheduleDeterminism := by
  intro graph inputs oracle valid deterministic leftOps rightOps left right leftRun rightRun leftDone rightDone
  have evaluate : ∀ ops last,
      ConformingSteps (fun s op => oracleConforms oracle s op = true) (.initial graph) (.start inputs :: ops) last →
      succeededDrained last = true → GraphEval oracle graph [] inputs (observedResult last [] graph) := by
    intro ops last run finished
    cases run with
    | @cons _ started _ _ _ allowed accepted tail =>
      obtain ⟨fs, ancestors⟩ := start_frameStart graph inputs started valid accepted
      have executed := transition_of_active accepted (show absorbed (.initial graph) (.start inputs) = false from rfl) (by simp)
      have notFinished : started.status ≠ .succeeded := by
        intro succeeded
        have impossible := transition_succeeded (.initial graph) started (.start inputs) executed succeeded
        contradiction
      have finalStatus : last.status = .succeeded := by
        have facts := finished
        simp only [succeededDrained, Bool.and_eq_true, beq_iff_eq] at facts
        exact facts.1.1
      exact adequacy oracle graph started last _ [] inputs fs ancestors tail
        (FrameCompletes.root oracle fs tail notFinished finalStatus) finished
  have results := GraphEval.functional (evaluate leftOps left leftRun leftDone) _ (evaluate rightOps right rightRun rightDone)
  have channels := congrArg Semantics.Result.channels results
  simpa only [observedResult, subtreeBags_root] using channels

end Suimon
