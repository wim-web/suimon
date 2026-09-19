import Suimon.Theorems.Work
import Suimon.Theorems.Stream

namespace Suimon
open Explore

theorem progress_active {s next : State} {op : Op} (accepted : step s op = .ok next) (changed : next ≠ s) :
    absorbed s op = false ∧ s.status.terminal = false := by
  have active : absorbed s op = false := by
    rcases step_ok_cases s op next accepted with absorbed | executed
    · exact False.elim (changed absorbed.2)
    · exact executed.1
  refine ⟨active, ?_⟩
  cases terminal : s.status.terminal with
  | false => rfl
  | true => exact False.elim (changed (terminal_absorbing s op next terminal accepted))

theorem hasWork_of_candidate {s next : State} {op : Op} (member : op ∈ candidates {} s)
    (work : op.countsAsWork = true) (accepted : step s op = .ok next) (changed : next ≠ s) : s.hasWork = true :=
  hasWork_iff s |>.mpr ⟨op, member, work, next, accepted, by simpa using changed⟩

theorem node_candidate_mem (s : State) (started : s.started = true) (active : s.status.terminal = false)
    (path : Path) (id : NodeId) (n : Node) (got : getNode s path id = .ok n)
    (op : Op) (member : op ∈ nodeCandidates s path n) : op ∈ candidates {} s := by
  cases frame : s.frame? path with
  | none => simp [getNode, frame, Option.toExcept, bind, Except.bind] at got
  | some f =>
    have memberF := List.mem_of_find?_eq_some frame
    have pathF : f.path = path := by simpa using List.find?_some frame
    simp only [getNode, frame, Option.toExcept, bind, Except.bind] at got
    cases ready : require (!f.closed) "CLOSED_FRAME" with
    | error e => simp [ready] at got
    | ok u =>
      have openF : f.closed = false := by simpa using require_ok _ _ _ u ready
      rw [ready] at got
      simp only [bind, Except.bind] at got
      cases found : f.graph.node? id with
      | none => simp [found, Option.toExcept] at got
      | some m =>
        have eq : m = n := by simpa [found, Option.toExcept] using got
        subst m
        have memberN := List.mem_of_find?_eq_some found
        simp only [candidates, active, started, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          List.mem_append, List.mem_flatMap]
        exact .inl (.inr ⟨f, List.mem_filter.mpr ⟨memberF, by simp [openF]⟩, n, memberN, by simpa only [pathF] using member⟩)

theorem instance_candidate_mem (s : State) (started : s.started = true) (active : s.status.terminal = false)
    (i : Instance) (memberI : i ∈ s.instances) (op : Op) (member : op ∈ instanceCandidates {} s i) :
    op ∈ candidates {} s := by
  simp only [candidates, active, started, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.mem_append]
  exact .inr (List.mem_flatMap.mpr ⟨i, memberI, member⟩)

/-- These operation families take all their arguments from the current graph,
    pending tokens, or the two Boolean choices enumerated by the scheduler. --/
def fixedArguments : Op → Bool
  | .activate .. | .spawn .. | .fireWaitAll .. | .fireBranch .. | .fireCoalesce .. | .fireCollect ..
  | .fireFilter .. | .fireMerge .. | .propagateEos .. | .finishSubworkflow .. | .loopIterate .. | .skip .. => true
  | _ => false

theorem fixedArguments_enumerated (s next : State) (op : Op) (safe : Invariants s) (started : s.started = true)
    (fixed : fixedArguments op = true) (accepted : step s op = .ok next) (changed : next ≠ s) : op ∈ candidates {} s := by
  obtain ⟨active, terminal⟩ := progress_active accepted changed
  have notIdle : op ≠ .idle := by intro eq; rw [eq] at fixed; contradiction
  have executed := transition_of_active accepted active notIdle
  cases op with
  | activate path id =>
    obtain ⟨_, n, _, got, _, kinds⟩ := effect_activate s next path id executed
    apply node_candidate_mem s started terminal path id n got
    have idN := getNode_id s path id n got
    rcases kinds with ⟨r, c, kind, _⟩ | ⟨body, k, ⟨kind, _⟩ | ⟨limit, kind, _⟩, _⟩ <;> simp [nodeCandidates, kind, idN]
  | spawn path id item =>
    obtain ⟨_, n, body, c, got, kind, incoming, pending, _⟩ := effect_spawn s next path id item safe.channelIds executed
    apply node_candidate_mem s started terminal path id n got
    have idN := getNode_id s path id n got
    simp only [nodeCandidates, kind, List.mem_cons]
    refine .inr (.inr (List.mem_flatMap.mpr ⟨c, ?_, ?_⟩))
    · rw [idN]; exact List.mem_of_mem_head? incoming
    · simp [pendingCandidates, pending, kind, idN]
  | fireWaitAll path id =>
    obtain ⟨n, _, got, kind, _⟩ := effect_fireWaitAll s next path id executed
    exact node_candidate_mem s started terminal path id n got _ (by simp [nodeCandidates, kind, getNode_id s path id n got])
  | fireBranch path id arm =>
    obtain ⟨n, arms, _, _, got, kind, chosen, _⟩ := effect_fireBranch s next path id arm executed
    apply node_candidate_mem s started terminal path id n got
    simp only [nodeCandidates, kind, List.mem_cons]
    exact .inr (List.mem_map.mpr ⟨arm, List.contains_iff_mem.mp chosen, by rw [getNode_id s path id n got]⟩)
  | fireCoalesce path id edge item =>
    obtain ⟨n, c, _, got, kind, incoming, pending, _⟩ := effect_fireCoalesce s next path id edge item safe.channelIds executed
    apply node_candidate_mem s started terminal path id n got
    have idN := getNode_id s path id n got
    have edgeC : c.id = edge := by simpa using List.find?_some incoming
    simp only [nodeCandidates, kind, List.mem_cons]
    refine .inr (List.mem_flatMap.mpr ⟨c, ?_, ?_⟩)
    · rw [idN]; exact List.mem_of_find?_eq_some incoming
    · simp [pendingCandidates, pending, kind, idN, edgeC]
  | fireCollect path id =>
    obtain ⟨n, _, got, kind, _⟩ := effect_fireCollect s next path id executed
    exact node_candidate_mem s started terminal path id n got _ (by simp [nodeCandidates, kind, getNode_id s path id n got])
  | fireFilter path id item keep =>
    obtain ⟨n, c, got, kind, incoming, pending, _⟩ := effect_fireFilter s next path id item keep safe.channelIds executed
    apply node_candidate_mem s started terminal path id n got
    have idN := getNode_id s path id n got
    simp only [nodeCandidates, kind, List.mem_cons]
    refine .inr (.inr (List.mem_flatMap.mpr ⟨c, ?_, ?_⟩))
    · rw [idN]; exact List.mem_of_mem_head? incoming
    · cases keep <;> simp [pendingCandidates, pending, kind, idN]
  | fireMerge path id edge item =>
    obtain ⟨n, c, _, got, kind, incoming, edgeC, pending, _⟩ := effect_fireMerge s next path id edge item safe.channelIds executed
    apply node_candidate_mem s started terminal path id n got
    have idN := getNode_id s path id n got
    simp only [nodeCandidates, kind, List.mem_cons]
    refine .inr (.inr (List.mem_flatMap.mpr ⟨c, ?_, ?_⟩))
    · rwa [idN]
    · simp [pendingCandidates, pending, kind, idN, edgeC]
  | propagateEos path id =>
    obtain ⟨n, got, kind, _⟩ := effect_propagateEos s next path id executed
    apply node_candidate_mem s started terminal path id n got
    have idN := getNode_id s path id n got
    cases k : n.kind <;> simp_all [nodeCandidates]
  | finishSubworkflow inst =>
    obtain ⟨i, _, _, _, found, waiting, _⟩ := effect_finishSubworkflow s next inst executed
    exact instance_candidate_mem s started terminal i (instance?_mem found) _
      (by simp [instanceCandidates, waiting, instance?_id found])
  | loopIterate inst done =>
    obtain ⟨i, _, _, _, _, _, _, found, waiting, _⟩ := effect_loopIterate s next inst done executed
    apply instance_candidate_mem s started terminal i (instance?_mem found)
    cases done <;> simp [instanceCandidates, waiting, instance?_id found]
  | skip path id =>
    obtain ⟨n, got, _⟩ := effect_skip s next path id executed
    exact node_candidate_mem s started terminal path id n got _ (by simp [nodeCandidates, getNode_id s path id n got])
  | _ => contradiction

theorem hasWork_of_fixedArguments (s next : State) (op : Op) (safe : Invariants s) (started : s.started = true)
    (fixed : fixedArguments op = true) (accepted : step s op = .ok next) (changed : next ≠ s) : s.hasWork = true := by
  have work : op.countsAsWork = true := by cases op <;> first | rfl | contradiction
  exact hasWork_of_candidate (fixedArguments_enumerated s next op safe started fixed accepted changed) work accepted changed

end Suimon
