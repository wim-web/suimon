import Suimon.Theorems.ForEachEval

namespace Suimon
open Semantics Effects

theorem ConformingSteps.nonCancelled {allows : State → Op → Prop} {s last : State} {ops : List Op}
    (run : ConformingSteps allows s ops last) (safe : Invariants s) (finished : last.status = .succeeded)
    (i : Instance) (memberI : i ∈ s.instances) (notCancelled : i.status ≠ .cancelled)
    (j : Instance) (memberJ : j ∈ last.instances) (sameId : j.id = i.id) : j.status ≠ .cancelled := by
  intro cancelled
  obtain ⟨pre, op, post, t, t', a, b, _, before, allowed, accepted, after, safeT,
    memberA, memberB, idA, idB, _, notA, yesB, evolution⟩ :=
    run.reached safe (fun k => k.status = .cancelled) i memberI notCancelled j memberJ sameId cancelled
  have active := active_of_status_change safeT accepted a memberA b memberB (idB.trans idA.symm)
    (fun equal => notA (equal ▸ yesB))
  have opEq : op = .cancel := by
    rcases evolution.2 with same | ⟨cancel, _⟩ | ⟨bad, _⟩ | ⟨bad, _⟩ | bad | bad | bad | ⟨bad, _⟩
    · exact False.elim (notA (same ▸ yesB))
    · exact cancel
    all_goals rw [yesB] at bad; cases bad
  subst op
  have status := (effect_cancel t t' (transition_of_active accepted active (by simp))).2.2.2
  have same := after.terminal (by rw [status]; rfl)
  rw [same, status] at finished
  cases finished

theorem cancelled_origin_skip (oracle : ScopedOracle) {s0 last : State} {ops : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input} (fs : FrameStart s0 P g inputs0)
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (finished : last.status = .succeeded)
    (n : Node) (memberN : n ∈ g.nodes)
    (i : Instance) (memberI : i ∈ last.instances) (pathI : i.path = P) (nodeI : i.node = n.id)
    (cancelled : i.status = .cancelled) :
    ∃ pre post t t',
      ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 pre t ∧
      oracleConforms oracle t (.skip P n.id) = true ∧ step t (.skip P n.id) = .ok t' ∧
      transition t (.skip P n.id) = .ok t' ∧
      ConformingSteps (fun s op => oracleConforms oracle s op = true) t' post last := by
  have absent0 : ∀ j ∈ s0.instances, j.id ≠ i.id := by
    intro j memberJ eq
    obtain ⟨_, pathEq, _, _⟩ := run.input_snapshot fs.scope.safe j i memberJ memberI eq
    exact fs.noInstances j memberJ (by rw [← pathEq, pathI]; exact List.prefix_refl _)
  obtain ⟨pre, op, post, t, t', j, _, head, allowed, accepted, rest, safeT, absentT, memberJ, idJ, bindingJ, created⟩ :=
    instance_created run fs.scope.safe i memberI absent0
  have cancelledJ : j.status = .cancelled := by
    by_cases h : j.status = .cancelled
    · exact h
    · exact False.elim (rest.nonCancelled (preserves_invariants t t' op safeT accepted) finished j memberJ h i memberI idJ.symm cancelled)
  have pathJ := (Instance.binding_path bindingJ).trans pathI
  have nodeJ := (Instance.binding_node bindingJ).trans nodeI
  rcases created with
      ⟨P', N', m, inputs, _, got, _, ⟨r, c, _, eq⟩ | ⟨body, iteration, _, eq⟩⟩ |
      ⟨P', N', m, inputs, _, got, _, _, eq⟩ |
      ⟨P', N', arm, m, arms, inputs, _, got, _, _, eq⟩ |
      ⟨P', N', m, c, _, got, _, _, eq⟩ |
      ⟨P', N', e, x, m, c, _, got, _, _, eq⟩ |
      ⟨P', N', m, _, got, eq⟩ |
      ⟨P', N', m, _, got, _, eq⟩ |
      ⟨P', N', m, opEq, got, eq⟩ |
      ⟨P', N', x, m, body, _, got, _, eq⟩
  all_goals try { rw [eq] at cancelledJ; contradiction }
  have pathEq : P' = P := by rw [eq] at pathJ; exact pathJ
  subst P'
  have nodeEq : N' = n.id := (getNode_id t P N' m got).symm.trans (by rw [eq] at nodeJ; exact nodeJ)
  subst N' op
  exact ⟨pre, post, t, t', head, allowed, accepted, transition_of_created accepted (by simp) j memberJ absentT, rest⟩

theorem skip_suppressed (oracle : ScopedOracle) {s0 t t' last : State} {pre post : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input} (fs : FrameStart s0 P g inputs0)
    (head : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 pre t)
    (n : Node) (memberN : n ∈ g.nodes) (notCoalesce : n.kind ≠ .coalesce)
    (allowed : oracleConforms oracle t (.skip P n.id) = true) (accepted : step t (.skip P n.id) = .ok t')
    (executed : transition t (.skip P n.id) = .ok t')
    (rest : ConformingSteps (fun s op => oracleConforms oracle s op = true) t' post last) :
    suppressed n (stateInputs last P n) = true := by
  have safeT := head.invariants fs.scope.safe
  have tail : ConformingSteps (fun s op => oracleConforms oracle s op = true) t (.skip P n.id :: post) last := .cons allowed accepted rest
  have scL := fs.scope.persist (head.append tail)
  obtain ⟨m, got, cond, _⟩ := effect_skip t t' P n.id executed
  have same := node?_of_getNode (head.node P n.id n (fs.scope.node?_of_mem n memberN)) got
  subst m
  obtain ⟨plain, condition⟩ := Bool.and_eq_true_iff.mp cond
  have anyEmpty : (t.incoming P n.id).any (fun c => c.closed && c.items.isEmpty) = true := by
    cases kind : n.kind <;> first | exact absurd kind notCoalesce | exact condition | simpa only [kind] using condition
  obtain ⟨c, incoming, props⟩ := List.any_eq_true.mp anyEmpty
  obtain ⟨memberC, fields⟩ := List.mem_filter.mp incoming
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at fields
  simp only [Bool.and_eq_true, List.isEmpty_iff] at props
  obtain ⟨d, memberD, idD, placedD⟩ := tail.retains_closed_channel safeT c memberC props.1
  obtain ⟨e, memberE, idE, layoutE, _⟩ := run_image tail safeT c memberC
  have same := unique_channel scL.safe memberE memberD (idE.trans idD.symm)
  subst e
  obtain ⟨_, edgeD, pathD, _, exitD, _⟩ := Channel.layout_fields layoutE
  exact suppressed_of_empty scL n memberN plain notCoalesce d memberD
    (pathD.trans fields.1.1) (exitD.trans fields.1.2) (by rw [edgeD]; exact fields.2)
    (by simpa only [Channel.items, placedD] using props.2)

theorem completed_node_eval (oracle : ScopedOracle) {s0 last : State} {ops : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input} (fs : FrameStart s0 P g inputs0) (ancestors : FrameAncestors s0)
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (complete : FrameCompletes oracle s0 last P g) (finished : succeededDrained last = true)
    (n : Node) (memberN : n ∈ g.nodes)
    (children : ∀ body, (n.kind = .subworkflow body ∨ n.kind = .forEach body ∨ ∃ limit, n.kind = .loop body limit) → FrameAdequacy oracle body) :
    NodeEval oracle g P n (stateInputs last P n) (nodeValue oracle last g P n) := by
  cases computed : primitive oracle g P n (stateInputs last P n) with
  | some value =>
    simpa only [nodeValue, computed] using NodeEval.primitive computed
  | none =>
    have awake : suppressed n (stateInputs last P n) = false := by
      cases h : suppressed n (stateInputs last P n)
      · rfl
      · simp [primitive, h] at computed
    have kinds : (∃ body, n.kind = .subworkflow body) ∨ (∃ body, n.kind = .forEach body) ∨ (∃ body limit, n.kind = .loop body limit) := by
      cases kind : n.kind <;> simp [primitive, awake, kind] at computed ⊢
    have notCoalesce : n.kind ≠ .coalesce := by
      rcases kinds with ⟨_, sub⟩ | ⟨_, each⟩ | ⟨_, _, loop⟩ <;> simp [*]
    obtain ⟨i, memberI, pathI, nodeI, triggerI, status⟩ := complete.nodes fs.scope.safe n memberN
    have succeeded : i.status = .succeeded := by
      rcases status with success | cancelled
      · exact success
      · have finalStatus : last.status = .succeeded := by
          simp only [succeededDrained, Bool.and_eq_true, beq_iff_eq] at finished
          exact finished.1.1
        obtain ⟨pre, post, t, t', head, allowed, accepted, executed, rest⟩ :=
          cancelled_origin_skip oracle fs run finalStatus n memberN i memberI pathI nodeI cancelled
        have sup := skip_suppressed oracle fs head n memberN notCoalesce allowed accepted executed rest
        rw [awake] at sup; contradiction
    rcases kinds with ⟨body, sub⟩ | ⟨body, each⟩ | ⟨body, limit, loop⟩
    · exact sub_node_eval oracle fs ancestors run finished n memberN body sub (children body (.inl sub)) i memberI pathI nodeI succeeded
    · exact forEach_node_eval oracle fs ancestors run finished n memberN body each (children body (.inr (.inl each))) i memberI pathI nodeI triggerI succeeded
    · exact loop_node_eval oracle fs ancestors run finished n memberN body limit loop (children body (.inr (.inr ⟨limit, loop⟩))) i memberI pathI nodeI succeeded

end Suimon
