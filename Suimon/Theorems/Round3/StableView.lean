import Suimon.Theorems.Round3.SettleView
import Suimon.Theorems.Round3.StableFrame

/-! Helpers for `Round3/Stable.lean` (task E4): a step keeps everything `settleOutcome` reads for a
    settled placement (`SettleViewAgree`), and so does the step that settles it. -/

namespace Suimon.Round3.StableAux
open State

section StableView
variable {p : Program} {s t : State} {op : Op}

theorem invocationsOf_nodup (wk : s.WellKeyed) (path : Path) (name : String) :
    (s.invocationsOf path name).Nodup :=
  nodup_filter' _ (nodup_of_map' wk.invocations)

/-- The invocations of one placement in one run have distinct triggers (their identities contain the
    trigger). -/
theorem triggers_nodup (h : Reachable p s) (path : Path) (name : String) :
    ((s.invocationsOf path name).map (·.trigger)).Nodup := by
  have inv := Delivery.Reachable.inv h
  exact nodup_map_on' (Delivery.uniq_trigger inv.own inv.wk) (invocationsOf_nodup inv.wk path name)

/-- A Single connection that resolved without a delivery gets none later: its source settled without
    a value on the connection's arm, so no result is eligible. -/
theorem deliveriesOn_nil_kept (h : Reachable p s) (hs : step p s op = .ok t) {path : Path} {w : Workflow}
    (hw : s.workflow? p path = some w) {j : Nat} {c : Connection} (hcj : w.connections[j]? = some c)
    (hne : s.resolveSingle path j c ≠ .pending) (hnil : s.deliveriesOn path j = []) :
    t.deliveriesOn path j = [] := by
  rcases hd : t.deliveriesOn path j with _ | ⟨d, rest⟩
  · rfl
  · exfalso
    have hdm : d ∈ t.deliveriesOn path j := by rw [hd]; exact List.mem_cons_self
    obtain ⟨hdm, hdr, hdc⟩ := Delivery.mem_deliveriesOn.mp hdm
    rcases Delivery.step_deliveries_back hs d hdm with hd' | ⟨-, -, -, w', c', r, hw', hc', hr, hrr, hrp, harm⟩
    · have : d ∈ s.deliveriesOn path j := Delivery.mem_deliveriesOn.mpr ⟨hd', hdr, hdc⟩
      rw [hnil] at this
      cases this
    · rw [hdr, hw] at hw'
      cases hw'
      rw [hdc, hcj] at hc'
      cases hc'
      have hres : s.resolveSingle path j c = .skipped ∨ s.resolveSingle path j c = .failure := by
        rw [Delivery.resolveSingle_of_nil hnil] at hne ⊢
        cases hx : s.settled? path c.source with
        | none => simp [hx] at hne
        | some y => cases ho : armOutcome y c.arm <;> simp [hx, ho] at hne ⊢
      obtain ⟨-, y, hy, hyo⟩ := Delivery.resolveSingle_no_delivery hres
      obtain ⟨hym, hyr, hyp⟩ := settled?_eq_some hy
      have := (Settle.reachable h).2.2.2.noEligible y hym c.arm hyo r
        (Delivery.mem_resultsOf.mpr ⟨(result?_eq_some hr).1, by rw [hyr, hrr, hdr], by rw [hyp, hrp]⟩)
      rcases harm with h' | h' <;> simp [h'] at this

/-- A Single connection keeps its resolution once it resolved. -/
theorem resolveSingle_kept (h : Reachable p s) (hs : step p s op = .ok t) {path : Path} {w : Workflow}
    (hw : s.workflow? p path = some w) {j : Nat} {c : Connection} (hcj : w.connections[j]? = some c)
    (hne : s.resolveSingle path j c ≠ .pending) : s.resolveSingle path j c = t.resolveSingle path j c :=
  (Delivery.resolveSingle_stable (step_grows hs) hne (deliveriesOn_nil_kept h hs hw hcj hne)).symm

/-- A Stream connection whose eligible results were all delivered gets no new delivery. -/
theorem deliveriesOn_stream_kept (h : Reachable p s) (hs : step p s op = .ok t) {path : Path} {w : Workflow}
    (hw : s.workflow? p path = some w) {j : Nat} {c : Connection} (hcj : w.connections[j]? = some c)
    (hall : ∀ r ∈ s.eligible path c, (s.delivery? path j r.id).isSome) :
    t.deliveriesOn path j = s.deliveriesOn path j := by
  have wk' := step_wellKeyed (Delivery.Reachable.inv h).wk hs
  unfold State.deliveriesOn
  refine filter_prefix_eq (step_grows hs).deliveries (nodup_of_map' wk'.deliveries) fun d hd hP => ?_
  simp only [Bool.and_eq_true, beq_iff_eq] at hP
  rcases Delivery.step_deliveries_back hs d hd with hd' | ⟨-, -, hfresh, w', c', r, hw', hc', hr, hrr, hrp, harm⟩
  · exact hd'
  · exfalso
    rw [hP.1, hw] at hw'
    cases hw'
    rw [hP.2, hcj] at hc'
    cases hc'
    obtain ⟨hrm, hrid⟩ := result?_eq_some hr
    obtain ⟨d', hd'⟩ := Option.isSome_iff_exists.mp
      (hall r (Delivery.mem_eligible.mpr ⟨hrm, by rw [hrr, hP.1], hrp, harm⟩))
    rw [hP.1, hP.2, ← hrid, hd'] at hfresh
    cases hfresh

/-- An ended stream stays ended: its source settled, so it gets no new eligible result. -/
theorem streamEnd?_kept (h : Reachable p s) (hs : step p s op = .ok t) {path : Path} {j : Nat} {c : Connection}
    (hsettled : (s.settled? path c.source).isSome)
    (hall : ∀ r ∈ s.eligible path c, (s.delivery? path j r.id).isSome) :
    s.streamEnd? path j c = t.streamEnd? path j c := by
  have inv := Delivery.Reachable.inv h
  have K := inv.kept hs
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hsettled
  obtain ⟨hym, hyr, hyp⟩ := settled?_eq_some hy
  rw [Delivery.streamEnd?_eq_some.mpr ⟨y, hy, hall, rfl⟩]
  refine (Delivery.streamEnd?_eq_some.mpr ⟨y, K.settled? hy, fun r hr => ?_, rfl⟩).symm
  obtain ⟨hrm, hrr, hrp, harm⟩ := Delivery.mem_eligible.mp hr
  have hr₀ := Delivery.frozen_results inv hs hym r hrm (by rw [hyr, hrr]) (by rw [hyp, hrp])
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (hall r (Delivery.mem_eligible.mpr ⟨hr₀, hrr, hrp, harm⟩))
  rw [K.delivery? hd]
  rfl

/-- The input connections of a Merge are those of its placement. -/
theorem merge_inputs {w : Workflow} {name : String} {cs : List (Nat × Connection)}
    (hsh : w.shape? p name = some (.merge cs)) : cs = w.inputs name := by
  obtain ⟨pl', -, ⟨-, hm⟩ | ⟨-, ⟨-, hm⟩ | ⟨-, -, hm⟩ | ⟨-, j, c, -, ⟨-, hm⟩ | ⟨-, hm⟩⟩⟩⟩ := Delivery.shape?_eq hsh
  · injection hm
  all_goals cases hm

/-- A step keeps everything the settlement of a settled placement read. -/
theorem view_kept (h : Reachable p s) (hs : step p s op = .ok t) {x : Settled} (hx : x ∈ s.settled)
    {w : Workflow} {pl : Placement} {shape : Workflow.Shape} {kind : Kind} {agg : Option Result}
    (hw : s.workflow? p x.run = some w) (hpl : w.placement? x.placement = some pl)
    (hsh : w.shape? p x.placement = some shape)
    (hout : s.settleOutcome x.run pl shape kind = some (x, agg)) :
    SettleViewAgree s t x.run pl shape := by
  have inv := Delivery.Reachable.inv h
  have wk' := step_wellKeyed inv.wk hs
  have K := inv.kept hs
  have hname : pl.name = x.placement := (Workflow.placement?_eq_some hpl).2
  obtain ⟨hall, -, -, -⟩ := State.settleOutcome_some hout
  have ended_s : ∀ i ∈ s.invocationsOf x.run pl.name, s.invocationEnded i = true :=
    fun i hi => List.all_eq_true.mp hall i hi
  -- The invocations of the placement ended, so they stay as they are.
  have keep : ∀ i ∈ s.invocationsOf x.run pl.name, i ∈ t.invocations := by
    intro i hi
    obtain ⟨hi', -, -⟩ := Delivery.mem_invocationsOf.mp hi
    obtain ⟨i', hi'', hid, -⟩ := K.invocation i hi'
    rw [Delivery.frozen inv hs hi' (Delivery.invocationEnded_iff.mp (ended_s i hi)).1 hi'' hid] at hi''
    exact hi''
  -- A settled placement is invoked no more.
  have back : ∀ i ∈ t.invocationsOf x.run pl.name, i ∈ s.invocations := by
    intro i hi
    obtain ⟨hi', hir, hip⟩ := Delivery.mem_invocationsOf.mp hi
    obtain ⟨i₀, hi₀, hid, hrun, hplc, -, -⟩ := Delivery.frozen_invocations inv hs hx i hi' hir (hip.trans hname)
    have hend := ended_s i₀ (Delivery.mem_invocationsOf.mpr ⟨hi₀, hrun.trans hir, hplc.trans hip⟩)
    rw [Delivery.frozen inv hs hi₀ (Delivery.invocationEnded_iff.mp hend).1 hi' hid.symm]
    exact hi₀
  refine ⟨?_, triggers_nodup h _ _, fun i hi => ?_, ?_, ?_⟩
  · refine (List.perm_ext_iff_of_nodup (invocationsOf_nodup inv.wk _ _) (invocationsOf_nodup wk' _ _)).mpr
      fun i => ⟨fun hi => ?_, fun hi => ?_⟩
    · obtain ⟨-, hir, hip⟩ := Delivery.mem_invocationsOf.mp hi
      exact Delivery.mem_invocationsOf.mpr ⟨keep i hi, hir, hip⟩
    · obtain ⟨-, hir, hip⟩ := Delivery.mem_invocationsOf.mp hi
      exact Delivery.mem_invocationsOf.mpr ⟨back i hi, hir, hip⟩
  · rw [ended_s i hi]
    exact (Delivery.ended_kept inv hs (Delivery.mem_invocationsOf.mp hi).1 (ended_s i hi) (keep i hi) rfl).symm
  · -- A settled placement accepts no new result.
    have heq : t.resultsOf x.run pl.name = s.resultsOf x.run pl.name := by
      unfold State.resultsOf
      refine filter_prefix_eq (step_grows hs).results (nodup_of_map' wk'.results) fun r hr hP => ?_
      simp only [Bool.and_eq_true, beq_iff_eq] at hP
      exact Delivery.frozen_results inv hs hx r hr hP.1 (hP.2.trans hname)
    rw [heq]
  · have hdone := Delivery.settleOutcome_input hout
    cases shape with
    | none => trivial
    | entry => trivial
    | single j c =>
      obtain ⟨-, hcj, -, -⟩ := Delivery.shape?_single hsh
      exact resolveSingle_kept h hs hw hcj hdone.1
    | stream j c =>
      obtain ⟨-, hcj, -, -⟩ := Delivery.shape?_stream hsh
      obtain ⟨hsettled, hall', -⟩ := hdone
      exact ⟨streamEnd?_kept h hs hsettled hall', by rw [deliveriesOn_stream_kept h hs hw hcj hall']⟩
    | merge cs =>
      intro jc hjc
      have hjc' : jc ∈ w.inputs x.placement := merge_inputs hsh ▸ hjc
      exact resolveSingle_kept h hs hw (Delivery.mem_inputs.mp hjc').1 (hdone jc hjc)

/-- The step that settles a placement keeps everything its settlement read: it adds only the
    settlement and the aggregate, which carries no arm and is no result of the placement's source. -/
theorem view_settle (h : Reachable p s) (g : s.Grows t) {x : Settled} {pl : Placement} {shape : Workflow.Shape}
    {kind : Kind} {res : Option Result} (hname : pl.name = x.placement) (hfresh : s.settled? x.run x.placement = none)
    (hout : s.settleOutcome x.run pl shape kind = some (x, res)) (hres : t.results = s.results ++ res.toList)
    (hruns : t.runs = s.runs) (hinv : t.invocations = s.invocations) (hcalls : t.calls = s.calls)
    (hexec : t.executions = s.executions) (hdel : t.deliveries = s.deliveries) :
    SettleViewAgree s t x.run pl shape := by
  have hrprop : ∀ r, res = some r → r.placement = pl.name ∧ r.arm = none := fun r hr => by
    subst hr
    obtain ⟨-, -, -, -, -, hp, -, ha⟩ := Delivery.settleOutcome_res hout
    exact ⟨hp, ha⟩
  have hinvOf : t.invocationsOf x.run pl.name = s.invocationsOf x.run pl.name := by
    simp only [State.invocationsOf, hinv]
  have hdelOn : ∀ j, t.deliveriesOn x.run j = s.deliveriesOn x.run j := fun j => by
    simp only [State.deliveriesOn, hdel]
  refine ⟨by rw [hinvOf], triggers_nodup h _ _, fun i _ => by simp only [State.invocationEnded, hcalls, hruns, hexec],
    ?_, ?_⟩
  · have heq : (t.resultsOf x.run pl.name).filterMap (·.arm) = (s.resultsOf x.run pl.name).filterMap (·.arm) := by
      simp only [State.resultsOf, hres, List.filter_append, List.filterMap_append]
      suffices hnil : (res.toList.filter fun r => r.run == x.run && r.placement == pl.name).filterMap (·.arm) = [] by
        rw [hnil, List.append_nil]
      cases res with
      | none => rfl
      | some r =>
        have ha := (hrprop r rfl).2
        cases hP : (r.run == x.run && r.placement == pl.name) <;> simp [List.filter, hP, ha]
    rw [heq]
  · have hdone := Delivery.settleOutcome_input hout
    cases shape with
    | none => trivial
    | entry => trivial
    | single j c =>
      exact (Delivery.resolveSingle_stable g hdone.1 fun hnil => by rw [hdelOn]; exact hnil).symm
    | stream j c =>
      obtain ⟨hsettled, hall, -⟩ := hdone
      refine ⟨?_, by rw [hdelOn]⟩
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hsettled
      rw [Delivery.streamEnd?_eq_some.mpr ⟨y, hy, hall, rfl⟩]
      refine (Delivery.streamEnd?_eq_some.mpr ⟨y, g.settled?_eq_some hy, fun r hr => ?_, rfl⟩).symm
      obtain ⟨hrm, hrr, hrp, harm⟩ := Delivery.mem_eligible.mp hr
      rw [hres, List.mem_append] at hrm
      rcases hrm with hrm | hrm
      · obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (hall r (Delivery.mem_eligible.mpr ⟨hrm, hrr, hrp, harm⟩))
        have hd' : t.delivery? x.run j r.id = some d := by
          unfold State.delivery?; rw [hdel]; exact hd
        rw [hd']
        rfl
      · -- The aggregate belongs to the settling placement, which is not its own source.
        exfalso
        cases res with
        | none => cases hrm
        | some r' =>
          rw [Option.toList_some, List.mem_singleton] at hrm
          subst hrm
          have hp := (hrprop r rfl).1
          have : s.settled? x.run x.placement = some y := by rw [← hname, ← hp, hrp]; exact hy
          rw [hfresh] at this
          cases this
    | merge cs =>
      intro jc hjc
      exact (Delivery.resolveSingle_stable g (hdone jc hjc) fun hnil => by rw [hdelOn]; exact hnil).symm

end StableView

end Suimon.Round3.StableAux
