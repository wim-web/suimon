import Suimon.Theorems.Round3.CoversCloseAux
import Suimon.Theorems.Round3.ShapeFits

/-! Helpers for [24] Round3/CoversClose.lean — task F6: the frozen footprint of the placement that a
`settle` of run 1 settles, against the final state `T` of the complete run 2.

Invocations come from the view (`SettleViewAgree.invocations`). A result of `T` of the placement comes
from an invocation of `T` of it, which is an ended invocation of run 1: its call is the same ended call
in both runs (`CallConform`), its execution completed in run 1 (execution footprint and
`OutputResults`, or `Stable.execution`), its sub-run completed in run 1 (`Stable.run`); or the result is
the aggregate that the settlement itself records. Input deliveries follow the input shape. -/

namespace Suimon.Round3
open State

namespace CoversCloseAux

variable {p : Definition} {env : Env} {s T : State}

/-- A result of `T` of a placement whose invocations in `T` are ended invocations of `s` is a result of
    `s`, unless it is the aggregate of a waitStream or Merge that `T` settled normally. -/
theorem results_back (valid : p.validate = .ok ()) {tr tr₂ : List Op} (h₁ : Conforming p env tr s)
    (us : Unstopped s) (h₂ : Conforming p env tr₂ T) (done : Done T) (cov : Covers p T s)
    {path : Path} {name : String} {w : Workflow} {pl : Placement}
    (hw : s.workflow? p path = some w) (hpl : w.placement? name = some pl)
    (hinv : ∀ i ∈ T.invocations, i.run = path → i.placement = name →
      i ∈ s.invocations ∧ s.invocationEnded i = true)
    {r : Result} (hr : r ∈ T.results) (hrr : r.run = path) (hrp : r.placement = name) :
    r ∈ s.results ∨
      (r.id = Key.aggregate path name ∧ (∃ e, pl.control = .waitStream e ∨ pl.control = .merge e) ∧
        ∃ x ∈ T.settled, x.run = path ∧ x.placement = name ∧ x.outcome = .normal) := by
  have hreach := h₁.reachable
  have hT := h₂.reachable
  have wkS := hreach.wellKeyed
  have wkT := hT.wellKeyed
  have rcS := runConform valid h₁ us
  have rcT := runConform valid h₂ (Or.inr done)
  have ownT := (Settle.reachable hT).1
  have hwT := covers_workflow? cov wkT hw
  -- The placement `T` reads at `(path, name)` is `pl`.
  have plT : ∀ {pl'}, Settle.placementAt p T path name = some pl' → pl' = pl := by
    intro pl' h'
    rw [Settle.placementAt_eq hwT, hpl] at h'
    exact (Option.some.inj h').symm
  -- A result of `s` with the identity of `r` is `r` (identities are unique in `T`).
  have back : ∀ r' ∈ s.results, r'.id = r.id → r ∈ s.results := fun r' hr' hid => by
    rw [← wkT.result_eq_of_id (cov.results r' hr') hr hid]
    exact hr'
  rcases reachable_resultOrigin hT r hr with ⟨c, hc, htask, k, hid⟩ |
      ⟨hid, ⟨w', pl', hw', hpl', hctrl⟩, x, hx, h1, h2, h3⟩ |
      ⟨e, he, h1, h2, ⟨cc, hcc, hout⟩, n, k, hid⟩ |
      ⟨e, he, h1, h2, ⟨cc, hcc, hout⟩, ⟨i, hi, hie, hst⟩, hid⟩ |
      ⟨i, hi, h1, h2, hst, ⟨pl', wf, out, hpl', hctrl⟩, hid⟩
  · -- A call result: the call of the ended invocation is the same ended call in both runs, and
    -- `CallConform` fixes its results by the call alone.
    left
    obtain ⟨-, i, hiT, hir, hip, -⟩ := (rcT.calls c hc).1.values r hr k hid
    obtain ⟨hiTm, hiTid⟩ := invocation?_eq_some hiT
    have hirun : i.run = path := hir.symm.trans hrr
    have hipl : i.placement = name := hip.symm.trans hrp
    obtain ⟨his, hend⟩ := hinv i hiTm hirun hipl
    obtain ⟨hcid, i', hi', hi'id, pl', hpl', hctrl⟩ := ownT.callNone c hc htask
    obtain rfl : i' = i := wkT.invocation_eq_of_id hi' hiTm (hi'id.trans hiTid.symm)
    obtain rfl : pl' = pl := plT (by rw [← hirun, ← hipl]; exact hpl')
    have hbody : (∃ f, pl'.control = .call (.function f)) ∨ ∃ j arms, pl'.control = .branch j arms := by
      rcases hctrl with ⟨f, -, hf, -⟩ | ⟨j, arms, hb, -⟩
      · exact Or.inl ⟨f, hf⟩
      · exact Or.inr ⟨j, arms, hb⟩
    obtain ⟨c₀, hc₀, hc₀id, hc₀o, hc₀t⟩ :=
      (invocation_body hreach i' his w pl' (hirun ▸ hw) (hipl ▸ hpl)).1 hbody
    have hc₀e := (Delivery.invocationEnded_iff.mp hend).2.1 c₀ hc₀ hc₀o hc₀t
    obtain ⟨c', hc', -, -, -, -, -, -, -, -, hsame⟩ := cov.calls c₀ hc₀
    rw [hsame hc₀e] at hc'
    obtain rfl : c₀ = c := wkT.call_eq_of_id hc' hc (by rw [hc₀id, hiTid, hcid])
    obtain ⟨r', hr', hid'⟩ := ((rcS.calls c₀ hc₀).1.results k).mpr (((rcT.calls c₀ hc).1.results k).mp ⟨r, hr, hid⟩)
    exact back r' hr' (hid'.trans hid.symm)
  · -- The aggregate of a normal waitStream or Merge settlement of `T`.
    right
    rw [hrr, hwT] at hw'
    cases hw'
    rw [hrp, hpl] at hpl'
    cases hpl'
    exact ⟨by rw [hid, hrr, hrp], hctrl, x, hx, h1.trans hrr, h2.trans hrp, h3⟩
  · -- An element of a Stream concurrency output: the execution completed in `s`, so `T` has no task
    -- result of it beyond `s`, and `OutputResults` gives the element in `s`.
    left
    obtain ⟨i, hi, hie, hir, hip, -⟩ := ownT.execOwner e he
    have hirun : i.run = path := hir.trans (h1.trans hrr)
    have hipl : i.placement = name := hip.trans (h2.trans hrp)
    obtain ⟨his, hend⟩ := hinv i hi hirun hipl
    obtain ⟨w₁, pl₁, hw₁, hpl₁, hctl⟩ := Delivery.concurrencyOf_iff.mp hcc
    rw [h1, hrr, hwT] at hw₁
    cases hw₁
    rw [h2, hrp, hpl] at hpl₁
    cases hpl₁
    obtain ⟨e₀, he₀, he₀id⟩ := (invocation_body hreach i his w pl (hirun ▸ hw) (hipl ▸ hpl)).2.2 cc hctl
    have he₀c := (Delivery.invocationEnded_iff.mp hend).2.2.2 e₀ he₀ he₀id
    obtain ⟨e', he', a1, a2, a3, -⟩ := cov.executions e₀ he₀
    obtain rfl : e' = e := wkT.execution_eq_of_id he' he (a1.trans (he₀id.trans hie))
    obtain ⟨tr, htr, t1, t2, t3, t4⟩ := (Reachable.outputResults hT).2 r hr e'.id n k hid
    have htrs := cov.execution e₀ he₀ he₀c tr htr (t1.trans a1)
    have hcc₀ : s.concurrencyOf p e₀ = .ok cc :=
      concurrencyOf_of_workflow? (h1.trans hrr) (a2.symm.trans (h1.trans hrr)) a3.symm hwT hw hcc
    have he₀s : s.execution? tr.execution = some e₀ := by
      rw [t1, a1]
      exact wkS.execution?_of_mem he₀
    refine back _ ((Reachable.outputResults hreach).1 tr htrs r.value t4 e₀ cc he₀s hcc₀ hout) ?_
    simp only [hid, ← a1, t2, t3]
  · -- The list of a List concurrency whose invocation succeeded: the execution completed in `s`, and
    -- `Stable.execution` in `s` records the list there.
    left
    obtain ⟨i₁, hi₁, hi₁e, hir, hip, -⟩ := ownT.execOwner e he
    obtain rfl : i₁ = i := wkT.invocation_eq_of_id hi₁ hi (hi₁e.trans hie.symm)
    have hirun : i₁.run = path := hir.trans (h1.trans hrr)
    have hipl : i₁.placement = name := hip.trans (h2.trans hrp)
    obtain ⟨his, hend⟩ := hinv i₁ hi₁ hirun hipl
    obtain ⟨w₁, pl₁, hw₁, hpl₁, hctl⟩ := Delivery.concurrencyOf_iff.mp hcc
    rw [h1, hrr, hwT] at hw₁
    cases hw₁
    rw [h2, hrp, hpl] at hpl₁
    cases hpl₁
    obtain ⟨e₀, he₀, he₀id⟩ := (invocation_body hreach i₁ his w pl (hirun ▸ hw) (hipl ▸ hpl)).2.2 cc hctl
    have he₀c := (Delivery.invocationEnded_iff.mp hend).2.2.2 e₀ he₀ he₀id
    obtain ⟨e', he', a1, a2, a3, -⟩ := cov.executions e₀ he₀
    obtain rfl : e' = e := wkT.execution_eq_of_id he' he (a1.trans (he₀id.trans hi₁e))
    have hcc₀ : s.concurrencyOf p e₀ = .ok cc :=
      concurrencyOf_of_workflow? (h1.trans hrr) (a2.symm.trans (h1.trans hrr)) a3.symm hwT hw hcc
    have hi₀ : s.invocation? e₀.id = some i₁ := by
      rw [he₀id]
      exact wkS.invocation?_of_mem his
    rcases (Reachable.stable valid hreach).execution e₀ he₀ he₀c cc i₁ hcc₀ hi₀ with ⟨-, hsk⟩ | ⟨-, -, hlist⟩
    · rw [hst] at hsk
      cases hsk
    · refine back _ (hlist hout) ?_
      simp only [listResult, hid, a1]
  · -- The result of a succeeded sub-workflow call: its sub-run completed in `s`, and `Stable.run` in `s`
    -- records the result there.
    left
    have hirun : i.run = path := h1.trans hrr
    have hipl : i.placement = name := h2.trans hrp
    obtain ⟨his, -⟩ := hinv i hi hirun hipl
    obtain rfl : pl' = pl := plT (by rw [← hirun, ← hipl]; exact hpl')
    have hpls : Settle.placementAt p s i.run i.placement = some pl' := by
      rw [Settle.placementAt_eq (hirun ▸ hw), hipl]
      exact hpl
    obtain ⟨R, hR, hRo, hRt, hRc⟩ := (Settle.reachable hreach).2.2.1.callRun i his hst pl' hpls ⟨wf, out, hctrl⟩
    have hdes : s.designatedOutput p R = .ok out :=
      State.designatedOutput_eq_ok.mpr ⟨i.id, hRo, Or.inl ⟨hRt, i, pl', wf, wkS.invocation?_of_mem his,
        State.placementOf_eq_ok.mpr ⟨w, hirun ▸ hw, hipl ▸ hpl⟩, hctrl⟩⟩
    obtain ⟨wR, hwR⟩ := Option.isSome_iff_exists.mp (run_workflow valid hreach R hR)
    obtain ⟨⟨plo, hplo, hploname⟩, -⟩ := run_output valid hreach hR hdes hwR
    obtain ⟨x', hx'⟩ :=
      Option.isSome_iff_exists.mp ((Settle.reachable hreach).2.2.1.completeSettled R hR hRc wR hwR plo hplo)
    rw [hploname] at hx'
    have hstab := (Reachable.stable valid hreach).run R hR hRc i.id out x' hRo hdes hx'
    rw [hRt] at hstab
    obtain ⟨i', hi', hsti', hres⟩ := hstab
    rw [wkS.invocation?_of_mem his] at hi'
    cases hi'
    have hn : x'.outcome = .normal := by
      cases ho : x'.outcome <;> rw [ho, hst] at hsti' <;> first | rfl | cases hsti'
    obtain ⟨res, -, hres'⟩ := hres hn
    exact back _ hres' (by simp only [returnedResult, hid])

/-- The input deliveries of the settled placement in `T` are those of `s`, by its input shape: none for
    none/entry (the entry has no incoming connection), the permutation of the view for a Stream input,
    and a Single connection resolved alike otherwise (Single inputs and the inputs of a Merge). -/
theorem inputs_back (valid : p.validate = .ok ()) (hT : Reachable p T) (cov : Covers p T s) {path : Path}
    {w : Workflow} {pl : Placement} {shape : Workflow.Shape} (hwT : T.workflow? p path = some w)
    (hwm : w ∈ p.workflows) (hplm : pl ∈ w.placements) (hsh : w.shape? p pl.name = some shape)
    (agree : SettleViewAgree s T path pl shape) :
    ∀ j c, (j, c) ∈ w.inputs pl.name → ∀ d ∈ T.deliveriesOn path j, d ∈ s.deliveries := by
  intro j c hjc d hd
  obtain ⟨sh, k, hsh', -, -, -, -, hmerge⟩ := shape_fits valid w hwm pl hplm
  rw [hsh] at hsh'
  cases hsh'
  have hin := agree.input
  obtain ⟨hcj, -⟩ := Delivery.mem_inputs.mp hjc
  -- Without a Merge and with the entry, validation leaves no incoming connection.
  have noInputs : (∀ e, pl.control ≠ .merge e) → w.isEntry pl.name = true → False := by
    intro hm he
    have hle := inputs_of_validate valid w hwm pl hplm hm
    rw [he] at hle
    have hinc : w.incoming pl.name = [] := by
      cases hi : w.incoming pl.name with
      | nil => rfl
      | cons a l => rw [hi] at hle; simp at hle
    have : c ∈ w.incoming pl.name := by
      rw [← Delivery.inputs_map_snd]
      exact List.mem_map.mpr ⟨(j, c), hjc, rfl⟩
    rw [hinc] at this
    cases this
  cases shape with
  | none =>
    exfalso
    obtain ⟨pl', -, hcase⟩ := Delivery.shape?_eq hsh
    rcases hcase with ⟨-, h⟩ | ⟨-, ⟨-, h⟩ | ⟨-, hnil, -⟩ | ⟨-, j', c', -, ⟨-, h⟩ | ⟨-, h⟩⟩⟩
    · cases h
    · cases h
    · rw [hnil] at hjc
      cases hjc
    · cases h
    · cases h
  | entry =>
    exfalso
    obtain ⟨pl', hpl', hcase⟩ := Delivery.shape?_eq hsh
    have hname := ((Definition.validate_ok valid).workflows w hwm).names
    rw [Workflow.placement?_of_mem hname hplm] at hpl'
    cases hpl'
    rcases hcase with ⟨-, h⟩ | ⟨hm, ⟨he, -⟩ | ⟨-, -, h⟩ | ⟨-, j', c', -, ⟨-, h⟩ | ⟨-, h⟩⟩⟩
    · cases h
    · exact noInputs hm he
    · cases h
    · cases h
    · cases h
  | single j' c' =>
    obtain ⟨hone, -, -, hk'⟩ := Delivery.shape?_single hsh
    rw [hone, List.mem_singleton, Prod.mk.injEq] at hjc
    obtain ⟨rfl, rfl⟩ := hjc
    exact single_deliveries_sub hT cov hwT hcj hk' hin d hd
  | stream j' c' =>
    obtain ⟨hone, -, -, -⟩ := Delivery.shape?_stream hsh
    rw [hone, List.mem_singleton, Prod.mk.injEq] at hjc
    obtain ⟨rfl, rfl⟩ := hjc
    exact (Delivery.mem_deliveriesOn.mp (hin.2.mem_iff.mpr hd)).1
  | merge cs =>
    obtain ⟨hcs, hks⟩ := hmerge cs rfl
    have hjc' : (j, c) ∈ cs := hcs ▸ hjc
    exact single_deliveries_sub hT cov hwT hcj (hks (j, c) hjc') (hin (j, c) hjc') d hd

end CoversCloseAux

end Suimon.Round3
