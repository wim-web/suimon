import Suimon.Theorems.DeliveryChange

/-! Every step keeps the ownership invariant `Own`. -/

namespace Suimon.Delivery
open State

theorem runs_nil_or_started {p : Definition} {s : State} (inv : Inv p s) : s.runs = [] ∨ s.started = true := by
  cases h : s.started
  · rw [inv.fresh h]; exact Or.inl rfl
  · exact Or.inr rfl

theorem Inv.kept {p : Definition} {s t : State} {op : Op} (inv : Inv p s) (hs : step p s op = .ok t) : Kept s t :=
  step_kept inv.wk (runs_nil_or_started inv) hs

/-- A delivered value on a Single connection stays its resolution. --/
theorem resolveSingle_value_kept {s t : State} (g : s.Grows t) {path : Path} {j : Nat} {c : Connection}
    {src : ResultId} {inp : Option Value} (h : s.resolveSingle path j c = .value src inp) :
    t.resolveSingle path j c = .value src inp := by
  rw [resolveSingle_stable g (by rw [h]; simp) (fun hnil => by
    obtain ⟨d, rest, hd, -⟩ := resolveSingle_value_iff.mp h
    rw [hd] at hnil; cases hnil), h]

theorem triggerOk_kept {s t : State} (g : s.Grows t) {path : Path} {i i' : Invocation} {sh : Workflow.Shape}
    (htr : i'.trigger = i.trigger) (h : TriggerOk s path i sh) : TriggerOk t path i' sh := by
  cases sh with
  | none => exact htr.trans h
  | entry => exact htr.trans h
  | single j c =>
    obtain ⟨src, inp, hres, htrig⟩ := h
    exact ⟨src, inp, resolveSingle_value_kept g hres, htr.trans htrig⟩
  | stream j c =>
    obtain ⟨src, d, htrig, hd, hout⟩ := h
    exact ⟨src, d, htr.trans htrig, g.delivery?_eq_some hd, hout⟩
  | merge cs => exact h.elim

theorem triggerOk_of_input {p : Definition} {s : State} {r : Run} {w : Workflow} {name : String}
    {trigger : Option ResultId} {input : Option Value} {i : Invocation} (hrun : r.path = i.run)
    (htr : i.trigger = trigger) (h : Step.invocationInput p s r w name trigger = .ok input) :
    ∃ sh, w.shape? p name = some sh ∧ TriggerOk s i.run i sh := by
  rcases Step.invocationInput_inv h with ⟨hsh, htrig, -⟩ | ⟨hsh, htrig, -⟩ | ⟨j, c, src, hsh, htrig, hres⟩ |
      ⟨j, c, src, d, hsh, htrig, hd, hout⟩
  · exact ⟨_, hsh, htr.trans htrig⟩
  · exact ⟨_, hsh, htr.trans htrig⟩
  · exact ⟨_, hsh, src, input, hrun ▸ hres, htr.trans htrig⟩
  · refine ⟨_, hsh, src, d, htr.trans htrig, hrun ▸ hd, ?_⟩
    rcases hout with ⟨v, hv, -⟩ | ⟨hv, -⟩ <;> rw [hv] <;> simp

theorem exists_task_kept {e e' : Execution} {name : String} (hnames : e'.tasks.map (·.name) = e.tasks.map (·.name))
    (h : ∃ tk ∈ e.tasks, tk.name = name) : ∃ tk ∈ e'.tasks, tk.name = name := by
  obtain ⟨tk, htk, rfl⟩ := h
  have : tk.name ∈ e'.tasks.map (·.name) := hnames ▸ List.mem_map_of_mem htk
  obtain ⟨tk', htk', h⟩ := List.mem_map.mp this
  exact ⟨tk', htk', h⟩

theorem exists_task_withTask {e : Execution} {name : String} {ts : TaskState} (hts : e.tasks.find? (·.name == name) = some ts)
    (st : TaskStatus) : ∃ tk ∈ (withTask e { ts with status := st }).tasks, tk.name = name :=
  exists_task_kept (Kept.withTask_names e _) ⟨ts, List.mem_of_find?_eq_some hts, find?_name_of_task hts⟩

open State in
/-- Every step keeps the ownership invariant. --/
theorem step_own {p : Definition} {s t : State} {op : Op} (inv : Inv p s) (hs : step p s op = .ok t) : Own p t := by
  have K := inv.kept hs
  have wk' := step_wellKeyed inv.wk hs
  have wf : ∀ {path w}, s.workflow? p path = some w → t.workflow? p path = some w := fun h => K.workflow? wk' h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- runs
    intro r hr
    rcases step_runs_back (runs_nil_or_started inv) hs r hr with ⟨r₀, hr₀, hpath, hwf, -, howner, htask, -⟩ | hnew
    · rcases inv.own.runs r₀ hr₀ with ⟨ho, ht, hp⟩ | ⟨ht, i, hi, ho, hp, w, pl, wf', out, hw, hpl, hc⟩ |
          ⟨name, ht, e, he, ho, hp, htk, spec, wf', out, hspec, hbody⟩
      · exact Or.inl ⟨howner ▸ ho, htask ▸ ht, hpath ▸ hp⟩
      · obtain ⟨i', hi', a1, a2, a3, -, -⟩ := K.invocation i hi
        refine Or.inr (Or.inl ⟨htask ▸ ht, i', hi', by rw [← howner, ho, a1], by rw [← hpath, hp, a1], w, pl, wf',
          out, by rw [a2]; exact wf hw, by rw [a3]; exact hpl, hc⟩)
      · obtain ⟨e', he', a1, a2, a3, a4, -⟩ := K.execution e he
        refine Or.inr (Or.inr ⟨name, htask ▸ ht, e', he', by rw [← howner, ho, a1], by rw [← hpath, hp, a1],
          exists_task_kept a4 htk, spec, wf', out, K.taskSpec wk' a2 a3 hspec, hbody⟩)
    · obtain ⟨-, -, hcase⟩ := hnew
      rcases hcase with ⟨-, ho, ht, hp⟩ | ⟨ht, i, hi, ho, hnewi, hp, w, pl, wf', out, hw, hpl, hc⟩ |
          ⟨name, e, ts, spec, wf', out, ht, ho, he, -, hts, -, hspec, hbody, hp, hmem, -⟩
      · exact Or.inl ⟨ho, ht, hp⟩
      · exact Or.inr (Or.inl ⟨ht, i, hi, ho, hp, w, pl, wf', out, wf hw, hpl, hc⟩)
      · refine Or.inr (Or.inr ⟨name, ht, _, hmem, ho, hp, exists_task_withTask hts _, spec, wf', out, ?_, hbody⟩)
        exact K.taskSpec wk' rfl rfl hspec
  · -- invocations
    intro i hi
    rcases step_invocations_back hs i hi with ⟨i₀, hi₀, hid, hrun, hpl, htr, -⟩ | hnew
    · obtain ⟨hkey, w, pl, sh, hw, hplc, hinvc, hsh, htrig, harm⟩ := inv.own.invocations i₀ hi₀
      refine ⟨by rw [← hid, hkey, hrun, hpl, htr], w, pl, sh, by rw [← hrun]; exact wf hw, by rw [← hpl]; exact hplc,
        hinvc, by rw [← hpl]; exact hsh, by rw [← hrun]; exact triggerOk_kept K.grows htr.symm htrig, ?_⟩
      rcases step_invocation_change inv.wk hs hi₀ hi hid.symm with rfl | ⟨-, -, -, -, -, hc⟩
      · exact harm
      · rcases hc with ⟨-, -, -, -, -, -, ha | hbr⟩ | ⟨-, -, -, -, ha, -⟩ | ⟨-, -, -, -, -, ha, -⟩ | ⟨-, ha, -⟩
        · exact ha ▸ harm
        · obtain ⟨j, arms, w', pl', hw', hpl', hb⟩ := hbr
          rw [hw] at hw'; cases hw'
          rw [hplc] at hpl'; cases hpl'
          exact Or.inr ⟨j, arms, hb⟩
        · exact ha ▸ harm
        · exact ha ▸ harm
        · exact ha ▸ harm
    · obtain ⟨-, -, r, w, pl, hr, -, hw, hpl, hinvc, hinput, hkey, -, harm, -, -⟩ := hnew
      obtain ⟨sh, hsh, htrig⟩ := triggerOk_of_input (run?_eq_some hr).2 rfl hinput
      exact ⟨hkey, w, pl, sh, wf (workflow?_iff.mpr ⟨r, hr, hw⟩), hpl, hinvc, hsh,
        triggerOk_kept K.grows rfl htrig, Or.inl harm⟩
  · -- calls
    intro c hc
    rcases step_calls_back hs c hc with ⟨c₀, hc₀, hid, howner, htask, htarget, hstream, -⟩ | hnew
    · rcases inv.own.calls c₀ hc₀ with ⟨ht, hco, i, hi, hio, w, pl, hw, hpl, hk⟩ |
          ⟨name, ht, hkey, e, he, heo, htk, spec, f, hspec, hbody⟩
      · obtain ⟨i', hi', a1, a2, a3, -, -⟩ := K.invocation i hi
        refine Or.inl ⟨htask ▸ ht, by rw [← hid, hco, howner], i', hi', by rw [a1, hio, howner], w, pl,
          by rw [a2]; exact wf hw, by rw [a3]; exact hpl, ?_⟩
        rw [← htarget, ← hstream]
        exact hk
      · obtain ⟨e', he', a1, a2, a3, a4, -⟩ := K.execution e he
        exact Or.inr ⟨name, htask ▸ ht, by rw [← hid, hkey, howner], e', he', by rw [a1, heo, howner],
          exists_task_kept a4 htk, spec, f, K.taskSpec wk' a2 a3 hspec, hbody⟩
    · obtain ⟨-, -, hcase⟩ := hnew
      rcases hcase with ⟨ht, hco, i, hi, hio, -, w, pl, hw, hpl, hk⟩ |
          ⟨name, e, ts, spec, f, ht, hkey, he, -, hts, -, hspec, hbody, hmem, -⟩
      · exact Or.inl ⟨ht, hco, i, hi, hio, w, pl, wf hw, hpl, hk⟩
      · obtain ⟨-, heid⟩ := execution?_eq_some he
        exact Or.inr ⟨name, ht, hkey, _, hmem, heid, exists_task_withTask hts _, spec, f, K.taskSpec wk' rfl rfl hspec,
          hbody⟩
  · -- executions
    intro e he
    rcases step_executions_back hs e he with ⟨e₀, he₀, hid, hrun, hpl, -, -⟩ | hnew
    · obtain ⟨i, hi, hio, hir, hip, c, hc⟩ := inv.own.executions e₀ he₀
      obtain ⟨i', hi', a1, a2, a3, -, -⟩ := K.invocation i hi
      exact ⟨i', hi', by rw [a1, hio, hid], by rw [a2, hir, hrun], by rw [a3, hip, hpl], c,
        K.concurrencyOf wk' hrun.symm hpl.symm hc⟩
    · obtain ⟨-, -, i, hi, hio, hir, hip, -, w, pl, c, hw, hpl, hc, -, -⟩ := hnew
      exact ⟨i, hi, hio, hir, hip, c, concurrencyOf_iff.mpr ⟨w, pl, wf hw, hpl, hc⟩⟩
  · -- deliveries
    intro d hd
    rcases step_deliveries_back hs d hd with hd | ⟨-, -, -, w, c, r, hw, hc, hr, hrun, hpl, harm⟩
    · obtain ⟨w, c, r, hw, hc, hr, hid, hrun, hpl, harm⟩ := inv.own.deliveries d hd
      exact ⟨w, c, r, wf hw, hc, K.mem_results hr, hid, hrun, hpl, harm⟩
    · obtain ⟨hr, hid⟩ := result?_eq_some hr
      exact ⟨w, c, r, wf hw, hc, K.mem_results hr, hid, hrun, hpl, harm⟩

end Suimon.Delivery
