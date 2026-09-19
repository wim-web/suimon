import Suimon.Theorems.Effects1

/-! Exact effects of each operation (part 2: stream controls, containers, skip, retry). -/

namespace Suimon
open Effects

/-- Instances after a stream-control operation: unchanged, or a fresh waiting controller. -/
def ControllerInstances (s next : State) (path : Path) (n : Node) : Prop :=
  (∃ old, s.nodeInstance? path n.id = some old ∧ next.instances = s.instances) ∨
    (s.nodeInstance? path n.id = none ∧ next.instances = s.instances ++ [makeInstance path n .waitingInputs])

theorem effect_fireFilter (s next : State) (path : Path) (node : NodeId) (item : ItemId) (keep : Bool)
    (distinct : (s.channels.map (·.id)).Nodup)
    (h : transition s (.fireFilter path node item keep) = .ok next) :
    ∃ n c, getNode s path node = .ok n ∧ n.kind = .filter ∧ (s.incoming path node).head? = some c ∧
      c.pending.head? = some (.item item) ∧ ControllerInstances s next path n ∧ next.frames = s.frames ∧
      next.consumed = s.consumed ++ [{ channel := c.id, index := c.consumed, item, byInstance := instanceId path node }] ∧
      ((keep = true ∧ ∃ p0, n.outputs.head? = some p0 ∧
          next.placedView = (applyWrites [.out path node p0.name (.item item)] s).placedView) ∨
        (keep = false ∧ next.placedView = s.placedView)) := by
  simp only [transition, Option.toExcept, bind, Except.bind, pure, Except.pure] at h
  cases hn : getNode s path node with
  | error e => simp [hn] at h
  | ok n =>
    simp only [hn] at h
    split at h
    · rename_i kind
      cases hc : (s.incoming path node).head? with
      | none => simp [hc] at h
      | some c =>
        simp only [hc] at h
        split at h
        · contradiction
        · rename_i s1 controlled
          obtain ⟨ch1, fr1, co1, _, inst1⟩ := streamController_value s s1 path n controlled
          split at h
          · contradiction
          · rename_i s2 decided
            obtain ⟨ch2, in2, fr2, co2, _⟩ := decision_value s1 s2 _ _ decided
            split at h
            · contradiction
            · rename_i s3 consumed
              obtain ⟨v3, in3, fr3, _, _⟩ := consume_effect s2 s3 c.id _ (some item) consumed
              obtain ⟨c', memberC', idC', headC', log⟩ := consume_item_receipt s2 s3 c.id _ item consumed
              have memberC : c ∈ s.channels := (List.mem_filter.mp (List.mem_of_mem_head? hc)).1
              have sameC : c' = c := by
                have memberC'' : c' ∈ s.channels := by rw [ch2, ch1] at memberC'; exact memberC'
                exact eq_of_mapped_nodup (·.id) s.channels distinct c' c memberC'' memberC idC'
              rw [sameC] at headC' log
              have base : ∀ s4 : State, s4.instances = s3.instances → s4.frames = s3.frames → s4.consumed = s3.consumed →
                  ControllerInstances s s4 path n ∧ s4.frames = s.frames ∧
                  s4.consumed = s.consumed ++ [{ channel := c.id, index := c.consumed, item, byInstance := instanceId path node }] := by
                intro s4 i4 f4 c4
                refine ⟨?_, by rw [f4, fr3, fr2, fr1], by rw [c4, log, co2, co1]⟩
                rcases inst1 with ⟨old, foundOld, same⟩ | ⟨none, fresh⟩
                · exact .inl ⟨old, foundOld, by rw [i4, in3, in2, same]⟩
                · exact .inr ⟨none, by rw [i4, in3, in2, fresh]⟩
              have view : s3.placedView = s.placedView := by
                rw [v3]; simp only [State.placedView, ch2, ch1]
              split at h
              · rename_i keepTrue
                cases hp : n.outputs.head? with
                | none => simp [hp] at h
                | some p0 =>
                  simp only [hp] at h
                  have value := putOutput_value s3 next _ _ _ _ h
                  subst value
                  obtain ⟨inst, fr, co⟩ := base _ rfl rfl rfl
                  refine ⟨n, c, rfl, kind, rfl, headC', inst, fr, co, .inl ⟨keepTrue, p0, hp, ?_⟩⟩
                  simp only [applyWrites_cons, applyWrites_nil, applyWrite_out]
                  exact applyWrite_placedView s3 s (.out path node p0.name (.item item)) view
              · rename_i keepFalse
                simp only [Except.ok.injEq] at h
                subst h
                obtain ⟨inst, fr, co⟩ := base _ rfl rfl rfl
                exact ⟨n, c, rfl, kind, rfl, headC', inst, fr, co, .inr ⟨by simpa using keepFalse, view⟩⟩
    · contradiction

theorem effect_fireMerge (s next : State) (path : Path) (node : NodeId) (edge : String) (item : ItemId)
    (distinct : (s.channels.map (·.id)).Nodup)
    (h : transition s (.fireMerge path node edge item) = .ok next) :
    ∃ n c p0, getNode s path node = .ok n ∧ n.kind = .merge ∧ c ∈ s.incoming path node ∧ c.id = edge ∧
      c.pending.head? = some (.item item) ∧ n.outputs.head? = some p0 ∧
      ControllerInstances s next path n ∧ next.frames = s.frames ∧
      next.consumed = s.consumed ++ [{ channel := edge, index := c.consumed, item, byInstance := instanceId path node }] ∧
      next.placedView = (applyWrites [.out path node p0.name (.item (derivedItem "merge" path node [edge, item]))] s).placedView := by
  simp only [transition, Option.toExcept, bind, Except.bind, pure, Except.pure] at h
  cases hn : getNode s path node with
  | error e => simp [hn] at h
  | ok n =>
    simp only [hn] at h
    split at h
    · rename_i kind
      split at h
      · contradiction
      · rename_i u hr
        have cond := require_ok _ _ _ u hr
        obtain ⟨c0, memberC0, idC0⟩ := List.any_eq_true.mp cond
        split at h
        · contradiction
        · rename_i s1 controlled
          obtain ⟨ch1, fr1, co1, _, inst1⟩ := streamController_value s s1 path n controlled
          split at h
          · contradiction
          · rename_i s2 consumed
            obtain ⟨v2, in2, fr2, _, _⟩ := consume_effect s1 s2 edge _ (some item) consumed
            obtain ⟨c', memberC', idC', headC', log⟩ := consume_item_receipt s1 s2 edge _ item consumed
            have memberC0' : c0 ∈ s.channels := (List.mem_filter.mp memberC0).1
            have sameC : c' = c0 := by
              have memberC'' : c' ∈ s.channels := by rw [ch1] at memberC'; exact memberC'
              exact eq_of_mapped_nodup (·.id) s.channels distinct c' c0 memberC'' memberC0' (idC'.trans (beq_iff_eq.mp idC0).symm)
            rw [sameC] at headC' log
            cases hp : n.outputs.head? with
            | none => simp [hp] at h
            | some p0 =>
              simp only [hp] at h
              have value := putOutput_value s2 next _ _ _ _ h
              subst value
              refine ⟨n, c0, p0, rfl, kind, memberC0, beq_iff_eq.mp idC0, headC', hp, ?_, ?_, ?_, ?_⟩
              · rcases inst1 with ⟨old, foundOld, same⟩ | ⟨none, fresh⟩
                · exact .inl ⟨old, foundOld, by simp only [Effects.output, write, in2, same]⟩
                · exact .inr ⟨none, by simp only [Effects.output, write, in2, fresh]⟩
              · simp only [Effects.output, write, fr2, fr1]
              · simp only [Effects.output, write, log, co1]
              · simp only [applyWrites_cons, applyWrites_nil, applyWrite_out]
                have step1 := applyWrite_placedView s2 s1 (.out path node p0.name (.item (derivedItem "merge" path node [edge, item]))) v2
                have step2 := applyWrite_placedView s1 s (.out path node p0.name (.item (derivedItem "merge" path node [edge, item])))
                  (by simp only [State.placedView, ch1])
                exact step1.trans step2
    · contradiction

theorem effect_propagateEos (s next : State) (path : Path) (node : NodeId)
    (h : transition s (.propagateEos path node) = .ok next) :
    ∃ n, getNode s path node = .ok n ∧
      (match n.kind with | .filter | .merge | .forEach _ => true | _ => false) = true ∧
      (s.incoming path node).all (fun c => c.closed && c.pendingItems.isEmpty) = true ∧
      (s.instances.filter (fun i => i.path == path && i.node == node && i.trigger.isSome)).all (·.status == .succeeded) = true ∧
      ((s.nodeInstance? path node = none ∧ next.instances = s.instances ++ [makeInstance path n .succeeded]) ∨
        (∃ old, s.nodeInstance? path node = some old ∧ old.status = .waitingInputs ∧
          next.instances = (setInstance s { old with status := .succeeded }).instances)) ∧
      next.frames = s.frames ∧ RecordsBy s next (instanceId path node) ((s.incoming path node).map (·.id)) ∧
      next.placedView = (applyWrites (eosWrites path n) s).placedView := by
  simp only [transition, Option.toExcept, bind, Except.bind, pure, Except.pure] at h
  cases hn : getNode s path node with
  | error e => simp [hn] at h
  | ok n =>
    simp only [hn] at h
    split at h
    · contradiction
    · rename_i u1 hk
      have kind := require_ok _ _ _ u1 hk
      split at h
      · contradiction
      · rename_i u2 hd
        have drained := require_ok _ _ _ u2 hd
        split at h
        · contradiction
        · rename_i u3 hch
          have children := require_ok _ _ _ u3 hch
          -- controller instance
          have finish : ∀ s1 s2 : State, s1.channels = s.channels → s1.frames = s.frames → s1.consumed = s.consumed →
              consumeChannels s1 (s.incoming path node) (makeInstance path n .succeeded).id = .ok s2 →
              closeOutputs s2 path n = .ok next →
              next.frames = s.frames ∧ RecordsBy s next (instanceId path node) ((s.incoming path node).map (·.id)) ∧
              next.placedView = (applyWrites (eosWrites path n) s).placedView ∧ next.instances = s1.instances := by
            intro s1 s2 ch1 fr1 co1 consumed rest
            · obtain ⟨v2, in2, fr2, _, rs, log, all⟩ := consumeChannels_effect s1 s2 _ _ consumed
              have closed := closeOutputs_writes s2 next path n rest
              subst closed
              refine ⟨by rw [applyWrites_frames, fr2, fr1], ⟨rs, by rw [applyWrites_consumed, log, co1], ?_⟩, ?_, by rw [applyWrites_instances, in2]⟩
              · intro r hr
                have := all r hr
                simpa [makeInstance, getNode_id s path node n hn] using this
              · apply applyWrites_placedView
                rw [v2]; simp only [State.placedView, ch1]
          cases found : s.nodeInstance? path node with
          | none =>
            simp only [found] at h
            split at h
            · contradiction
            · rename_i s1 created
              have value := freshInstance_value s s1 _ created
              subst value
              split at h
              · contradiction
              · rename_i s2 consumed
                obtain ⟨fr, rec, view, inst⟩ := finish { s with instances := s.instances ++ [makeInstance path n .succeeded] } s2 rfl rfl rfl consumed h
                exact ⟨n, rfl, kind, drained, children, .inl ⟨rfl, inst⟩, fr, rec, view⟩
          | some old =>
            simp only [found] at h
            split at h
            · contradiction
            · rename_i u4 hw
              have waiting := require_ok _ _ _ u4 hw
              split at h
              · contradiction
              · rename_i s2 consumed
                obtain ⟨fr, rec, view, inst⟩ := finish (setInstance s { old with status := .succeeded }) s2 rfl rfl rfl consumed h
                exact ⟨n, rfl, kind, drained, children, .inr ⟨old, rfl, beq_iff_eq.mp waiting, inst⟩, fr, rec, view⟩


/-! ### Containers -/

theorem kind_sub_or_forEach (n : Node)
    (h : (match n.kind with | .subworkflow _ | .forEach _ => true | _ => false) = true) :
    (∃ b, n.kind = .subworkflow b) ∨ (∃ b, n.kind = .forEach b) := by
  cases hk : n.kind <;> simp [hk] at h <;> simp [hk]

theorem setInstance_instances_congr (a b : State) (j : Instance) (same : a.instances = b.instances) :
    (setInstance a j).instances = (setInstance b j).instances := by
  simp only [setInstance, same]

/-- Exit channels of frame `f` as they are in `s`. -/
def exitIds (s : State) (f : Frame) : List String :=
  (s.channels.filter (fun c => c.path == f.path && c.exit)).map (·.id)

def closeFrames (frames : List Frame) (path : Path) : List Frame :=
  frames.map (fun g => if g.path == path then { g with closed := true } else g)

theorem effect_finishSubworkflow (s next : State) (inst : InstanceId)
    (h : transition s (.finishSubworkflow inst) = .ok next) :
    ∃ i n f items, s.instance? inst = some i ∧ i.status = .waitingInputs ∧ getNode s i.path i.node = .ok n ∧
      currentFrame s i = .ok f ∧ bodyResults s f = .ok items ∧ n.outputs.length = items.length ∧
      next.frames = closeFrames s.frames f.path ∧ RecordsBy s next i.id (exitIds s f) ∧
      next.instances = (setInstance s { i with status := .succeeded }).instances ∧
      ((∃ body, n.kind = .subworkflow body ∧
          next.placedView = (applyWrites (bodyWrites i.path n items ++ eosWrites i.path n) s).placedView) ∨
        (∃ body, n.kind = .forEach body ∧
          next.placedView = (applyWrites (bodyWrites i.path n items) s).placedView)) := by
  simp only [transition, getInstance, Option.toExcept, bind, Except.bind, pure, Except.pure] at h
  cases found : s.instance? inst with
  | none => simp [found] at h
  | some i =>
    simp only [found] at h
    split at h
    · contradiction
    · rename_i u1 hw
      have waiting := require_ok _ _ _ u1 hw
      cases hn : getNode s i.path i.node with
      | error e => simp [hn] at h
      | ok n =>
        simp only [hn] at h
        split at h
        · contradiction
        · rename_i u2 hk
          have kind := require_ok _ _ _ u2 hk
          cases hf : currentFrame s i with
          | error e => simp [hf] at h
          | ok f =>
            simp only [hf] at h
            cases hb : bodyResults s f with
            | error e => simp [hb] at h
            | ok items =>
              simp only [hb] at h
              split at h
              · contradiction
              · rename_i u3 ha
                have arity := require_ok _ _ _ u3 ha
                split at h
                · contradiction
                · rename_i s1 closed
                  obtain ⟨⟨v1, in1, _, _, rs, log, all⟩, frames1⟩ := closeFrame_effect s s1 f i.id closed
                  split at h
                  · contradiction
                  · rename_i s2 placed
                    have p2 := placeBodyOutputs_writes s1 s2 _ _ _ placed
                    subst p2
                    have common : ∀ s4 : State, s4.frames = s1.frames → s4.consumed = s1.consumed →
                        s4.instances = (setInstance (applyWrites (bodyWrites i.path n items) s1) { i with status := .succeeded }).instances →
                        next.frames = s4.frames → next.consumed = s4.consumed → next.instances = s4.instances →
                        next.frames = closeFrames s.frames f.path ∧ RecordsBy s next i.id (exitIds s f) ∧
                        next.instances = (setInstance s { i with status := .succeeded }).instances := by
                      intro s4 f4 c4 i4 nf nc ni
                      refine ⟨by rw [nf, f4, frames1]; rfl, ⟨rs, by rw [nc, c4]; exact log, all⟩, ?_⟩
                      rw [ni, i4]
                      exact setInstance_instances_congr _ _ _ (by rw [applyWrites_instances]; exact in1)
                    have baseView : (setInstance (applyWrites (bodyWrites i.path n items) s1) { i with status := .succeeded }).placedView =
                        (applyWrites (bodyWrites i.path n items) s).placedView := by
                      show (applyWrites (bodyWrites i.path n items) s1).placedView = _
                      exact applyWrites_placedView _ _ _ v1
                    split at h
                    · rename_i body kindEq
                      have p3 := closeOutputs_writes _ next _ _ h
                      subst p3
                      obtain ⟨fr, rec, inst⟩ := common _ (by simp only [applyWrites_frames, setInstance]) (by simp only [applyWrites_consumed, setInstance])
                        rfl (applyWrites_frames _ _) (applyWrites_consumed _ _) (applyWrites_instances _ _)
                      refine ⟨i, n, f, items, rfl, beq_iff_eq.mp waiting, hn, hf, hb, beq_iff_eq.mp arity, fr, rec, inst, .inl ⟨body, kindEq, ?_⟩⟩
                      rw [applyWrites_append]
                      exact applyWrites_placedView _ _ _ baseView
                    · rename_i notSub
                      simp only [Except.ok.injEq] at h
                      subst h
                      obtain ⟨fr, rec, inst⟩ := common _ (by simp only [applyWrites_frames, setInstance]) (by simp only [applyWrites_consumed, setInstance]) rfl rfl rfl rfl
                      rcases kind_sub_or_forEach n kind with ⟨body, isSub⟩ | ⟨body, isFor⟩
                      · exact absurd isSub (notSub body)
                      · exact ⟨i, n, f, items, rfl, beq_iff_eq.mp waiting, hn, hf, hb, beq_iff_eq.mp arity, fr, rec, inst, .inr ⟨body, isFor, baseView⟩⟩

theorem effect_loopIterate (s next : State) (inst : InstanceId) (done : Bool)
    (h : transition s (.loopIterate inst done) = .ok next) :
    ∃ i n body limit f items item, s.instance? inst = some i ∧ i.status = .waitingInputs ∧
      getNode s i.path i.node = .ok n ∧ n.kind = .loop body limit ∧ currentFrame s i = .ok f ∧
      bodyResults s f = .ok items ∧ items.head? = some item ∧ RecordsBy s next i.id (exitIds s f) ∧
      ((done = true ∧ ∃ p0, n.outputs.head? = some p0 ∧
          next.placedView = (applyWrites (.out i.path n.id p0.name (.item item) :: eosWrites i.path n) s).placedView ∧
          next.instances = (setInstance s { i with status := .succeeded }).instances ∧
          next.frames = closeFrames s.frames f.path) ∨
        (done = false ∧ i.iteration ≥ limit + i.extraIterations ∧ next.placedView = s.placedView ∧
          next.instances = (setInstance s { i with status := .failed }).instances ∧
          next.frames = closeFrames s.frames f.path ∧ next.status = .blocked) ∨
        (done = false ∧ i.iteration < limit + i.extraIterations ∧
          let i' := { i with iteration := i.iteration + 1 }
          ∃ f', OpenedFrame i' body f' ∧ (∀ g ∈ s.frames, g.path ≠ f'.path) ∧ 1 = body.entries.length ∧
            next.placedView = (applyWrites (seedWrites f'.path body.entries [item])
              { s with channels := s.channels ++ f'.channels }).placedView ∧
            next.instances = (setInstance s i').instances ∧
            next.frames = closeFrames s.frames f.path ++ [f'])) := by
  simp only [transition, getInstance, Option.toExcept, bind, Except.bind, pure, Except.pure] at h
  cases found : s.instance? inst with
  | none => simp [found] at h
  | some i =>
    simp only [found] at h
    split at h
    · contradiction
    · rename_i u1 hw
      have waiting := require_ok _ _ _ u1 hw
      cases hn : getNode s i.path i.node with
      | error e => simp [hn] at h
      | ok n =>
        simp only [hn] at h
        split at h
        · rename_i body limit kind
          cases hf : currentFrame s i with
          | error e => simp [hf] at h
          | ok f =>
            simp only [hf] at h
            cases hb : bodyResults s f with
            | error e => simp [hb] at h
            | ok items =>
              simp only [hb] at h
              cases hi : items.head? with
              | none => simp [hi] at h
              | some item =>
                simp only [hi] at h
                split at h
                · contradiction
                · rename_i s1 decided
                  obtain ⟨ch1, in1, fr1, co1, _⟩ := decision_value s s1 _ _ decided
                  split at h
                  · contradiction
                  · rename_i s2 closed
                    obtain ⟨⟨v2, in2, _, _, rs, log, all⟩, frames2⟩ := closeFrame_effect s1 s2 f i.id closed
                    have view2 : s2.placedView = s.placedView := by
                      have : ({ s2 with frames := s1.frames } : State).placedView = s2.placedView := rfl
                      rw [← this, v2]; simp only [State.placedView, ch1]
                    have frames2' : s2.frames = closeFrames s.frames f.path := by rw [frames2, fr1]; rfl
                    have records : ∀ s4 : State, s4.consumed = s2.consumed → RecordsBy s s4 i.id (exitIds s f) := by
                      intro s4 c4
                      refine ⟨rs, by rw [c4]; exact log.trans (by rw [co1]), ?_⟩
                      intro r hr
                      have := all r hr
                      simpa [exitIds, ch1] using this
                    have inst2 : s2.instances = s.instances := by rw [in2, in1]
                    split at h
                    · rename_i isDone
                      cases hp : n.outputs.head? with
                      | none => simp [hp] at h
                      | some p0 =>
                        simp only [hp] at h
                        split at h
                        · contradiction
                        · rename_i s3 placed
                          have p3 := putOutput_value s2 s3 _ _ _ _ placed
                          subst p3
                          split at h
                          · contradiction
                          · rename_i s4 closedOut
                            have p4 := closeOutputs_writes _ s4 _ _ closedOut
                            subst p4
                            simp only [Except.ok.injEq] at h
                            subst h
                            refine ⟨i, n, body, limit, f, items, item, rfl, beq_iff_eq.mp waiting, hn, kind, hf, hb, hi,
                              records _ (by simp only [setInstance, applyWrites_consumed, Effects.output, write]), .inl ⟨isDone, p0, hp, ?_, ?_, ?_⟩⟩
                            · show (applyWrites (eosWrites i.path n) (output s2 i.path n.id p0.name (.item item))).placedView = _
                              simp only [applyWrites_cons, applyWrite_out]
                              apply applyWrites_placedView
                              exact applyWrite_placedView s2 s (.out i.path n.id p0.name (.item item)) view2
                            · simp only [setInstance, applyWrites_instances, Effects.output, write, inst2]
                            · simp only [setInstance, applyWrites_frames, Effects.output, write, frames2']
                    · rename_i notDone
                      split at h
                      · rename_i limitHit
                        simp only [Except.ok.injEq] at h
                        subst h
                        refine ⟨i, n, body, limit, f, items, item, rfl, beq_iff_eq.mp waiting, hn, kind, hf, hb, hi,
                          records _ rfl, .inr (.inl ⟨by simpa using notDone, limitHit, view2, ?_, frames2', rfl⟩)⟩
                        simp only [setInstance, inst2]
                      · rename_i limitFree
                        obtain ⟨none, arity, view, frames, instances, consumedEq, _⟩ :=
                          addFrame_effect _ next _ body [item] h
                        refine ⟨i, n, body, limit, f, items, item, rfl, beq_iff_eq.mp waiting, hn, kind, hf, hb, hi,
                          records _ (by rw [consumedEq]; rfl), .inr (.inr ⟨by simpa using notDone, by omega,
                            childFrame (setInstance s2 { i with iteration := i.iteration + 1 }) { i with iteration := i.iteration + 1 } body,
                            childFrame_opened _ _ body, ?_, arity, ?_, ?_, ?_⟩)⟩
                        · intro g hg eq
                          unfold State.frame? at none
                          have all := List.find?_eq_none.mp none
                          have memberG : (if g.path == f.path then { g with closed := true } else g) ∈
                              (setInstance s2 { i with iteration := i.iteration + 1 }).frames := by
                            simp only [setInstance, frames2', closeFrames]
                            exact List.mem_map.mpr ⟨g, hg, rfl⟩
                          have pathG : (if g.path == f.path then { g with closed := true } else g : Frame).path = g.path := by
                            split <;> rfl
                          apply all _ memberG
                          rw [pathG]
                          exact beq_iff_eq.mpr eq
                        · rw [view]
                          exact applyWrites_placedView _ _ _ (by simp only [State.placedView, setInstance, List.map_append]; rw [show s2.channels.map Channel.core = s.channels.map Channel.core from view2])
                        · rw [instances]
                          exact setInstance_instances_congr _ _ _ inst2
                        · rw [frames]
                          simp only [setInstance, frames2']
        · contradiction


/-! ### Skip, manual retry, idle, cancel -/

theorem effect_skip (s next : State) (path : Path) (node : NodeId)
    (h : transition s (.skip path node) = .ok next) :
    ∃ n, getNode s path node = .ok n ∧
      (allKind n.inputs .plain && (match n.kind with
        | .coalesce => !(s.incoming path node).isEmpty && (s.incoming path node).all (fun c => c.closed && c.items.isEmpty)
        | _ => (s.incoming path node).any (fun c => c.closed && c.items.isEmpty))) = true ∧
      (s.incoming path node).all (·.closed) = true ∧
      (∀ j ∈ s.instances, ¬ (j.path = path ∧ j.node = node)) ∧
      let i := makeInstance path n .cancelled
      next.instances = s.instances ++ [i] ∧ next.frames = s.frames ∧
      RecordsBy s next i.id ((s.incoming path node).map (·.id)) ∧
      next.placedView = (applyWrites (eosWrites path n) s).placedView := by
  simp only [transition, Option.toExcept, bind, Except.bind, pure, Except.pure] at h
  cases hn : getNode s path node with
  | error e => simp [hn] at h
  | ok n =>
    simp only [hn] at h
    split at h
    · contradiction
    · rename_i u1 h1
      have absent := require_ok _ _ _ u1 h1
      split at h
      · contradiction
      · rename_i u2 h2
        have closed := require_ok _ _ _ u2 h2
        split at h
        · contradiction
        · rename_i u3 h3
          have fresh := require_ok _ _ _ u3 h3
          have noInstance : ∀ j ∈ s.instances, ¬ (j.path = path ∧ j.node = node) := by
            intro j hj ⟨hp, hnode⟩
            simp only [Bool.not_eq_true', List.any_eq_false] at fresh
            have := fresh j hj
            simp [hp, hnode] at this
          split at h
          · contradiction
          · rename_i s1 created
            have value := freshInstance_value s s1 _ created
            subst value
            split at h
            · contradiction
            · rename_i s2 consumed
              obtain ⟨v, inst, fr, _, rs, log, all⟩ := consumeInputs_effect _ s2 path node _ consumed
              have p := closeOutputs_writes s2 next path n h
              subst p
              refine ⟨n, rfl, absent, closed, noInstance, ?_, ?_, ⟨rs, ?_, ?_⟩, ?_⟩
              · rw [applyWrites_instances, inst]
              · rw [applyWrites_frames, fr]
              · rw [applyWrites_consumed, log]
              · intro r hr; simpa [State.incoming] using all r hr
              · exact applyWrites_placedView _ _ _ (by simpa [State.placedView] using v)

theorem effect_manualRetry (s next : State) (inst : InstanceId)
    (h : transition s (.manualRetry inst) = .ok next) :
    ∃ i n, s.instance? inst = some i ∧ i.status = .failed ∧ getNode s i.path i.node = .ok n ∧
      ((∃ r c, n.kind = .leaf r c ∧ AdminEffect s next ∧
          next.instances = (setInstance s { i with status := .retryWait, extraAttempts := i.extraAttempts + 1, retryAt := some s.now }).instances) ∨
       (∃ body limit f items, n.kind = .loop body limit ∧ currentFrame s i = .ok f ∧ f.closed = true ∧
          frameOutputItems s f = .ok items ∧
          let i' := { i with status := .waitingInputs, extraIterations := i.extraIterations + 1, iteration := i.iteration + 1 }
          ∃ f', OpenedFrame i' body f' ∧ (∀ g ∈ s.frames, g.path ≠ f'.path) ∧ items.length = body.entries.length ∧
            next.placedView = (applyWrites (seedWrites f'.path body.entries items)
              { s with channels := s.channels ++ f'.channels }).placedView ∧
            next.instances = (setInstance s i').instances ∧ next.frames = s.frames ++ [f'] ∧
            next.consumed = s.consumed)) := by
  simp only [transition, getInstance, Option.toExcept, bind, Except.bind, pure, Except.pure] at h
  cases found : s.instance? inst with
  | none => simp [found] at h
  | some i =>
    simp only [found] at h
    cases hn : getNode s i.path i.node with
    | error e => simp [hn] at h
    | ok n =>
      simp only [hn] at h
      split at h
      · contradiction
      · rename_i u1 hf
        have failed := require_ok _ _ _ u1 hf
        split at h
        · rename_i r c kind
          simp only [Except.ok.injEq] at h
          subst h
          refine ⟨i, n, rfl, beq_iff_eq.mp failed, hn, .inl ⟨r, c, kind, ⟨rfl, rfl, rfl, ?_⟩, rfl⟩⟩
          exact noNewSuccess_setInstance s i _ (instance?_mem found) rfl (fun done => by simp at done)
        · rename_i body limit kind
          cases hcf : currentFrame s i with
          | error e => simp [hcf] at h
          | ok f =>
            simp only [hcf] at h
            split at h
            · contradiction
            · rename_i u2 hc
              have closed := require_ok _ _ _ u2 hc
              cases hi : frameOutputItems s f with
              | error e => simp [hi] at h
              | ok items =>
                simp only [hi] at h
                split at h
                · contradiction
                · rename_i s1 added
                  obtain ⟨none, arity, view, frames, instances, consumedEq, _⟩ := addFrame_effect _ s1 _ body items added
                  simp only [Except.ok.injEq] at h
                  subst h
                  refine ⟨i, n, rfl, beq_iff_eq.mp failed, hn, .inr ⟨body, limit, f, items, kind, hcf, closed, hi,
                    childFrame (setInstance s { i with status := .waitingInputs, extraIterations := i.extraIterations + 1, iteration := i.iteration + 1 })
                      { i with status := .waitingInputs, extraIterations := i.extraIterations + 1, iteration := i.iteration + 1 } body,
                    childFrame_opened _ _ body, ?_, arity, ?_, ?_, ?_, ?_⟩⟩
                  · intro g hg eq
                    unfold State.frame? at none
                    have all := List.find?_eq_none.mp none
                    apply all g (by simpa [setInstance] using hg)
                    simp [eq]
                  · show s1.placedView = _
                    rw [view]
                    exact applyWrites_placedView _ _ _ rfl
                  · show s1.instances = _
                    rw [instances]
                  · show s1.frames = _
                    rw [frames]
                    rfl
                  · show s1.consumed = _
                    rw [consumedEq]
                    rfl
        · contradiction

theorem effect_idle (s next : State) (h : transition s .idle = .ok next) : next = s := by
  simp only [transition, pure, Except.pure, Except.ok.injEq] at h
  exact h.symm

theorem effect_cancel (s next : State) (h : transition s .cancel = .ok next) :
    next.channels = s.channels ∧ next.frames = s.frames ∧ next.consumed = s.consumed ∧ next.status = .cancelled := by
  simp only [transition, pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨rfl, rfl, rfl, rfl⟩

end Suimon
