import Suimon.Theorems.Scoped
import Suimon.Theorems.ChannelLayout

/-! Plain control nodes: the values recorded by `plainInputs`, uniqueness of a node's
    instance, and the final contents of WaitAll / Branch / Collect outputs. -/

namespace Suimon
open Effects

/-- The head item of the input channel feeding `port` of node `N` in frame `P`. -/
def inputHead (s : State) (P : Path) (N : NodeId) (port : PortName) : ItemId :=
  match (s.incoming P N).find? (·.edge.dst.port == port) with
  | some c => match c.pending.head? with
    | some (.item id) => id
    | _ => ""
  | none => ""

/-- `plainInputs` records, per input port, the head item of the (closed) input channel. -/
theorem plainInputs_spec (s : State) (P : Path) (n : Node) (inputs : List (PortName × ItemId))
    (h : plainInputs s P n = .ok inputs) :
    inputs = n.inputs.map (fun p => (p.name, inputHead s P n.id p.name)) ∧
    ∀ p ∈ n.inputs, ∃ c ∈ s.incoming P n.id, c.edge.dst.port = p.name ∧ c.closed = true ∧
      c.pending.head? = some (.item (inputHead s P n.id p.name)) := by
  simp only [plainInputs, require, bind, Except.bind, pure, Except.pure] at h
  split at h
  · contradiction
  · refine ⟨?_, ?_⟩
    · apply mapM_eq_map _ (fun p => (p.name, inputHead s P n.id p.name)) n.inputs inputs _ h
      intro p member y hy
      cases found : (s.incoming P n.id).find? (·.edge.dst.port == p.name) with
      | none => simp [found, Option.toExcept] at hy
      | some c =>
        simp only [found, Option.toExcept] at hy
        split at hy
        · contradiction
        · split at hy
          · contradiction
          · cases pending : c.pending with
            | nil => simp [pending, throw, throwThe, MonadExceptOf.throw, instMonadExceptOfExcept] at hy
            | cons t rest =>
              cases t with
              | eos => simp [pending, throw, throwThe, MonadExceptOf.throw, instMonadExceptOfExcept] at hy
              | item id =>
                simp only [pending, pure, Except.pure, Except.ok.injEq] at hy
                rw [← hy]
                simp [inputHead, found, pending]
    · intro p member
      obtain ⟨y, hy⟩ := mapM_ok_members _ _ _ h p member
      cases found : (s.incoming P n.id).find? (·.edge.dst.port == p.name) with
      | none => simp [found, Option.toExcept] at hy
      | some c =>
        have memberC := List.mem_of_find?_eq_some found
        have portC : c.edge.dst.port = p.name := by simpa using List.find?_some found
        simp only [found, Option.toExcept] at hy
        split at hy
        · contradiction
        · rename_i u1 closedEq
          have closed : c.closed = true := by
            split at closedEq
            · assumption
            · contradiction
          split at hy
          · contradiction
          · cases pending : c.pending with
            | nil => simp [pending, throw, throwThe, MonadExceptOf.throw, instMonadExceptOfExcept] at hy
            | cons t rest =>
              cases t with
              | eos => simp [pending, throw, throwThe, MonadExceptOf.throw, instMonadExceptOfExcept] at hy
              | item id =>
                refine ⟨c, memberC, portC, closed, ?_⟩
                simp [pending, inputHead, found]


/-- An appended instance has a key distinct from every earlier instance (by key uniqueness). -/
theorem fresh_of_append {s s' : State} (safe' : Invariants s') (i : Instance)
    (instances : s'.instances = s.instances ++ [i]) :
    ∀ j ∈ s.instances, instanceKey j ≠ instanceKey i := by
  intro j memberJ same
  have keys : (s'.instances.map instanceKey).Nodup := by
    simp only [Invariants, invariants, Bool.and_eq_true] at safe'
    exact unique_nodup _ safe'.1.1.1.1.2
  have ids : (s'.instances.map (·.id)).Nodup := safe'.instanceIds
  have memberJ' : j ∈ s'.instances := by rw [instances]; exact List.mem_append_left _ memberJ
  have memberI : i ∈ s'.instances := by rw [instances]; simp
  have eq : j = i := eq_of_mapped_nodup instanceKey s'.instances keys j i memberJ' memberI same
  subst eq
  rw [instances, List.map_append, List.nodup_append] at ids
  exact ids.2.2 j.id (List.mem_map.mpr ⟨j, memberJ, rfl⟩) j.id (by simp) rfl

/-- Instances of a node that is not a forEach carry no trigger. -/
theorem instance_trigger_none (oracle : ScopedOracle) {s0 s : State} {ops : List Op}
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops s)
    (safe0 : Invariants s0) (P : Path) (N : NodeId) (n : Node) (found : s0.node? P N = some n)
    (notForEach : ∀ body, n.kind ≠ .forEach body)
    (fresh0 : ∀ j ∈ s0.instances, ¬ (j.path = P ∧ j.node = N))
    (j : Instance) (memberJ : j ∈ s.instances) (pathJ : j.path = P) (nodeJ : j.node = N) : j.trigger = none := by
  have absent0 : ∀ k ∈ s0.instances, k.id ≠ j.id := by
    intro k memberK eq
    obtain ⟨node, path, _, _⟩ := run.input_snapshot safe0 k j memberK memberJ eq
    exact fresh0 k memberK ⟨path.symm.trans pathJ, node.symm.trans nodeJ⟩
  obtain ⟨pre, op, post, t, t', j', _, head, allowed, accepted, rest, safeT, absentT, memberJ', idJ', bindJ'⟩ :=
    instance_origin run safe0 j memberJ absent0
  rcases step_instances_origin t t' op safeT accepted j' memberJ' with ⟨k, memberK, idK⟩ | none | ⟨path, node, item, n', body, _, hn, kind, eq⟩
  · exact absurd (idK.trans idJ') (absentT k memberK)
  · rw [← Instance.binding_trigger bindJ', none]
  · exfalso
    have pathJ' : j'.path = P := (Instance.binding_path bindJ').trans pathJ
    have nodeJ' : j'.node = N := (Instance.binding_node bindJ').trans nodeJ
    rw [eq] at pathJ' nodeJ'
    simp only [makeInstance] at pathJ' nodeJ'
    have nodeT : t.node? path N = some n := by rw [pathJ']; exact head.node P N n found
    have NN : N = node := nodeJ'.symm.trans (getNode_id t path node n' hn)
    rw [NN] at nodeT
    have := node?_of_getNode nodeT hn
    subst this
    exact notForEach body kind

/-- The final state of an output channel closed by a skip of a node with plain inputs
    (any kind except Coalesce): empty, with a cancelled instance and an empty input. -/
theorem skip_closing_final (oracle : ScopedOracle) {s0 s s' last : State} {pre post : List Op}
    (head : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 pre s)
    (allowed : oracleConforms oracle s (.skip P N) = true) (accepted : step s (.skip P N) = .ok s')
    (rest : ConformingSteps (fun s op => oracleConforms oracle s op = true) s' post last)
    (safe0 : Invariants s0) (safeS : Invariants s) (active : absorbed s (.skip P N) = false)
    (n : Node) (found : s0.node? P N = some n) (notCoalesce : n.kind ≠ .coalesce)
    (c0 : Channel) (member0 : c0 ∈ s0.channels) (empty0 : c0.placed = []) (entry0 : c0.entry = false)
    (path0 : c0.path = P) (src0 : c0.edge.src.node = N)
    (c : Channel) (memberC : c ∈ s.channels) (idC : c.id = c0.id)
    (c' : Channel) (memberC' : c' ∈ s'.channels) (idC' : c'.id = c0.id) (closedC' : c'.closed = true)
    (cl : Channel) (memberL : cl ∈ last.channels) (idL : cl.id = c0.id) :
    cl.items = [] ∧ (∃ i ∈ last.instances, i.path = P ∧ i.node = N ∧ i.status = .cancelled) ∧
      ∃ d ∈ last.channels, d.path = P ∧ d.exit = false ∧ d.edge.dst.node = N ∧ d.closed = true ∧ d.items = [] := by
  have safeS' := preserves_invariants s s' _ safeS accepted
  have safeLast : Invariants last := rest.invariants safeS'
  have nodeS : s.node? P N = some n := head.node P N n found
  rcases step_ok_cases s _ s' accepted with ⟨a, _⟩ | ⟨_, _, prepared, _, _⟩
  · rw [active] at a; contradiction
  · have executed := prepareWith_body transitionOrIdle s s' _ prepared
    simp only [transitionOrIdle] at executed
    obtain ⟨n', hn, cond, _, noInstance, instances, _, _, _⟩ := effect_skip s s' P N executed
    have sameN := node?_of_getNode nodeS hn
    subst n'
    have found' : s0.node? c0.path c0.edge.src.node = some n := by rw [path0, src0]; exact found
    have noInstance' : ∀ j ∈ s.instances, ¬ (j.path = c0.path ∧ j.node = c0.edge.src.node) := by
      rw [path0, src0]; exact noInstance
    have emptyC : c.items = [] := by
      cases hi : c.items with
      | nil => rfl
      | cons x xs =>
        exfalso
        obtain ⟨j, memberJ, pathJ, nodeJ⟩ := items_imply_instance oracle head safe0 n c0 found' member0 empty0 entry0
          c memberC idC x (by rw [hi]; simp)
        exact noInstance' j memberJ ⟨pathJ, nodeJ⟩
    have finalPlaced : cl.placed = c'.placed := by
      obtain ⟨e, memberE, idE, placedE⟩ := rest.retains_closed_channel safeS' c' memberC' closedC'
      have same : e = cl := unique_channel safeLast memberE memberL (idE.trans (idC'.trans idL.symm))
      subst same
      exact placedE
    have itemsL : cl.items = [] := by
      have same := skip_no_items s s' _ _ safeS safeS' active accepted c memberC c' memberC' (idC'.trans idC.symm)
      simp only [Channel.items, finalPlaced]
      exact same.trans emptyC
    refine ⟨itemsL, ?_, ?_⟩
    · let j := makeInstance P n .cancelled
      have memberJ : j ∈ s'.instances := by rw [instances]; simp [j]
      obtain ⟨k, memberK, idK, statusK⟩ := rest.retains_status safeS' j memberJ (.inr rfl)
      obtain ⟨nodeK, pathK, _, _⟩ := rest.input_snapshot safeS' j k memberJ memberK idK.symm
      refine ⟨k, memberK, pathK, ?_, statusK⟩
      rw [nodeK]
      exact getNode_id s _ _ n hn
    · have anyEmpty : (s.incoming P N).any (fun c => c.closed && c.items.isEmpty) = true := by
        simp only [Bool.and_eq_true] at cond
        have raw := cond.2
        cases hk : n.kind <;> first | exact absurd hk notCoalesce | exact raw | simpa using raw
      obtain ⟨d, memberD, props⟩ := List.any_eq_true.mp anyEmpty
      simp only [Bool.and_eq_true, List.isEmpty_iff] at props
      have inChannels : d ∈ s.channels := (List.mem_filter.mp memberD).1
      have fields := (List.mem_filter.mp memberD).2
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at fields
      have runS : ConformingSteps (fun s op => oracleConforms oracle s op = true) s (.skip P N :: post) last :=
        .cons allowed accepted rest
      obtain ⟨e, memberE, idE, placedE⟩ := runS.retains_closed_channel safeS d inChannels props.1
      obtain ⟨e', memberE', idE', layoutE', _⟩ := run_image runS safeS d inChannels
      have same : e' = e := unique_channel safeLast memberE' memberE (idE'.trans idE.symm)
      subst same
      obtain ⟨_, edgeE, pathE, _, exitE, _⟩ := Channel.layout_fields layoutE'
      refine ⟨e', memberE, pathE.trans fields.1.1, exitE.trans fields.1.2, ?_, ?_, ?_⟩
      · rw [edgeE]; exact fields.2
      · simpa [Channel.closed, placedE] using props.1
      · simp only [Channel.items, placedE]; exact props.2


/-- A nodup list contained in `[x]` and containing `x` is `[x]`. -/
theorem singleton_of_subset {l : List ItemId} (nodup : l.Nodup) (sub : l ⊆ [x]) (present : x ∈ l) : l = [x] := by
  have bound := nodup.length_le_of_subset sub
  simp only [List.length_singleton] at bound
  match l, bound, present with
  | [y], _, present =>
    have : x = y := by simpa using present
    rw [this]

theorem channelOK_of_invariants {s : State} (safe : Invariants s) {c : Channel} (member : c ∈ s.channels) :
    channelOK c = true := by
  simp only [Invariants, invariants, Bool.and_eq_true] at safe
  exact List.all_eq_true.mp safe.1.1.1.1.1.1.1 c member

theorem items_nodup_of_invariants {s : State} (safe : Invariants s) {c : Channel} (member : c ∈ s.channels) :
    c.items.Nodup := by
  have ok := channelOK_of_invariants safe member
  simp only [channelOK, Bool.and_eq_true] at ok
  exact unique_nodup _ ok.1.2

/-- Every channel of a frame that already existed at `s0` has a counterpart at `s0` with the same layout. -/
theorem channel_origin_layout {allows : State → Op → Prop} {s0 s : State} {ops : List Op}
    (run : ConformingSteps allows s0 ops s) (layout0 : LayoutOK s0) (distinct0 : (s0.frames.map Frame.path).Nodup)
    (f0 : Frame) (memberF0 : f0 ∈ s0.frames) (c : Channel) (memberC : c ∈ s.channels) (pathC : c.path = f0.path) :
    ∃ c00 ∈ s0.channels, c00.layout = c.layout := by
  have layoutS : LayoutOK s := run.layout layout0
  have distinctS : (s.frames.map Frame.path).Nodup := run.unique_frames distinct0
  obtain ⟨fs, memberFs, channelFs, pathFs⟩ := LayoutOK.channel_frame layoutS c memberC
  obtain ⟨graphs, _, _⟩ := run.frame_definition f0 memberF0 distinctS fs memberFs (pathFs.symm.trans pathC)
  have samePath : fs.path = f0.path := pathFs.symm.trans pathC
  have channels : fs.channels = f0.channels := by
    simp only [Frame.channels, Frame.edgeChannels, Frame.entryChannels, Frame.exitChannels, graphs, samePath]
  rw [channels] at channelFs
  have inLayout : c.layout ∈ s0.channelLayout := by
    rw [layout0]
    exact List.mem_flatMap.mpr ⟨f0, memberF0, channelFs⟩
  obtain ⟨c00, member00, eq⟩ := List.mem_map.mp inLayout
  exact ⟨c00, member00, eq⟩

theorem routeWrites_all_mem (path : Path) (n : Node) (item : ItemId) (q : Port) (port : q ∈ n.outputs) :
    Write.out path n.id q.name (.item item) ∈ routeWrites path n (some item) none := by
  simp only [routeWrites]
  exact List.mem_filterMap.mpr ⟨q, port, by simp [routeOutput]⟩

theorem routeWrites_tokens (path : Path) (n : Node) (value : Option ItemId) (arm : Option PortName) :
    ∀ w ∈ routeWrites path n value arm, ∃ id, w.token = .item id ∧ value = some id := by
  intro w hw
  obtain ⟨q, _, inner⟩ := List.mem_filterMap.mp hw
  cases h : routeOutput arm q.name value with
  | none => rw [h] at inner; contradiction
  | some id =>
    rw [h] at inner
    simp only [Option.map_some, Option.some.injEq] at inner
    subst inner
    refine ⟨id, rfl, ?_⟩
    unfold routeOutput at h
    split at h
    · exact h
    · contradiction

/-- Final contents of one output channel of a WaitAll node. -/
theorem waitAll_output_final (oracle : ScopedOracle) {s0 last : State} {ops : List Op}
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (safe0 : Invariants s0) (layout0 : LayoutOK s0) (distinct0 : (s0.frames.map Frame.path).Nodup)
    (finished : succeededDrained last = true)
    (n : Node) (c0 : Channel) (found : s0.node? c0.path c0.edge.src.node = some n) (kind : n.kind = .waitAll)
    (frame0 : ∃ f ∈ s0.frames, f.path = c0.path)
    (fresh0 : ∀ j ∈ s0.instances, ¬ (j.path = c0.path ∧ j.node = c0.edge.src.node))
    (inputKinds : ∀ c ∈ s0.channels, c.path = c0.path → c.exit = false → c.edge.dst.node = c0.edge.src.node → c.kind = .plain)
    (q : Port) (port : q ∈ n.outputs) (portC : c0.edge.src.port = q.name)
    (member0 : c0 ∈ s0.channels) (empty0 : c0.placed = []) (entry0 : c0.entry = false)
    (cl : Channel) (memberL : cl ∈ last.channels) (idL : cl.id = c0.id) :
    (∃ f : Port → ItemId,
        (∀ p ∈ n.inputs, ∃ d ∈ last.channels, d.path = c0.path ∧ d.exit = false ∧
          d.edge.dst = ⟨c0.edge.src.node, p.name⟩ ∧ d.items = [f p]) ∧
        cl.items = [derivedItem "record" c0.path c0.edge.src.node
          ((n.inputs.map fun p => (p.name, f p)).map fun (p, i) => identity [p, i])] ∧
        ∃ i ∈ last.instances, i.path = c0.path ∧ i.node = c0.edge.src.node ∧ i.status = .succeeded) ∨
    (cl.items = [] ∧ (∃ i ∈ last.instances, i.path = c0.path ∧ i.node = c0.edge.src.node ∧ i.status = .cancelled) ∧
        ∃ d ∈ last.channels, d.path = c0.path ∧ d.exit = false ∧ d.edge.dst.node = c0.edge.src.node ∧
          d.closed = true ∧ d.items = []) := by
  have closedL := closed_of_drained finished memberL
  have open0 : Token.eos ∉ c0.placed := by rw [empty0]; simp
  have present : Token.eos ∈ cl.placed := by simpa [Channel.closed] using closedL
  obtain ⟨pre, op, post, s, s', c, c', _, head, allowed, accepted, rest, safeS, active,
    memberC, idC, layoutC, absentC, memberC', idC', layoutC', presentC', _, target⟩ :=
    token_step run safe0 .eos c0 member0 open0 entry0 cl memberL idL present
  have nodeS := head.node c0.path c0.edge.src.node n found
  have safeS' := preserves_invariants s s' op safeS accepted
  have safeLast : Invariants last := rest.invariants safeS'
  obtain ⟨_, edgeC, pathC, entryC, _, kindC⟩ := Channel.layout_fields layoutC
  have closedC' : c'.closed = true := by simpa [Channel.closed] using presentC'
  have finalPlaced : cl.placed = c'.placed := by
    obtain ⟨e, memberE, idE, placedE⟩ := rest.retains_closed_channel safeS' c' memberC' closedC'
    have same : e = cl := unique_channel safeLast memberE memberL (idE.trans (idC'.trans idL.symm))
    subst same
    exact placedE
  rcases target_shape s s' op safeS active accepted _ _ target n nodeS with
      ⟨_, _, _, _, _, _, k⟩ | ⟨_, _, _, _, _, k⟩ | ⟨eq, _⟩ | ⟨_, _, _, k⟩ | ⟨_, _, _, k⟩ | ⟨_, k⟩
    | ⟨_, _, _, k⟩ | ⟨_, _, _, k⟩ | ⟨_, k⟩ | ⟨_, _, _, k⟩ | ⟨_, _, _, _, _, k⟩ | ⟨eq, _⟩
  · rw [kind] at k; cases k
  · rw [kind] at k; cases k
  · -- fireWaitAll
    subst eq
    left
    rcases step_ok_cases s _ s' accepted with ⟨a, _⟩ | ⟨_, _, prepared, _, _⟩
    · rw [active] at a; contradiction
    · have executed := prepareWith_body transitionOrIdle s s' _ prepared
      simp only [transitionOrIdle] at executed
      obtain ⟨n', inputs, hn, _, plain, view, instances, _, _⟩ := effect_fireWaitAll s s' _ _ executed
      have sameN := node?_of_getNode nodeS hn
      subst n'
      have nid := getNode_id s _ _ n hn
      obtain ⟨inputsEq, inputFacts⟩ := plainInputs_spec s c0.path n inputs plain
      let f : Port → ItemId := fun p => inputHead s c0.path n.id p.name
      refine ⟨f, ?_, ?_, ?_⟩
      · -- input channels are plain, closed, and hold exactly the recorded item
        intro p memberP
        obtain ⟨d, memberD, portD, closedD, headD⟩ := inputFacts p memberP
        have inChannels : d ∈ s.channels := (List.mem_filter.mp memberD).1
        have fields := (List.mem_filter.mp memberD).2
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at fields
        obtain ⟨f0, memberF0, pathF0⟩ := frame0
        obtain ⟨d00, member00, layout00⟩ := channel_origin_layout head layout0 distinct0 f0 memberF0 d inChannels
          (fields.1.1.trans pathF0.symm)
        obtain ⟨_, edge00, path00, _, exit00, kind00⟩ := Channel.layout_fields layout00
        have plainD : d.kind = .plain := by
          rw [← kind00]
          exact inputKinds d00 member00 (path00.trans fields.1.1) (exit00.trans fields.1.2) (by rw [edge00]; exact fields.2.trans nid)
        have itemsD : d.items = [f p] := by
          apply plain_items_singleton d (channelOK_of_invariants safeS inChannels) plainD
          exact (Effects.item_mem d _).mpr (List.drop_subset _ _ (List.mem_of_mem_head? headD))
        have runS : ConformingSteps (fun s op => oracleConforms oracle s op = true) s (.fireWaitAll c0.path c0.edge.src.node :: post) last :=
          .cons allowed accepted rest
        obtain ⟨e, memberE, idE, placedE⟩ := runS.retains_closed_channel safeS d inChannels closedD
        obtain ⟨e', memberE', idE', layoutE', _⟩ := run_image runS safeS d inChannels
        have same : e' = e := unique_channel safeLast memberE' memberE (idE'.trans idE.symm)
        subst same
        obtain ⟨_, edgeE, pathE, _, exitE, _⟩ := Channel.layout_fields layoutE'
        refine ⟨e', memberE, pathE.trans fields.1.1, exitE.trans fields.1.2, ?_, ?_⟩
        · rw [edgeE]
          cases hd : d.edge.dst with
          | mk node port'' =>
            rw [hd] at fields portD
            simp only at fields portD
            rw [fields.2, portD, nid]
        · simp only [Channel.items, placedE]
          exact itemsD
      · -- the output holds exactly the record
        have emptyC : c.items = [] := by
          cases hi : c.items with
          | nil => rfl
          | cons x xs =>
            exfalso
            obtain ⟨j, memberJ, pathJ, nodeJ⟩ := items_imply_instance oracle head safe0 n c0 found member0 empty0 entry0
              c memberC idC x (by rw [hi]; simp)
            have triggerJ := instance_trigger_none oracle head safe0 _ _ n found (fun body h => by rw [kind] at h; cases h)
              fresh0 j memberJ pathJ nodeJ
            have fresh := fresh_of_append safeS' _ instances j memberJ
            apply fresh
            simp only [instanceKey, makeInstance, pathJ, nodeJ, triggerJ, nid]
        let record := derivedItem "record" c0.path c0.edge.src.node (inputs.map fun (p, i) => identity [p, i])
        have hit : Write.out c.path c.edge.src.node c.edge.src.port (.item record) ∈
            routeWrites c0.path n (some record) none ++ eosWrites c0.path n := by
          apply List.mem_append_left
          rw [pathC, edgeC]
          cases hsrc : c0.edge.src with
          | mk node port'' =>
            rw [hsrc] at portC nid
            simp only at portC nid
            rw [portC, ← nid]
            exact routeWrites_all_mem c0.path n record q port
        obtain ⟨d, memberD, idD, _, presentD⟩ :=
          applyWrites_token _ s c memberC (entryC.trans entry0) safeS.channelIds (.item record) hit
        have inView : d.core ∈ s'.placedView := by rw [view]; exact placedView_member memberD
        obtain ⟨e, memberE, coreE⟩ := List.mem_map.mp inView
        have idE : e.id = d.id := by simpa using congrArg Channel.id coreE
        have same : e = c' := unique_channel safeS' memberE memberC' (idE.trans (idD.trans (idC.trans idC'.symm)))
        subst same
        have recordIn : record ∈ e.items := by
          rw [Effects.item_mem]
          have := congrArg Channel.placed coreE
          simp only [Channel.core_placed] at this
          rw [this]; exact presentD
        have tokens := view_tokens s' s _ safeS.channelIds view c memberC e memberE (idC'.trans idC.symm)
        have subset : e.items ⊆ [record] := by
          intro x hx
          have tok := tokens (.item x) ((Effects.item_mem e x).mp hx)
          rcases tok with old | ⟨w, hw, tw⟩
          · exact absurd ((Effects.item_mem c x).mpr old) (by rw [emptyC]; simp)
          · rcases List.mem_append.mp hw with route | eos
            · obtain ⟨id, tokW, valueEq⟩ := routeWrites_tokens _ _ _ _ w route
              rw [tokW] at tw
              cases tw
              simp only [Option.some.injEq] at valueEq
              subst valueEq
              simp [record]
            · have := eosWrites_eos _ _ w eos
              rw [this] at tw; cases tw
        have itemsE : e.items = [record] := singleton_of_subset (items_nodup_of_invariants safeS' memberE) subset recordIn
        rw [show cl.items = e.items from by simp only [Channel.items, finalPlaced]]
        rw [itemsE]
        simp only [record, inputsEq]
        rfl
      · -- the succeeded instance
        let j := makeInstance c0.path n .succeeded inputs
        have memberJ : j ∈ s'.instances := by rw [instances]; simp [j]
        obtain ⟨k, memberK, idK, statusK⟩ := rest.retains_status safeS' j memberJ (.inl rfl)
        obtain ⟨nodeK, pathK, _, _⟩ := rest.input_snapshot safeS' j k memberJ memberK idK.symm
        exact ⟨k, memberK, pathK, nodeK.trans nid, statusK⟩
  · rw [kind] at k; cases k
  · rw [kind] at k; cases k
  · rw [kind] at k; cases k
  · rw [kind] at k; cases k
  · rw [kind] at k; cases k
  · rw [kind] at k; simp at k
  · rcases k with k | k <;> (rw [kind] at k; cases k)
  · rw [kind] at k; cases k
  · subst eq
    exact .inr (skip_closing_final oracle head allowed accepted rest safe0 safeS active n found
      (by rw [kind]; intro h; cases h) c0 member0 empty0 entry0 rfl rfl c memberC idC c' memberC' idC' closedC' cl memberL idL)


/-- Writes that either miss the channel's group or carry EOS leave its items unchanged. -/
theorem applyWrites_items_untouched (ws : List Write) (st : State) (c : Channel) (member : c ∈ st.channels)
    (nonEntry : c.entry = false) (distinct : (st.channels.map (·.id)).Nodup)
    (safe : ∀ w ∈ ws, (∀ t, w ≠ .out c.path c.edge.src.node c.edge.src.port t) ∨ w.token = .eos) :
    ∃ d ∈ (applyWrites ws st).channels, d.id = c.id ∧ d.layout = c.layout ∧ d.items = c.items := by
  induction ws generalizing st c with
  | nil => exact ⟨c, member, rfl, rfl, rfl⟩
  | cons w ws ih =>
    simp only [applyWrites_cons]
    have one : ∃ d ∈ (applyWrite st w).channels, d.id = c.id ∧ d.layout = c.layout ∧ d.items = c.items := by
      rcases safe w (by simp) with miss | eos
      · exact ⟨c, applyWrite_untouched st w c member distinct nonEntry miss, rfl, rfl, rfl⟩
      · unfold applyWrite
        refine ⟨_, write_member st _ _ c member, ?_⟩
        split
        · rw [eos]
          exact ⟨insertToken_id _ _, insertToken_layout _ _, insertToken_eos_items _⟩
        · exact ⟨rfl, rfl, rfl⟩
    obtain ⟨d, memberD, idD, layoutD, itemsD⟩ := one
    have distinct' : ((applyWrite st w).channels.map (·.id)).Nodup := by rw [applyWrite_ids]; exact distinct
    have nonEntryD : d.entry = false := by simpa using (congrArg Channel.entry layoutD).trans nonEntry
    obtain ⟨_, edgeD, pathD, _, _, _⟩ := Channel.layout_fields layoutD
    obtain ⟨e, memberE, idE, layoutE, itemsE⟩ := ih (applyWrite st w) d memberD nonEntryD distinct' (by
      intro v hv
      rcases safe v (by simp [hv]) with miss | eos
      · left; intro t eq; exact miss t (by rw [eq, pathD, edgeD])
      · right; exact eos)
    exact ⟨e, memberE, idE.trans idD, layoutE.trans layoutD, itemsE.trans itemsD⟩

/-- Two input channels of the same node in the same frame coincide when the frame has at most
    one input channel for that node (transported from the frame-opening state). -/
theorem unique_input_channel {allows : State → Op → Prop} {s0 s : State} {ops : List Op}
    (run : ConformingSteps allows s0 ops s) (safe0 : Invariants s0) (layout0 : LayoutOK s0)
    (distinct0 : (s0.frames.map Frame.path).Nodup) (P : Path) (N : NodeId)
    (frame0 : ∃ f ∈ s0.frames, f.path = P)
    (uniqueInput : ∀ c ∈ s0.channels, ∀ d ∈ s0.channels, c.path = P → d.path = P → c.exit = false → d.exit = false →
      c.edge.dst.node = N → d.edge.dst.node = N → c.id = d.id)
    (c d : Channel) (memberC : c ∈ s.channels) (memberD : d ∈ s.channels)
    (pathC : c.path = P) (pathD : d.path = P) (exitC : c.exit = false) (exitD : d.exit = false)
    (nodeC : c.edge.dst.node = N) (nodeD : d.edge.dst.node = N) : c = d := by
  obtain ⟨f0, memberF0, pathF0⟩ := frame0
  obtain ⟨c00, member00, layoutC⟩ := channel_origin_layout run layout0 distinct0 f0 memberF0 c memberC (pathC.trans pathF0.symm)
  obtain ⟨d00, memberD0, layoutD⟩ := channel_origin_layout run layout0 distinct0 f0 memberF0 d memberD (pathD.trans pathF0.symm)
  obtain ⟨idC, edgeC, pathC0, _, exitC0, _⟩ := Channel.layout_fields layoutC
  obtain ⟨idD, edgeD, pathD0, _, exitD0, _⟩ := Channel.layout_fields layoutD
  have same := uniqueInput c00 member00 d00 memberD0 (pathC0.trans pathC) (pathD0.trans pathD) (exitC0.trans exitC)
    (exitD0.trans exitD) (by rw [edgeC]; exact nodeC) (by rw [edgeD]; exact nodeD)
  exact unique_channel (run.invariants safe0) memberC memberD (idC.symm.trans (same.trans idD))

/-- Final contents of one output channel of a Branch node. -/
theorem branch_output_final (oracle : ScopedOracle) {s0 last : State} {ops : List Op}
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (safe0 : Invariants s0) (layout0 : LayoutOK s0) (distinct0 : (s0.frames.map Frame.path).Nodup)
    (finished : succeededDrained last = true)
    (n : Node) (c0 : Channel) (found : s0.node? c0.path c0.edge.src.node = some n) (arms : List PortName)
    (kind : n.kind = .branch arms) (p1 : Port) (single : n.inputs = [p1])
    (frame0 : ∃ f ∈ s0.frames, f.path = c0.path)
    (fresh0 : ∀ j ∈ s0.instances, ¬ (j.path = c0.path ∧ j.node = c0.edge.src.node))
    (inputKinds : ∀ c ∈ s0.channels, c.path = c0.path → c.exit = false → c.edge.dst.node = c0.edge.src.node → c.kind = .plain)
    (uniqueInput : ∀ c ∈ s0.channels, ∀ d ∈ s0.channels, c.path = c0.path → d.path = c0.path → c.exit = false → d.exit = false →
      c.edge.dst.node = c0.edge.src.node → d.edge.dst.node = c0.edge.src.node → c.id = d.id)
    (q : Port) (port : q ∈ n.outputs) (portC : c0.edge.src.port = q.name)
    (member0 : c0 ∈ s0.channels) (empty0 : c0.placed = []) (entry0 : c0.entry = false)
    (cl : Channel) (memberL : cl ∈ last.channels) (idL : cl.id = c0.id) :
    (∃ item, (∃ d ∈ last.channels, d.path = c0.path ∧ d.exit = false ∧ d.edge.dst = ⟨c0.edge.src.node, p1.name⟩ ∧ d.items = [item]) ∧
        cl.items = (if q.name = (oracle c0.path).branch c0.edge.src.node item then [item] else []) ∧
        ∃ i ∈ last.instances, i.path = c0.path ∧ i.node = c0.edge.src.node ∧ i.status = .succeeded) ∨
    (cl.items = [] ∧ (∃ i ∈ last.instances, i.path = c0.path ∧ i.node = c0.edge.src.node ∧ i.status = .cancelled) ∧
        ∃ d ∈ last.channels, d.path = c0.path ∧ d.exit = false ∧ d.edge.dst.node = c0.edge.src.node ∧
          d.closed = true ∧ d.items = []) := by
  have closedL := closed_of_drained finished memberL
  have open0 : Token.eos ∉ c0.placed := by rw [empty0]; simp
  have present : Token.eos ∈ cl.placed := by simpa [Channel.closed] using closedL
  obtain ⟨pre, op, post, s, s', c, c', _, head, allowed, accepted, rest, safeS, active,
    memberC, idC, layoutC, absentC, memberC', idC', layoutC', presentC', _, target⟩ :=
    token_step run safe0 .eos c0 member0 open0 entry0 cl memberL idL present
  have nodeS := head.node c0.path c0.edge.src.node n found
  have safeS' := preserves_invariants s s' op safeS accepted
  have safeLast : Invariants last := rest.invariants safeS'
  obtain ⟨_, edgeC, pathC, entryC, _, kindC⟩ := Channel.layout_fields layoutC
  have closedC' : c'.closed = true := by simpa [Channel.closed] using presentC'
  have finalPlaced : cl.placed = c'.placed := by
    obtain ⟨e, memberE, idE, placedE⟩ := rest.retains_closed_channel safeS' c' memberC' closedC'
    have same : e = cl := unique_channel safeLast memberE memberL (idE.trans (idC'.trans idL.symm))
    subst same
    exact placedE
  rcases target_shape s s' op safeS active accepted _ _ target n nodeS with
      ⟨_, _, _, _, _, _, k⟩ | ⟨_, _, _, _, _, k⟩ | ⟨_, k⟩ | ⟨arm, arms', eq, k⟩ | ⟨_, _, _, k⟩ | ⟨_, k⟩
    | ⟨_, _, _, k⟩ | ⟨_, _, _, k⟩ | ⟨_, k⟩ | ⟨_, _, _, k⟩ | ⟨_, _, _, _, _, k⟩ | ⟨eq, _⟩
  · rw [kind] at k; cases k
  · rw [kind] at k; cases k
  · rw [kind] at k; cases k
  · -- fireBranch
    subst eq
    left
    rcases step_ok_cases s _ s' accepted with ⟨a, _⟩ | ⟨_, _, prepared, _, _⟩
    · rw [active] at a; contradiction
    · have executed := prepareWith_body transitionOrIdle s s' _ prepared
      simp only [transitionOrIdle] at executed
      obtain ⟨n', arms'', inputs, item, hn, _, _, plain, headItem, view, instances, _, _⟩ :=
        effect_fireBranch s s' _ _ arm executed
      have sameN := node?_of_getNode nodeS hn
      subst n'
      have nid := getNode_id s _ _ n hn
      obtain ⟨inputsEq, inputFacts⟩ := plainInputs_spec s c0.path n inputs plain
      -- the single input channel
      have p1mem : p1 ∈ n.inputs := by rw [single]; simp
      obtain ⟨d, memberD, portD, closedD, headD⟩ := inputFacts p1 p1mem
      have inChannels : d ∈ s.channels := (List.mem_filter.mp memberD).1
      have fields := (List.mem_filter.mp memberD).2
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at fields
      have itemEq : item = inputHead s c0.path n.id p1.name := by
        rw [inputsEq, single] at headItem
        simpa using headItem.symm
      obtain ⟨f0, memberF0, pathF0⟩ := frame0
      obtain ⟨d00, member00, layout00⟩ := channel_origin_layout head layout0 distinct0 f0 memberF0 d inChannels
        (fields.1.1.trans pathF0.symm)
      obtain ⟨_, edge00, path00, _, exit00, kind00⟩ := Channel.layout_fields layout00
      have plainD : d.kind = .plain := by
        rw [← kind00]
        exact inputKinds d00 member00 (path00.trans fields.1.1) (exit00.trans fields.1.2) (by rw [edge00]; exact fields.2.trans nid)
      have itemsD : d.items = [item] := by
        rw [itemEq]
        apply plain_items_singleton d (channelOK_of_invariants safeS inChannels) plainD
        exact (Effects.item_mem d _).mpr (List.drop_subset _ _ (List.mem_of_mem_head? headD))
      -- conformance fixes the arm from the same input item
      have armEq : arm = (oracle c0.path).branch c0.edge.src.node item := by
        have h := allowed
        simp only [oracleConforms, active, Bool.false_eq_true, ↓reduceIte] at h
        cases hhd : (s.incoming c0.path c0.edge.src.node).head? with
        | none => rw [hhd] at h; simp at h
        | some hd =>
          rw [hhd] at h
          have memberHd : hd ∈ s.incoming c0.path c0.edge.src.node := List.mem_of_mem_head? hhd
          have inChannelsHd : hd ∈ s.channels := (List.mem_filter.mp memberHd).1
          have fieldsHd := (List.mem_filter.mp memberHd).2
          simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at fieldsHd
          have same : hd = d := unique_input_channel head safe0 layout0 distinct0 _ _ ⟨f0, memberF0, pathF0⟩ uniqueInput hd d inChannelsHd inChannels
            fieldsHd.1.1 fields.1.1 fieldsHd.1.2 fields.1.2 fieldsHd.2 (fields.2.trans nid)
          subst same
          have pendingHead : hd.pendingItems.head? = some item := by
            simp only [Channel.pendingItems]
            cases hp : hd.pending with
            | nil => rw [hp] at headD; simp at headD
            | cons tk rest =>
              rw [hp] at headD
              simp only [List.head?_cons, Option.some.injEq] at headD
              subst headD
              simp [itemEq]
          simp only [Option.bind_some, pendingHead, Option.any_some] at h
          exact beq_iff_eq.mp h
      refine ⟨item, ?_, ?_, ?_⟩
      · -- the input channel at the end
        have runS : ConformingSteps (fun s op => oracleConforms oracle s op = true) s (.fireBranch c0.path c0.edge.src.node arm :: post) last :=
          .cons allowed accepted rest
        obtain ⟨e, memberE, idE, placedE⟩ := runS.retains_closed_channel safeS d inChannels closedD
        obtain ⟨e', memberE', idE', layoutE', _⟩ := run_image runS safeS d inChannels
        have same : e' = e := unique_channel safeLast memberE' memberE (idE'.trans idE.symm)
        subst same
        obtain ⟨_, edgeE, pathE, _, exitE, _⟩ := Channel.layout_fields layoutE'
        refine ⟨e', memberE, pathE.trans fields.1.1, exitE.trans fields.1.2, ?_, ?_⟩
        · rw [edgeE]
          cases hd : d.edge.dst with
          | mk node port'' =>
            rw [hd] at fields portD
            simp only at fields portD
            rw [fields.2, portD, nid]
        · simp only [Channel.items, placedE]
          exact itemsD
      · -- the output: the item on the chosen arm, nothing elsewhere
        have emptyC : c.items = [] := by
          cases hi : c.items with
          | nil => rfl
          | cons x xs =>
            exfalso
            obtain ⟨j, memberJ, pathJ, nodeJ⟩ := items_imply_instance oracle head safe0 n c0 found member0 empty0 entry0
              c memberC idC x (by rw [hi]; simp)
            have triggerJ := instance_trigger_none oracle head safe0 _ _ n found (fun body h => by rw [kind] at h; cases h)
              fresh0 j memberJ pathJ nodeJ
            have fresh := fresh_of_append safeS' _ instances j memberJ
            apply fresh
            simp only [instanceKey, makeInstance, pathJ, nodeJ, triggerJ, nid]
        have clItems : cl.items = c'.items := by simp only [Channel.items, finalPlaced]
        rw [clItems, ← armEq]
        by_cases chosen : q.name = arm
        · rw [ite_eq_left chosen]
          have hit : Write.out c.path c.edge.src.node c.edge.src.port (.item item) ∈
              routeWrites c0.path n (some item) (some arm) ++ eosWrites c0.path n := by
            apply List.mem_append_left
            rw [pathC, edgeC]
            cases hsrc : c0.edge.src with
            | mk node port'' =>
              rw [hsrc] at portC nid
              simp only at portC nid
              rw [portC, ← nid]
              simp only [routeWrites]
              exact List.mem_filterMap.mpr ⟨q, port, by simp [routeOutput, chosen]⟩
          obtain ⟨d', memberD', idD', _, presentD'⟩ :=
            applyWrites_token _ s c memberC (entryC.trans entry0) safeS.channelIds (.item item) hit
          have inView : d'.core ∈ s'.placedView := by rw [view]; exact placedView_member memberD'
          obtain ⟨e, memberE, coreE⟩ := List.mem_map.mp inView
          have idE : e.id = d'.id := by simpa using congrArg Channel.id coreE
          have same : e = c' := unique_channel safeS' memberE memberC' (idE.trans (idD'.trans (idC.trans idC'.symm)))
          subst same
          have itemIn : item ∈ e.items := by
            rw [Effects.item_mem]
            have := congrArg Channel.placed coreE
            simp only [Channel.core_placed] at this
            rw [this]; exact presentD'
          have tokens := view_tokens s' s _ safeS.channelIds view c memberC e memberE (idC'.trans idC.symm)
          have subset : e.items ⊆ [item] := by
            intro x hx
            rcases tokens (.item x) ((Effects.item_mem e x).mp hx) with old | ⟨w, hw, tw⟩
            · exact absurd ((Effects.item_mem c x).mpr old) (by rw [emptyC]; simp)
            · rcases List.mem_append.mp hw with route | eos
              · obtain ⟨id, tokW, valueEq⟩ := routeWrites_tokens _ _ _ _ w route
                rw [tokW] at tw
                cases tw
                simp only [Option.some.injEq] at valueEq
                subst valueEq
                simp
              · have := eosWrites_eos _ _ w eos
                rw [this] at tw; cases tw
          exact singleton_of_subset (items_nodup_of_invariants safeS' memberE) subset itemIn
        · rw [ite_eq_right chosen]
          have safeWrites : ∀ w ∈ routeWrites c0.path n (some item) (some arm) ++ eosWrites c0.path n,
              (∀ t, w ≠ .out c.path c.edge.src.node c.edge.src.port t) ∨ w.token = .eos := by
            intro w hw
            rcases List.mem_append.mp hw with route | eos
            · left
              intro t eq
              obtain ⟨q', _, inner⟩ := List.mem_filterMap.mp route
              cases hr : routeOutput (some arm) q'.name (some item) with
              | none => rw [hr] at inner; contradiction
              | some id =>
                rw [hr] at inner
                simp only [Option.map_some, Option.some.injEq] at inner
                subst inner
                simp only [routeOutput, Option.isNone_some, Bool.false_or] at hr
                split at hr
                · rename_i armEq'
                  have portEq : q'.name = c.edge.src.port := (Write.out.inj eq).2.2.1
                  have : c.edge.src.port = q.name := by rw [edgeC]; exact portC
                  have armQ : arm = q.name := by
                    have := beq_iff_eq.mp (by simpa using armEq' : (some arm == some q'.name) = true)
                    rw [Option.some.injEq] at this
                    rw [this, portEq, ‹c.edge.src.port = q.name›]
                  exact chosen armQ.symm
                · contradiction
            · right; exact eosWrites_eos _ _ w eos
          obtain ⟨d', memberD', idD', _, itemsD'⟩ :=
            applyWrites_items_untouched _ s c memberC (entryC.trans entry0) safeS.channelIds safeWrites
          have inView : d'.core ∈ s'.placedView := by rw [view]; exact placedView_member memberD'
          obtain ⟨e, memberE, coreE⟩ := List.mem_map.mp inView
          have idE : e.id = d'.id := by simpa using congrArg Channel.id coreE
          have same : e = c' := unique_channel safeS' memberE memberC' (idE.trans (idD'.trans (idC.trans idC'.symm)))
          subst same
          have itemsE : e.items = d'.items := by simpa using congrArg Channel.items coreE
          rw [itemsE, itemsD', emptyC]
      · let j := makeInstance c0.path n .succeeded inputs
        have memberJ : j ∈ s'.instances := by rw [instances]; simp [j]
        obtain ⟨k, memberK, idK, statusK⟩ := rest.retains_status safeS' j memberJ (.inl rfl)
        obtain ⟨nodeK, pathK, _, _⟩ := rest.input_snapshot safeS' j k memberJ memberK idK.symm
        exact ⟨k, memberK, pathK, nodeK.trans nid, statusK⟩
  · rw [kind] at k; cases k
  · rw [kind] at k; cases k
  · rw [kind] at k; cases k
  · rw [kind] at k; cases k
  · rw [kind] at k; simp at k
  · rcases k with k | k <;> (rw [kind] at k; cases k)
  · rw [kind] at k; cases k
  · subst eq
    exact .inr (skip_closing_final oracle head allowed accepted rest safe0 safeS active n found
      (by rw [kind]; intro h; cases h) c0 member0 empty0 entry0 rfl rfl c memberC idC c' memberC' idC' closedC' cl memberL idL)


/-- Final contents of one output channel of a Collect node (never skipped: stream input). -/
theorem collect_output_final (oracle : ScopedOracle) {s0 last : State} {ops : List Op}
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (safe0 : Invariants s0) (finished : succeededDrained last = true)
    (n : Node) (c0 : Channel) (found : s0.node? c0.path c0.edge.src.node = some n) (kind : n.kind = .collect)
    (streamInput : allKind n.inputs .plain = false)
    (fresh0 : ∀ j ∈ s0.instances, ¬ (j.path = c0.path ∧ j.node = c0.edge.src.node))
    (q : Port) (port : q ∈ n.outputs) (portC : c0.edge.src.port = q.name)
    (member0 : c0 ∈ s0.channels) (empty0 : c0.placed = []) (entry0 : c0.entry = false)
    (cl : Channel) (memberL : cl ∈ last.channels) (idL : cl.id = c0.id) :
    ∃ d ∈ last.channels, d.path = c0.path ∧ d.exit = false ∧ d.edge.dst.node = c0.edge.src.node ∧ d.closed = true ∧
      cl.items = [derivedItem "list" c0.path c0.edge.src.node (sortedItems d.items)] ∧
      ∃ i ∈ last.instances, i.path = c0.path ∧ i.node = c0.edge.src.node ∧ i.status = .succeeded := by
  have closedL := closed_of_drained finished memberL
  have open0 : Token.eos ∉ c0.placed := by rw [empty0]; simp
  have present : Token.eos ∈ cl.placed := by simpa [Channel.closed] using closedL
  obtain ⟨pre, op, post, s, s', c, c', _, head, allowed, accepted, rest, safeS, active,
    memberC, idC, layoutC, absentC, memberC', idC', layoutC', presentC', _, target⟩ :=
    token_step run safe0 .eos c0 member0 open0 entry0 cl memberL idL present
  have nodeS := head.node c0.path c0.edge.src.node n found
  have safeS' := preserves_invariants s s' op safeS accepted
  have safeLast : Invariants last := rest.invariants safeS'
  obtain ⟨_, edgeC, pathC, entryC, _, kindC⟩ := Channel.layout_fields layoutC
  have closedC' : c'.closed = true := by simpa [Channel.closed] using presentC'
  have finalPlaced : cl.placed = c'.placed := by
    obtain ⟨e, memberE, idE, placedE⟩ := rest.retains_closed_channel safeS' c' memberC' closedC'
    have same : e = cl := unique_channel safeLast memberE memberL (idE.trans (idC'.trans idL.symm))
    subst same
    exact placedE
  rcases target_shape s s' op safeS active accepted _ _ target n nodeS with
      ⟨_, _, _, _, _, _, k⟩ | ⟨_, _, _, _, _, k⟩ | ⟨_, k⟩ | ⟨_, _, _, k⟩ | ⟨_, _, _, k⟩ | ⟨eq, _⟩
    | ⟨_, _, _, k⟩ | ⟨_, _, _, k⟩ | ⟨_, k⟩ | ⟨_, _, _, k⟩ | ⟨_, _, _, _, _, k⟩ | ⟨_, plainK⟩
  · rw [kind] at k; cases k
  · rw [kind] at k; cases k
  · rw [kind] at k; cases k
  · rw [kind] at k; cases k
  · rw [kind] at k; cases k
  · -- fireCollect
    subst eq
    rcases step_ok_cases s _ s' accepted with ⟨a, _⟩ | ⟨_, _, prepared, _, _⟩
    · rw [active] at a; contradiction
    · have executed := prepareWith_body transitionOrIdle s s' _ prepared
      simp only [transitionOrIdle] at executed
      obtain ⟨n', c1, hn, _, hc1, closed1, _, view, instances, _, _⟩ := effect_fireCollect s s' _ _ executed
      have sameN := node?_of_getNode nodeS hn
      subst n'
      have nid := getNode_id s _ _ n hn
      have member1 : c1 ∈ s.incoming c0.path c0.edge.src.node := List.mem_of_mem_head? hc1
      have inChannels1 : c1 ∈ s.channels := (List.mem_filter.mp member1).1
      have fields1 := (List.mem_filter.mp member1).2
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at fields1
      let listId := derivedItem "list" c0.path c0.edge.src.node (sortedItems c1.items)
      -- input channel at the end
      have runS : ConformingSteps (fun s op => oracleConforms oracle s op = true) s (.fireCollect c0.path c0.edge.src.node :: post) last :=
        .cons allowed accepted rest
      obtain ⟨e, memberE, idE, placedE⟩ := runS.retains_closed_channel safeS c1 inChannels1 closed1
      obtain ⟨e', memberE', idE', layoutE', _⟩ := run_image runS safeS c1 inChannels1
      have sameE : e' = e := unique_channel safeLast memberE' memberE (idE'.trans idE.symm)
      subst sameE
      obtain ⟨_, edgeE, pathE, _, exitE, _⟩ := Channel.layout_fields layoutE'
      refine ⟨e', memberE, pathE.trans fields1.1.1, exitE.trans fields1.1.2, by rw [edgeE]; exact fields1.2, ?_, ?_, ?_⟩
      · simpa [Channel.closed, placedE] using closed1
      · -- the output holds exactly the list identifier
        have emptyC : c.items = [] := by
          cases hi : c.items with
          | nil => rfl
          | cons x xs =>
            exfalso
            obtain ⟨j, memberJ, pathJ, nodeJ⟩ := items_imply_instance oracle head safe0 n c0 found member0 empty0 entry0
              c memberC idC x (by rw [hi]; simp)
            have triggerJ := instance_trigger_none oracle head safe0 _ _ n found (fun body h => by rw [kind] at h; cases h)
              fresh0 j memberJ pathJ nodeJ
            have fresh := fresh_of_append safeS' _ instances j memberJ
            apply fresh
            simp only [instanceKey, makeInstance, pathJ, nodeJ, triggerJ, nid]
        have hit : Write.out c.path c.edge.src.node c.edge.src.port (.item listId) ∈
            routeWrites c0.path n (some listId) none ++ eosWrites c0.path n := by
          apply List.mem_append_left
          rw [pathC, edgeC]
          cases hsrc : c0.edge.src with
          | mk node port'' =>
            rw [hsrc] at portC nid
            simp only at portC nid
            rw [portC, ← nid]
            exact routeWrites_all_mem c0.path n listId q port
        obtain ⟨d', memberD', idD', _, presentD'⟩ :=
          applyWrites_token _ s c memberC (entryC.trans entry0) safeS.channelIds (.item listId) hit
        have inView : d'.core ∈ s'.placedView := by rw [view]; exact placedView_member memberD'
        obtain ⟨f, memberF, coreF⟩ := List.mem_map.mp inView
        have idF : f.id = d'.id := by simpa using congrArg Channel.id coreF
        have sameF : f = c' := unique_channel safeS' memberF memberC' (idF.trans (idD'.trans (idC.trans idC'.symm)))
        subst sameF
        have itemIn : listId ∈ f.items := by
          rw [Effects.item_mem]
          have := congrArg Channel.placed coreF
          simp only [Channel.core_placed] at this
          rw [this]; exact presentD'
        have tokens := view_tokens s' s _ safeS.channelIds view c memberC f memberF (idC'.trans idC.symm)
        have subset : f.items ⊆ [listId] := by
          intro x hx
          rcases tokens (.item x) ((Effects.item_mem f x).mp hx) with old | ⟨w, hw, tw⟩
          · exact absurd ((Effects.item_mem c x).mpr old) (by rw [emptyC]; simp)
          · rcases List.mem_append.mp hw with route | eos
            · obtain ⟨id, tokW, valueEq⟩ := routeWrites_tokens _ _ _ _ w route
              rw [tokW] at tw
              cases tw
              simp only [Option.some.injEq] at valueEq
              subst valueEq
              simp [listId]
            · have := eosWrites_eos _ _ w eos
              rw [this] at tw; cases tw
        have itemsF : f.items = [listId] := singleton_of_subset (items_nodup_of_invariants safeS' memberF) subset itemIn
        rw [show cl.items = f.items from by simp only [Channel.items, finalPlaced], itemsF]
        simp only [listId, Channel.items, placedE]
      · let j := makeInstance c0.path n .succeeded ((sortedItems c1.items).map ("item", ·))
        have memberJ : j ∈ s'.instances := by rw [instances]; simp [j]
        obtain ⟨k, memberK, idK, statusK⟩ := rest.retains_status safeS' j memberJ (.inl rfl)
        obtain ⟨nodeK, pathK, _, _⟩ := rest.input_snapshot safeS' j k memberJ memberK idK.symm
        exact ⟨k, memberK, pathK, nodeK.trans nid, statusK⟩
  · rw [kind] at k; cases k
  · rw [kind] at k; cases k
  · rw [kind] at k; simp at k
  · rcases k with k | k <;> (rw [kind] at k; cases k)
  · rw [kind] at k; cases k
  · rw [plainK] at streamInput; contradiction

end Suimon
