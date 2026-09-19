import Suimon.Theorems.ChildPartition

namespace Suimon
open Semantics

theorem flatMap_congr_on {α β : Type} {xs : List α} {f g : α → List β}
    (same : ∀ x ∈ xs, f x = g x) : xs.flatMap f = xs.flatMap g :=
  congrArg List.flatten (List.map_congr_left same)

theorem flatMap_filtered {α β : Type} (xs : List α) (p : α → Bool) (f : α → List β) :
    (xs.filter p).flatMap f = xs.flatMap (fun x => if p x then f x else []) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hx : p x <;> simp [hx, ih]

def ownData (g : Graph) (P : Path) (inputs : List Input) (values : Values) : ChannelData :=
  ({path := P, graph := g} : Frame).channels.map fun c =>
    (c.id, canonical (if c.entry then ((inputs.find? (·.entry == c.edge.dst)).map (·.items)).getD []
      else outputItems (values c.edge.src.node).outputs c.edge.src.port))

theorem list_nodup_of_map {α β : Type} (f : α → β) {xs : List α} (distinct : (xs.map f).Nodup) : xs.Nodup :=
  (List.pairwise_map.mp distinct).imp (fun different equal => different (congrArg f equal))

theorem Scope.template_ids_nodup {s : State} {P : Path} {g : Graph} (sc : Scope s P g) :
    (({path := P, graph := g} : Frame).channels.map Channel.id).Nodup := by
  have keys : (s.frameChannels.map Channel.id).Nodup := by
    rw [← sc.layout, State.channelLayout, List.map_map]
    exact sc.safe.channelIds
  have each : ∀ f ∈ s.frames, (f.channels.map Channel.id).Nodup := by
    have combined : List.Pairwise (fun a b : String => a ≠ b)
        (s.frames.flatMap fun f => f.channels.map Channel.id) := by
      change List.Pairwise (fun a b : String => a ≠ b) _ at keys
      simpa only [State.frameChannels, List.map_flatMap] using keys
    exact (List.pairwise_flatMap.mp combined).1
  obtain ⟨f, memberF, pathF, graphF⟩ := sc.frame
  have distinct := each f memberF
  rwa [Frame.channels_template, pathF, graphF] at distinct

theorem frame_row_value (oracle : ScopedOracle) {s0 last : State} {ops : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input} (fs : FrameStart s0 P g inputs0)
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (finished : succeededDrained last = true) (c : Channel) (memberC : c ∈ last.channels) (pathC : c.path = P) :
    canonical (if c.entry then ((inputs0.find? (·.entry == c.edge.dst)).map (·.items)).getD []
      else outputItems (frameValues oracle last g P c.edge.src.node).outputs c.edge.src.port) = bag c := by
  have sc := fs.scope.persist run
  cases entry : c.entry with
  | true => simpa only [entry, ↓reduceIte] using (fs.entry_bag run c memberC pathC entry).symm
  | false =>
    obtain ⟨body, valid⟩ := sc.valid
    obtain ⟨q, foundQ, _⟩ := Frame.channel_output {path := P, graph := g} body valid c.layout (sc.template c memberC pathC) entry
    simp only [Channel.layout_edge] at foundQ
    cases foundN : g.node? c.edge.src.node with
    | none => simp [Graph.output?, foundN] at foundQ
    | some n =>
      have memberN := List.mem_of_find?_eq_some foundN
      have nodeN : n.id = c.edge.src.node := by simpa using List.find?_some foundN
      have value := node_output_value oracle run fs finished n memberN c memberC pathC entry nodeN.symm
      simpa only [entry, Bool.false_eq_true, ↓reduceIte, ← nodeN, frameValues_node oracle sc n memberN] using value.symm

theorem frame_own_perm (oracle : ScopedOracle) {s0 last : State} {ops : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input} (fs : FrameStart s0 P g inputs0)
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (finished : succeededDrained last = true) :
    (ownData g P inputs0 (frameValues oracle last g P)).Perm
      ((last.channels.filter (·.path == P)).map fun c => (c.id, bag c)) := by
  have sc := fs.scope.persist run
  have leftKeys : ((ownData g P inputs0 (frameValues oracle last g P)).map (·.1)).Nodup := by
    simpa only [ownData, List.map_map, Function.comp_def] using sc.template_ids_nodup
  have rightKeys : (((last.channels.filter (·.path == P)).map fun c => (c.id, bag c)).map (·.1)).Nodup := by
    simpa only [List.map_map, Function.comp_def] using sc.safe.channelIds.sublist (List.filter_sublist.map Channel.id)
  apply (List.perm_ext_iff_of_nodup (list_nodup_of_map _ leftKeys) (list_nodup_of_map _ rightKeys)).mpr
  intro row
  constructor
  · intro member
    obtain ⟨d, memberD, rowD⟩ := List.mem_map.mp member
    obtain ⟨c, memberC, layoutC⟩ := sc.realized d memberD
    have pathD := Frame.channel_path {path := P, graph := g} d memberD
    have pathC : c.path = P := by simpa only [Channel.layout_path] using (congrArg Channel.path layoutC).trans pathD
    have value := frame_row_value oracle fs run finished c memberC pathC
    apply List.mem_map.mpr
    refine ⟨c, List.mem_filter.mpr ⟨memberC, by simpa using pathC⟩, ?_⟩
    rw [← layoutC] at rowD
    exact (congrArg (fun items => (c.id, items)) value).symm.trans rowD
  · intro member
    obtain ⟨c, memberC, rowC⟩ := List.mem_map.mp member
    obtain ⟨memberC, pathC⟩ := List.mem_filter.mp memberC
    have path : c.path = P := by simpa using pathC
    have value := frame_row_value oracle fs run finished c memberC path
    exact List.mem_map.mpr ⟨c.layout, sc.template c memberC path, (congrArg (fun items => (c.id, items)) value).trans rowC⟩

theorem loopChannels_range (s : State) (P : Path) (N : NodeId) (start count : Nat) :
    loopChannels s P N start count = (List.range count).flatMap (fun k => subtreeBags s (childPath P N none (start + k))) := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    simp only [loopChannels, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, Nat.add_zero, ih, Function.comp_def]
    congr 1
    apply flatMap_congr_on
    intro k _
    congr 2
    omega

theorem node_children_paths (oracle : ScopedOracle) (s : State) (g : Graph) (P : Path) (n : Node) :
    (nodeValue oracle s g P n).children =
      (if suppressed n (stateInputs s P n) then [] else childPaths s P n).flatMap (subtreeBags s) := by
  unfold nodeValue primitive
  cases awake : suppressed n (stateInputs s P n) with
  | true => simp
  | false =>
    cases kind : n.kind <;> simp [kind, compoundValue, childPaths, loopChannels_range, List.flatMap_map, Nat.add_comm]

theorem frame_children_paths (oracle : ScopedOracle) {s : State} {P : Path} {g : Graph} (sc : Scope s P g) :
    g.nodes.flatMap (fun n => (frameValues oracle s g P n.id).children) =
      (allChildPaths s P g).flatMap (subtreeBags s) := by
  rw [allChildPaths, List.flatMap_assoc]
  rw [flatMap_filtered]
  apply flatMap_congr_on
  intro n memberN
  rw [frameValues_node oracle sc n memberN, node_children_paths]
  cases suppressed n (stateInputs s P n) <;> rfl

/-- Distinct immediate child roots partition all proper descendants of a frame. --/
theorem frame_channel_partition (oracle : ScopedOracle) {s0 last : State} {ops : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input} (fs : FrameStart s0 P g inputs0) (ancestors : FrameAncestors s0)
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (complete : FrameCompletes oracle s0 last P g) (finished : succeededDrained last = true) :
    ((last.channels.filter (·.path == P)) ++
      (allChildPaths last P g).flatMap (fun Q => last.channels.filter (fun c => Q.isPrefixOf c.path))).Perm
      (last.channels.filter (fun c => P.isPrefixOf c.path)) := by
  have sc := fs.scope.persist run
  have tree := run.frameAncestors fs.scope.safe ancestors
  have distinct := allChildPaths_nodup oracle fs run complete finished
  have channelsDistinct := list_nodup_of_map Channel.id sc.safe.channelIds
  have roots : ∀ Q ∈ allChildPaths last P g, ∃ segment, Q = P ++ [segment] := by
    intro Q memberQ
    obtain ⟨n, _, _, inNode⟩ := mem_allChildPaths.mp memberQ
    exact childPaths_immediate last P n Q inNode
  have disjoint : ∀ Q ∈ allChildPaths last P g, ∀ R ∈ allChildPaths last P g, Q ≠ R →
      ∀ c ∈ last.channels.filter (fun c => Q.isPrefixOf c.path),
      ∀ d ∈ last.channels.filter (fun c => R.isPrefixOf c.path), c ≠ d := by
    intro Q memberQ R memberR different c memberC d memberD equal
    subst d
    have qPrefix : Q <+: c.path := List.isPrefixOf_iff_prefix.mp (List.mem_filter.mp memberC).2
    have rPrefix : R <+: c.path := List.isPrefixOf_iff_prefix.mp (List.mem_filter.mp memberD).2
    obtain ⟨_, eqQ⟩ := roots Q memberQ
    obtain ⟨_, eqR⟩ := roots R memberR
    have lengths : Q.length = R.length := by simp [eqQ, eqR]
    exact different ((List.prefix_of_prefix_length_le qPrefix rPrefix (by omega)).eq_of_length lengths)
  have childDistinct := nodup_flatMap_disjoint _ _ distinct
    (fun _ _ => channelsDistinct.sublist List.filter_sublist) disjoint
  have combinedDistinct : ((last.channels.filter (·.path == P)) ++
      (allChildPaths last P g).flatMap (fun Q => last.channels.filter (fun c => Q.isPrefixOf c.path))).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨channelsDistinct.sublist List.filter_sublist, childDistinct, ?_⟩
    intro c memberC d memberD equal
    subst d
    have pathC : c.path = P := by simpa using (List.mem_filter.mp memberC).2
    obtain ⟨Q, memberQ, below⟩ := List.mem_flatMap.mp memberD
    have prefixQ : Q <+: c.path := List.isPrefixOf_iff_prefix.mp (List.mem_filter.mp below).2
    obtain ⟨segment, eqQ⟩ := roots Q memberQ
    have lengths := prefixQ.length_le
    simp only [eqQ, pathC, List.length_append, List.length_singleton] at lengths
    omega
  apply (List.perm_ext_iff_of_nodup combinedDistinct (channelsDistinct.sublist List.filter_sublist)).mpr
  intro c
  constructor
  · intro member
    rcases List.mem_append.mp member with own | child
    · obtain ⟨memberC, pathC⟩ := List.mem_filter.mp own
      exact List.mem_filter.mpr ⟨memberC, by simpa [beq_iff_eq.mp pathC]⟩
    · obtain ⟨Q, memberQ, memberC⟩ := List.mem_flatMap.mp child
      obtain ⟨memberC, prefixQ⟩ := List.mem_filter.mp memberC
      obtain ⟨segment, eqQ⟩ := roots Q memberQ
      apply List.mem_filter.mpr
      refine ⟨memberC, List.isPrefixOf_iff_prefix.mpr ?_⟩
      exact (show P <+: Q by rw [eqQ]; exact List.prefix_append _ _).trans (List.isPrefixOf_iff_prefix.mp prefixQ)
  · intro member
    obtain ⟨memberC, prefixC⟩ := List.mem_filter.mp member
    have prefixP : P <+: c.path := List.isPrefixOf_iff_prefix.mp prefixC
    by_cases own : c.path = P
    · exact List.mem_append_left _ (List.mem_filter.mpr ⟨memberC, by simpa using own⟩)
    · obtain ⟨suffix, pathC⟩ := prefixP
      cases suffix with
      | nil => simp only [List.append_nil] at pathC; exact False.elim (own pathC.symm)
      | cons segment suffix =>
        let Q := P ++ [segment]
        have prefixQ : Q <+: c.path := ⟨suffix, by simp only [Q, List.append_assoc, List.singleton_append]; exact pathC⟩
        obtain ⟨frame, memberFrame, _, pathFrame⟩ := sc.layout.channel_frame c memberC
        obtain ⟨child, memberChild, pathChild⟩ := tree frame memberFrame Q (by rw [← pathFrame]; exact prefixQ)
        have status : last.status = .succeeded := by
          simp only [succeededDrained, Bool.and_eq_true, beq_iff_eq] at finished
          exact finished.1.1
        have covered := immediate_child_covered oracle fs run complete status child memberChild segment pathChild
        rw [pathChild] at covered
        exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨Q, covered,
          List.mem_filter.mpr ⟨memberC, List.isPrefixOf_iff_prefix.mpr prefixQ⟩⟩)


theorem child_rows_perm (s : State) (paths : List Path) :
    (paths.flatMap (subtreeBags s)).Perm
      ((paths.flatMap (fun P => s.channels.filter (fun c => P.isPrefixOf c.path))).map fun c => (c.id, bag c)) := by
  induction paths with
  | nil => exact .nil
  | cons P paths ih =>
    simp only [List.flatMap_cons, List.map_append]
    exact (List.mergeSort_perm _ _).append ih

/-- The assembled channel multiset includes exactly the root's own entry,
    edge and exit channels and all descendant frame channels. --/
theorem frame_channels_equations (oracle : ScopedOracle) {s0 last : State} {ops : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input} (fs : FrameStart s0 P g inputs0) (ancestors : FrameAncestors s0)
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (complete : FrameCompletes oracle s0 last P g) (finished : succeededDrained last = true) :
    (assemble g P inputs0 (frameValues oracle last g P)).channels = subtreeBags last P := by
  have sc := fs.scope.persist run
  have own := frame_own_perm oracle fs run finished
  have child := child_rows_perm last (allChildPaths last P g)
  have partition := (frame_channel_partition oracle fs ancestors run complete finished).map (fun c => (c.id, bag c))
  simp only [List.map_append] at partition
  have perm := (own.append child).trans partition
  have targetKeys : (((last.channels.filter (fun c => P.isPrefixOf c.path)).map fun c => (c.id, bag c)).map (·.1)).Nodup := by
    simpa only [List.map_map, Function.comp_def] using sc.safe.channelIds.sublist (List.filter_sublist.map Channel.id)
  have keys := (perm.map (·.1)).nodup_iff.mpr targetKeys
  change (ownData g P inputs0 (frameValues oracle last g P) ++
    g.nodes.flatMap (fun n => (frameValues oracle last g P n.id).children)).mergeSort (fun a b => a.1 ≤ b.1) = _
  rw [frame_children_paths oracle sc]
  exact sorted_data_eq_of_perm keys perm

end Suimon
