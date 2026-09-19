import Suimon.Theorems.ChildFrames

namespace Suimon
open Semantics Effects

theorem nodup_subset_same_length_perm {α : Type} [DecidableEq α] {xs ys : List α}
    (distinct : xs.Nodup) (subset : xs ⊆ ys) (length : xs.length = ys.length) : xs.Perm ys := by
  induction xs generalizing ys with
  | nil => have empty : ys = [] := List.length_eq_zero_iff.mp length.symm; subst ys; exact .nil
  | cons x xs ih =>
    have memberX : x ∈ ys := subset (by simp)
    have parts := List.nodup_cons.mp distinct
    have subsetRest : xs ⊆ ys.erase x := by
      intro y memberY
      have notSame : y ≠ x := fun eq => parts.1 (eq ▸ memberY)
      exact (List.mem_erase_of_ne notSame).mpr (subset (by simp [memberY]))
    have lengthRest : xs.length = (ys.erase x).length := by
      simp only [List.length_cons] at length
      rw [List.length_erase_of_mem memberX]
      omega
    exact (List.Perm.cons x (ih parts.2 subsetRest lengthRest)).trans (List.perm_cons_erase memberX).symm

theorem nodup_map_on {α β : Type} (f : α → β) (xs : List α) (distinct : xs.Nodup)
    (injective : ∀ x ∈ xs, ∀ y ∈ xs, f x = f y → x = y) : (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨notX, nodup⟩ := List.nodup_cons.mp distinct
    apply List.nodup_cons.mpr
    constructor
    · intro present
      obtain ⟨y, memberY, eq⟩ := List.mem_map.mp present
      have same := injective y (by simp [memberY]) x (by simp) eq
      exact notX (same ▸ memberY)
    · exact ih nodup (fun a ha b hb eq => injective a (by simp [ha]) b (by simp [hb]) eq)

theorem childPaths_immediate (s : State) (P : Path) (n : Node) (Q : Path) (member : Q ∈ childPaths s P n) :
    ∃ segment, Q = P ++ [segment] := by
  cases kind : n.kind <;> simp only [childPaths, kind] at member
  all_goals try { simp at member }
  · obtain ⟨k, _, eq⟩ := List.mem_map.mp member
    exact ⟨_, eq.symm⟩
  · have eq : Q = childPath P n.id none 0 := by simpa using member
    exact ⟨_, eq⟩
  · obtain ⟨y, _, eq⟩ := List.mem_map.mp member
    exact ⟨_, eq.symm⟩

theorem ChildShape.member {s : State} {P : Path} {n : Node} {i : Instance} {f : Frame}
    (shape : ChildShape s P n i f) (safe : Invariants s) (memberI : i ∈ s.instances)
    (pathI : i.path = P) (nodeI : i.node = n.id) : f.path ∈ childPaths s P n := by
  rcases shape with ⟨body, kind, _, path, _⟩ | ⟨body, y, kind, _, path, _, present⟩ |
    ⟨body, limit, k, kind, trigger, path, _, positive, bound⟩
  · simp [childPaths, kind, path]
  · simp only [childPaths, kind]
    exact List.mem_map.mpr ⟨y, present, path.symm⟩
  · have found := nodeInstance?_of_mem safe i memberI trigger
    rw [pathI, nodeI] at found
    have count : loopCount s P n.id = i.iteration := by simp [loopCount, found]
    simp only [childPaths, kind]
    exact List.mem_map.mpr ⟨k - 1, List.mem_range.mpr (by omega), by rw [Nat.sub_add_cancel positive]; exact path.symm⟩

theorem loop_childPaths_owned (oracle : ScopedOracle) {s0 last : State} {ops : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input} (fs : FrameStart s0 P g inputs0)
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (finished : last.status = .succeeded)
    (n : Node) (memberN : n ∈ g.nodes) (body : Graph) (limit : Nat) (kind : n.kind = .loop body limit)
    (i : Instance) (memberI : i ∈ last.instances) (pathI : i.path = P) (nodeI : i.node = n.id) (triggerI : i.trigger = none) :
    ((last.frames.filter (·.owner == some i.id)).map Frame.path).Perm (childPaths last P n) := by
  have scL := fs.scope.persist run
  have owners := run.frameOwners fs.scope.safe fs.scope.distinct fs.owners
  have found := nodeInstance?_of_mem scL.safe i memberI triggerI
  rw [pathI, nodeI] at found
  have count : loopCount last P n.id = i.iteration := by simp [loopCount, found]
  have bounds := scL.safe
  simp only [Invariants, invariants, Bool.and_eq_true] at bounds
  have bound := List.all_eq_true.mp bounds.2 i memberI
  have nodeFound : last.node? i.path i.node = some n := by rw [pathI, nodeI]; exact scL.node?_of_mem n memberN
  simp only [nodeFound, kind, Bool.and_eq_true, beq_iff_eq] at bound
  have distinct : ((last.frames.filter (·.owner == some i.id)).map Frame.path).Nodup :=
    scL.distinct.sublist (List.filter_sublist.map Frame.path)
  apply nodup_subset_same_length_perm distinct
  · intro Q memberQ
    obtain ⟨f, memberF, eqQ⟩ := List.mem_map.mp memberQ
    obtain ⟨memberF, ownerF⟩ := List.mem_filter.mp memberF
    have owner : f.owner = some i.id := by simpa using ownerF
    obtain ⟨j, memberJ, idJ, segment, pathF⟩ := owners f memberF i.id owner
    have same := unique_instance scL.safe memberJ memberI idJ
    subst j
    rw [pathI] at pathF
    obtain ⟨m, memberM, j, memberJ, _, nodeJ, _, ownerJ, shape⟩ :=
      immediate_child_owner oracle fs run finished f memberF segment pathF
    have same := unique_instance scL.safe memberJ memberI (Option.some.inj (ownerJ.symm.trans owner))
    subst j
    have sameN := eq_of_mapped_nodup (·.id) g.nodes scL.nodes_nodup m n memberM memberN (nodeJ.symm.trans nodeI)
    subst m
    rw [← eqQ]
    exact shape.member scL.safe memberI pathI nodeI
  · simp only [List.length_map, childPaths, kind, List.length_range, count]
    exact bound.2


theorem completed_awake_succeeded (oracle : ScopedOracle) {s0 last : State} {ops : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input} (fs : FrameStart s0 P g inputs0)
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (complete : FrameCompletes oracle s0 last P g) (finished : last.status = .succeeded)
    (n : Node) (memberN : n ∈ g.nodes) (notCoalesce : n.kind ≠ .coalesce)
    (awake : suppressed n (stateInputs last P n) = false) :
    ∃ i ∈ last.instances, i.path = P ∧ i.node = n.id ∧ i.trigger = none ∧ i.status = .succeeded := by
  obtain ⟨i, memberI, pathI, nodeI, triggerI, status⟩ := complete.nodes fs.scope.safe n memberN
  refine ⟨i, memberI, pathI, nodeI, triggerI, ?_⟩
  rcases status with succeeded | cancelled
  · exact succeeded
  · obtain ⟨pre, post, t, t', head, allowed, accepted, executed, rest⟩ :=
      cancelled_origin_skip oracle fs run finished n memberN i memberI pathI nodeI cancelled
    have sup := skip_suppressed oracle fs head n memberN notCoalesce allowed accepted executed rest
    rw [awake] at sup; contradiction

theorem forEach_trigger_frame (oracle : ScopedOracle) {s0 last : State} {ops : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input} (fs : FrameStart s0 P g inputs0)
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (finished : succeededDrained last = true)
    (n : Node) (memberN : n ∈ g.nodes) (body : Graph) (kind : n.kind = .forEach body)
    (y : ItemId) (present : y ∈ (((stateInputs last P n).head?.map (·.2)).getD [])) :
    ∃ f ∈ last.frames, ∃ i ∈ last.instances, f.path = childPath P n.id (some y) 0 ∧ f.owner = some i.id ∧
      i.path = P ∧ i.node = n.id ∧ i.trigger = some y := by
  have scL := fs.scope.persist run
  obtain ⟨p, _, ins, _, _⟩ := forEach_ports fs.scope n memberN body kind
  obtain ⟨c, memberC, found, pathC, exitC, dstC, _, _, _⟩ := scL.input_channel n memberN p (by simp [ins])
  have inputEq : ((stateInputs last P n).head?.map (·.2)).getD [] = bag c := by simp [stateInputs, ins, found]
  have drained : c.pendingItems = [] := by
    have all := finished
    simp only [succeededDrained, Bool.and_eq_true] at all
    have fact := List.all_eq_true.mp all.1.2 c memberC
    simpa [exitC] using (Bool.and_eq_true_iff.mp fact).2
  obtain ⟨pre, post, t, t', _, head, allowed, accepted, rest, safeT, executed, memberStart⟩ :=
    forEach_input_spawn oracle run fs n memberN body kind c memberC pathC exitC (congrArg PortRef.node dstC)
      drained y (by rw [inputEq] at present; exact (sortedItems_perm c.items).mem_iff.mp present)
  have safeNext := preserves_invariants t t' _ safeT accepted
  let initial := makeInstance P n .waitingInputs [("item", y)] (some y)
  obtain ⟨_, m, b, _, got, kindM, _, _, f, opened, _, _, _, _, frames, _⟩ :=
    effect_spawn t t' P n.id y safeT.channelIds executed
  have sameN := node?_of_getNode (head.node P n.id n (fs.scope.node?_of_mem n memberN)) got
  subst m
  obtain ⟨j, memberJ, bindingJ⟩ := rest.retains_binding safeNext initial memberStart
  have memberF : f ∈ t'.frames := by rw [frames]; simp
  obtain ⟨f', memberF', pathF'⟩ := rest.frame_path f memberF
  have definitions := rest.frame_definition f memberF scL.distinct f' memberF' pathF'
  refine ⟨f', memberF', j, memberJ, ?_, ?_, Instance.binding_path bindingJ, Instance.binding_node bindingJ,
    Instance.binding_trigger bindingJ⟩
  · rw [pathF', opened.1]; rfl
  · rw [definitions.2.1, opened.2.2.1]
    exact congrArg some (show j.id = initial.id from congrArg Prod.fst bindingJ).symm

theorem childPaths_nodup (oracle : ScopedOracle) {s0 last : State} {ops : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input} (fs : FrameStart s0 P g inputs0)
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (complete : FrameCompletes oracle s0 last P g) (finished : succeededDrained last = true)
    (n : Node) (memberN : n ∈ g.nodes) (awake : suppressed n (stateInputs last P n) = false) :
    (childPaths last P n).Nodup := by
  have scL := fs.scope.persist run
  have finalStatus : last.status = .succeeded := by
    simp only [succeededDrained, Bool.and_eq_true, beq_iff_eq] at finished
    exact finished.1.1
  cases kind : n.kind <;> simp only [childPaths, kind]
  all_goals try { simp }
  · rename_i body limit
    obtain ⟨i, memberI, pathI, nodeI, triggerI, _⟩ := completed_awake_succeeded oracle fs run complete finalStatus n memberN
      (by simp [kind]) awake
    have perm := loop_childPaths_owned oracle fs run finalStatus n memberN body limit kind i memberI pathI nodeI triggerI
    have distinct := perm.nodup_iff.mp (scL.distinct.sublist (List.filter_sublist.map Frame.path))
    simpa only [childPaths, kind] using distinct
  · rename_i body
    obtain ⟨p, _, ins, _, _⟩ := forEach_ports fs.scope n memberN body kind
    obtain ⟨c, memberC, found, _, _, _, _, _, _⟩ := scL.input_channel n memberN p (by simp [ins])
    have inputEq : ((stateInputs last P n).head?.map (·.2)).getD [] = bag c := by simp [stateInputs, ins, found]
    have distinct : (((stateInputs last P n).head?.map (·.2)).getD []).Nodup := by
      rw [inputEq]; exact sortedItems_nodup (items_nodup_of_invariants scL.safe memberC)
    apply nodup_map_on _ _ distinct
    intro y memberY z memberZ same
    obtain ⟨f, memberF, i, memberI, pathF, ownerF, _, _, triggerI⟩ := forEach_trigger_frame oracle fs run finished n memberN body kind y memberY
    obtain ⟨h, memberH, j, memberJ, pathH, ownerH, _, _, triggerJ⟩ := forEach_trigger_frame oracle fs run finished n memberN body kind z memberZ
    have sameF := eq_of_mapped_nodup Frame.path last.frames scL.distinct f h memberF memberH (pathF.trans (same.trans pathH.symm))
    subst h
    have sameI := unique_instance scL.safe memberI memberJ (Option.some.inj (ownerF.symm.trans ownerH))
    subst j
    exact Option.some.inj (triggerI.symm.trans triggerJ)


theorem childPaths_realized (oracle : ScopedOracle) {s0 last : State} {ops : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input} (fs : FrameStart s0 P g inputs0)
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (complete : FrameCompletes oracle s0 last P g) (finished : succeededDrained last = true)
    (n : Node) (memberN : n ∈ g.nodes) (awake : suppressed n (stateInputs last P n) = false)
    (Q : Path) (memberQ : Q ∈ childPaths last P n) :
    ∃ f ∈ last.frames, ∃ i ∈ last.instances, f.path = Q ∧ f.owner = some i.id ∧ i.path = P ∧ i.node = n.id := by
  have scL := fs.scope.persist run
  have finalStatus : last.status = .succeeded := by
    simp only [succeededDrained, Bool.and_eq_true, beq_iff_eq] at finished
    exact finished.1.1
  cases kind : n.kind <;> simp only [childPaths, kind] at memberQ
  all_goals try { simp at memberQ }
  · rename_i body limit
    obtain ⟨i, memberI, pathI, nodeI, triggerI, _⟩ := completed_awake_succeeded oracle fs run complete finalStatus n memberN
      (by simp [kind]) awake
    have perm := loop_childPaths_owned oracle fs run finalStatus n memberN body limit kind i memberI pathI nodeI triggerI
    have present : Q ∈ childPaths last P n := by simpa only [childPaths, kind] using memberQ
    obtain ⟨f, memberF, eqQ⟩ := List.mem_map.mp (perm.symm.subset present)
    obtain ⟨memberF, ownerF⟩ := List.mem_filter.mp memberF
    exact ⟨f, memberF, i, memberI, eqQ, by simpa using ownerF, pathI, nodeI⟩
  · rename_i body
    have eqQ : Q = childPath P n.id none 0 := by simpa using memberQ
    obtain ⟨i, memberI, pathI, nodeI, _, succeeded⟩ := completed_awake_succeeded oracle fs run complete finalStatus n memberN
      (by simp [kind]) awake
    obtain ⟨_, _, _, f, memberF, pathF, _, ownerF⟩ := sub_instance_shape oracle run fs n memberN body kind i memberI pathI nodeI
      (by rw [succeeded]; decide)
    exact ⟨f, memberF, i, memberI, pathF.trans eqQ.symm, ownerF, pathI, nodeI⟩
  · rename_i body
    obtain ⟨y, memberY, eqQ⟩ := List.mem_map.mp memberQ
    obtain ⟨f, memberF, i, memberI, pathF, ownerF, pathI, nodeI, _⟩ :=
      forEach_trigger_frame oracle fs run finished n memberN body kind y memberY
    exact ⟨f, memberF, i, memberI, pathF.trans eqQ, ownerF, pathI, nodeI⟩

theorem child_owner_awake (oracle : ScopedOracle) {s0 last : State} {ops : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input} (fs : FrameStart s0 P g inputs0)
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (complete : FrameCompletes oracle s0 last P g)
    (n : Node) (memberN : n ∈ g.nodes) (i : Instance) (memberI : i ∈ last.instances)
    (pathI : i.path = P) (nodeI : i.node = n.id) (notCancelled : i.status ≠ .cancelled)
    (f : Frame) (shape : ChildShape last P n i f) : suppressed n (stateInputs last P n) = false := by
  have scL := fs.scope.persist run
  have staticSuccess : i.trigger = none → i.status = .succeeded := by
    intro triggerI
    obtain ⟨j, memberJ, pathJ, nodeJ, triggerJ, status⟩ := complete.nodes fs.scope.safe n memberN
    have foundI := nodeInstance?_of_mem scL.safe i memberI triggerI
    have foundJ := nodeInstance?_of_mem scL.safe j memberJ triggerJ
    rw [pathI, nodeI] at foundI
    rw [pathJ, nodeJ, foundI] at foundJ
    have same := Option.some.inj foundJ
    subst j
    exact status.resolve_right notCancelled
  rcases shape with ⟨body, kind, trigger, _⟩ | ⟨body, y, kind, _⟩ | ⟨body, limit, k, kind, trigger, _⟩
  · obtain ⟨values, _, channels⟩ := plain_instance_inputs oracle run fs n memberN
      (.inr (.inr (.inr (.inl ⟨body, kind⟩)))) i memberI pathI nodeI (staticSuccess trigger)
    rw [stateInputs_of_singletons scL n memberN values channels]
    exact suppressed_singletons n values (by simp [kind])
  · obtain ⟨p, _, ins, _, stream⟩ := forEach_ports fs.scope n memberN body kind
    have plain := allKind_plain_false_of_stream n.inputs p (by simp [ins]) stream
    simp [suppressed, plain]
  · obtain ⟨values, _, channels⟩ := plain_instance_inputs oracle run fs n memberN
      (.inr (.inr (.inr (.inr ⟨body, limit, kind⟩)))) i memberI pathI nodeI (staticSuccess trigger)
    rw [stateInputs_of_singletons scL n memberN values channels]
    exact suppressed_singletons n values (by simp [kind])

def allChildPaths (s : State) (P : Path) (g : Graph) : List Path :=
  (g.nodes.filter fun n => !(suppressed n (stateInputs s P n))).flatMap (childPaths s P)

theorem mem_allChildPaths {s : State} {P : Path} {g : Graph} {Q : Path} :
    Q ∈ allChildPaths s P g ↔ ∃ n ∈ g.nodes, suppressed n (stateInputs s P n) = false ∧ Q ∈ childPaths s P n := by
  simp [allChildPaths, List.mem_flatMap, List.mem_filter, and_assoc]

theorem nodup_flatMap_disjoint {α β : Type} (xs : List α) (f : α → List β) (distinct : xs.Nodup)
    (each : ∀ x ∈ xs, (f x).Nodup)
    (disjoint : ∀ x ∈ xs, ∀ y ∈ xs, x ≠ y → ∀ a ∈ f x, ∀ b ∈ f y, a ≠ b) : (xs.flatMap f).Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨notX, nodup⟩ := List.nodup_cons.mp distinct
    simp only [List.flatMap_cons, List.nodup_append]
    refine ⟨each x (by simp), ih nodup (fun y hy => each y (by simp [hy]))
      (fun y hy z hz ne => disjoint y (by simp [hy]) z (by simp [hz]) ne), ?_⟩
    intro a memberA b memberB
    obtain ⟨y, memberY, inY⟩ := List.mem_flatMap.mp memberB
    exact disjoint x (by simp) y (by simp [memberY]) (fun eq => notX (eq ▸ memberY)) a memberA b inY

theorem allChildPaths_nodup (oracle : ScopedOracle) {s0 last : State} {ops : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input} (fs : FrameStart s0 P g inputs0)
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (complete : FrameCompletes oracle s0 last P g) (finished : succeededDrained last = true) :
    (allChildPaths last P g).Nodup := by
  have scL := fs.scope.persist run
  have nodeDistinct : g.nodes.Nodup := (List.pairwise_map.mp scL.nodes_nodup).imp (fun different equal => different (congrArg Node.id equal))
  apply nodup_flatMap_disjoint _ _ (nodeDistinct.sublist List.filter_sublist)
  · intro n memberN
    obtain ⟨memberN, awake⟩ := List.mem_filter.mp memberN
    exact childPaths_nodup oracle fs run complete finished n memberN (by simpa using awake)
  · intro n memberN m memberM different Q memberQ R memberR equal
    obtain ⟨memberN, awakeN⟩ := List.mem_filter.mp memberN
    obtain ⟨memberM, awakeM⟩ := List.mem_filter.mp memberM
    obtain ⟨f, memberF, i, memberI, pathF, ownerF, _, nodeI⟩ :=
      childPaths_realized oracle fs run complete finished n memberN (by simpa using awakeN) Q memberQ
    obtain ⟨h, memberH, j, memberJ, pathH, ownerH, _, nodeJ⟩ :=
      childPaths_realized oracle fs run complete finished m memberM (by simpa using awakeM) R memberR
    have sameF := eq_of_mapped_nodup Frame.path last.frames scL.distinct f h memberF memberH (pathF.trans (equal.trans pathH.symm))
    subst h
    have sameI := unique_instance scL.safe memberI memberJ (Option.some.inj (ownerF.symm.trans ownerH))
    subst j
    exact different (eq_of_mapped_nodup (·.id) g.nodes scL.nodes_nodup n m memberN memberM (nodeI.symm.trans nodeJ))

theorem immediate_child_covered (oracle : ScopedOracle) {s0 last : State} {ops : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input} (fs : FrameStart s0 P g inputs0)
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (complete : FrameCompletes oracle s0 last P g) (finished : last.status = .succeeded)
    (f : Frame) (memberF : f ∈ last.frames) (segment : String) (immediate : f.path = P ++ [segment]) :
    f.path ∈ allChildPaths last P g := by
  obtain ⟨n, memberN, i, memberI, pathI, nodeI, notCancelled, _, shape⟩ :=
    immediate_child_owner oracle fs run finished f memberF segment immediate
  exact mem_allChildPaths.mpr ⟨n, memberN, child_owner_awake oracle fs run complete n memberN i memberI pathI nodeI notCancelled f shape,
    shape.member (run.invariants fs.scope.safe) memberI pathI nodeI⟩

end Suimon
