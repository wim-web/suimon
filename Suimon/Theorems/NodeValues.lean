import Suimon.Theorems.Created

/-! Node results read off a final state, and the channel equations they satisfy. -/

namespace Suimon
open Semantics

def loopCount (s : State) (P : Path) (N : NodeId) : Nat := ((s.nodeInstance? P N).map (·.iteration)).getD 0

def loopChannels (s : State) (P : Path) (N : NodeId) : Nat → Nat → ChannelData
  | _, 0 => []
  | j, m + 1 => subtreeBags s (childPath P N none j) ++ loopChannels s P N (j + 1) m

def compoundValue (s : State) (P : Path) (n : Node) : NodeResult :=
  match n.kind with
  | .subworkflow body =>
    { outputs := (n.outputs.zip (exitItems s (childPath P n.id none 0) body)).map (fun (p, items) => { port := p.name, items })
      children := subtreeBags s (childPath P n.id none 0) }
  | .forEach body =>
    let items := ((stateInputs s P n).head?.map (·.2)).getD []
    { outputs := ports n (fun _ => items.flatMap fun item => (exitItems s (childPath P n.id (some item) 0) body).flatten)
      children := items.flatMap fun item => subtreeBags s (childPath P n.id (some item) 0) }
  | .loop body _ =>
    let k := loopCount s P n.id
    { outputs := ports n (fun _ => [(exitItems s (childPath P n.id none k) body).flatten.headD ""])
      children := loopChannels s P n.id 1 k }
  | _ => { outputs := [] }

def nodeValue (oracle : ScopedOracle) (s : State) (g : Graph) (P : Path) (n : Node) : NodeResult :=
  match primitive oracle g P n (stateInputs s P n) with
  | some r => r
  | none => compoundValue s P n

def frameValues (oracle : ScopedOracle) (s : State) (g : Graph) (P : Path) : Values := fun id =>
  match g.node? id with
  | some n => nodeValue oracle s g P n
  | none => { outputs := [] }

/-- Every child frame is owned by an existing instance in its immediate parent frame. -/
def FrameOwners (s : State) : Prop :=
  ∀ f ∈ s.frames, ∀ id, f.owner = some id → ∃ i ∈ s.instances,
    i.id = id ∧ ∃ segment, f.path = i.path ++ [segment]

/-- The state right after a frame was opened and seeded: no instances, records, descendants,
    or tokens of its own yet, except the seeded entry channels. -/
structure FrameStart (s0 : State) (P : Path) (g : Graph) (inputs : List Input) : Prop where
  scope : Scope s0 P g
  noInstances : ∀ j ∈ s0.instances, ¬ (P <+: j.path)
  noRecords : ∀ r ∈ s0.consumed, ∀ c ∈ s0.channels, P <+: c.path → r.channel ≠ c.id
  noDescendants : ∀ k ∈ s0.frames, P <+: k.path → k.path = P
  empty : ∀ c ∈ s0.channels, c.path = P → c.entry = false → c.placed = []
  seeded : ∀ c ∈ s0.channels, c.path = P → c.entry = true →
    c.closed = true ∧ bag c = canonical (((inputs.find? (·.entry == c.edge.dst)).map (·.items)).getD [])
  owners : FrameOwners s0

theorem Scope.persist {allows : State → Op → Prop} {s last : State} {ops : List Op} {P : Path} {g : Graph}
    (sc : Scope s P g) (run : ConformingSteps allows s ops last) : Scope last P g := by
  refine ⟨run.invariants sc.safe, run.layout sc.layout, run.unique_frames sc.distinct, ?_, sc.valid⟩
  obtain ⟨f, memberF, pathF, graphF⟩ := sc.frame
  have inDefs : f.definitionView ∈ last.frameDefinitions :=
    run.frameDefinitions.subset (List.mem_map.mpr ⟨f, memberF, rfl⟩)
  obtain ⟨h, memberH, viewH⟩ := List.mem_map.mp inDefs
  refine ⟨h, memberH, ?_, ?_⟩
  · have := congrArg Frame.path viewH
    simp only [Frame.definitionView] at this
    exact this.trans pathF
  · have := congrArg Frame.graph viewH
    simp only [Frame.definitionView] at this
    exact this.trans graphF

theorem Graph.node?_of_mem (g : Graph) (nodup : (g.nodes.map (·.id)).Nodup) (n : Node) (member : n ∈ g.nodes) :
    g.node? n.id = some n := by
  have exists_ : (g.nodes.find? (·.id == n.id)).isSome := List.find?_isSome.mpr ⟨n, member, by simp⟩
  cases found : g.nodes.find? (·.id == n.id) with
  | none => rw [found] at exists_; contradiction
  | some m =>
    have memberM := List.mem_of_find?_eq_some found
    have idM : m.id = n.id := by simpa using List.find?_some found
    have same := eq_of_mapped_nodup (·.id) g.nodes nodup m n memberM member idM
    unfold Graph.node?
    rw [found, same]

theorem Scope.nodes_nodup {s : State} {P : Path} {g : Graph} (sc : Scope s P g) : (g.nodes.map (·.id)).Nodup := by
  obtain ⟨body, valid⟩ := sc.valid
  exact g.validate_node_names body valid

theorem Scope.node?_of_mem {s : State} {P : Path} {g : Graph} (sc : Scope s P g) (n : Node) (member : n ∈ g.nodes) :
    s.node? P n.id = some n := by
  rw [sc.node?]
  exact g.node?_of_mem sc.nodes_nodup n member

theorem Scope.checked {s : State} {P : Path} {g : Graph} (sc : Scope s P g) (n : Node) (member : n ∈ g.nodes) :
    g.validateNode n = .ok () := by
  obtain ⟨body, valid⟩ := sc.valid
  exact g.validate_nodes body valid n member

/-- A non-exit channel into a node of the frame feeds one of its input ports, with matching kind. -/
theorem Scope.input_port {s : State} {P : Path} {g : Graph} (sc : Scope s P g) (n : Node) (memberN : n ∈ g.nodes)
    (c : Channel) (memberC : c ∈ s.channels) (pathC : c.path = P) (exitC : c.exit = false) (nodeC : c.edge.dst.node = n.id) :
    ∃ p ∈ n.inputs, c.edge.dst.port = p.name ∧ c.kind = p.kind := by
  obtain ⟨body, valid⟩ := sc.valid
  have inTemplate := sc.template c memberC pathC
  obtain ⟨p, found, kind⟩ := Frame.channel_input { path := P, graph := g } body valid c.layout inTemplate exitC
  simp only [Channel.layout_edge, Channel.layout_kind] at found kind
  have nodeFound : g.node? c.edge.dst.node = some n := by rw [nodeC]; exact g.node?_of_mem sc.nodes_nodup n memberN
  simp [Graph.input?, nodeFound] at found
  have memberP := List.mem_of_find?_eq_some found
  have nameP : p.name = c.edge.dst.port := by simpa using List.find?_some found
  exact ⟨p, memberP, nameP.symm, kind⟩

/-- A non-entry channel out of a node of the frame drains one of its output ports, with matching kind. -/
theorem Scope.output_port {s : State} {P : Path} {g : Graph} (sc : Scope s P g) (n : Node) (memberN : n ∈ g.nodes)
    (c : Channel) (memberC : c ∈ s.channels) (pathC : c.path = P) (entryC : c.entry = false) (nodeC : c.edge.src.node = n.id) :
    ∃ q ∈ n.outputs, c.edge.src.port = q.name ∧ c.kind = q.kind := by
  obtain ⟨body, valid⟩ := sc.valid
  have inTemplate := sc.template c memberC pathC
  obtain ⟨q, found, kind⟩ := Frame.channel_output { path := P, graph := g } body valid c.layout inTemplate entryC
  simp only [Channel.layout_edge, Channel.layout_kind] at found kind
  have nodeFound : g.node? c.edge.src.node = some n := by rw [nodeC]; exact g.node?_of_mem sc.nodes_nodup n memberN
  simp [Graph.output?, nodeFound] at found
  have memberQ := List.mem_of_find?_eq_some found
  have nameQ : q.name = c.edge.src.port := by simpa using List.find?_some found
  exact ⟨q, memberQ, nameQ.symm, kind⟩

/-- A closed plain channel whose pending head is an item holds exactly that item. -/
theorem plain_closed_items {c : Channel} (ok : channelOK c = true) (plain : c.kind = .plain) (x : ItemId)
    (head : c.pending.head? = some (.item x)) : c.items = [x] := by
  simp only [channelOK, Bool.and_eq_true] at ok
  have bound : c.items.length ≤ 1 := by
    have := ok.2
    rw [plain] at this
    simpa using this
  have memberX : x ∈ c.items := by
    rw [Effects.item_mem]
    have : Token.item x ∈ c.pending := List.mem_of_mem_head? head
    exact List.drop_subset _ _ this
  cases hl : c.items with
  | nil => rw [hl] at memberX; simp at memberX
  | cons y ys =>
    cases ys with
    | nil =>
      rw [hl] at memberX
      simp only [List.mem_singleton] at memberX
      rw [memberX]
    | cons z zs => rw [hl] at bound; simp at bound

theorem outputItems_ports (n : Node) (names : (n.outputs.map (·.name)).Nodup) (f : PortName → List ItemId)
    (q : Port) (port : q ∈ n.outputs) : outputItems (ports n f) q.name = canonical (f q.name) := by
  have found : n.outputs.find? (fun p => p.name == q.name) = some q := by
    have exists_ : (n.outputs.find? (fun p => p.name == q.name)).isSome := List.find?_isSome.mpr ⟨q, port, by simp⟩
    cases h : n.outputs.find? (fun p => p.name == q.name) with
    | none => rw [h] at exists_; contradiction
    | some m =>
      have memberM := List.mem_of_find?_eq_some h
      have nameM : m.name = q.name := by simpa using List.find?_some h
      rw [eq_of_mapped_nodup (·.name) n.outputs names m q memberM port nameM]
  unfold outputItems ports
  rw [List.find?_map]
  have : ((fun (o : Output) => o.port == q.name) ∘ fun (p : Port) => ({ port := p.name, items := canonical (f p.name) } : Output)) =
      fun (p : Port) => p.name == q.name := by
    funext p; rfl
  rw [this, found]
  rfl

theorem suppressed_singletons (n : Node) (f : Port → ItemId) (notCoalesce : n.kind ≠ .coalesce) :
    suppressed n (n.inputs.map fun p => (p.name, [f p])) = false := by
  unfold suppressed
  cases hk : n.kind <;> simp_all [List.any_map]

theorem plainValues_singletons (n : Node) (f : Port → ItemId) :
    plainValues (n.inputs.map fun p => (p.name, [f p])) = n.inputs.map fun p => (p.name, f p) := by
  simp [plainValues, List.map_map, Function.comp_def]

/-- The stateInputs of a node whose input channels each hold exactly one item. -/
theorem stateInputs_of_singletons {s : State} {P : Path} {g : Graph} (sc : Scope s P g) (n : Node) (memberN : n ∈ g.nodes)
    (f : Port → ItemId)
    (channels : ∀ p ∈ n.inputs, ∃ d ∈ s.channels, d.path = P ∧ d.exit = false ∧ d.edge.dst = ⟨n.id, p.name⟩ ∧ d.items = [f p]) :
    stateInputs s P n = n.inputs.map fun p => (p.name, [f p]) := by
  unfold stateInputs
  apply List.map_congr_left
  intro p memberP
  obtain ⟨d, memberD, pathD, exitD, dstD, itemsD⟩ := channels p memberP
  obtain ⟨c, memberC, found, pathC, exitC, dstC, _, _, uniqueC⟩ := sc.input_channel n memberN p memberP
  have same : d = c := uniqueC d memberD pathD exitD dstD
  subst same
  rw [found]
  simp [bag, itemsD, sortedItems]

/-- An empty plain input channel makes the node suppressed. -/
theorem suppressed_of_empty {s : State} {P : Path} {g : Graph} (sc : Scope s P g) (n : Node) (memberN : n ∈ g.nodes)
    (plain : allKind n.inputs .plain = true) (notCoalesce : n.kind ≠ .coalesce)
    (d : Channel) (memberD : d ∈ s.channels) (pathD : d.path = P) (exitD : d.exit = false)
    (nodeD : d.edge.dst.node = n.id) (emptyD : d.items = []) : suppressed n (stateInputs s P n) = true := by
  obtain ⟨p, memberP, portD, _⟩ := sc.input_port n memberN d memberD pathD exitD nodeD
  have dstD : d.edge.dst = ⟨n.id, p.name⟩ := by
    cases h : d.edge.dst with
    | mk a b =>
      rw [h] at nodeD portD
      simp only at nodeD portD
      rw [nodeD, portD]
  obtain ⟨c, memberC, found, _, _, _, _, _, uniqueC⟩ := sc.input_channel n memberN p memberP
  have same : d = c := uniqueC d memberD pathD exitD dstD
  subst same
  have present : (p.name, ([] : List ItemId)) ∈ stateInputs s P n := by
    unfold stateInputs
    apply List.mem_map.mpr
    refine ⟨p, memberP, ?_⟩
    rw [found]
    simp [bag, emptyD, sortedItems]
  unfold suppressed
  rw [plain]
  cases hk : n.kind <;> first
    | exact absurd hk notCoalesce
    | (simp only [Bool.true_and]
       exact List.any_eq_true.mpr ⟨(p.name, []), present, by simp⟩)

/-- A succeeded instance of a plain-input node (leaf, waitAll, branch, subworkflow, loop) recorded
    per input port the single item of the corresponding input channel, as it stands at the end. -/
theorem plain_instance_inputs (oracle : ScopedOracle) {s0 last : State} {ops : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input}
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (fs : FrameStart s0 P g inputs0) (n : Node) (memberN : n ∈ g.nodes)
    (kindOK : (∃ r c, n.kind = .leaf r c) ∨ n.kind = .waitAll ∨ (∃ arms, n.kind = .branch arms) ∨
      (∃ b, n.kind = .subworkflow b) ∨ (∃ b m, n.kind = .loop b m))
    (i : Instance) (memberI : i ∈ last.instances) (pathI : i.path = P) (nodeI : i.node = n.id)
    (statusI : i.status = .succeeded) :
    ∃ f : Port → ItemId, i.inputs = n.inputs.map (fun p => (p.name, f p)) ∧
      ∀ p ∈ n.inputs, ∃ d ∈ last.channels, d.path = P ∧ d.exit = false ∧ d.edge.dst = ⟨n.id, p.name⟩ ∧ d.items = [f p] := by
  have safe0 := fs.scope.safe
  have safeLast := run.invariants safe0
  have plain : allKind n.inputs .plain = true := by
    have shape := g.validateNode_shape n (fs.scope.checked n memberN)
    rcases kindOK with ⟨r, c, k⟩ | k | ⟨arms, k⟩ | ⟨b, k⟩ | ⟨b, m, k⟩ <;>
      (simp only [Node.shapeOK, k, Bool.and_eq_true] at shape; first | exact shape.1.1.1 | exact shape.1.1.1.1 | exact shape.1.1.1.1.1 | exact shape.1.1.1.1.1.1 | exact shape.1.1.1.1.1.1.1 | exact shape.1.1.1.1.1.1.1.1 | exact shape.1.1)
  obtain ⟨inNames, _⟩ := g.validate_port_names n (fs.scope.checked n memberN)
  have absent0 : ∀ j ∈ s0.instances, j.id ≠ i.id := by
    intro j memberJ eq
    obtain ⟨_, pathEq, _, _⟩ := run.input_snapshot safe0 j i memberJ memberI eq
    exact fs.noInstances j memberJ (by rw [← pathEq, pathI]; exact List.prefix_refl _)
  obtain ⟨pre, op, post, t, t', j, _, head, allowed, accepted, rest, safeT, _, memberJ, idJ, bindJ, created⟩ :=
    instance_created run safe0 i memberI absent0
  have safeT' := preserves_invariants t t' op safeT accepted
  have nodeT : t.node? P n.id = some n := head.node P n.id n (fs.scope.node?_of_mem n memberN)
  have pathJ : j.path = P := (Instance.binding_path bindJ).trans pathI
  have nodeJ : j.node = n.id := (Instance.binding_node bindJ).trans nodeI
  have inputsJ : j.inputs = i.inputs := Instance.binding_inputs bindJ
  -- from `plainInputs` at `t` to the channels at the end
  have finish : ∀ inputs, plainInputs t P n = .ok inputs → j.inputs = inputs →
      ∃ f : Port → ItemId, i.inputs = n.inputs.map (fun p => (p.name, f p)) ∧
        ∀ p ∈ n.inputs, ∃ d ∈ last.channels, d.path = P ∧ d.exit = false ∧ d.edge.dst = ⟨n.id, p.name⟩ ∧ d.items = [f p] := by
    intro inputs hi eqJ
    obtain ⟨inputsEq, chans⟩ := plainInputs_spec t P n inputs hi
    refine ⟨fun p => inputHead t P n.id p.name, by rw [← inputsJ, eqJ, inputsEq], ?_⟩
    intro p memberP
    obtain ⟨c, memberIn, portC, closedC, headC⟩ := chans p memberP
    have memberC : c ∈ t.channels := (List.mem_filter.mp memberIn).1
    have fields := (List.mem_filter.mp memberIn).2
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at fields
    have scT := fs.scope.persist head
    obtain ⟨p', memberP', portP', kindP'⟩ := scT.input_port n memberN c memberC fields.1.1 fields.1.2 fields.2
    have same : p' = p := eq_of_mapped_nodup (·.name) n.inputs inNames p' p memberP' memberP (portP'.symm.trans portC)
    subst same
    have plainP : p'.kind = .plain := by simpa using List.all_eq_true.mp plain p' memberP'
    have itemsC : c.items = [inputHead t P n.id p'.name] :=
      plain_closed_items (channelOK_of_invariants safeT memberC) (kindP'.trans plainP) _ headC
    have full : ConformingSteps (fun s op => oracleConforms oracle s op = true) t (op :: post) last := .cons allowed accepted rest
    obtain ⟨d, memberD, idD, placedD⟩ := full.retains_closed_channel safeT c memberC closedC
    obtain ⟨d', memberD', idD', layoutD', _⟩ := run_image full safeT c memberC
    have sameD : d' = d := unique_channel safeLast memberD' memberD (idD'.trans idD.symm)
    subst sameD
    obtain ⟨_, edgeD, pathD, _, exitD, _⟩ := Channel.layout_fields layoutD'
    refine ⟨d', memberD', pathD.trans fields.1.1, exitD.trans fields.1.2, ?_, ?_⟩
    · rw [edgeD]
      cases h : c.edge.dst with
      | mk a b =>
        rw [h] at fields portC
        simp only at fields portC
        rw [fields.2, portC]
    · simp only [Channel.items, placedD]
      exact itemsC
  rcases created with
      ⟨P', N', n', inputs, _, hn, hi, ⟨r, cc, kind', eq⟩ | ⟨body, iteration, kinds, eq⟩⟩
    | ⟨P', N', n', inputs, _, hn, kind', hi, eq⟩
    | ⟨P', N', arm, n', arms, inputs, _, hn, kind', hi, eq⟩
    | ⟨P', N', n', c, _, hn, kind', hc, eq⟩
    | ⟨P', N', e, x, n', c, _, hn, kind', hc, eq⟩
    | ⟨P', N', n', ⟨x, k, _, kind'⟩ | ⟨e, x, _, kind'⟩, hn, eq⟩
    | ⟨P', N', n', _, hn, kind', eq⟩
    | ⟨P', N', n', _, hn, eq⟩
    | ⟨P', N', x, n', body, _, hn, kind', eq⟩
  all_goals
    have pathEq : P' = P := by rw [eq] at pathJ; exact pathJ
    have idEq : n'.id = n.id := by rw [eq] at nodeJ; exact nodeJ
    subst pathEq
    have NEq : N' = n.id := (getNode_id t P' N' n' hn).symm.trans idEq
    subst NEq
    have sameN : n' = n := node?_of_getNode nodeT hn
    subst sameN
  · exact finish inputs hi (by rw [eq]; rfl)
  · exact finish inputs hi (by rw [eq]; rfl)
  · exact finish inputs hi (by rw [eq]; rfl)
  · exact finish inputs hi (by rw [eq]; rfl)
  · exfalso
    rcases kindOK with ⟨r, c, k⟩ | k | ⟨arms, k⟩ | ⟨b, k⟩ | ⟨b, m, k⟩ <;> (rw [k] at kind'; cases kind')
  · exfalso
    rcases kindOK with ⟨r, c, k⟩ | k | ⟨arms, k⟩ | ⟨b, k⟩ | ⟨b, m, k⟩ <;> (rw [k] at kind'; cases kind')
  · exfalso
    rcases kindOK with ⟨r, c, k⟩ | k | ⟨arms, k⟩ | ⟨b, k⟩ | ⟨b, m, k⟩ <;> (rw [k] at kind'; cases kind')
  · exfalso
    rcases kindOK with ⟨r, c, k⟩ | k | ⟨arms, k⟩ | ⟨b, k⟩ | ⟨b, m, k⟩ <;> (rw [k] at kind'; cases kind')
  · exfalso
    rcases kindOK with ⟨r, c, k⟩ | k | ⟨arms, k⟩ | ⟨b, k⟩ | ⟨b, m, k⟩ <;> (rw [k] at kind'; cases kind')
  · -- skipped: the instance is cancelled for good
    exfalso
    have cancelledJ : j.status = .cancelled := by rw [eq]; rfl
    obtain ⟨k, memberK, idK, statusK⟩ := rest.retains_status safeT' j memberJ (.inr cancelledJ)
    have same : k = i := eq_of_mapped_nodup (·.id) last.instances safeLast.instanceIds k i memberK memberI (idK.trans idJ)
    subst same
    rw [statusI] at statusK
    rw [cancelledJ] at statusK
    cases statusK
  · exfalso
    rcases kindOK with ⟨r, c, k⟩ | k | ⟨arms, k⟩ | ⟨b, k⟩ | ⟨b, m, k⟩ <;> (rw [k] at kind'; cases kind')


@[simp] theorem sortedItems_nil : sortedItems [] = [] := by simp [sortedItems]
@[simp] theorem sortedItems_singleton (x : ItemId) : sortedItems [x] = [x] := by simp [sortedItems]
@[simp] theorem canonical_nil : canonical [] = [] := by simp [canonical]
@[simp] theorem canonical_singleton (x : ItemId) : canonical [x] = [x] := by simp [canonical, List.eraseDups_cons]
@[simp] theorem bag_nil {c : Channel} (h : c.items = []) : bag c = [] := by simp [bag, h]

theorem canonical_eq_of_mem_iff {a b : List ItemId} (h : ∀ x, x ∈ a ↔ x ∈ b) : canonical a = canonical b := by
  unfold canonical
  apply sortedItems_eq_of_perm
  apply (List.perm_ext_iff_of_nodup (eraseDups_nodup a) (eraseDups_nodup b)).mpr
  intro x
  rw [List.mem_eraseDups, List.mem_eraseDups]
  exact h x

theorem bag_eq_canonical {s : State} (safe : Invariants s) {c : Channel} (member : c ∈ s.channels) :
    bag c = canonical c.items := by
  unfold bag
  rw [canonical_of_nodup (items_nodup_of_invariants safe member)]

/-! ### Common facts from a frame start -/

theorem FrameStart.fresh0 {s0 : State} {P : Path} {g : Graph} {inputs : List Input} (fs : FrameStart s0 P g inputs)
    (N : NodeId) : ∀ j ∈ s0.instances, ¬ (j.path = P ∧ j.node = N) := by
  intro j memberJ ⟨pathJ, _⟩
  exact fs.noInstances j memberJ (by rw [pathJ]; exact List.prefix_refl _)

theorem FrameStart.noRecords0 {s0 : State} {P : Path} {g : Graph} {inputs : List Input} (fs : FrameStart s0 P g inputs) :
    ∀ r ∈ s0.consumed, ∀ c ∈ s0.channels, c.path = P → c.exit = false → r.channel ≠ c.id := by
  intro r memberR c memberC pathC _
  exact fs.noRecords r memberR c memberC (by rw [pathC]; exact List.prefix_refl _)

theorem Scope.inputKinds {s : State} {P : Path} {g : Graph} (sc : Scope s P g) (n : Node) (memberN : n ∈ g.nodes)
    (plain : allKind n.inputs .plain = true) :
    ∀ c ∈ s.channels, c.path = P → c.exit = false → c.edge.dst.node = n.id → c.kind = .plain := by
  intro c memberC pathC exitC nodeC
  obtain ⟨p, memberP, _, kindC⟩ := sc.input_port n memberN c memberC pathC exitC nodeC
  rw [kindC]
  simpa using List.all_eq_true.mp plain p memberP

theorem Scope.uniqueDst {s : State} {P : Path} {g : Graph} (sc : Scope s P g) (n : Node) (memberN : n ∈ g.nodes) :
    ∀ c ∈ s.channels, ∀ d ∈ s.channels, c.path = P → d.path = P → c.exit = false → d.exit = false →
      c.edge.dst.node = n.id → d.edge.dst.node = n.id → c.edge.dst = d.edge.dst → c.id = d.id := by
  intro c memberC d memberD pathC pathD exitC exitD nodeC _ same
  obtain ⟨p, memberP, portC, _⟩ := sc.input_port n memberN c memberC pathC exitC nodeC
  have dstC : c.edge.dst = ⟨n.id, p.name⟩ := by
    cases h : c.edge.dst with
    | mk a b => rw [h] at nodeC portC; simp only at nodeC portC; rw [nodeC, portC]
  obtain ⟨e, _, _, _, _, _, _, _, uniqueE⟩ := sc.input_channel n memberN p memberP
  have ce : c = e := uniqueE c memberC pathC exitC dstC
  have de : d = e := uniqueE d memberD pathD exitD (same.symm.trans dstC)
  rw [ce, de]

/-- The destination node of a non-exit channel of the frame is a node of its graph. -/
theorem Scope.dst_node {s : State} {P : Path} {g : Graph} (sc : Scope s P g) (c : Channel) (memberC : c ∈ s.channels)
    (pathC : c.path = P) (exitC : c.exit = false) : ∃ n ∈ g.nodes, c.edge.dst.node = n.id := by
  obtain ⟨body, valid⟩ := sc.valid
  have inTemplate := sc.template c memberC pathC
  obtain ⟨p, found, _⟩ := Frame.channel_input { path := P, graph := g } body valid c.layout inTemplate exitC
  simp only [Channel.layout_edge] at found
  cases foundNode : g.node? c.edge.dst.node with
  | none => simp [Graph.input?, foundNode] at found
  | some n =>
    have memberN := List.mem_of_find?_eq_some foundNode
    have idN : n.id = c.edge.dst.node := by simpa using List.find?_some foundNode
    exact ⟨n, memberN, idN.symm⟩

theorem Scope.uniqueDst' {s : State} {P : Path} {g : Graph} (sc : Scope s P g) :
    ∀ c ∈ s.channels, ∀ d ∈ s.channels, c.path = P → d.path = P → c.exit = false → d.exit = false →
      c.edge.dst = d.edge.dst → c.id = d.id := by
  intro c memberC d memberD pathC pathD exitC exitD same
  obtain ⟨n, memberN, nodeC⟩ := sc.dst_node c memberC pathC exitC
  exact sc.uniqueDst n memberN c memberC d memberD pathC pathD exitC exitD nodeC (by rw [← same]; exact nodeC) same

theorem Scope.uniqueInput {s : State} {P : Path} {g : Graph} (sc : Scope s P g) (n : Node) (memberN : n ∈ g.nodes)
    (p1 : Port) (single : n.inputs = [p1]) :
    ∀ c ∈ s.channels, ∀ d ∈ s.channels, c.path = P → d.path = P → c.exit = false → d.exit = false →
      c.edge.dst.node = n.id → d.edge.dst.node = n.id → c.id = d.id := by
  intro c memberC d memberD pathC pathD exitC exitD nodeC nodeD
  apply sc.uniqueDst n memberN c memberC d memberD pathC pathD exitC exitD nodeC nodeD
  obtain ⟨p, memberP, portC, _⟩ := sc.input_port n memberN c memberC pathC exitC nodeC
  obtain ⟨q, memberQ, portD, _⟩ := sc.input_port n memberN d memberD pathD exitD nodeD
  rw [single] at memberP memberQ
  simp only [List.mem_singleton] at memberP memberQ
  subst memberP; subst memberQ
  cases hc : c.edge.dst with
  | mk a b =>
    cases hd : d.edge.dst with
    | mk a' b' =>
      rw [hc] at nodeC portC; rw [hd] at nodeD portD
      simp only at nodeC portC nodeD portD
      rw [nodeC, portC, nodeD, portD]

/-- Fields shared by the equations: the origin of a final channel of the frame at its start. -/
theorem FrameStart.origin {s0 last : State} {ops : List Op} {P : Path} {g : Graph} {inputs : List Input}
    {allows : State → Op → Prop} (fs : FrameStart s0 P g inputs) (run : ConformingSteps allows s0 ops last)
    (c : Channel) (memberC : c ∈ last.channels) (pathC : c.path = P) :
    ∃ c0 ∈ s0.channels, c0.id = c.id ∧ c0.edge = c.edge ∧ c0.path = c.path ∧ c0.entry = c.entry ∧ c0.exit = c.exit ∧
      c0.kind = c.kind ∧ (c.entry = false → c0.placed = []) := by
  obtain ⟨f0, memberF0, pathF0, _⟩ := fs.scope.frame
  obtain ⟨c0, member0, layout0⟩ := channel_origin_layout run fs.scope.layout fs.scope.distinct f0 memberF0 c memberC (pathC.trans pathF0.symm)
  obtain ⟨id0, edge0, path0, entry0, exit0, kind0⟩ := Channel.layout_fields layout0
  exact ⟨c0, member0, id0, edge0, path0, entry0, exit0, kind0, fun h => fs.empty c0 member0 (path0.trans pathC) (entry0.trans h)⟩

theorem nodeValue_suppressed (oracle : ScopedOracle) (s : State) (g : Graph) (P : Path) (n : Node)
    (sup : suppressed n (stateInputs s P n) = true) : nodeValue oracle s g P n = { outputs := ports n (fun _ => []) } := by
  unfold nodeValue primitive
  rw [sup]
  rfl

/-! ### Leaf -/

theorem leaf_value (oracle : ScopedOracle) {s0 last : State} {ops : List Op} {P : Path} {g : Graph} {inputs0 : List Input}
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (fs : FrameStart s0 P g inputs0) (finished : succeededDrained last = true)
    (n : Node) (memberN : n ∈ g.nodes) (r : RetryPolicy) (cc : Nat) (kind : n.kind = .leaf r cc)
    (c : Channel) (memberC : c ∈ last.channels) (pathC : c.path = P) (entryC : c.entry = false)
    (srcC : c.edge.src.node = n.id) :
    bag c = canonical (outputItems (nodeValue oracle last g P n).outputs c.edge.src.port) := by
  have scL := fs.scope.persist run
  have checkedN := fs.scope.checked n memberN
  obtain ⟨inNames, outNames⟩ := g.validate_port_names n checkedN
  have plain : allKind n.inputs .plain = true := by
    have shape := g.validateNode_shape n checkedN
    simp only [Node.shapeOK, kind, Bool.and_eq_true] at shape
    exact shape.1.1.1
  obtain ⟨q, port, portC, kindC⟩ := scL.output_port n memberN c memberC pathC entryC srcC
  obtain ⟨c0, member0, id0, edge0, path0, entry0, exit0, kind0, emptyOf⟩ := fs.origin run c memberC pathC
  have empty0 := emptyOf entryC
  have found0 : s0.node? c0.path c0.edge.src.node = some n := by
    rw [path0, pathC, edge0, srcC]; exact fs.scope.node?_of_mem n memberN
  rcases leaf_output_final oracle run fs.scope.safe finished n c0 found0 r cc kind outNames q port
      (by rw [edge0]; exact portC) (by rw [kind0]; exact kindC) member0 empty0 (entry0.trans entryC) c memberC id0.symm with
      ⟨i, memberI, pathI, nodeI, statusI, stream, plainCase⟩ | ⟨emptyC, _, d, memberD, pathD, exitD, nodeD, _, emptyD⟩
  · rw [path0, pathC] at pathI
    rw [edge0, srcC] at nodeI
    obtain ⟨f, inputsI, chans⟩ := plain_instance_inputs oracle run fs n memberN (.inl ⟨r, cc, kind⟩) i memberI pathI nodeI statusI
    have inputsL := stateInputs_of_singletons scL n memberN f chans
    have notSup : suppressed n (stateInputs last P n) = false := by
      rw [inputsL]; exact suppressed_singletons n f (by rw [kind]; simp)
    have valueEq : nodeValue oracle last g P n =
        { outputs := ports n (outputItems ((oracle P).leaf n.id (plainValues (stateInputs last P n)))) } := by
      unfold nodeValue primitive
      rw [notSup]
      simp [kind]
    have plainEq : plainValues (stateInputs last P n) = i.inputs := by
      rw [inputsL, inputsI, plainValues_singletons]
    rw [valueEq, plainEq, portC, outputItems_ports n outNames _ q port, canonical_idem, bag_eq_canonical scL.safe memberC]
    rw [path0, pathC, edge0, srcC] at stream plainCase
    cases hq : q.kind with
    | stream => exact canonical_eq_of_perm (items_nodup_of_invariants scL.safe memberC) (stream hq)
    | plain => rw [plainCase hq]
  · have sup : suppressed n (stateInputs last P n) = true :=
      suppressed_of_empty scL n memberN plain (by rw [kind]; simp) d memberD (pathD.trans (path0.trans pathC)) exitD
        (nodeD.trans (by rw [edge0]; exact srcC)) emptyD
    rw [nodeValue_suppressed oracle last g P n sup, portC, outputItems_ports n outNames _ q port]
    simp [bag, emptyC]


/-- The semantics' input-channel id of a port is the id of the state's channel into that port. -/
theorem Scope.inputChannel_id {s : State} {P : Path} {g : Graph} (sc : Scope s P g) (n : Node) (memberN : n ∈ g.nodes)
    (p : Port) (memberP : p ∈ n.inputs) (c : Channel) (memberC : c ∈ s.channels) (pathC : c.path = P)
    (exitC : c.exit = false) (dstC : c.edge.dst = ⟨n.id, p.name⟩) : inputChannel g P n.id p.name = c.id := by
  have inTemplate := sc.template c memberC pathC
  have exists_ : (({ path := P, graph := g } : Frame).channels.find? (fun d => !d.exit && d.edge.dst == ⟨n.id, p.name⟩)).isSome :=
    List.find?_isSome.mpr ⟨c.layout, inTemplate, by simp [exitC, dstC]⟩
  unfold inputChannel
  cases found : ({ path := P, graph := g } : Frame).channels.find? (fun d => !d.exit && d.edge.dst == ⟨n.id, p.name⟩) with
  | none => rw [found] at exists_; contradiction
  | some d =>
    have memberD := List.mem_of_find?_eq_some found
    have props := List.find?_some found
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at props
    obtain ⟨c', memberC', layoutC'⟩ := sc.realized d memberD
    obtain ⟨idC', edgeC', pathC', _, exitC', _⟩ := Channel.layout_eq_fields layoutC'
    have pathD : d.path = P := Frame.channel_path { path := P, graph := g } d memberD
    obtain ⟨e, _, _, _, _, _, _, _, uniqueE⟩ := sc.input_channel n memberN p memberP
    have ce : c = e := uniqueE c memberC pathC exitC dstC
    have c'e : c' = e := uniqueE c' memberC' (pathC'.trans pathD) (exitC'.trans props.1) (by rw [edgeC']; exact props.2)
    simp only [Option.map_some, Option.getD_some]
    rw [← idC', c'e, ← ce]

theorem allKind_plain_false_of_stream (ps : List Port) (p : Port) (member : p ∈ ps) (stream : p.kind = .stream) :
    allKind ps .plain = false := by
  cases h : allKind ps .plain with
  | false => rfl
  | true =>
    exfalso
    have := List.all_eq_true.mp h p member
    rw [stream] at this
    simp at this

theorem mem_bag {c : Channel} {x : ItemId} : x ∈ bag c ↔ x ∈ c.items := (sortedItems_perm c.items).mem_iff

/-! ### WaitAll -/

theorem waitAll_value (oracle : ScopedOracle) {s0 last : State} {ops : List Op} {P : Path} {g : Graph} {inputs0 : List Input}
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (fs : FrameStart s0 P g inputs0) (finished : succeededDrained last = true)
    (n : Node) (memberN : n ∈ g.nodes) (kind : n.kind = .waitAll)
    (c : Channel) (memberC : c ∈ last.channels) (pathC : c.path = P) (entryC : c.entry = false)
    (srcC : c.edge.src.node = n.id) :
    bag c = canonical (outputItems (nodeValue oracle last g P n).outputs c.edge.src.port) := by
  have scL := fs.scope.persist run
  have checkedN := fs.scope.checked n memberN
  obtain ⟨inNames, outNames⟩ := g.validate_port_names n checkedN
  have plain : allKind n.inputs .plain = true := by
    have shape := g.validateNode_shape n checkedN
    simp only [Node.shapeOK, kind, Bool.and_eq_true] at shape
    exact shape.1.1
  obtain ⟨q, port, portC, kindC⟩ := scL.output_port n memberN c memberC pathC entryC srcC
  obtain ⟨c0, member0, id0, edge0, path0, entry0, exit0, kind0, emptyOf⟩ := fs.origin run c memberC pathC
  have empty0 := emptyOf entryC
  have found0 : s0.node? c0.path c0.edge.src.node = some n := by
    rw [path0, pathC, edge0, srcC]; exact fs.scope.node?_of_mem n memberN
  have frame0 : ∃ f ∈ s0.frames, f.path = c0.path := by
    obtain ⟨f, memberF, pathF, _⟩ := fs.scope.frame
    exact ⟨f, memberF, by rw [path0, pathC, pathF]⟩
  rcases waitAll_output_final oracle run fs.scope.safe fs.scope.layout fs.scope.distinct finished n c0 found0 kind frame0
      (by rw [path0, pathC, edge0, srcC]; exact fs.fresh0 n.id)
      (by rw [path0, pathC, edge0, srcC]; exact fs.scope.inputKinds n memberN plain)
      q port (by rw [edge0]; exact portC) member0 empty0 (entry0.trans entryC) c memberC id0.symm with
      ⟨f, chans, itemsC, i, memberI, pathI, nodeI, statusI⟩ | ⟨emptyC, _, d, memberD, pathD, exitD, nodeD, _, emptyD⟩
  · simp only [path0, pathC, edge0, srcC] at chans itemsC
    have inputsL := stateInputs_of_singletons scL n memberN f chans
    have notSup : suppressed n (stateInputs last P n) = false := by
      rw [inputsL]; exact suppressed_singletons n f (by rw [kind]; simp)
    have valueEq : nodeValue oracle last g P n = { outputs := ports n (fun _ =>
        [derivedItem "record" P n.id ((plainValues (stateInputs last P n)).map fun (p, i) => identity [p, i])]) } := by
      unfold nodeValue primitive
      rw [notSup]
      simp [kind]
    rw [valueEq, portC, outputItems_ports n outNames _ q port, inputsL, plainValues_singletons,
      bag_eq_canonical scL.safe memberC, itemsC, canonical_idem]
  · have sup : suppressed n (stateInputs last P n) = true :=
      suppressed_of_empty scL n memberN plain (by rw [kind]; simp) d memberD (pathD.trans (path0.trans pathC)) exitD
        (nodeD.trans (by rw [edge0]; exact srcC)) emptyD
    rw [nodeValue_suppressed oracle last g P n sup, portC, outputItems_ports n outNames _ q port]
    simp [bag, emptyC]

/-! ### Branch -/

theorem branch_value (oracle : ScopedOracle) {s0 last : State} {ops : List Op} {P : Path} {g : Graph} {inputs0 : List Input}
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (fs : FrameStart s0 P g inputs0) (finished : succeededDrained last = true)
    (n : Node) (memberN : n ∈ g.nodes) (arms : List PortName) (kind : n.kind = .branch arms)
    (c : Channel) (memberC : c ∈ last.channels) (pathC : c.path = P) (entryC : c.entry = false)
    (srcC : c.edge.src.node = n.id) :
    bag c = canonical (outputItems (nodeValue oracle last g P n).outputs c.edge.src.port) := by
  have scL := fs.scope.persist run
  have checkedN := fs.scope.checked n memberN
  obtain ⟨inNames, outNames⟩ := g.validate_port_names n checkedN
  have shape := g.validateNode_shape n checkedN
  simp only [Node.shapeOK, kind, Bool.and_eq_true, beq_iff_eq] at shape
  have plain : allKind n.inputs .plain = true := shape.1.1.1.1.1
  obtain ⟨p1, single⟩ := List.length_eq_one_iff.mp shape.1.1.1.2
  obtain ⟨q, port, portC, kindC⟩ := scL.output_port n memberN c memberC pathC entryC srcC
  obtain ⟨c0, member0, id0, edge0, path0, entry0, exit0, kind0, emptyOf⟩ := fs.origin run c memberC pathC
  have empty0 := emptyOf entryC
  have found0 : s0.node? c0.path c0.edge.src.node = some n := by
    rw [path0, pathC, edge0, srcC]; exact fs.scope.node?_of_mem n memberN
  have frame0 : ∃ f ∈ s0.frames, f.path = c0.path := by
    obtain ⟨f, memberF, pathF, _⟩ := fs.scope.frame
    exact ⟨f, memberF, by rw [path0, pathC, pathF]⟩
  rcases branch_output_final oracle run fs.scope.safe fs.scope.layout fs.scope.distinct finished n c0 found0 arms kind p1 single
      frame0 (by rw [path0, pathC, edge0, srcC]; exact fs.fresh0 n.id)
      (by rw [path0, pathC, edge0, srcC]; exact fs.scope.inputKinds n memberN plain)
      (by rw [path0, pathC, edge0, srcC]; exact fs.scope.uniqueInput n memberN p1 single)
      q port (by rw [edge0]; exact portC) member0 empty0 (entry0.trans entryC) c memberC id0.symm with
      ⟨item, ⟨d, memberD, pathD, exitD, dstD, itemsD⟩, itemsC, i, memberI, pathI, nodeI, statusI⟩
    | ⟨emptyC, _, d, memberD, pathD, exitD, nodeD, _, emptyD⟩
  · simp only [path0, pathC, edge0, srcC] at pathD dstD itemsC
    have chans : ∀ p ∈ n.inputs, ∃ d ∈ last.channels, d.path = P ∧ d.exit = false ∧ d.edge.dst = ⟨n.id, p.name⟩ ∧
        d.items = [(fun _ => item) p] := by
      intro p memberP
      rw [single] at memberP
      simp only [List.mem_singleton] at memberP
      subst memberP
      exact ⟨d, memberD, pathD, exitD, dstD, itemsD⟩
    have inputsL := stateInputs_of_singletons scL n memberN (fun _ => item) chans
    have notSup : suppressed n (stateInputs last P n) = false := by
      rw [inputsL]; exact suppressed_singletons n (fun _ => item) (by rw [kind]; simp)
    have first : (((plainValues (stateInputs last P n)).head?.map (·.2)).getD "") = item := by
      rw [inputsL, plainValues_singletons, single]
      rfl
    have valueEq : nodeValue oracle last g P n = { outputs := ports n (fun port =>
        if port == (oracle P).branch n.id item then [item] else []) } := by
      unfold nodeValue primitive
      rw [notSup]
      simp only [kind, Bool.false_eq_true, ↓reduceIte]
      rw [first]
    rw [valueEq, portC, outputItems_ports n outNames _ q port, bag_eq_canonical scL.safe memberC, itemsC]
    by_cases h : q.name = (oracle P).branch n.id item
    · simp [h]
    · simp [h]
  · have sup : suppressed n (stateInputs last P n) = true :=
      suppressed_of_empty scL n memberN plain (by rw [kind]; simp) d memberD (pathD.trans (path0.trans pathC)) exitD
        (nodeD.trans (by rw [edge0]; exact srcC)) emptyD
    rw [nodeValue_suppressed oracle last g P n sup, portC, outputItems_ports n outNames _ q port]
    simp [bag, emptyC]

/-! ### Collect -/

theorem collect_value (oracle : ScopedOracle) {s0 last : State} {ops : List Op} {P : Path} {g : Graph} {inputs0 : List Input}
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (fs : FrameStart s0 P g inputs0) (finished : succeededDrained last = true)
    (n : Node) (memberN : n ∈ g.nodes) (kind : n.kind = .collect)
    (c : Channel) (memberC : c ∈ last.channels) (pathC : c.path = P) (entryC : c.entry = false)
    (srcC : c.edge.src.node = n.id) :
    bag c = canonical (outputItems (nodeValue oracle last g P n).outputs c.edge.src.port) := by
  have scL := fs.scope.persist run
  have checkedN := fs.scope.checked n memberN
  obtain ⟨inNames, outNames⟩ := g.validate_port_names n checkedN
  have shape := g.validateNode_shape n checkedN
  simp only [Node.shapeOK, kind, Bool.and_eq_true, beq_iff_eq] at shape
  obtain ⟨p1, single⟩ := List.length_eq_one_iff.mp shape.1.2
  have streamP1 : p1.kind = .stream := by
    have := List.all_eq_true.mp shape.1.1.1 p1 (by rw [single]; simp)
    simpa using this
  have streamInput : allKind n.inputs .plain = false :=
    allKind_plain_false_of_stream n.inputs p1 (by rw [single]; simp) streamP1
  obtain ⟨q, port, portC, kindC⟩ := scL.output_port n memberN c memberC pathC entryC srcC
  obtain ⟨c0, member0, id0, edge0, path0, entry0, exit0, kind0, emptyOf⟩ := fs.origin run c memberC pathC
  have empty0 := emptyOf entryC
  have found0 : s0.node? c0.path c0.edge.src.node = some n := by
    rw [path0, pathC, edge0, srcC]; exact fs.scope.node?_of_mem n memberN
  obtain ⟨d, memberD, pathD, exitD, nodeD, _, itemsC, _⟩ := collect_output_final oracle run fs.scope.safe finished n c0 found0 kind
    streamInput (by rw [path0, pathC, edge0, srcC]; exact fs.fresh0 n.id)
    q port (by rw [edge0]; exact portC) member0 empty0 (entry0.trans entryC) c memberC id0.symm
  simp only [path0, pathC, edge0, srcC] at pathD nodeD itemsC
  -- the input channel of the single port is `d`
  have memberP1 : p1 ∈ n.inputs := by rw [single]; simp
  obtain ⟨e, memberE, found, _, _, _, _, _, uniqueE⟩ := scL.input_channel n memberN p1 memberP1
  obtain ⟨p', memberP', portD, _⟩ := scL.input_port n memberN d memberD pathD exitD nodeD
  have same : p' = p1 := by rw [single] at memberP'; simpa using memberP'
  subst same
  have dstD : d.edge.dst = ⟨n.id, p'.name⟩ := by
    cases h : d.edge.dst with
    | mk a b => rw [h] at nodeD portD; simp only at nodeD portD; rw [nodeD, portD]
  have de : d = e := uniqueE d memberD pathD exitD dstD
  subst de
  have inputsL : stateInputs last P n = [(p'.name, bag d)] := by
    unfold stateInputs
    rw [single]
    simp [found]
  have notSup : suppressed n (stateInputs last P n) = false := by
    unfold suppressed
    rw [streamInput]
    rfl
  have valueEq : nodeValue oracle last g P n = { outputs := ports n (fun _ =>
      [derivedItem "list" P n.id (sortedItems d.items)]) } := by
    unfold nodeValue primitive
    rw [notSup]
    simp only [kind, Bool.false_eq_true, ↓reduceIte, inputsL]
    simp [bag, sortedItems_of_pairwise (sortedItems_pairwise d.items)]
  rw [valueEq, portC, outputItems_ports n outNames _ q port, bag_eq_canonical scL.safe memberC, itemsC, canonical_idem]

/-! ### Filter -/

theorem filter_value (oracle : ScopedOracle) {s0 last : State} {ops : List Op} {P : Path} {g : Graph} {inputs0 : List Input}
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (fs : FrameStart s0 P g inputs0) (finished : succeededDrained last = true)
    (n : Node) (memberN : n ∈ g.nodes) (kind : n.kind = .filter)
    (c : Channel) (memberC : c ∈ last.channels) (pathC : c.path = P) (entryC : c.entry = false)
    (srcC : c.edge.src.node = n.id) :
    bag c = canonical (outputItems (nodeValue oracle last g P n).outputs c.edge.src.port) := by
  have scL := fs.scope.persist run
  have checkedN := fs.scope.checked n memberN
  obtain ⟨inNames, outNames⟩ := g.validate_port_names n checkedN
  have shape := g.validateNode_shape n checkedN
  simp only [Node.shapeOK, kind, Bool.and_eq_true, beq_iff_eq] at shape
  obtain ⟨p1, single⟩ := List.length_eq_one_iff.mp shape.1.2
  have singleOut : n.outputs.length = 1 := shape.2
  have streamP1 : p1.kind = .stream := by
    have := List.all_eq_true.mp shape.1.1.1 p1 (by rw [single]; simp)
    simpa using this
  have streamInput : allKind n.inputs .plain = false :=
    allKind_plain_false_of_stream n.inputs p1 (by rw [single]; simp) streamP1
  obtain ⟨q, port, portC, kindC⟩ := scL.output_port n memberN c memberC pathC entryC srcC
  obtain ⟨c0, member0, id0, edge0, path0, entry0, exit0, kind0, emptyOf⟩ := fs.origin run c memberC pathC
  have empty0 := emptyOf entryC
  have found0 : s0.node? c0.path c0.edge.src.node = some n := by
    rw [path0, pathC, edge0, srcC]; exact fs.scope.node?_of_mem n memberN
  have frame0 : ∃ f ∈ s0.frames, f.path = c0.path := by
    obtain ⟨f, memberF, pathF, _⟩ := fs.scope.frame
    exact ⟨f, memberF, by rw [path0, pathC, pathF]⟩
  have memberP1 : p1 ∈ n.inputs := by rw [single]; simp
  obtain ⟨d, memberD, found, pathD, exitD, dstD, _, _, _⟩ := scL.input_channel n memberN p1 memberP1
  have members := filter_output_final oracle run fs.scope.safe fs.scope.layout fs.scope.distinct finished n c0 found0 kind
    singleOut streamInput frame0 (by rw [path0, pathC]; exact fs.noRecords0)
    (by rw [path0, pathC, edge0, srcC]; exact fs.scope.uniqueInput n memberN p1 single)
    q port (by rw [edge0]; exact portC) member0 empty0 (entry0.trans entryC) c memberC id0.symm
    d memberD (by rw [path0, pathC]; exact pathD) exitD (by rw [edge0, srcC, dstD])
  simp only [path0, pathC, edge0, srcC] at members
  have inputsL : stateInputs last P n = [(p1.name, bag d)] := by
    unfold stateInputs
    rw [single]
    simp [found]
  have notSup : suppressed n (stateInputs last P n) = false := by
    unfold suppressed
    rw [streamInput]
    rfl
  have valueEq : nodeValue oracle last g P n = { outputs := ports n (fun _ =>
      (bag d).filter ((oracle P).filter n.id)) } := by
    unfold nodeValue primitive
    rw [notSup]
    simp only [kind, Bool.false_eq_true, ↓reduceIte, inputsL]
    rfl
  rw [valueEq, portC, outputItems_ports n outNames _ q port, bag_eq_canonical scL.safe memberC, canonical_idem]
  apply canonical_eq_of_mem_iff
  intro x
  rw [members x, List.mem_filter, mem_bag]

/-! ### Merge -/

theorem merge_value (oracle : ScopedOracle) {s0 last : State} {ops : List Op} {P : Path} {g : Graph} {inputs0 : List Input}
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (fs : FrameStart s0 P g inputs0) (finished : succeededDrained last = true)
    (n : Node) (memberN : n ∈ g.nodes) (kind : n.kind = .merge)
    (c : Channel) (memberC : c ∈ last.channels) (pathC : c.path = P) (entryC : c.entry = false)
    (srcC : c.edge.src.node = n.id) :
    bag c = canonical (outputItems (nodeValue oracle last g P n).outputs c.edge.src.port) := by
  have scL := fs.scope.persist run
  have checkedN := fs.scope.checked n memberN
  obtain ⟨inNames, outNames⟩ := g.validate_port_names n checkedN
  have shape := g.validateNode_shape n checkedN
  simp only [Node.shapeOK, kind, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff] at shape
  have singleOut : n.outputs.length = 1 := shape.2
  obtain ⟨p1, memberP1⟩ := List.exists_mem_of_ne_nil n.inputs shape.1.2
  have streamP1 : p1.kind = .stream := by
    have := List.all_eq_true.mp shape.1.1.1 p1 memberP1
    simpa using this
  have streamInput : allKind n.inputs .plain = false := allKind_plain_false_of_stream n.inputs p1 memberP1 streamP1
  obtain ⟨q, port, portC, kindC⟩ := scL.output_port n memberN c memberC pathC entryC srcC
  obtain ⟨c0, member0, id0, edge0, path0, entry0, exit0, kind0, emptyOf⟩ := fs.origin run c memberC pathC
  have empty0 := emptyOf entryC
  have found0 : s0.node? c0.path c0.edge.src.node = some n := by
    rw [path0, pathC, edge0, srcC]; exact fs.scope.node?_of_mem n memberN
  have frame0 : ∃ f ∈ s0.frames, f.path = c0.path := by
    obtain ⟨f, memberF, pathF, _⟩ := fs.scope.frame
    exact ⟨f, memberF, by rw [path0, pathC, pathF]⟩
  have members := merge_output_final oracle run fs.scope.safe fs.scope.layout fs.scope.distinct finished n c0 found0 kind
    singleOut streamInput frame0 (by rw [path0, pathC]; exact fs.noRecords0)
    q port (by rw [edge0]; exact portC) member0 empty0 (entry0.trans entryC) c memberC id0.symm
  simp only [path0, pathC, edge0, srcC] at members
  have notSup : suppressed n (stateInputs last P n) = false := by
    unfold suppressed
    rw [streamInput]
    rfl
  have valueEq : nodeValue oracle last g P n = { outputs := ports n (fun _ =>
      (stateInputs last P n).flatMap fun (port, items) => items.map fun item =>
        derivedItem "merge" P n.id [inputChannel g P n.id port, item]) } := by
    unfold nodeValue primitive
    rw [notSup]
    simp only [kind, Bool.false_eq_true, ↓reduceIte]
  rw [valueEq, portC, outputItems_ports n outNames _ q port, bag_eq_canonical scL.safe memberC, canonical_idem]
  apply canonical_eq_of_mem_iff
  intro x
  rw [members x, List.mem_flatMap]
  constructor
  · rintro ⟨input, memberIn, pathIn, exitIn, nodeIn, y, memberY, eqX⟩
    obtain ⟨p, memberP, portIn, _⟩ := scL.input_port n memberN input memberIn pathIn exitIn nodeIn
    have dstIn : input.edge.dst = ⟨n.id, p.name⟩ := by
      cases h : input.edge.dst with
      | mk a b => rw [h] at nodeIn portIn; simp only at nodeIn portIn; rw [nodeIn, portIn]
    obtain ⟨e, memberE, found, _, _, _, _, _, uniqueE⟩ := scL.input_channel n memberN p memberP
    have same : input = e := uniqueE input memberIn pathIn exitIn dstIn
    subst same
    refine ⟨(p.name, bag input), ?_, ?_⟩
    · unfold stateInputs
      apply List.mem_map.mpr
      exact ⟨p, memberP, by rw [found]; rfl⟩
    · apply List.mem_map.mpr
      refine ⟨y, mem_bag.mpr memberY, ?_⟩
      rw [eqX, scL.inputChannel_id n memberN p memberP input memberIn pathIn exitIn dstIn]
  · rintro ⟨⟨port, items⟩, memberPair, memberX⟩
    unfold stateInputs at memberPair
    obtain ⟨p, memberP, eqPair⟩ := List.mem_map.mp memberPair
    simp only [Prod.mk.injEq] at eqPair
    obtain ⟨portEq, itemsEq⟩ := eqPair
    obtain ⟨e, memberE, found, pathE, exitE, dstE, _, _, _⟩ := scL.input_channel n memberN p memberP
    rw [found] at itemsEq
    simp only [Option.map_some, Option.getD_some] at itemsEq
    obtain ⟨y, memberY, eqX⟩ := List.mem_map.mp memberX
    refine ⟨e, memberE, pathE, exitE, by rw [dstE], y, mem_bag.mp (itemsEq ▸ memberY), ?_⟩
    rw [← eqX, ← portEq, scL.inputChannel_id n memberN p memberP e memberE pathE exitE dstE]

/-! ### Coalesce -/

theorem coalesce_value (oracle : ScopedOracle) {s0 last : State} {ops : List Op} {P : Path} {g : Graph} {inputs0 : List Input}
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (fs : FrameStart s0 P g inputs0) (finished : succeededDrained last = true)
    (n : Node) (memberN : n ∈ g.nodes) (kind : n.kind = .coalesce)
    (c : Channel) (memberC : c ∈ last.channels) (pathC : c.path = P) (entryC : c.entry = false)
    (srcC : c.edge.src.node = n.id) :
    bag c = canonical (outputItems (nodeValue oracle last g P n).outputs c.edge.src.port) := by
  have scL := fs.scope.persist run
  have checkedN := fs.scope.checked n memberN
  obtain ⟨inNames, outNames⟩ := g.validate_port_names n checkedN
  have shape := g.validateNode_shape n checkedN
  simp only [Node.shapeOK, kind, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff] at shape
  have plain : allKind n.inputs .plain = true := shape.1.1.1
  have singleOut : n.outputs.length = 1 := shape.2
  have nonempty : n.inputs ≠ [] := shape.1.2
  obtain ⟨q, port, portC, kindC⟩ := scL.output_port n memberN c memberC pathC entryC srcC
  obtain ⟨c0, member0, id0, edge0, path0, entry0, exit0, kind0, emptyOf⟩ := fs.origin run c memberC pathC
  have empty0 := emptyOf entryC
  have found0 : s0.node? c0.path c0.edge.src.node = some n := by
    rw [path0, pathC, edge0, srcC]; exact fs.scope.node?_of_mem n memberN
  have frame0 : ∃ f ∈ s0.frames, f.path = c0.path := by
    obtain ⟨f, memberF, pathF, _⟩ := fs.scope.frame
    exact ⟨f, memberF, by rw [path0, pathC, pathF]⟩
  -- every input port's channel
  have portChannel : ∀ p ∈ n.inputs, ∃ d ∈ last.channels, inputChannel? last P ⟨n.id, p.name⟩ = some d ∧ d.path = P ∧
      d.exit = false ∧ d.edge.dst = ⟨n.id, p.name⟩ := by
    intro p memberP
    obtain ⟨d, memberD, found, pathD, exitD, dstD, _, _, _⟩ := scL.input_channel n memberN p memberP
    exact ⟨d, memberD, found, pathD, exitD, dstD⟩
  rcases coalesce_output_final oracle run fs.scope.safe fs.scope.layout fs.scope.distinct finished n c0 found0 kind singleOut
      frame0 (by rw [path0, pathC, edge0, srcC]; exact fs.fresh0 n.id) (by rw [path0, pathC]; exact fs.noRecords0)
      (by rw [path0, pathC, edge0, srcC]; exact fs.scope.inputKinds n memberN plain)
      (by rw [path0, pathC]; exact fs.scope.uniqueDst')
      q port (by rw [edge0]; exact portC) member0 empty0 (entry0.trans entryC) c memberC id0.symm with
      ⟨item, selected, memberSel, pathSel, exitSel, nodeSel, itemsSel, others, itemsC, _⟩
    | ⟨emptyC, _, allEmpty⟩
  · simp only [path0, pathC, edge0, srcC] at pathSel nodeSel others itemsC
    obtain ⟨pSel, memberPSel, portSel, _⟩ := scL.input_port n memberN selected memberSel pathSel exitSel nodeSel
    have dstSel : selected.edge.dst = ⟨n.id, pSel.name⟩ := by
      cases h : selected.edge.dst with
      | mk a b => rw [h] at nodeSel portSel; simp only at nodeSel portSel; rw [nodeSel, portSel]
    obtain ⟨e, memberE, foundSel, _, _, _, _, _, uniqueE⟩ := scL.input_channel n memberN pSel memberPSel
    have same : selected = e := uniqueE selected memberSel pathSel exitSel dstSel
    subst same
    -- the bags per port: `[item]` at `pSel`, `[]` elsewhere
    have bags : ∀ p ∈ n.inputs, ∀ d, inputChannel? last P ⟨n.id, p.name⟩ = some d →
        (p = pSel → bag d = [item]) ∧ (p ≠ pSel → bag d = []) := by
      intro p memberP d found
      have memberD := List.mem_of_find?_eq_some found
      have props := List.find?_some found
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at props
      constructor
      · intro eq
        subst eq
        rw [foundSel] at found
        cases found
        simp [bag, itemsSel]
      · intro ne
        have diff : d.id ≠ selected.id := by
          intro same
          have := unique_channel scL.safe memberD memberSel same
          subst this
          rw [dstSel] at props
          simp only [PortRef.mk.injEq] at props
          exact ne (eq_of_mapped_nodup (·.name) n.inputs inNames p pSel memberP memberPSel props.2.2.symm)
        rw [bag_nil (others d memberD props.1.1 props.1.2 (by rw [props.2]) diff)]
    have selectedPresent : (pSel.name, [item]) ∈ stateInputs last P n := by
      unfold stateInputs
      apply List.mem_map.mpr
      refine ⟨pSel, memberPSel, ?_⟩
      rw [foundSel]
      simp [bag, itemsSel]
    have notSup : suppressed n (stateInputs last P n) = false := by
      unfold suppressed
      rw [plain]
      simp only [kind, Bool.true_and]
      apply Bool.and_eq_false_iff.mpr
      right
      apply Bool.eq_false_iff.mpr
      intro all
      have := List.all_eq_true.mp all _ selectedPresent
      simp at this
    have chosen : ((stateInputs last P n).find? (fun p => !p.2.isEmpty)).map (·.2) = some [item] := by
      have exists_ : ((stateInputs last P n).find? (fun p => !p.2.isEmpty)).isSome :=
        List.find?_isSome.mpr ⟨(pSel.name, [item]), selectedPresent, by simp⟩
      cases found : (stateInputs last P n).find? (fun p => !p.2.isEmpty) with
      | none => rw [found] at exists_; contradiction
      | some pair =>
        have memberPair := List.mem_of_find?_eq_some found
        have props := List.find?_some found
        unfold stateInputs at memberPair
        obtain ⟨p, memberP, eqPair⟩ := List.mem_map.mp memberPair
        obtain ⟨d, _, foundD, _, _, _⟩ := portChannel p memberP
        rw [foundD] at eqPair
        simp only [Option.map_some, Option.getD_some] at eqPair
        subst eqPair
        simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff] at props
        by_cases eq : p = pSel
        · rw [(bags p memberP d foundD).1 eq]
          rfl
        · exact absurd ((bags p memberP d foundD).2 eq) props
    have valueEq : nodeValue oracle last g P n = { outputs := ports n (fun _ => [item]) } := by
      unfold nodeValue primitive
      rw [notSup]
      simp only [kind, Bool.false_eq_true, ↓reduceIte, chosen]
      rfl
    rw [valueEq, portC, outputItems_ports n outNames _ q port, bag_eq_canonical scL.safe memberC, itemsC]
    simp
  · simp only [path0, pathC, edge0, srcC] at allEmpty
    have sup : suppressed n (stateInputs last P n) = true := by
      unfold suppressed
      rw [plain]
      simp only [kind, Bool.true_and, Bool.and_eq_true]
      constructor
      · simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff]
        unfold stateInputs
        intro h
        exact nonempty (List.map_eq_nil_iff.mp h)
      · apply List.all_eq_true.mpr
        intro pair memberPair
        unfold stateInputs at memberPair
        obtain ⟨p, memberP, eqPair⟩ := List.mem_map.mp memberPair
        obtain ⟨d, memberD, foundD, pathD, exitD, dstD⟩ := portChannel p memberP
        rw [foundD] at eqPair
        simp only [Option.map_some, Option.getD_some] at eqPair
        subst eqPair
        simp only [decide_eq_true_eq]
        rw [bag_nil (allEmpty d memberD pathD exitD (by rw [dstD]))]
        rfl
    rw [nodeValue_suppressed oracle last g P n sup, portC, outputItems_ports n outNames _ q port]
    simp [bag, emptyC]

end Suimon
