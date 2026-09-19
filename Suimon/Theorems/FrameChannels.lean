import Suimon.Theorems.Canonical
import Suimon.Theorems.ChannelLayout
import Suimon.Theorems.Stream

/-! Channels of a frame in a state, located through the layout invariant. -/

namespace Suimon
open Semantics

def bag (c : Channel) : List ItemId := sortedItems c.items

def inputChannel? (s : State) (P : Path) (ref : PortRef) : Option Channel :=
  s.channels.find? fun c => c.path == P && !c.exit && c.edge.dst == ref

def exitChannel? (s : State) (P : Path) (ref : PortRef) : Option Channel :=
  s.channels.find? fun c => c.path == P && c.exit && c.edge.src == ref

def stateInputs (s : State) (P : Path) (n : Node) : PortData :=
  n.inputs.map fun p => (p.name, ((inputChannel? s P ⟨n.id, p.name⟩).map bag).getD [])

def exitItems (s : State) (P : Path) (g : Graph) : List (List ItemId) :=
  g.exits.map fun p => ((exitChannel? s P p).map bag).getD []

def subtreeBags (s : State) (P : Path) : ChannelData :=
  ((s.channels.filter fun c => P.isPrefixOf c.path).map fun c => (c.id, bag c)).mergeSort (fun a b => a.1 ≤ b.1)

/-- A frame's channels depend on its path and graph only. -/
theorem Frame.channels_template (f : Frame) :
    f.channels = ({ path := f.path, graph := f.graph } : Frame).channels := by
  cases f; rfl


/-- Under a singleton filter, two hits share the index. -/
theorem index_unique_of_filter {α : Type} (p : α → Bool) : ∀ (l : List α), (l.filter p).length ≤ 1 →
    ∀ {i j : Nat} {a b : α}, l[i]? = some a → l[j]? = some b → p a = true → p b = true → i = j
  | [], _, i, j, a, b, hi, _, _, _ => by simp at hi
  | x :: xs, bound, i, j, a, b, hi, hj, pa, pb => by
    cases px : p x with
    | true =>
      rw [List.filter_cons, px] at bound
      simp only [↓reduceIte, List.length_cons] at bound
      have rest : xs.filter p = [] := List.length_eq_zero_iff.mp (by omega)
      have none : ∀ y ∈ xs, p y = false := by
        intro y hy
        have := List.filter_eq_nil_iff.mp rest y hy
        simpa using this
      cases i with
      | zero =>
        cases j with
        | zero => rfl
        | succ j =>
          simp only [List.getElem?_cons_succ] at hj
          have := none b (List.mem_of_getElem? hj)
          rw [this] at pb; contradiction
      | succ i =>
        simp only [List.getElem?_cons_succ] at hi
        have := none a (List.mem_of_getElem? hi)
        rw [this] at pa; contradiction
    | false =>
      rw [List.filter_cons, px] at bound
      simp only [Bool.false_eq_true, ↓reduceIte] at bound
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst hi; rw [px] at pa; contradiction
      | succ i =>
        cases j with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
          subst hj; rw [px] at pb; contradiction
        | succ j =>
          simp only [List.getElem?_cons_succ] at hi hj
          have := index_unique_of_filter p xs bound hi hj pa pb
          omega

theorem filter_eq_length_le_one_of_nodup {α : Type} [BEq α] [LawfulBEq α] {l : List α} (nd : l.Nodup) (a : α) :
    (l.filter (· == a)).length ≤ 1 := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have parts := List.nodup_cons.mp nd
    rw [List.filter_cons]
    split
    · rename_i hx
      have xa : x = a := by simpa using hx
      subst xa
      have empty : xs.filter (· == x) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro y hy eq
        have same : y = x := by simpa using eq
        exact parts.1 (same ▸ hy)
      simp [empty]
    · exact ih parts.2

theorem Graph.validate_boundaries (g : Graph) (body : Bool) (checked : g.validate body = .ok ()) :
    g.entries.Nodup ∧ g.exits.Nodup := by
  have both : (unique g.entries && unique g.exits) = true := by
    rw [Graph.validate] at checked
    repeat' (first
      | split at checked
      | (simp only [bind, Except.bind, pure, Except.pure] at checked)
      | contradiction
      | assumption)
  simp only [Bool.and_eq_true] at both
  exact ⟨unique_nodup _ both.1, unique_nodup _ both.2⟩

/-- A frame with a given path and graph, in a well-laid-out state. -/
structure Scope (s : State) (P : Path) (g : Graph) : Prop where
  safe : Invariants s
  layout : LayoutOK s
  distinct : (s.frames.map Frame.path).Nodup
  frame : ∃ f ∈ s.frames, f.path = P ∧ f.graph = g
  valid : ∃ body, g.validate body = .ok ()

theorem frame?_of_mem {s : State} (distinct : (s.frames.map Frame.path).Nodup) (f : Frame) (member : f ∈ s.frames) :
    s.frame? f.path = some f := by
  have exists_ : (s.frames.find? (·.path == f.path)).isSome := List.find?_isSome.mpr ⟨f, member, by simp⟩
  cases found : s.frames.find? (·.path == f.path) with
  | none => rw [found] at exists_; contradiction
  | some g =>
    have memberG : g ∈ s.frames := List.mem_of_find?_eq_some found
    have pathG : g.path = f.path := by simpa using List.find?_some found
    have same : g = f := eq_of_mapped_nodup Frame.path s.frames distinct g f memberG member pathG
    unfold State.frame?
    rw [found, same]

theorem Scope.frame? {s : State} {P : Path} {g : Graph} (sc : Scope s P g) :
    ∃ f, s.frame? P = some f ∧ f.path = P ∧ f.graph = g := by
  obtain ⟨f, member, path, graph⟩ := sc.frame
  refine ⟨f, ?_, path, graph⟩
  rw [← path]
  exact frame?_of_mem sc.distinct f member

theorem Scope.node? {s : State} {P : Path} {g : Graph} (sc : Scope s P g) (N : NodeId) :
    s.node? P N = g.node? N := by
  obtain ⟨f, found, _, graph⟩ := sc.frame?
  simp [State.node?, found, graph]

theorem Scope.template {s : State} {P : Path} {g : Graph} (sc : Scope s P g) (c : Channel)
    (member : c ∈ s.channels) (path : c.path = P) :
    c.layout ∈ ({ path := P, graph := g } : Frame).channels := by
  obtain ⟨f, found, pathF, graphF⟩ := sc.frame?
  have inFrame := sc.layout.channel_in_scope sc.distinct c f member (by rw [path]; exact found)
  rw [Frame.channels_template, pathF, graphF] at inFrame
  exact inFrame

theorem Scope.realized {s : State} {P : Path} {g : Graph} (sc : Scope s P g) (d : Channel)
    (member : d ∈ ({ path := P, graph := g } : Frame).channels) : ∃ c ∈ s.channels, c.layout = d := by
  obtain ⟨f, memberF, pathF, graphF⟩ := sc.frame
  have inFrame : d ∈ f.channels := by rw [Frame.channels_template, pathF, graphF]; exact member
  have inAll : d ∈ s.frameChannels := List.mem_flatMap.mpr ⟨f, memberF, inFrame⟩
  rw [← sc.layout] at inAll
  exact List.mem_map.mp inAll

theorem Scope.unique_layout {s : State} {P : Path} {g : Graph} (sc : Scope s P g) {c d : Channel}
    (hc : c ∈ s.channels) (hd : d ∈ s.channels) (same : c.layout = d.layout) : c = d :=
  unique_channel sc.safe hc hd (by simpa using congrArg Channel.id same)

def edgeTemplate (P : Path) (g : Graph) (e : Edge) (i : Nat) : Channel :=
  { id := identity (P ++ ["edge", toString i]), edge := e, path := P, kind := ((g.output? e.src).map (·.kind)).getD .plain }

def entryTemplate (P : Path) (g : Graph) (p : PortRef) (i : Nat) : Channel :=
  { id := identity (P ++ ["entry", toString i]), edge := { src := { node := "$input", port := toString i }, dst := p }, path := P, kind := ((g.input? p).map (·.kind)).getD .plain, entry := true }

def exitTemplate (P : Path) (g : Graph) (p : PortRef) (i : Nat) : Channel :=
  { id := identity (P ++ ["exit", toString i]), edge := { src := p, dst := { node := "$output", port := toString i } }, path := P, kind := ((g.output? p).map (·.kind)).getD .plain, exit := true }

theorem Frame.edgeChannels_eq (f : Frame) : f.edgeChannels = f.graph.edges.zipIdx.map fun (e, i) => edgeTemplate f.path f.graph e i := rfl
theorem Frame.entryChannels_eq (f : Frame) : f.entryChannels = f.graph.entries.zipIdx.map fun (p, i) => entryTemplate f.path f.graph p i := rfl
theorem Frame.exitChannels_eq (f : Frame) : f.exitChannels = f.graph.exits.zipIdx.map fun (p, i) => exitTemplate f.path f.graph p i := rfl

@[simp] theorem edgeTemplate_id (P g e i) : (edgeTemplate P g e i).id = identity (P ++ ["edge", toString i]) := rfl
@[simp] theorem edgeTemplate_edge (P g e i) : (edgeTemplate P g e i).edge = e := rfl
@[simp] theorem edgeTemplate_path (P g e i) : (edgeTemplate P g e i).path = P := rfl
@[simp] theorem edgeTemplate_entry (P g e i) : (edgeTemplate P g e i).entry = false := rfl
@[simp] theorem edgeTemplate_exit (P g e i) : (edgeTemplate P g e i).exit = false := rfl
@[simp] theorem edgeTemplate_kind (P g e i) : (edgeTemplate P g e i).kind = ((g.output? e.src).map (·.kind)).getD .plain := rfl
@[simp] theorem entryTemplate_id (P g p i) : (entryTemplate P g p i).id = identity (P ++ ["entry", toString i]) := rfl
@[simp] theorem entryTemplate_dst (P g p i) : (entryTemplate P g p i).edge.dst = p := rfl
@[simp] theorem entryTemplate_path (P g p i) : (entryTemplate P g p i).path = P := rfl
@[simp] theorem entryTemplate_entry (P g p i) : (entryTemplate P g p i).entry = true := rfl
@[simp] theorem entryTemplate_exit (P g p i) : (entryTemplate P g p i).exit = false := rfl
@[simp] theorem entryTemplate_kind (P g p i) : (entryTemplate P g p i).kind = ((g.input? p).map (·.kind)).getD .plain := rfl
@[simp] theorem exitTemplate_id (P g p i) : (exitTemplate P g p i).id = identity (P ++ ["exit", toString i]) := rfl
@[simp] theorem exitTemplate_src (P g p i) : (exitTemplate P g p i).edge.src = p := rfl
@[simp] theorem exitTemplate_path (P g p i) : (exitTemplate P g p i).path = P := rfl
@[simp] theorem exitTemplate_entry (P g p i) : (exitTemplate P g p i).entry = false := rfl
@[simp] theorem exitTemplate_exit (P g p i) : (exitTemplate P g p i).exit = true := rfl
@[simp] theorem exitTemplate_kind (P g p i) : (exitTemplate P g p i).kind = ((g.output? p).map (·.kind)).getD .plain := rfl

/-- Frame channels split into edge, entry and exit channels. -/
theorem template_cases (P : Path) (g : Graph) (d : Channel)
    (member : d ∈ ({ path := P, graph := g } : Frame).channels) :
    (∃ e i, (e, i) ∈ g.edges.zipIdx ∧ d = edgeTemplate P g e i) ∨
    (∃ p i, (p, i) ∈ g.entries.zipIdx ∧ d = entryTemplate P g p i) ∨
    (∃ p i, (p, i) ∈ g.exits.zipIdx ∧ d = exitTemplate P g p i) := by
  simp only [Frame.channels, Frame.edgeChannels_eq, Frame.entryChannels_eq, Frame.exitChannels_eq, List.mem_append] at member
  rcases member with (edge | entry) | exit
  · obtain ⟨⟨e, i⟩, hm, rfl⟩ := List.mem_map.mp edge
    exact .inl ⟨e, i, hm, rfl⟩
  · obtain ⟨⟨p, i⟩, hm, rfl⟩ := List.mem_map.mp entry
    exact .inr (.inl ⟨p, i, hm, rfl⟩)
  · obtain ⟨⟨p, i⟩, hm, rfl⟩ := List.mem_map.mp exit
    exact .inr (.inr ⟨p, i, hm, rfl⟩)

theorem template_edge_mem (P : Path) (g : Graph) (e : Edge) (i : Nat) (hm : (e, i) ∈ g.edges.zipIdx) :
    edgeTemplate P g e i ∈ ({ path := P, graph := g } : Frame).channels := by
  simp only [Frame.channels, Frame.edgeChannels_eq, List.mem_append]
  exact .inl (.inl (List.mem_map.mpr ⟨(e, i), hm, rfl⟩))

theorem template_entry_mem (P : Path) (g : Graph) (p : PortRef) (i : Nat) (hm : (p, i) ∈ g.entries.zipIdx) :
    entryTemplate P g p i ∈ ({ path := P, graph := g } : Frame).channels := by
  simp only [Frame.channels, Frame.entryChannels_eq, List.mem_append]
  exact .inl (.inr (List.mem_map.mpr ⟨(p, i), hm, rfl⟩))

theorem template_exit_mem (P : Path) (g : Graph) (p : PortRef) (i : Nat) (hm : (p, i) ∈ g.exits.zipIdx) :
    exitTemplate P g p i ∈ ({ path := P, graph := g } : Frame).channels := by
  simp only [Frame.channels, Frame.exitChannels_eq, List.mem_append]
  exact .inr (List.mem_map.mpr ⟨(p, i), hm, rfl⟩)

/-- Fields of a channel whose layout is a given channel. -/
theorem Channel.layout_eq_fields {c d : Channel} (h : c.layout = d) :
    c.id = d.id ∧ c.edge = d.edge ∧ c.path = d.path ∧ c.entry = d.entry ∧ c.exit = d.exit ∧ c.kind = d.kind := by
  subst h
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The unique non-exit channel of a frame feeding a validated input port. -/
theorem Scope.input_channel {s : State} {P : Path} {g : Graph} (sc : Scope s P g) (n : Node)
    (memberN : n ∈ g.nodes) (p : Port) (memberP : p ∈ n.inputs) :
    ∃ c ∈ s.channels, inputChannel? s P ⟨n.id, p.name⟩ = some c ∧ c.path = P ∧ c.exit = false ∧
      c.edge.dst = ⟨n.id, p.name⟩ ∧
      (c.entry = true → g.entries.contains (⟨n.id, p.name⟩ : PortRef) = true) ∧
      (c.entry = false → g.entries.contains (⟨n.id, p.name⟩ : PortRef) = false ∧ c.edge ∈ g.edges ∧
        g.edges.filter (·.dst == (⟨n.id, p.name⟩ : PortRef)) = [c.edge]) ∧
      (∀ d ∈ s.channels, d.path = P → d.exit = false → d.edge.dst = ⟨n.id, p.name⟩ → d = c) := by
  obtain ⟨body, valid⟩ := sc.valid
  have checkedN := g.validate_nodes body valid n memberN
  have source := g.input_single_source n p (g.validate_inputs n checkedN p memberP)
  obtain ⟨entriesNodup, _⟩ := g.validate_boundaries body valid
  let ref : PortRef := ⟨n.id, p.name⟩
  -- a witness channel `c0`, and the fact that every candidate equals it
  have key : ∃ c0 ∈ s.channels, c0.path = P ∧ c0.exit = false ∧ c0.edge.dst = ref ∧
      (c0.entry = true → g.entries.contains ref = true) ∧
      (c0.entry = false → g.entries.contains ref = false ∧ c0.edge ∈ g.edges ∧
        g.edges.filter (·.dst == ref) = [c0.edge]) ∧
      (∀ d ∈ s.channels, d.path = P → d.exit = false → d.edge.dst = ref → d = c0) := by
    rcases source with ⟨entry, noEdges⟩ | ⟨noEntry, e, single⟩
    · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (List.contains_iff_mem.mp entry)
      have hm : (ref, i) ∈ g.entries.zipIdx := List.mk_mem_zipIdx_iff_getElem?.mpr hi
      obtain ⟨c0, memberC0, layoutC0⟩ := sc.realized _ (template_entry_mem P g ref i hm)
      obtain ⟨idC0, edgeC0, pathC0, entryC0, exitC0, _⟩ := Channel.layout_eq_fields layoutC0
      simp only [entryTemplate_entry, entryTemplate_exit, entryTemplate_path] at entryC0 exitC0 pathC0
      refine ⟨c0, memberC0, pathC0, exitC0, by rw [edgeC0]; rfl, fun _ => entry, fun h => by rw [entryC0] at h; contradiction, ?_⟩
      intro d memberD pathD exitD dstD
      rcases template_cases P g d.layout (sc.template d memberD pathD) with ⟨e, j, hj, eq⟩ | ⟨q, j, hj, eq⟩ | ⟨q, j, hj, eq⟩
      · exfalso
        have edgeD : d.edge = e := by simpa using congrArg Channel.edge eq
        have inFilter : e ∈ g.edges.filter (·.dst == ref) :=
          List.mem_filter.mpr ⟨List.fst_mem_of_mem_zipIdx hj, by rw [← edgeD, dstD]; simp⟩
        rw [noEdges] at inFilter
        simp at inFilter
      · have dstD' : q = ref := by
          have := congrArg (fun c : Channel => c.edge.dst) eq
          simp only [Channel.layout_edge, entryTemplate_dst] at this
          rw [← this]
          exact dstD
        rw [dstD'] at hj eq
        have sameIndex : j = i := index_unique_of_filter (· == ref) g.entries
          (filter_eq_length_le_one_of_nodup entriesNodup ref)
          (List.mk_mem_zipIdx_iff_getElem?.mp hj) (List.mk_mem_zipIdx_iff_getElem?.mp hm)
          (beq_self_eq_true ref) (beq_self_eq_true ref)
        subst sameIndex
        exact sc.unique_layout memberD memberC0 (eq.trans layoutC0.symm)
      · exfalso
        have := congrArg Channel.exit eq
        simp [exitD] at this
    · have eMember : e ∈ g.edges := by
        have : e ∈ g.edges.filter (·.dst == ref) := by rw [single]; simp
        exact (List.mem_filter.mp this).1
      have eDst : e.dst = ref := by
        have : e ∈ g.edges.filter (·.dst == ref) := by rw [single]; simp
        simpa using (List.mem_filter.mp this).2
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp eMember
      have hm : (e, i) ∈ g.edges.zipIdx := List.mk_mem_zipIdx_iff_getElem?.mpr hi
      obtain ⟨c0, memberC0, layoutC0⟩ := sc.realized _ (template_edge_mem P g e i hm)
      obtain ⟨idC0, edgeC0, pathC0, entryC0, exitC0, _⟩ := Channel.layout_eq_fields layoutC0
      simp only [entryTemplate_entry, entryTemplate_exit, entryTemplate_path, edgeTemplate_entry, edgeTemplate_exit, edgeTemplate_path, edgeTemplate_edge] at entryC0 exitC0 pathC0 edgeC0
      refine ⟨c0, memberC0, pathC0, exitC0, by rw [edgeC0, eDst], fun h => by rw [entryC0] at h; contradiction,
        fun _ => ⟨noEntry, by rw [edgeC0]; exact eMember, by rw [edgeC0]; exact single⟩, ?_⟩
      intro d memberD pathD exitD dstD
      rcases template_cases P g d.layout (sc.template d memberD pathD) with ⟨e', j, hj, eq⟩ | ⟨q, j, hj, eq⟩ | ⟨q, j, hj, eq⟩
      · have edgeD : d.edge = e' := by simpa using congrArg Channel.edge eq
        have e'Dst : e'.dst = ref := by rw [← edgeD]; exact dstD
        have sameIndex : j = i := index_unique_of_filter (·.dst == ref) g.edges (by rw [single]; simp)
          (List.mk_mem_zipIdx_iff_getElem?.mp hj) (List.mk_mem_zipIdx_iff_getElem?.mp hm) (by simp [e'Dst]) (by simp [eDst])
        subst sameIndex
        have sameEdge : e' = e := by
          have : e' ∈ g.edges.filter (·.dst == ref) :=
            List.mem_filter.mpr ⟨List.fst_mem_of_mem_zipIdx hj, by simp [e'Dst]⟩
          rw [single] at this
          simpa using this
        subst sameEdge
        exact sc.unique_layout memberD memberC0 (eq.trans layoutC0.symm)
      · exfalso
        have dstD' : q = ref := by
          have := congrArg (fun c : Channel => c.edge.dst) eq
          simp only [Channel.layout_edge, entryTemplate_dst] at this
          rw [← this]
          exact dstD
        rw [dstD'] at hj
        have : ref ∈ g.entries := List.fst_mem_of_mem_zipIdx hj
        rw [← List.contains_iff_mem, noEntry] at this
        contradiction
      · exfalso
        have := congrArg Channel.exit eq
        simp [exitD] at this
  obtain ⟨c0, memberC0, pathC0, exitC0, dstC0, entryC0, edgeC0, uniqueC0⟩ := key
  have exists_ : (inputChannel? s P ref).isSome :=
    List.find?_isSome.mpr ⟨c0, memberC0, by simp [pathC0, exitC0, dstC0]⟩
  cases found : inputChannel? s P ref with
  | none => rw [found] at exists_; contradiction
  | some c =>
    have memberC : c ∈ s.channels := List.mem_of_find?_eq_some found
    have props := List.find?_some found
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at props
    have same : c = c0 := uniqueC0 c memberC props.1.1 props.1.2 props.2
    subst same
    exact ⟨c, memberC, rfl, pathC0, exitC0, dstC0, entryC0, edgeC0, uniqueC0⟩

/-- The unique exit channel of a frame for a validated exit port. -/
theorem Scope.exit_channel {s : State} {P : Path} {g : Graph} (sc : Scope s P g) (p : PortRef) (memberP : p ∈ g.exits) :
    ∃ c ∈ s.channels, exitChannel? s P p = some c ∧ c.path = P ∧ c.exit = true ∧ c.entry = false ∧
      c.edge.src = p ∧ (∀ d ∈ s.channels, d.path = P → d.exit = true → d.edge.src = p → d = c) := by
  obtain ⟨body, valid⟩ := sc.valid
  obtain ⟨_, exitsNodup⟩ := g.validate_boundaries body valid
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp memberP
  have hm : (p, i) ∈ g.exits.zipIdx := List.mk_mem_zipIdx_iff_getElem?.mpr hi
  obtain ⟨c0, memberC0, layoutC0⟩ := sc.realized _ (template_exit_mem P g p i hm)
  obtain ⟨idC0, edgeC0, pathC0, entryC0, exitC0, _⟩ := Channel.layout_eq_fields layoutC0
  simp only [exitTemplate_entry, exitTemplate_exit, exitTemplate_path] at entryC0 exitC0 pathC0
  have uniqueC0 : ∀ d ∈ s.channels, d.path = P → d.exit = true → d.edge.src = p → d = c0 := by
    intro d memberD pathD exitD srcD
    rcases template_cases P g d.layout (sc.template d memberD pathD) with ⟨e, j, hj, eq⟩ | ⟨q, j, hj, eq⟩ | ⟨q, j, hj, eq⟩
    · exfalso
      have := congrArg Channel.exit eq
      simp [exitD] at this
    · exfalso
      have := congrArg Channel.exit eq
      simp [exitD] at this
    · have srcD' : q = p := by
        have := congrArg (fun c : Channel => c.edge.src) eq
        simp only [Channel.layout_edge, exitTemplate_src] at this
        rw [← this]
        exact srcD
      rw [srcD'] at hj eq
      have sameIndex : j = i := index_unique_of_filter (· == p) g.exits
        (filter_eq_length_le_one_of_nodup exitsNodup p)
        (List.mk_mem_zipIdx_iff_getElem?.mp hj) (List.mk_mem_zipIdx_iff_getElem?.mp hm)
        (beq_self_eq_true p) (beq_self_eq_true p)
      subst sameIndex
      exact sc.unique_layout memberD memberC0 (eq.trans layoutC0.symm)
  have exists_ : (exitChannel? s P p).isSome :=
    List.find?_isSome.mpr ⟨c0, memberC0, by simp [pathC0, exitC0, edgeC0]⟩
  cases found : exitChannel? s P p with
  | none => rw [found] at exists_; contradiction
  | some c =>
    have memberC : c ∈ s.channels := List.mem_of_find?_eq_some found
    have props := List.find?_some found
    simp only [Bool.and_eq_true, beq_iff_eq] at props
    have same : c = c0 := uniqueC0 c memberC props.1.1 props.1.2 props.2
    subst same
    exact ⟨c, memberC, rfl, pathC0, exitC0, entryC0, by rw [edgeC0]; rfl, uniqueC0⟩

end Suimon
