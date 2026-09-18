import Suimon.Graph
import Suimon.Theorems.Traversal

namespace Suimon

theorem unique_nodup {α : Type} [BEq α] [LawfulBEq α] (xs : List α)
    (checked : unique xs = true) : xs.Nodup := by
  have same : xs.eraseDups = xs := (eraseDups_sublist xs).eq_of_length (by simpa [unique] using checked)
  rw [← same]
  exact eraseDups_nodup xs

/-- A successful Kahn check gives a rank increasing along every internal edge. --/
theorem acyclicAux_rank (edges : List Edge) (fuel : Nat) (nodes : List NodeId)
    (checked : acyclicAux edges fuel nodes = true) :
    ∃ rank : NodeId → Nat, ∀ e ∈ edges,
      e.src.node ∈ nodes → e.dst.node ∈ nodes → rank e.src.node < rank e.dst.node := by
  induction fuel generalizing nodes with
  | zero =>
    have empty : nodes = [] := by simpa [acyclicAux] using checked
    subst nodes
    exact ⟨fun _ => 0, by simp⟩
  | succ fuel ih =>
    by_cases empty : nodes.isEmpty = true
    · have nil : nodes = [] := by simpa using empty
      subst nodes
      exact ⟨fun _ => 0, by simp⟩
    · let roots := nodes.filter fun n => !edges.any (fun e => e.dst.node == n && nodes.contains e.src.node)
      let rest := nodes.filter (!roots.contains ·)
      have reduced : acyclicAux edges fuel rest = true := by
        simp only [acyclicAux, empty] at checked
        exact (Bool.and_eq_true_iff.mp checked).2
      obtain ⟨rank, increasing⟩ := ih rest reduced
      refine ⟨fun n => if n ∈ roots then 0 else rank n + 1, ?_⟩
      intro e edge source target
      have targetNotRoot : e.dst.node ∉ roots := by
        intro root
        have absent := (List.mem_filter.mp root).2
        have present : edges.any (fun a => a.dst.node == e.dst.node && nodes.contains a.src.node) = true :=
          List.any_eq_true.mpr ⟨e, edge, by simp [source]⟩
        simp only [present, Bool.not_true, Bool.false_eq_true] at absent
      by_cases sourceRoot : e.src.node ∈ roots
      · simp [sourceRoot, targetNotRoot]
      · simp only [sourceRoot, targetNotRoot, ↓reduceIte]
        apply Nat.add_lt_add_right
        exact increasing e edge (by simp [rest, source, sourceRoot]) (by simp [rest, target, targetNotRoot])

theorem Graph.validate_acyclic (g : Graph) (body : Bool)
    (checked : g.validate body = .ok ()) :
    acyclicAux g.edges g.nodes.length (g.nodes.map (·.id)) = true := by
  rw [Graph.validate] at checked
  repeat (first
    | (split at checked)
    | (simp only [bind, Except.bind, pure, Except.pure] at checked)
    | contradiction
    | assumption)

theorem Graph.WellFormed.topologicalRank (g : Graph) (wellFormed : g.WellFormed) :
    ∃ rank : NodeId → Nat, ∀ e ∈ g.edges,
      e.src.node ∈ g.nodes.map (·.id) → e.dst.node ∈ g.nodes.map (·.id) →
        rank e.src.node < rank e.dst.node :=
  acyclicAux_rank g.edges g.nodes.length (g.nodes.map (·.id)) (g.validate_acyclic false wellFormed)

theorem Graph.validate_edges (g : Graph) (body : Bool) (checked : g.validate body = .ok ()) :
    ∀ e ∈ g.edges, g.validateEdge e = .ok () := by
  have all : ∃ values, g.edges.mapM g.validateEdge = .ok values := by
    rw [Graph.validate] at checked
    repeat (first
      | (exact ⟨_, by assumption⟩)
      | (split at checked)
      | (simp only [bind, Except.bind, pure, Except.pure] at checked)
      | contradiction)
  obtain ⟨values, accepted⟩ := all
  intro e member
  obtain ⟨value, correct⟩ := mapM_ok_members g.validateEdge g.edges values accepted e member
  cases value
  exact correct

theorem Graph.validate_exits (g : Graph) (body : Bool) (checked : g.validate body = .ok ()) :
    ∀ p ∈ g.exits, g.validateExit p = .ok () := by
  have all : ∃ values, g.exits.mapM g.validateExit = .ok values := by
    rw [Graph.validate] at checked
    repeat (first
      | (exact ⟨_, by assumption⟩)
      | (split at checked)
      | (simp only [bind, Except.bind, pure, Except.pure] at checked)
      | contradiction)
  obtain ⟨values, accepted⟩ := all
  intro p member
  obtain ⟨value, correct⟩ := mapM_ok_members g.validateExit g.exits values accepted p member
  cases value
  exact correct

theorem Graph.output_node_member (g : Graph) (ref : PortRef) (port : Port)
    (found : g.output? ref = some port) : ref.node ∈ g.nodes.map (·.id) := by
  unfold Graph.output? at found
  cases node : g.node? ref.node with
  | none => simp [node] at found
  | some n =>
    have member := List.mem_of_find?_eq_some node
    have name := List.find?_some node
    exact List.mem_map.mpr ⟨n, member, by simpa using name⟩

theorem Graph.input_node_member (g : Graph) (ref : PortRef) (port : Port)
    (found : g.input? ref = some port) : ref.node ∈ g.nodes.map (·.id) := by
  unfold Graph.input? at found
  cases node : g.node? ref.node with
  | none => simp [node] at found
  | some n =>
    have member := List.mem_of_find?_eq_some node
    have name := List.find?_some node
    exact List.mem_map.mpr ⟨n, member, by simpa using name⟩

theorem Graph.validateEdge_nodes (g : Graph) (e : Edge) (checked : g.validateEdge e = .ok ()) :
    e.src.node ∈ g.nodes.map (·.id) ∧ e.dst.node ∈ g.nodes.map (·.id) := by
  cases output : g.output? e.src with
  | none => simp [Graph.validateEdge, output] at checked
  | some a =>
    cases input : g.input? e.dst with
    | none => simp [Graph.validateEdge, output, input] at checked
    | some b => exact ⟨g.output_node_member e.src a output, g.input_node_member e.dst b input⟩

theorem Graph.validateExit_node (g : Graph) (p : PortRef) (checked : g.validateExit p = .ok ()) :
    p.node ∈ g.nodes.map (·.id) := by
  cases found : g.output? p with
  | none => simp [Graph.validateExit, found] at checked
  | some a => exact g.output_node_member p a found

theorem Graph.validate_nodes (g : Graph) (body : Bool) (checked : g.validate body = .ok ()) :
    ∀ n ∈ g.nodes, g.validateNode n = .ok () := by
  have all : ∃ values, g.nodes.attach.mapM (fun n => g.validateNode n.val) = .ok values := by
    rw [Graph.validate] at checked
    repeat (first
      | (exact ⟨_, by assumption⟩)
      | (split at checked)
      | (simp only [bind, Except.bind, pure, Except.pure] at checked)
      | contradiction)
  obtain ⟨values, accepted⟩ := all
  intro n member
  obtain ⟨value, correct⟩ := mapM_ok_members (fun n => g.validateNode n.val) g.nodes.attach values
    accepted ⟨n, member⟩ (by simp)
  cases value
  exact correct

theorem Graph.validateNode_shape (g : Graph) (n : Node) (checked : g.validateNode n = .ok ()) :
    n.shapeOK = true := by
  rw [Graph.validateNode] at checked
  cases shape : g.validateShape n with
  | error e => simp [shape, bind, Except.bind] at checked
  | ok value =>
    cases ready : n.shapeOK with
    | true => rfl
    | false =>
      simp only [Graph.validateShape, ready, bind, Except.bind, pure, Except.pure] at shape
      repeat (first | split at shape | contradiction)

theorem Graph.validateNode_child (g : Graph) (n : Node) (child : Graph)
    (kind : (∃ limit, n.kind = .loop child limit) ∨ n.kind = .subworkflow child ∨ n.kind = .forEach child)
    (checked : g.validateNode n = .ok ()) : child.validate true = .ok () := by
  rw [Graph.validateNode] at checked
  cases shape : g.validateShape n with
  | error e => simp [shape, bind, Except.bind] at checked
  | ok value =>
    simp only [shape, bind, Except.bind] at checked
    rcases kind with ⟨limit, loopKind⟩ | subKind | eachKind
    · rw [loopKind] at checked
      exact checked
    · rw [subKind] at checked
      exact checked
    · rw [eachKind] at checked
      exact checked

theorem Graph.validateNode_validateShape (g : Graph) (n : Node)
    (checked : g.validateNode n = .ok ()) : g.validateShape n = .ok () := by
  rw [Graph.validateNode] at checked
  cases shape : g.validateShape n with
  | error e => simp [shape, bind, Except.bind] at checked
  | ok value => cases value; rfl

theorem Graph.validate_node_names (g : Graph) (body : Bool) (checked : g.validate body = .ok ()) :
    (g.nodes.map (·.id)).Nodup := by
  apply unique_nodup
  rw [Graph.validate] at checked
  repeat' (first
    | split at checked
    | (simp only [bind, Except.bind, pure, Except.pure] at checked)
    | contradiction
    | assumption)

theorem Graph.validate_port_names (g : Graph) (n : Node) (checked : g.validateNode n = .ok ()) :
    (n.inputs.map (·.name)).Nodup ∧ (n.outputs.map (·.name)).Nodup := by
  have shape := g.validateNode_validateShape n checked
  have names : (!n.id.isEmpty && unique (n.inputs.map (·.name)) && unique (n.outputs.map (·.name)) &&
      (n.inputs ++ n.outputs).all (fun p => !p.name.isEmpty)) = true := by
    unfold Graph.validateShape at shape
    repeat' (first
      | split at shape
      | (simp only [bind, Except.bind, pure, Except.pure] at shape)
      | contradiction
      | assumption)
  simp only [Bool.and_eq_true] at names
  exact ⟨unique_nodup _ names.1.1.2, unique_nodup _ names.1.2⟩

theorem Graph.validate_inputs (g : Graph) (n : Node) (checked : g.validateNode n = .ok ()) :
    ∀ p ∈ n.inputs, g.validateInput n p = .ok () := by
  have shape := g.validateNode_validateShape n checked
  have all : ∃ values, n.inputs.mapM (g.validateInput n) = .ok values := by
    unfold Graph.validateShape at shape
    repeat' (first
      | (exact ⟨_, by assumption⟩)
      | split at shape
      | (simp only [bind, Except.bind, pure, Except.pure] at shape)
      | contradiction)
  obtain ⟨values, accepted⟩ := all
  intro p member
  obtain ⟨value, correct⟩ := mapM_ok_members (g.validateInput n) n.inputs values accepted p member
  cases value
  exact correct

theorem Graph.input_single_source (g : Graph) (n : Node) (p : Port)
    (checked : g.validateInput n p = .ok ()) :
    let ref : PortRef := ⟨n.id, p.name⟩
    (g.entries.contains ref = true ∧ g.edges.filter (·.dst == ref) = []) ∨
    (g.entries.contains ref = false ∧ ∃ e, g.edges.filter (·.dst == ref) = [e]) := by
  let ref : PortRef := ⟨n.id, p.name⟩
  change (g.entries.contains ref = true ∧ g.edges.filter (·.dst == ref) = []) ∨
    (g.entries.contains ref = false ∧ ∃ e, g.edges.filter (·.dst == ref) = [e])
  have count : (g.edges.filter (·.dst == ref)).length + (if g.entries.contains ref then 1 else 0) = 1 := by
    unfold Graph.validateInput at checked
    dsimp only at checked
    repeat' (first
      | split at checked
      | (solve | simp_all [ref, pure, Except.pure]))
  cases entry : g.entries.contains ref with
  | true =>
    refine .inl ⟨rfl, ?_⟩
    apply List.length_eq_zero_iff.mp
    simp only [entry, ↓reduceIte] at count
    omega
  | false =>
    refine .inr ⟨rfl, ?_⟩
    apply List.length_eq_one_iff.mp
    simpa only [entry, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using count

end Suimon
