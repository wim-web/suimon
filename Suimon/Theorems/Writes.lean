import Suimon.Theorems.LeafOutputs

/-! Placement descriptors. Every channel mutation performed by `transition` is a
    consume (which never changes `placed`) or a group write described by `Write`.
    Reasoning about which operations can touch a channel then becomes generic. -/

namespace Suimon
open Effects

/-- The scheduling-independent part of a channel: everything except the cursor. -/
def Channel.core (c : Channel) : Channel := { c with consumed := 0 }
def State.placedView (s : State) : List Channel := s.channels.map Channel.core

inductive Write where
  | out (path : Path) (node port : String) (t : Token)
  | seed (path : Path) (p : PortRef) (t : Token)
  | root (p : PortRef) (t : Token)
  deriving Repr

def Write.ids (st : State) : Write → List String
  | .out path node port _ => (st.outgoing path node port).map (·.id)
  | .seed path p _ => ((st.incoming path p.node).filter (fun c => c.entry && c.edge.dst == p)).map (·.id)
  | .root p _ => (st.channels.filter (fun c => c.path.isEmpty && c.entry && c.edge.dst == p)).map (·.id)

def Write.token : Write → Token
  | .out _ _ _ t | .seed _ _ t | .root _ t => t

def applyWrite (st : State) (w : Write) : State := write st (w.ids st) w.token
def applyWrites (ws : List Write) (st : State) : State := ws.foldl applyWrite st

@[simp] theorem applyWrite_out (st : State) (path : Path) (node port : String) (t : Token) :
    applyWrite st (.out path node port t) = output st path node port t := rfl

@[simp] theorem applyWrites_nil (st : State) : applyWrites [] st = st := rfl
@[simp] theorem applyWrites_cons (w : Write) (ws : List Write) (st : State) :
    applyWrites (w :: ws) st = applyWrites ws (applyWrite st w) := rfl
theorem applyWrites_append (a b : List Write) (st : State) :
    applyWrites (a ++ b) st = applyWrites b (applyWrites a st) := List.foldl_append

/-! ### Core-field facts -/

@[simp] theorem Channel.core_id (c : Channel) : c.core.id = c.id := rfl
@[simp] theorem Channel.core_edge (c : Channel) : c.core.edge = c.edge := rfl
@[simp] theorem Channel.core_path (c : Channel) : c.core.path = c.path := rfl
@[simp] theorem Channel.core_entry (c : Channel) : c.core.entry = c.entry := rfl
@[simp] theorem Channel.core_exit (c : Channel) : c.core.exit = c.exit := rfl
@[simp] theorem Channel.core_kind (c : Channel) : c.core.kind = c.kind := rfl
@[simp] theorem Channel.core_placed (c : Channel) : c.core.placed = c.placed := rfl
@[simp] theorem Channel.core_items (c : Channel) : c.core.items = c.items := rfl
@[simp] theorem Channel.core_closed (c : Channel) : c.core.closed = c.closed := rfl
@[simp] theorem Channel.core_core (c : Channel) : c.core.core = c.core := rfl

theorem insertToken_core (c : Channel) (t : Token) : (insertToken c t).core = insertToken c.core t := by
  unfold insertToken
  split <;> simp_all [Channel.core]

theorem placedView_ids (s : State) : s.placedView.map (·.id) = s.channels.map (·.id) := by
  simp [State.placedView, List.map_map, Function.comp_def]

theorem placedView_member {s : State} {c : Channel} (member : c ∈ s.channels) : c.core ∈ s.placedView :=
  List.mem_map.mpr ⟨c, member, rfl⟩

/-- The selected identifiers of a write depend only on the placed view. -/
theorem Write.ids_placedView (w : Write) (a b : State) (same : a.placedView = b.placedView) :
    w.ids a = w.ids b := by
  have channels : ∀ (pred : Channel → Bool), (∀ c : Channel, pred c.core = pred c) →
      (a.channels.filter pred).map (·.id) = (b.channels.filter pred).map (·.id) := by
    intro pred stable
    have view : ∀ s : State, (s.channels.filter pred).map (·.id) = (s.placedView.filter pred).map (·.id) := by
      intro s
      simp only [State.placedView, List.filter_map, List.map_map]
      congr 1
      exact List.filter_congr (fun c _ => by simp [Function.comp_def, stable])
    rw [view a, view b, same]
  cases w with
  | out path node port t =>
    exact channels _ (fun c => by simp [Channel.core])
  | seed path p t =>
    simp only [Write.ids, State.incoming, List.filter_filter]
    exact channels _ (fun c => by simp [Channel.core])
  | root p t =>
    exact channels _ (fun c => by simp [Channel.core])

theorem write_placedView (a b : State) (ids : List String) (t : Token) (same : a.placedView = b.placedView) :
    (write a ids t).placedView = (write b ids t).placedView := by
  have view : ∀ s : State, (write s ids t).placedView =
      s.placedView.map (fun c => if ids.contains c.id then insertToken c t else c) := by
    intro s
    simp only [write, State.placedView, List.map_map]
    apply List.map_congr_left
    intro c _
    simp only [Function.comp_def]
    split <;> simp_all [insertToken_core]
  rw [view a, view b, same]

theorem applyWrite_placedView (a b : State) (w : Write) (same : a.placedView = b.placedView) :
    (applyWrite a w).placedView = (applyWrite b w).placedView := by
  unfold applyWrite
  rw [w.ids_placedView a b same]
  exact write_placedView a b _ _ same

theorem applyWrites_placedView (ws : List Write) (a b : State) (same : a.placedView = b.placedView) :
    (applyWrites ws a).placedView = (applyWrites ws b).placedView := by
  induction ws generalizing a b with
  | nil => exact same
  | cons w ws ih => exact ih _ _ (applyWrite_placedView a b w same)

theorem applyWrite_ids (st : State) (w : Write) :
    (applyWrite st w).channels.map (·.id) = st.channels.map (·.id) := write_ids _ _ _

theorem applyWrites_ids (ws : List Write) (st : State) :
    (applyWrites ws st).channels.map (·.id) = st.channels.map (·.id) := by
  induction ws generalizing st with
  | nil => rfl
  | cons w ws ih => exact (ih _).trans (applyWrite_ids st w)

/-! ### Locality: a write leaves every channel outside its group untouched -/

theorem write_unselected (st : State) (ids : List String) (t : Token) (c : Channel)
    (member : c ∈ st.channels) (unselected : ids.contains c.id = false) : c ∈ (write st ids t).channels := by
  simp only [write]
  refine List.mem_map.mpr ⟨c, member, ?_⟩
  have notMem : c.id ∉ ids := fun h => by
    have := List.contains_iff_mem.mpr h
    rw [unselected] at this
    contradiction
  simp [notMem]

theorem applyWrite_untouched (st : State) (w : Write) (c : Channel) (member : c ∈ st.channels)
    (distinct : (st.channels.map (·.id)).Nodup) (nonEntry : c.entry = false)
    (miss : ∀ t, w ≠ .out c.path c.edge.src.node c.edge.src.port t) :
    c ∈ (applyWrite st w).channels := by
  apply write_unselected st _ _ c member
  cases w with
  | out path node port t =>
    by_cases selected : ((st.outgoing path node port).map (·.id)).contains c.id = true
    · exfalso
      have facts := (outgoing_ids_of_follows c st path node port distinct (Follows.refl c st member)).mp selected
      obtain ⟨pathC, _, srcC⟩ := facts
      apply miss t
      rw [pathC, srcC]
    · simpa [Write.ids] using selected
  | seed path p t =>
    simp only [Write.ids, Bool.eq_false_iff, ne_eq, List.contains_iff_mem, List.mem_map, not_exists, not_and]
    intro e memberE idE
    have inChannels : e ∈ st.channels := (List.mem_filter.mp (List.mem_filter.mp memberE).1).1
    have entryE : e.entry = true := by
      have := (List.mem_filter.mp memberE).2
      simp only [Bool.and_eq_true] at this
      exact this.1
    have same : e = c := eq_of_mapped_nodup (·.id) st.channels distinct e c inChannels member idE
    subst same
    rw [entryE] at nonEntry
    contradiction
  | root p t =>
    simp only [Write.ids, Bool.eq_false_iff, ne_eq, List.contains_iff_mem, List.mem_map, not_exists, not_and]
    intro e memberE idE
    have inChannels : e ∈ st.channels := (List.mem_filter.mp memberE).1
    have entryE : e.entry = true := by
      have := (List.mem_filter.mp memberE).2
      simp only [Bool.and_eq_true] at this
      exact this.1.2
    have same : e = c := eq_of_mapped_nodup (·.id) st.channels distinct e c inChannels member idE
    subst same
    rw [entryE] at nonEntry
    contradiction

theorem applyWrites_untouched (ws : List Write) (st : State) (c : Channel) (member : c ∈ st.channels)
    (distinct : (st.channels.map (·.id)).Nodup) (nonEntry : c.entry = false)
    (miss : ∀ w ∈ ws, ∀ t, w ≠ .out c.path c.edge.src.node c.edge.src.port t) :
    c ∈ (applyWrites ws st).channels := by
  induction ws generalizing st with
  | nil => exact member
  | cons w ws ih =>
    simp only [applyWrites_cons]
    apply ih (applyWrite st w) (applyWrite_untouched st w c member distinct nonEntry (miss w (by simp)))
    · rw [applyWrite_ids]; exact distinct
    · intro v hv t; exact miss v (by simp [hv]) t

end Suimon
