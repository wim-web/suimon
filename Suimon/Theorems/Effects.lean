import Suimon.Theorems.Layout

namespace Suimon.Effects

/-- Erasing the checks from a successful placement exposes exactly this update. --/
def insertToken (c : Channel) (t : Token) : Channel :=
  if c.placed.contains t then c else { c with placed := c.placed ++ [t] }

def write (s : State) (ids : List String) (t : Token) : State :=
  { s with channels := s.channels.map fun c => if ids.contains c.id then insertToken c t else c }

def output (s : State) (path : Path) (node port : String) (t : Token) : State :=
  write s ((s.outgoing path node port).map (·.id)) t

theorem placeToken_value (c next : Channel) (t : Token)
    (accepted : placeToken c t = .ok next) : next = insertToken c t := by
  simp only [placeToken, require, bind, Except.bind, pure, Except.pure] at accepted
  repeat (first
    | split at accepted
    | contradiction
    | (cases accepted; simp_all [insertToken]))

theorem place_value (s next : State) (ids : List String) (t : Token)
    (accepted : place s ids t = .ok next) : next = write s ids t := by
  change ((s.channels.mapM (fun c => if ids.contains c.id then placeToken c t else .ok c)) >>= fun cs =>
    Except.ok { s with channels := cs }) = .ok next at accepted
  cases computed : s.channels.mapM (fun c => if ids.contains c.id then placeToken c t else .ok c) with
  | error e => rw [computed] at accepted; contradiction
  | ok cs =>
    have effect := mapM_eq_map _ (fun c => if ids.contains c.id then insertToken c t else c)
      s.channels cs (by
        intro c member d valid
        dsimp at valid ⊢
        split at valid
        · rename_i selected
          simp only [selected, ↓reduceIte]
          exact placeToken_value c d t valid
        · rename_i absent
          simp only [absent, ↓reduceIte]
          cases valid
          rfl) computed
    simp only [computed, bind, Except.bind, pure, Except.pure] at accepted
    cases accepted
    simp only [write, effect]

theorem putOutput_value (s next : State) (path : Path) (node port : String) (t : Token)
    (accepted : putOutput s path node port t = .ok next) : next = output s path node port t :=
  place_value s next _ t accepted

theorem closeOutputs_value (s next : State) (path : Path) (n : Node)
    (accepted : closeOutputs s path n = .ok next) :
    next = n.outputs.foldl (fun state p => output state path n.id p.name .eos) s :=
  foldlM_eq_foldl _ _ n.outputs s next
    (fun state p _ after valid => putOutput_value state after path n.id p.name .eos valid) accepted

theorem placeOutputs_value (s next : State) (path : Path) (node : NodeId) (outputs : List Output)
    (accepted : placeOutputs s path node outputs = .ok next) :
    next = outputs.foldl (fun state out => out.items.foldl
      (fun state item => output state path node out.port (.item item)) state) s := by
  apply foldlM_eq_foldl _ _ outputs s next _ accepted
  intro state out _ after valid
  exact foldlM_eq_foldl _ _ out.items state after
    (fun current item _ written correct => putOutput_value current written path node out.port (.item item) correct) valid

theorem placeBodyOutputs_value (s next : State) (path : Path) (n : Node) (items : List ItemId)
    (accepted : placeBodyOutputs s path n items = .ok next) :
    next = (n.outputs.zip items).foldl
      (fun state pair => output state path n.id pair.1.name (.item pair.2)) s :=
  foldlM_eq_foldl _ _ (n.outputs.zip items) s next
    (fun state pair _ after valid => putOutput_value state after path n.id pair.1.name (.item pair.2) valid) accepted

theorem insertToken_mem (c : Channel) (t token : Token) :
    token ∈ (insertToken c t).placed ↔ token ∈ c.placed ∨ token = t := by
  unfold insertToken
  split
  · rename_i present
    have member : t ∈ c.placed := by simpa using present
    constructor
    · exact Or.inl
    · rintro (old | same)
      · exact old
      · simpa [same] using member
  · simp [List.mem_append, eq_comm]

/-- A successful placement is a set insertion even after the cursor has passed
    the original occurrence. It never changes the occurrence's multiplicity. --/
theorem placeToken_items (c next : Channel) (t : Token) (item : ItemId)
    (accepted : placeToken c t = .ok next) :
    item ∈ next.items ↔ item ∈ c.items ∨ t = .item item := by
  rw [placeToken_value c next t accepted]
  have items : ∀ d : Channel, item ∈ d.items ↔ Token.item item ∈ d.placed := by
    intro d
    simp only [Channel.items, List.mem_filterMap]
    constructor
    · rintro ⟨token, member, correct⟩
      cases token with
      | eos => contradiction
      | item value => cases correct; exact member
    · intro member
      exact ⟨.item item, member, rfl⟩
  rw [items, items, insertToken_mem]
  simp only [eq_comm]

def HasItem (s : State) (channel : String) (item : ItemId) : Prop :=
  ∃ c ∈ s.channels, c.id = channel ∧ item ∈ c.items

theorem insertToken_id (c : Channel) (token : Token) : (insertToken c token).id = c.id := by
  unfold insertToken
  split <;> rfl

theorem item_mem (c : Channel) (item : ItemId) : item ∈ c.items ↔ Token.item item ∈ c.placed := by
  simp only [Channel.items, List.mem_filterMap]
  constructor
  · rintro ⟨token, member, correct⟩
    cases token with
    | eos => contradiction
    | item value => cases correct; exact member
  · intro member
    exact ⟨.item item, member, rfl⟩

theorem insertToken_item_mem (c : Channel) (token : Token) (item : ItemId) :
    item ∈ (insertToken c token).items ↔ item ∈ c.items ∨ token = .item item := by
  rw [item_mem, item_mem, insertToken_mem]
  simp only [eq_comm]

/-- Placement adds just the requested occurrence to existing selected channels.
    This equality of predicates needs no scheduling or termination premise. --/
theorem write_items (s : State) (ids : List String) (token : Token) (channel : String) (item : ItemId) :
    HasItem (write s ids token) channel item ↔
      HasItem s channel item ∨
      (channel ∈ ids ∧ token = .item item ∧ ∃ c ∈ s.channels, c.id = channel) := by
  constructor
  · rintro ⟨d, member, idD, itemD⟩
    obtain ⟨c, memberC, same⟩ := List.mem_map.mp member
    by_cases selected : c.id ∈ ids
    · have same' : insertToken c token = d := by simpa only [List.contains_iff_mem, selected, ↓reduceIte] using same
      rw [← same'] at idD itemD
      have idC : c.id = channel := by simpa only [insertToken_id] using idD
      rcases (insertToken_item_mem c token item).mp itemD with old | added
      · exact .inl ⟨c, memberC, idC, old⟩
      · exact .inr ⟨idC ▸ selected, added, c, memberC, idC⟩
    · have same' : c = d := by simpa only [List.contains_iff_mem, selected, ↓reduceIte] using same
      rw [← same'] at idD itemD
      exact .inl ⟨c, memberC, idD, itemD⟩
  · intro itemPresent
    rcases itemPresent with ⟨c, member, idC, old⟩ | ⟨selected, tokenEq, c, member, idC⟩
    · by_cases selected : c.id ∈ ids
      · refine ⟨insertToken c token, List.mem_map.mpr ⟨c, member, ?_⟩, ?_, ?_⟩
        · simp only [List.contains_iff_mem, selected, ↓reduceIte]
        · simpa only [insertToken_id] using idC
        · exact (insertToken_item_mem c token item).mpr (.inl old)
      · refine ⟨c, List.mem_map.mpr ⟨c, member, ?_⟩, idC, old⟩
        simp only [List.contains_iff_mem, selected, ↓reduceIte]
    · have selectedC : c.id ∈ ids := idC ▸ selected
      refine ⟨insertToken c token, List.mem_map.mpr ⟨c, member, ?_⟩, ?_, ?_⟩
      · simp only [List.contains_iff_mem, selectedC, ↓reduceIte]
      · simpa only [insertToken_id] using idC
      · exact (insertToken_item_mem c token item).mpr (.inr tokenEq)

theorem place_items (s next : State) (ids : List String) (token : Token) (channel : String) (item : ItemId)
    (accepted : place s ids token = .ok next) :
    HasItem next channel item ↔ HasItem s channel item ∨
      (channel ∈ ids ∧ token = .item item ∧ ∃ c ∈ s.channels, c.id = channel) := by
  rw [place_value s next ids token accepted]
  exact write_items s ids token channel item

theorem consume_placed (s next : State) (channel who : String) (expected : Option ItemId)
    (accepted : consume s channel who expected = .ok next) :
    next.channels.map (fun c => (c.id, c.placed)) = s.channels.map (fun c => (c.id, c.placed)) := by
  simp only [consume, Option.toExcept, require, bind, Except.bind, pure, Except.pure] at accepted
  repeat (first
    | split at accepted
    | (simp only [bind, Except.bind, pure, Except.pure] at accepted)
    | contradiction
    | (cases accepted
       simp only [List.map_map]
       apply List.map_congr_left
       intro c member
       dsimp
       split <;> rfl))

end Suimon.Effects
