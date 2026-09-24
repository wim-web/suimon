import Suimon.Workflow
import Std.Data.HashMap.Lemmas

namespace Suimon

/-- The input of one call: `some none` for a body without input, `none` for an unknown body. --/
def Definition.bodyInput (p : Definition) : Body → Option (Option ValueType)
  | .function id => (p.function? id).map (·.input)
  | .workflow id _ => (p.workflow? id).map (·.input.map (·.valueType))

def Definition.bodyKind (p : Definition) : Body → Option Kind
  | .function id => (p.function? id).map (·.output.kind)
  | .workflow id _ => (p.workflow? id).map fun _ => .single

/-- Result element types of the controls other than calls. --/
def Definition.localResult (p : Definition) : Control → Option ValueType
  | .call _ => none
  | .branch judge _ => (p.judge? judge).map (·.input)
  | .waitStream element | .merge element => some (.list element)
  | .concurrency c => some (match c.output with
      | .list => .list c.element
      | .stream => c.element)

/-- Element type of a body's results. The fuel bounds nested workflow references. --/
def Definition.bodyElement (p : Definition) : Nat → Body → Option ValueType
  | 0, _ => none
  | _ + 1, .function id => (p.function? id).map (·.output.element)
  | fuel + 1, .workflow id output => do
    let placement ← (← p.workflow? id).placement? output
    match placement.control with
    | .call body => p.bodyElement fuel body
    | control => p.localResult control

/-- Enough fuel for an acyclic call graph, where each nested reference names another workflow. --/
def Definition.depth (p : Definition) : Nat := p.workflows.length + 1

/-- Element type of the results of one placement. --/
def Definition.resultType (p : Definition) : Control → Option ValueType
  | .call body => p.bodyElement p.depth body
  | control => p.localResult control

/-- What an input connection's transform returns: `some none` when the control takes no input. --/
def Definition.inputType (p : Definition) : Control → Option (Option ValueType)
  | .call body => p.bodyInput body
  | .branch judge _ => (p.judge? judge).map (some ·.input)
  | .waitStream element | .merge element => some (some element)
  | .concurrency c => some c.input

/-- Output kind of one placement from its input kind (§5.2, §8.4). --/
def Definition.outputKind (p : Definition) (control : Control) (input : Option Kind) : Option Kind :=
  match control, input with
  | .call body, none | .call body, some .single => p.bodyKind body
  | .call _, some .stream => some .stream
  | .branch .., some kind => some kind
  | .waitStream _, some .stream => some .single
  | .merge _, some .single => some .single
  | .concurrency c, none | .concurrency c, some .single =>
    some (match c.output with | .list => .single | .stream => .stream)
  | .concurrency _, some .stream => some .stream
  | _, _ => none

/-- An entry supplies one Single input; otherwise every source must agree. --/
def Workflow.combineInput (w : Workflow) (name : String) (sources : List Kind) : Option (Option Kind) :=
  if w.isEntry name then
    if sources.isEmpty then some (some .single) else none
  else match sources with
    | [] => some none
    | kind :: rest => if rest.all (· == kind) then some (some kind) else none

/-- Output kind of a placement; the fuel bounds the length of connection paths. --/
def Workflow.kind? (p : Definition) (w : Workflow) : Nat → String → Option Kind
  | 0, _ => none
  | fuel + 1, name => do
    let placement ← w.placement? name
    let sources ← (w.incoming name).mapM fun c => w.kind? p fuel c.source
    p.outputKind placement.control (← w.combineInput name sources)

/-! `kind?` derives the kind of a source once for each path to it, which a chain of Merges with two
connections from each to the next doubles at every step. Compiled code uses `kindFast` instead
(`kind?_eq_kindFast`): it keeps the kind at each fuel and name that it derives in a table, so it
derives each at most once, and only those the result depends on. -/

/-- The kinds derived so far, by fuel and name. --/
abbrev KindMemo := Std.HashMap (Nat × String) (Option Kind)

/-- The kinds of the sources of `incoming`, from `kind`, which reads and extends the table; `none` from
    the first source without a kind, as `mapM` gives. --/
def kindsOfSources (kind : String → KindMemo → Option Kind × KindMemo) :
    List Connection → KindMemo → Option (List Kind) × KindMemo
  | [], memo => (some [], memo)
  | c :: rest, memo =>
    match kind c.source memo with
    | (none, memo) => (none, memo)
    | (some first, memo) =>
      let (kinds, memo) := kindsOfSources kind rest memo
      (kinds.map (first :: ·), memo)

/-- `kind?`, reading and extending the table of the kinds derived so far. --/
def Workflow.kindMemo (p : Definition) (w : Workflow) : Nat → String → KindMemo → Option Kind × KindMemo
  | 0, _, memo => (none, memo)
  | fuel + 1, name, memo =>
    match memo[(fuel + 1, name)]? with
    | some kind => (kind, memo)
    | none =>
      let (kind, memo) : Option Kind × KindMemo := match w.placement? name with
        | none => (none, memo)
        | some placement =>
          let (sources, memo) := kindsOfSources (w.kindMemo p fuel) (w.incoming name) memo
          ((do p.outputKind placement.control (← w.combineInput name (← sources))), memo)
      (kind, memo.insert (fuel + 1, name) kind)

def Workflow.kindFast (p : Definition) (w : Workflow) (fuel : Nat) (name : String) : Option Kind :=
  (w.kindMemo p fuel name ∅).1

/-- Every kind in the table is the kind `kind?` derives. --/
def Workflow.KindMemoSound (p : Definition) (w : Workflow) (memo : KindMemo) : Prop :=
  ∀ fuel name kind, memo[(fuel, name)]? = some kind → w.kind? p fuel name = kind

theorem Workflow.KindMemoSound.insert {p : Definition} {w : Workflow} {memo : KindMemo}
    (h : w.KindMemoSound p memo) {fuel : Nat} {name : String} {kind : Option Kind}
    (hk : w.kind? p fuel name = kind) : w.KindMemoSound p (memo.insert (fuel, name) kind) := by
  intro n x k hx
  rw [Std.HashMap.getElem?_insert] at hx
  split at hx
  · rename_i heq
    simp only [beq_iff_eq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simp only [Option.some.injEq] at hx
    rw [← hx, hk]
  · exact h n x k hx

/-- If `kind` gives what `g` does and keeps `S`, `kindsOfSources kind` gives what `mapM` of `g` does. --/
theorem kindsOfSources_eq {S : KindMemo → Prop} {kind : String → KindMemo → Option Kind × KindMemo}
    {g : String → Option Kind} (hkind : ∀ x memo, S memo → (kind x memo).1 = g x ∧ S (kind x memo).2) :
    ∀ (incoming : List Connection) memo, S memo →
      (kindsOfSources kind incoming memo).1 = incoming.mapM (fun c => g c.source) ∧
        S (kindsOfSources kind incoming memo).2
  | [], memo, h => by simp [kindsOfSources, h]
  | c :: rest, memo, h => by
    obtain ⟨hfirst, hS⟩ := hkind c.source memo h
    unfold kindsOfSources
    split
    · rename_i memo' heq
      rw [heq] at hfirst hS
      simp [List.mapM_cons, ← hfirst, hS]
    · rename_i first memo' heq
      rw [heq] at hfirst hS
      obtain ⟨hrest, hS'⟩ := kindsOfSources_eq hkind rest memo' hS
      refine ⟨?_, hS'⟩
      simp only [List.mapM_cons, ← hfirst, ← hrest]
      cases (kindsOfSources kind rest memo').1 <;> rfl

theorem Workflow.kindMemo_eq (p : Definition) (w : Workflow) :
    ∀ fuel name memo, w.KindMemoSound p memo →
      (w.kindMemo p fuel name memo).1 = w.kind? p fuel name ∧ w.KindMemoSound p (w.kindMemo p fuel name memo).2
  | 0, name, memo, h => by simp [Workflow.kindMemo, Workflow.kind?, h]
  | fuel + 1, name, memo, h => by
    unfold Workflow.kindMemo
    split
    · rename_i kind hk
      exact ⟨(h _ _ _ hk).symm, h⟩
    · cases hpl : w.placement? name with
      | none =>
        have hnone : w.kind? p (fuel + 1) name = none := by rw [Workflow.kind?, hpl]; rfl
        exact ⟨hnone.symm, h.insert hnone⟩
      | some placement =>
        obtain ⟨hsources, hS⟩ := kindsOfSources_eq (S := w.KindMemoSound p) (g := w.kind? p fuel)
          (w.kindMemo_eq p fuel) (w.incoming name) memo h
        have hkind : w.kind? p (fuel + 1) name = (do
            p.outputKind placement.control
              (← w.combineInput name (← (kindsOfSources (w.kindMemo p fuel) (w.incoming name) memo).1))) := by
          rw [Workflow.kind?, hpl, hsources]; rfl
        exact ⟨hkind.symm, hS.insert hkind⟩

@[csimp] theorem Workflow.kind?_eq_kindFast : @Workflow.kind? = @Workflow.kindFast := by
  funext p w fuel name
  refine ((w.kindMemo_eq p fuel name ∅ ?_).1).symm
  intro _ _ _ h
  simp at h

def Workflow.depth (w : Workflow) : Nat := w.placements.length + 1

def Workflow.inputKind? (p : Definition) (w : Workflow) (name : String) : Option (Option Kind) := do
  let sources ← (w.incoming name).mapM fun c => w.kind? p w.depth c.source
  w.combineInput name sources

def Workflow.outputKind? (p : Definition) (w : Workflow) (name : String) : Option Kind :=
  w.kind? p w.depth name

end Suimon
