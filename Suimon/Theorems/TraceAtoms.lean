import Suimon.Trace.AtomCodec

namespace Suimon.Trace

@[simp] theorem expectAtom_self (atom : JsonAtom) (rest : List JsonAtom) : expectAtom atom (atom :: rest) = some rest := by
  simp [expectAtom]

theorem stringCodec_lawful : LawfulAtomCodec stringCodec := ⟨by intro a; simp [stringCodec], by intro a; simp [stringCodec], by intros; rfl⟩
theorem natCodec_lawful : LawfulAtomCodec natCodec := ⟨by intro a; simp [natCodec], by intro a; simp [natCodec], by intros; rfl⟩
theorem boolCodec_lawful : LawfulAtomCodec boolCodec := ⟨by intro a; simp [boolCodec], by intro a; simp [boolCodec], by intros; rfl⟩

theorem readMany_roundtrip (codec : AtomCodec α) (lawful : LawfulAtomCodec codec)
    (values : List α) (tail : List JsonAtom) (fuel : Nat)
    (enough : (values.flatMap codec.encode).length + 1 ≤ fuel) :
    readMany codec.decode fuel (values.flatMap codec.encode ++ .arrayEnd :: tail) = some (values, tail) := by
  induction values generalizing fuel with
  | nil =>
    cases fuel with
    | zero => simp at enough
    | succ fuel => simp [readMany]
  | cons value values ih =>
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      have firstLength : 0 < (codec.encode value).length := List.length_pos_iff.mpr (lawful.nonempty value)
      have restEnough : (values.flatMap codec.encode).length + 1 ≤ fuel := by
        simp only [List.flatMap_cons, List.length_append] at enough
        omega
      have head : ((codec.encode value ++ values.flatMap codec.encode ++ .arrayEnd :: tail).head? == some .arrayEnd) = false := by
        cases encoded : codec.encode value with
        | nil => exact False.elim (lawful.nonempty value encoded)
        | cons first rest =>
          have notEnd := lawful.notEnd value
          rw [encoded] at notEnd
          simpa using notEnd
      simp only [List.append_assoc] at head
      simp only [List.flatMap_cons, readMany, List.append_assoc, head, Bool.false_eq_true, ↓reduceIte]
      rw [lawful.roundtrip]
      simp only [bind, Option.bind]
      rw [ih fuel restEnough]
      rfl

theorem arrayCodec_lawful (codec : AtomCodec α) (lawful : LawfulAtomCodec codec) : LawfulAtomCodec (arrayCodec codec) := by
  refine ⟨by intro a; simp [arrayCodec], by intro a; simp [arrayCodec], ?_⟩
  intro values tail
  simp only [arrayCodec, List.cons_append, List.append_assoc, expectAtom_self, bind, Option.bind]
  apply readMany_roundtrip codec lawful
  simp only [List.length_append, List.length_cons]
  omega

theorem refCodec_lawful : LawfulAtomCodec refCodec := by
  refine ⟨by intro a; simp [refCodec], by intro a; simp [refCodec], ?_⟩
  intro ref tail
  cases ref
  rfl

theorem inputCodec_lawful : LawfulAtomCodec inputCodec := by
  refine ⟨by intro a; simp [inputCodec], by intro a; simp [inputCodec], ?_⟩
  intro input tail
  simp only [inputCodec, List.append_assoc, List.cons_append, List.nil_append, expectAtom_self,
    bind, Option.bind, refCodec_lawful.roundtrip, (arrayCodec_lawful stringCodec stringCodec_lawful).roundtrip]
  cases input; rfl

theorem outputCodec_lawful : LawfulAtomCodec outputCodec := by
  refine ⟨by intro a; simp [outputCodec], by intro a; simp [outputCodec], ?_⟩
  intro output tail
  simp only [outputCodec, List.append_assoc, List.cons_append, List.nil_append, expectAtom_self,
    bind, Option.bind, stringCodec_lawful.roundtrip, (arrayCodec_lawful stringCodec stringCodec_lawful).roundtrip]
  cases output; rfl

theorem credentialsCodec_lawful : LawfulAtomCodec credentialsCodec := by
  refine ⟨by intro a; simp [credentialsCodec], by intro a; simp [credentialsCodec], ?_⟩
  intro auth tail
  cases auth; rfl

end Suimon.Trace
