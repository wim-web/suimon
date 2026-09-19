import Suimon.Trace.OpAtoms
import Suimon.Theorems.TraceAtoms

namespace Suimon.Trace
set_option maxHeartbeats 1000000

theorem opCodec_lawful : LawfulAtomCodec opCodec := by
  refine ⟨?_, ?_, ?_⟩
  · intro op; cases op <;> simp [opCodec, encodeOpAtoms]
  · intro op; cases op <;> simp [opCodec, encodeOpAtoms]
  · intro op tail
    cases op <;> simp only [opCodec, encodeOpAtoms, List.append_assoc, List.cons_append, List.nil_append,
      decodeOpAtoms, expectAtom_self, bind, Option.bind, pure,
      stringCodec_lawful.roundtrip, natCodec_lawful.roundtrip, boolCodec_lawful.roundtrip,
      credentialsCodec_lawful.roundtrip, (arrayCodec_lawful stringCodec stringCodec_lawful).roundtrip,
      (arrayCodec_lawful inputCodec inputCodec_lawful).roundtrip,
      (arrayCodec_lawful outputCodec outputCodec_lawful).roundtrip]

theorem optionalOpCodec_lawful : LawfulAtomCodec optionalOpCodec := by
  refine ⟨?_, ?_, ?_⟩
  · intro op; cases op with
    | none => simp [optionalOpCodec]
    | some op => exact opCodec_lawful.nonempty op
  · intro op; cases op with
    | none => simp [optionalOpCodec]
    | some op => exact opCodec_lawful.notEnd op
  · intro op tail; cases op with
    | none => rfl
    | some op =>
      cases op <;> simp only [optionalOpCodec, opCodec, encodeOpAtoms, List.append_assoc, List.cons_append, List.nil_append,
        decodeOpAtoms, expectAtom_self, bind, Option.bind, pure,
        stringCodec_lawful.roundtrip, natCodec_lawful.roundtrip, boolCodec_lawful.roundtrip,
        credentialsCodec_lawful.roundtrip, (arrayCodec_lawful stringCodec stringCodec_lawful).roundtrip,
        (arrayCodec_lawful inputCodec inputCodec_lawful).roundtrip,
        (arrayCodec_lawful outputCodec outputCodec_lawful).roundtrip]

end Suimon.Trace
