import Suimon.Trace.Wire
import Suimon.Theorems.TraceLex
import Suimon.Theorems.TraceOpAtoms
import Suimon.Theorems.TraceGrammar
import Suimon.Theorems.TraceRecording

namespace Suimon.Trace

/-- Prefix codec laws and JSON grammar validation compose for every Event,
    including arbitrary Unicode strings and arbitrarily nested fact data. --/
theorem wireAtoms_roundtrip (e : Event) : decodeWireAtoms (encodeWireAtoms e.toWire) = some e.toWire := by
  simp only [encodeWireAtoms, decodeWireAtoms, Event.toWire,
    List.append_assoc, List.cons_append, List.nil_append, expectAtom_self,
    natCodec_lawful.roundtrip, stringCodec_lawful.roundtrip, optionalOpCodec_lawful.roundtrip,
    bind, Option.bind]
  simp [List.reverse_append, validJsonAtoms_json]

theorem decodeWire_roundtrip (e : Event) (version : e.schema_version = 2) :
    decodeWire (encodeEvent e) = some e.toWire := by
  simp only [decodeWire, encodeEvent, Text.roundtrip, bind, Option.bind, wireAtoms_roundtrip]
  simp [Event.toWire, version]

theorem parseWireEvent_roundtrip (e : Event) (version : e.schema_version = 2) :
    parseWireEvent (encodeEvent e) = .ok e.toWire := by
  simp [parseWireEvent, decodeWire_roundtrip e version]

theorem checkWireEvent_toWire (c : Cursor) (e : Event) :
    checkWireEvent c e.toWire = checkEvent c e := by
  rfl

theorem checkLine_encode (c : Cursor) (e : Event) (version : e.schema_version = 2) :
    checkLine c (encodeEvent e) = .ok (checkEvent c e) := by
  simp [checkLine, parseWireEvent_roundtrip e version, Except.map, checkWireEvent_toWire]

theorem checkMetadata_version (c next : Cursor) (e : Event) (accepted : checkMetadata c e = .ok next) :
    e.schema_version = 2 := by
  by_cases version : e.schema_version == 2
  · exact beq_iff_eq.mp version
  · simp [checkMetadata, version, bind, Except.bind] at accepted

theorem checkEvent_version (c next : Cursor) (e : Event) (accepted : checkEvent c e = .ok next) :
    e.schema_version = 2 := by
  cases metadata : checkMetadata c e with
  | error d => simp [checkEvent, metadata, bind, Except.bind] at accepted
  | ok ready => exact checkMetadata_version c ready e metadata

theorem checkTextLine_encode (c : Cursor) (e : Event) (version : e.schema_version = 2) :
    checkTextLine c (encodeEvent e) = checkEvent c e := by
  simp [checkTextLine, parseWireEvent_roundtrip e version, checkWireEvent_toWire]

/-- No bound on values, nesting, event count, operations, or transaction count. --/
theorem checkTextLines_encode (c next : Cursor) (events : List Event)
    (accepted : events.foldlM checkEvent c = .ok next) :
    (events.map encodeEvent).foldlM checkTextLine c = .ok next := by
  induction events generalizing c with
  | nil => exact accepted
  | cons e events ih =>
    cases head : checkEvent c e with
    | error d => simp [List.foldlM_cons, head, bind, Except.bind] at accepted
    | ok middle =>
      have tail : events.foldlM checkEvent middle = .ok next := by
        simpa [List.foldlM_cons, head, bind, Except.bind] using accepted
      simp only [List.map_cons, List.foldlM_cons, checkTextLine_encode c e (checkEvent_version c middle e head),
        head, bind, Except.bind]
      exact ih middle tail

theorem checkText_encode (g : Graph) (events : List Event) (s : State)
    (checked : check g events = .ok s) : checkText g (events.map encodeEvent) = .ok s := by
  cases scanned : events.foldlM checkEvent {state := .initial g, boundary := .initial g} with
  | error d => simp [check, scanned, bind, Except.bind] at checked
  | ok cursor =>
    have done : finish cursor = .ok s := by simpa [check, scanned, bind, Except.bind] using checked
    simp [checkText, checkTextLines_encode _ cursor events scanned, done, bind, Except.bind]

/-- The actual recorder, string encoder, line decoder and checker compose to
    reproduce the model state, with no codec/replay equality hypothesis. --/
theorem recordTransaction_jsonl_roundtrip (g : Graph) (ops : List Op) (txn : String) (time : Nat)
    (s : State) (events : List Event)
    (recorded : recordTransaction (.initial g) ops 1 txn time = .ok (s, events)) :
    checkText g (events.map encodeEvent) = .ok s :=
  checkText_encode g events s (recordTransaction_roundtrip g ops txn time s events recorded)

theorem recoverText_encode (g : Graph) (events : List Event) (s : State)
    (recovered : recover g events = .ok s) : recoverText g (events.map encodeEvent) = .ok s := by
  cases scanned : events.foldlM checkEvent {state := .initial g, boundary := .initial g} with
  | error d => simp [recover, scanned, bind, Except.bind] at recovered
  | ok cursor =>
    have boundary : cursor.boundary = s := by simpa [recover, scanned, bind, Except.bind, pure, Except.pure] using recovered
    simp [recoverText, checkTextLines_encode _ cursor events scanned, boundary, bind, Except.bind, pure, Except.pure]

/-- The uncommitted suffix may stop between any command and its facts. --/
theorem recoverText_torn_suffix (g : Graph) (durable torn : List Event) (boundary next : Cursor)
    (prefixAccepted : durable.foldlM checkEvent {state := .initial g, boundary := .initial g} = .ok boundary)
    (suffixAccepted : torn.foldlM checkEvent boundary = .ok next)
    (noCommit : ∀ e ∈ torn, e.type ≠ "transaction.committed") :
    recoverText g ((durable ++ torn).map encodeEvent) = .ok boundary.boundary :=
  recoverText_encode g (durable ++ torn) boundary.boundary
    (recover_torn_suffix g durable torn boundary next prefixAccepted suffixAccepted noCommit)

theorem decodeWire_roundtrip_newline (e : Event) (version : e.schema_version = 2) :
    decodeWire (encodeEvent e ++ "\n") = some e.toWire := by
  simp only [decodeWire, encodeEvent, Text.roundtrip_suffix _ "\n" (by rfl), bind, Option.bind, wireAtoms_roundtrip]
  simp [Event.toWire, version]

theorem checkTextLine_encode_newline (c : Cursor) (e : Event) (version : e.schema_version = 2) :
    checkTextLine c (encodeEvent e ++ "\n") = checkEvent c e := by
  simp [checkTextLine, parseWireEvent, decodeWire_roundtrip_newline e version, checkWireEvent_toWire]

end Suimon.Trace
