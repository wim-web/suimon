import Lean

namespace Suimon

/-- Values are opaque to the engine. A type is compared only by its names and structure. --/
inductive ValueType where
  | named (name : String)
  | list (element : ValueType)
  deriving DecidableEq, Repr, Inhabited

def ValueType.render : ValueType → String
  | .named name => name
  | .list element => s!"List<{element.render}>"

instance : ToString ValueType := ⟨ValueType.render⟩

/-- The output contract of one call: `single` returns one value, `stream` yields values. --/
inductive Contract where
  | single (value : ValueType)
  | stream (element : ValueType)
  deriving DecidableEq, Repr

inductive Kind where
  | single
  | stream
  deriving DecidableEq, Repr

inductive Policy where
  | stop
  | «continue»
  deriving DecidableEq, Repr

/-- Durations are runtime configuration; the model only uses whether a timeout exists. --/
structure Timeout where
  callMs : Option Nat := none
  elementMs : Option Nat := none
  deriving DecidableEq, Repr

def Contract.kind : Contract → Kind
  | .single _ => .single
  | .stream _ => .stream

def Contract.element : Contract → ValueType
  | .single value | .stream value => value

def Timeout.isEmpty (t : Timeout) : Bool := t.callMs.isNone && t.elementMs.isNone

end Suimon
