import Suimon.State
namespace Suimon
/-- Node code is opaque. Keys include the input identity, never arrival order. --/
structure Oracle where
  leaf : NodeId → List (PortName × ItemId) → List Output
  branch : NodeId → ItemId → PortName
  filter : NodeId → ItemId → Bool
  loop : NodeId → Nat → ItemId → Bool

def Oracle.Deterministic (o : Oracle) : Prop :=
  ∀ n a b, a.Perm b → o.leaf n a = o.leaf n b

/-- Canonical, injectively encoded symbolic value; payloads remain outside the model. --/
def derivedItem (tag : String) (path : Path) (node : NodeId) (items : List ItemId) : ItemId :=
  identity ([tag, identity path, node] ++ items)

def sortedItems (items : List ItemId) : List ItemId := items.mergeSort (· ≤ ·)
end Suimon
