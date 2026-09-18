import Suimon.Trace.Check

namespace Suimon

/-- A logical invocation has a stable path across schedules and retry attempts.
    Scoping permits occurrence IDs to include that path, never a worker/attempt. --/
abbrev ScopedOracle := Path → Oracle

def ScopedOracle.Deterministic (oracle : ScopedOracle) : Prop :=
  ∀ path, (oracle path).Deterministic

def outputItems (outputs : List Output) (port : PortName) : List ItemId :=
  ((outputs.find? (·.port == port)).map (·.items)).getD []

/-- Oracle conformance constrains accepted commands, not the scheduler. Besides
    allowing only prescribed yields, completion requires their full multiset on
    every outgoing stream. Omitting this clause would allow successful truncation. --/
def oracleConforms (oracle : ScopedOracle) (s : State) (op : Op) : Bool :=
  if absorbed s op then true else match op with
  | .emit auth port item => (s.instance? auth.instance).any fun i =>
      (outputItems ((oracle i.path).leaf i.node i.inputs) port).contains item
  | .complete auth outputs => (s.instance? auth.instance).any fun i =>
      (s.node? i.path i.node).any fun n =>
        let expected := (oracle i.path).leaf i.node i.inputs
        let plain := expected.filter fun out => n.outputs.any (fun p => p.name == out.port && p.kind == .plain)
        decide (outputs.Perm plain) &&
          (n.outputs.filter (·.kind == .stream)).all fun p =>
            (s.outgoing i.path i.node p.name).all fun c =>
              decide (c.items.Perm (outputItems expected p.name))
  | .fireBranch path node arm =>
      (((s.incoming path node).head?).bind (·.pendingItems.head?)).any fun item =>
        arm == (oracle path).branch node item
  | .fireFilter path node item keep => keep == (oracle path).filter node item
  | .loopIterate id done => (s.instance? id).any fun i =>
      ((currentFrame s i).toOption.bind fun f => (frameOutputItems s f).toOption).any fun items =>
        items.head?.any (fun item => done == (oracle i.path).loop i.node i.iteration item)
  | _ => true

/-- An accepted execution with an explicit, state-local constraint on each Op. --/
inductive ConformingSteps (allows : State → Op → Prop) : State → List Op → State → Prop
  | nil (s) : ConformingSteps allows s [] s
  | cons {s middle last op ops} (allowed : allows s op) (step : Suimon.step s op = .ok middle)
      (tail : ConformingSteps allows middle ops last) : ConformingSteps allows s (op :: ops) last

/-- Include logical channel IDs so a missing empty channel cannot go unnoticed.
    Sorting retains multiplicity and includes all child-frame boundaries. --/
def channelBags (s : State) : List (String × List ItemId) :=
  (s.channels.map fun c => (c.id, sortedItems c.items)).mergeSort (fun a b => a.1 ≤ b.1)

def succeededDrained (s : State) : Bool :=
  s.status == .succeeded && s.channels.all (fun c =>
    c.closed && ((c.path.isEmpty && c.exit) || c.pendingItems.isEmpty)) &&
  s.frames.all (fun f => f.path.isEmpty || f.closed)

/-- The unrestricted T9 proof target. This is a proposition, not a completed
    theorem: no candidate enumeration, bound or equality of results is assumed. --/
def ScheduleDeterminism : Prop :=
  ∀ (graph : Graph) (inputs : List Input) (oracle : ScopedOracle),
    graph.WellFormed → oracle.Deterministic →
    ∀ (leftOps rightOps : List Op) (left right : State),
      ConformingSteps (fun s op => oracleConforms oracle s op = true)
        (.initial graph) (.start inputs :: leftOps) left →
      ConformingSteps (fun s op => oracleConforms oracle s op = true)
        (.initial graph) (.start inputs :: rightOps) right →
      succeededDrained left = true → succeededDrained right = true →
      channelBags left = channelBags right

end Suimon
