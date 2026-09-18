import Suimon.Oracle
namespace Suimon

/-- Empty plain channels model a branch that was not selected. --/
def channelOK (c : Channel) : Bool :=
  c.consumed ≤ c.placed.length &&
  (c.placed.takeWhile (· != .eos)).length + (if c.closed then 1 else 0) == c.placed.length &&
  unique c.items && (c.kind != .plain || c.items.length ≤ 1)

def instanceKey (i : Instance) := (i.node, i.trigger, i.path)

def leaseOK (s : State) : Bool := s.instances.all fun i =>
  if i.status == .running then
    i.lease.any fun l => s.attempts.any fun a =>
      a.id == l.attempt && a.instance == i.id && a.token == l.token && a.status == .running
  else i.lease.isNone

def attemptOK (s : State) : Bool :=
  unique (s.attempts.map (·.id)) && unique (s.attempts.map (·.token)) &&
  s.attempts.all (fun a => (s.instance? a.instance).isSome) &&
  s.instances.all (fun i => (s.attempts.filter (fun a => a.instance == i.id && a.status == .running)).length ≤ 1) &&
  s.attempts.all (fun a => a.status != .running ||
    (s.instance? a.instance).any (fun i => i.status == .running && i.lease.any (·.attempt == a.id)))

def accountingOK (s : State) : Bool :=
  unique (s.consumed.map fun c => (c.channel, c.index)) &&
  s.channels.all (fun c => (c.placed.take c.consumed).zipIdx.all fun (t, idx) =>
    match t with
    | .eos => true
    | .item id => s.consumed.any (fun a => a.channel == c.id && a.index == idx && a.item == id)) &&
  s.consumed.all (fun a => (s.instance? a.byInstance).isSome && s.channels.any fun c => c.id == a.channel &&
    a.index < c.consumed && c.placed[a.index]? == some (.item a.item))

def loopBoundsOK (s : State) : Bool := s.instances.all fun i =>
  match s.node? i.path i.node with
  | some n => match n.kind with
    | .loop _ m => i.iteration ≤ m + i.extraIterations &&
      (s.frames.filter (fun f => f.owner == some i.id)).length == i.iteration
    | _ => true
  | none => false

/-- I1, I2, I3 and the accounting/attempt/loop refinements checked at commit. --/
def invariants (s : State) : Bool :=
  s.channels.all channelOK && unique (s.channels.map (·.id)) &&
  unique (s.instances.map (·.id)) && unique (s.instances.map instanceKey) &&
  leaseOK s && attemptOK s && accountingOK s && loopBoundsOK s

def Invariants (s : State) : Prop := invariants s = true

/-- I4 also permits no change, and waiting containers settling or being cancelled. --/
def allowedStatus (a b : InstanceStatus) : Bool :=
  a == b || match a, b with
  | .waitingInputs, .succeeded | .waitingInputs, .failed | .waitingInputs, .cancelled
  | .ready, .running | .ready, .cancelled
  | .running, .succeeded | .running, .failed | .running, .retryWait | .running, .cancelled
  | .retryWait, .ready | .retryWait, .cancelled
  | .failed, .retryWait | .failed, .waitingInputs | .failed, .cancelled => true
  | _, _ => false

def historyOK (a b : State) : Bool :=
  a.now ≤ b.now &&
  a.instances.all (fun i => (b.instance? i.id).any (fun j =>
    instanceKey i == instanceKey j && allowedStatus i.status j.status && i.attemptCount ≤ j.attemptCount)) &&
  a.channels.all (fun c => b.channels.any (fun d => c.id == d.id &&
    c.placed.isPrefixOf d.placed && c.consumed ≤ d.consumed))
end Suimon
