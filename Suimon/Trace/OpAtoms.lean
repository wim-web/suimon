import Suimon.Trace.AtomCodec

namespace Suimon.Trace

def encodeOpAtoms : Op → List JsonAtom
  | .start inputs => [.objectStart, .field "start", .objectStart] ++
      [.field "inputs"] ++ (arrayCodec inputCodec).encode inputs ++ [.objectEnd, .objectEnd]
  | .activate path node => [.objectStart, .field "activate", .objectStart] ++
      [.field "path"] ++ (arrayCodec stringCodec).encode path ++
      [.field "node"] ++ stringCodec.encode node ++ [.objectEnd, .objectEnd]
  | .spawn path node item => [.objectStart, .field "spawn", .objectStart] ++
      [.field "path"] ++ (arrayCodec stringCodec).encode path ++
      [.field "node"] ++ stringCodec.encode node ++
      [.field "item"] ++ stringCodec.encode item ++ [.objectEnd, .objectEnd]
  | .claim auth worker => [.objectStart, .field "claim", .objectStart] ++
      [.field "auth"] ++ credentialsCodec.encode auth ++
      [.field "worker"] ++ stringCodec.encode worker ++ [.objectEnd, .objectEnd]
  | .renew auth => [.objectStart, .field "renew", .objectStart] ++
      [.field "auth"] ++ credentialsCodec.encode auth ++ [.objectEnd, .objectEnd]
  | .expireLease inst now => [.objectStart, .field "expireLease", .objectStart] ++
      [.field "inst"] ++ stringCodec.encode inst ++
      [.field "now"] ++ natCodec.encode now ++ [.objectEnd, .objectEnd]
  | .promoteRetry inst now => [.objectStart, .field "promoteRetry", .objectStart] ++
      [.field "inst"] ++ stringCodec.encode inst ++
      [.field "now"] ++ natCodec.encode now ++ [.objectEnd, .objectEnd]
  | .emit auth port item => [.objectStart, .field "emit", .objectStart] ++
      [.field "auth"] ++ credentialsCodec.encode auth ++
      [.field "port"] ++ stringCodec.encode port ++
      [.field "item"] ++ stringCodec.encode item ++ [.objectEnd, .objectEnd]
  | .complete auth outputs => [.objectStart, .field "complete", .objectStart] ++
      [.field "auth"] ++ credentialsCodec.encode auth ++
      [.field "outputs"] ++ (arrayCodec outputCodec).encode outputs ++ [.objectEnd, .objectEnd]
  | .fail auth code retryable => [.objectStart, .field "fail", .objectStart] ++
      [.field "auth"] ++ credentialsCodec.encode auth ++
      [.field "code"] ++ stringCodec.encode code ++
      [.field "retryable"] ++ boolCodec.encode retryable ++ [.objectEnd, .objectEnd]
  | .fireWaitAll path node => [.objectStart, .field "fireWaitAll", .objectStart] ++
      [.field "path"] ++ (arrayCodec stringCodec).encode path ++
      [.field "node"] ++ stringCodec.encode node ++ [.objectEnd, .objectEnd]
  | .fireBranch path node arm => [.objectStart, .field "fireBranch", .objectStart] ++
      [.field "path"] ++ (arrayCodec stringCodec).encode path ++
      [.field "node"] ++ stringCodec.encode node ++
      [.field "arm"] ++ stringCodec.encode arm ++ [.objectEnd, .objectEnd]
  | .fireCoalesce path node edge item => [.objectStart, .field "fireCoalesce", .objectStart] ++
      [.field "path"] ++ (arrayCodec stringCodec).encode path ++
      [.field "node"] ++ stringCodec.encode node ++
      [.field "edge"] ++ stringCodec.encode edge ++
      [.field "item"] ++ stringCodec.encode item ++ [.objectEnd, .objectEnd]
  | .fireCollect path node => [.objectStart, .field "fireCollect", .objectStart] ++
      [.field "path"] ++ (arrayCodec stringCodec).encode path ++
      [.field "node"] ++ stringCodec.encode node ++ [.objectEnd, .objectEnd]
  | .fireFilter path node item keep => [.objectStart, .field "fireFilter", .objectStart] ++
      [.field "path"] ++ (arrayCodec stringCodec).encode path ++
      [.field "node"] ++ stringCodec.encode node ++
      [.field "item"] ++ stringCodec.encode item ++
      [.field "keep"] ++ boolCodec.encode keep ++ [.objectEnd, .objectEnd]
  | .fireMerge path node edge item => [.objectStart, .field "fireMerge", .objectStart] ++
      [.field "path"] ++ (arrayCodec stringCodec).encode path ++
      [.field "node"] ++ stringCodec.encode node ++
      [.field "edge"] ++ stringCodec.encode edge ++
      [.field "item"] ++ stringCodec.encode item ++ [.objectEnd, .objectEnd]
  | .propagateEos path node => [.objectStart, .field "propagateEos", .objectStart] ++
      [.field "path"] ++ (arrayCodec stringCodec).encode path ++
      [.field "node"] ++ stringCodec.encode node ++ [.objectEnd, .objectEnd]
  | .finishSubworkflow inst => [.objectStart, .field "finishSubworkflow", .objectStart] ++
      [.field "inst"] ++ stringCodec.encode inst ++ [.objectEnd, .objectEnd]
  | .loopIterate inst done => [.objectStart, .field "loopIterate", .objectStart] ++
      [.field "inst"] ++ stringCodec.encode inst ++
      [.field "done"] ++ boolCodec.encode done ++ [.objectEnd, .objectEnd]
  | .skip path node => [.objectStart, .field "skip", .objectStart] ++
      [.field "path"] ++ (arrayCodec stringCodec).encode path ++
      [.field "node"] ++ stringCodec.encode node ++ [.objectEnd, .objectEnd]
  | .idle => [.string "idle"]
  | .cancel => [.string "cancel"]
  | .manualRetry inst => [.objectStart, .field "manualRetry", .objectStart] ++
      [.field "inst"] ++ stringCodec.encode inst ++ [.objectEnd, .objectEnd]

def decodeOpAtoms : AtomReader Op
  | .objectStart :: .field "start" :: .objectStart :: atoms => do
    let atoms ← expectAtom (.field "inputs") atoms
    let (inputs, atoms) ← (arrayCodec inputCodec).decode atoms
    let atoms ← expectAtom .objectEnd atoms
    let atoms ← expectAtom .objectEnd atoms
    return (.start inputs, atoms)
  | .objectStart :: .field "activate" :: .objectStart :: atoms => do
    let atoms ← expectAtom (.field "path") atoms
    let (path, atoms) ← (arrayCodec stringCodec).decode atoms
    let atoms ← expectAtom (.field "node") atoms
    let (node, atoms) ← stringCodec.decode atoms
    let atoms ← expectAtom .objectEnd atoms
    let atoms ← expectAtom .objectEnd atoms
    return (.activate path node, atoms)
  | .objectStart :: .field "spawn" :: .objectStart :: atoms => do
    let atoms ← expectAtom (.field "path") atoms
    let (path, atoms) ← (arrayCodec stringCodec).decode atoms
    let atoms ← expectAtom (.field "node") atoms
    let (node, atoms) ← stringCodec.decode atoms
    let atoms ← expectAtom (.field "item") atoms
    let (item, atoms) ← stringCodec.decode atoms
    let atoms ← expectAtom .objectEnd atoms
    let atoms ← expectAtom .objectEnd atoms
    return (.spawn path node item, atoms)
  | .objectStart :: .field "claim" :: .objectStart :: atoms => do
    let atoms ← expectAtom (.field "auth") atoms
    let (auth, atoms) ← credentialsCodec.decode atoms
    let atoms ← expectAtom (.field "worker") atoms
    let (worker, atoms) ← stringCodec.decode atoms
    let atoms ← expectAtom .objectEnd atoms
    let atoms ← expectAtom .objectEnd atoms
    return (.claim auth worker, atoms)
  | .objectStart :: .field "renew" :: .objectStart :: atoms => do
    let atoms ← expectAtom (.field "auth") atoms
    let (auth, atoms) ← credentialsCodec.decode atoms
    let atoms ← expectAtom .objectEnd atoms
    let atoms ← expectAtom .objectEnd atoms
    return (.renew auth, atoms)
  | .objectStart :: .field "expireLease" :: .objectStart :: atoms => do
    let atoms ← expectAtom (.field "inst") atoms
    let (inst, atoms) ← stringCodec.decode atoms
    let atoms ← expectAtom (.field "now") atoms
    let (now, atoms) ← natCodec.decode atoms
    let atoms ← expectAtom .objectEnd atoms
    let atoms ← expectAtom .objectEnd atoms
    return (.expireLease inst now, atoms)
  | .objectStart :: .field "promoteRetry" :: .objectStart :: atoms => do
    let atoms ← expectAtom (.field "inst") atoms
    let (inst, atoms) ← stringCodec.decode atoms
    let atoms ← expectAtom (.field "now") atoms
    let (now, atoms) ← natCodec.decode atoms
    let atoms ← expectAtom .objectEnd atoms
    let atoms ← expectAtom .objectEnd atoms
    return (.promoteRetry inst now, atoms)
  | .objectStart :: .field "emit" :: .objectStart :: atoms => do
    let atoms ← expectAtom (.field "auth") atoms
    let (auth, atoms) ← credentialsCodec.decode atoms
    let atoms ← expectAtom (.field "port") atoms
    let (port, atoms) ← stringCodec.decode atoms
    let atoms ← expectAtom (.field "item") atoms
    let (item, atoms) ← stringCodec.decode atoms
    let atoms ← expectAtom .objectEnd atoms
    let atoms ← expectAtom .objectEnd atoms
    return (.emit auth port item, atoms)
  | .objectStart :: .field "complete" :: .objectStart :: atoms => do
    let atoms ← expectAtom (.field "auth") atoms
    let (auth, atoms) ← credentialsCodec.decode atoms
    let atoms ← expectAtom (.field "outputs") atoms
    let (outputs, atoms) ← (arrayCodec outputCodec).decode atoms
    let atoms ← expectAtom .objectEnd atoms
    let atoms ← expectAtom .objectEnd atoms
    return (.complete auth outputs, atoms)
  | .objectStart :: .field "fail" :: .objectStart :: atoms => do
    let atoms ← expectAtom (.field "auth") atoms
    let (auth, atoms) ← credentialsCodec.decode atoms
    let atoms ← expectAtom (.field "code") atoms
    let (code, atoms) ← stringCodec.decode atoms
    let atoms ← expectAtom (.field "retryable") atoms
    let (retryable, atoms) ← boolCodec.decode atoms
    let atoms ← expectAtom .objectEnd atoms
    let atoms ← expectAtom .objectEnd atoms
    return (.fail auth code retryable, atoms)
  | .objectStart :: .field "fireWaitAll" :: .objectStart :: atoms => do
    let atoms ← expectAtom (.field "path") atoms
    let (path, atoms) ← (arrayCodec stringCodec).decode atoms
    let atoms ← expectAtom (.field "node") atoms
    let (node, atoms) ← stringCodec.decode atoms
    let atoms ← expectAtom .objectEnd atoms
    let atoms ← expectAtom .objectEnd atoms
    return (.fireWaitAll path node, atoms)
  | .objectStart :: .field "fireBranch" :: .objectStart :: atoms => do
    let atoms ← expectAtom (.field "path") atoms
    let (path, atoms) ← (arrayCodec stringCodec).decode atoms
    let atoms ← expectAtom (.field "node") atoms
    let (node, atoms) ← stringCodec.decode atoms
    let atoms ← expectAtom (.field "arm") atoms
    let (arm, atoms) ← stringCodec.decode atoms
    let atoms ← expectAtom .objectEnd atoms
    let atoms ← expectAtom .objectEnd atoms
    return (.fireBranch path node arm, atoms)
  | .objectStart :: .field "fireCoalesce" :: .objectStart :: atoms => do
    let atoms ← expectAtom (.field "path") atoms
    let (path, atoms) ← (arrayCodec stringCodec).decode atoms
    let atoms ← expectAtom (.field "node") atoms
    let (node, atoms) ← stringCodec.decode atoms
    let atoms ← expectAtom (.field "edge") atoms
    let (edge, atoms) ← stringCodec.decode atoms
    let atoms ← expectAtom (.field "item") atoms
    let (item, atoms) ← stringCodec.decode atoms
    let atoms ← expectAtom .objectEnd atoms
    let atoms ← expectAtom .objectEnd atoms
    return (.fireCoalesce path node edge item, atoms)
  | .objectStart :: .field "fireCollect" :: .objectStart :: atoms => do
    let atoms ← expectAtom (.field "path") atoms
    let (path, atoms) ← (arrayCodec stringCodec).decode atoms
    let atoms ← expectAtom (.field "node") atoms
    let (node, atoms) ← stringCodec.decode atoms
    let atoms ← expectAtom .objectEnd atoms
    let atoms ← expectAtom .objectEnd atoms
    return (.fireCollect path node, atoms)
  | .objectStart :: .field "fireFilter" :: .objectStart :: atoms => do
    let atoms ← expectAtom (.field "path") atoms
    let (path, atoms) ← (arrayCodec stringCodec).decode atoms
    let atoms ← expectAtom (.field "node") atoms
    let (node, atoms) ← stringCodec.decode atoms
    let atoms ← expectAtom (.field "item") atoms
    let (item, atoms) ← stringCodec.decode atoms
    let atoms ← expectAtom (.field "keep") atoms
    let (keep, atoms) ← boolCodec.decode atoms
    let atoms ← expectAtom .objectEnd atoms
    let atoms ← expectAtom .objectEnd atoms
    return (.fireFilter path node item keep, atoms)
  | .objectStart :: .field "fireMerge" :: .objectStart :: atoms => do
    let atoms ← expectAtom (.field "path") atoms
    let (path, atoms) ← (arrayCodec stringCodec).decode atoms
    let atoms ← expectAtom (.field "node") atoms
    let (node, atoms) ← stringCodec.decode atoms
    let atoms ← expectAtom (.field "edge") atoms
    let (edge, atoms) ← stringCodec.decode atoms
    let atoms ← expectAtom (.field "item") atoms
    let (item, atoms) ← stringCodec.decode atoms
    let atoms ← expectAtom .objectEnd atoms
    let atoms ← expectAtom .objectEnd atoms
    return (.fireMerge path node edge item, atoms)
  | .objectStart :: .field "propagateEos" :: .objectStart :: atoms => do
    let atoms ← expectAtom (.field "path") atoms
    let (path, atoms) ← (arrayCodec stringCodec).decode atoms
    let atoms ← expectAtom (.field "node") atoms
    let (node, atoms) ← stringCodec.decode atoms
    let atoms ← expectAtom .objectEnd atoms
    let atoms ← expectAtom .objectEnd atoms
    return (.propagateEos path node, atoms)
  | .objectStart :: .field "finishSubworkflow" :: .objectStart :: atoms => do
    let atoms ← expectAtom (.field "inst") atoms
    let (inst, atoms) ← stringCodec.decode atoms
    let atoms ← expectAtom .objectEnd atoms
    let atoms ← expectAtom .objectEnd atoms
    return (.finishSubworkflow inst, atoms)
  | .objectStart :: .field "loopIterate" :: .objectStart :: atoms => do
    let atoms ← expectAtom (.field "inst") atoms
    let (inst, atoms) ← stringCodec.decode atoms
    let atoms ← expectAtom (.field "done") atoms
    let (done, atoms) ← boolCodec.decode atoms
    let atoms ← expectAtom .objectEnd atoms
    let atoms ← expectAtom .objectEnd atoms
    return (.loopIterate inst done, atoms)
  | .objectStart :: .field "skip" :: .objectStart :: atoms => do
    let atoms ← expectAtom (.field "path") atoms
    let (path, atoms) ← (arrayCodec stringCodec).decode atoms
    let atoms ← expectAtom (.field "node") atoms
    let (node, atoms) ← stringCodec.decode atoms
    let atoms ← expectAtom .objectEnd atoms
    let atoms ← expectAtom .objectEnd atoms
    return (.skip path node, atoms)
  | .string "idle" :: rest => some (.idle, rest)
  | .string "cancel" :: rest => some (.cancel, rest)
  | .objectStart :: .field "manualRetry" :: .objectStart :: atoms => do
    let atoms ← expectAtom (.field "inst") atoms
    let (inst, atoms) ← stringCodec.decode atoms
    let atoms ← expectAtom .objectEnd atoms
    let atoms ← expectAtom .objectEnd atoms
    return (.manualRetry inst, atoms)
  | _ => none

def opCodec : AtomCodec Op := ⟨encodeOpAtoms, decodeOpAtoms⟩

def optionalOpCodec : AtomCodec (Option Op) where
  encode
    | none => [.null]
    | some op => opCodec.encode op
  decode
    | .null :: rest => some (none, rest)
    | atoms => do
      let (op, rest) ← opCodec.decode atoms
      return (some op, rest)

end Suimon.Trace
