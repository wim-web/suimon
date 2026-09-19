import Suimon.Theorems.TraceRecording
import Std.Data.TreeMap.Raw.Lemmas
import Std.Data.TreeMap.Raw.WF

namespace Suimon.Trace
open Lean

@[simp] theorem json_nat_roundtrip (n : Nat) : fromJson? (toJson n) = Except.ok n := rfl
@[simp] theorem json_string_roundtrip (s : String) : fromJson? (toJson s) = Except.ok s := rfl
@[simp] theorem json_bool_roundtrip (b : Bool) : fromJson? (toJson b) = Except.ok b := rfl

@[simp] theorem json_portRef_roundtrip (p : PortRef) : fromJson? (toJson p) = Except.ok p := by cases p; rfl
@[simp] theorem json_credentials_roundtrip (c : Credentials) : fromJson? (toJson c) = Except.ok c := by cases c; rfl

theorem json_list_roundtrip {α : Type} [ToJson α] [FromJson α]
    (elements : ∀ x : α, fromJson? (toJson x) = Except.ok x) (xs : List α) :
    fromJson? (toJson xs) = Except.ok xs := by
  change Except.map Array.toList (Array.mapM fromJson? (Array.map toJson xs.toArray)) = .ok xs
  rw [Array.mapM_map]
  have funcs : (fromJson? ∘ toJson : α → Except String α) = fun x => pure x := funext elements
  rw [funcs, Array.mapM_pure]
  simp [pure, Except.pure, Except.map]

@[simp] theorem json_path_roundtrip (p : Path) : fromJson? (toJson p) = Except.ok p :=
  json_list_roundtrip json_string_roundtrip p

@[simp] theorem json_input_roundtrip (input : Input) : fromJson? (toJson input) = Except.ok input := by
  cases input with
  | mk entry items =>
    change (do
      let ref ← Except.mapError (fun message => toString `Suimon.Input ++ "." ++ toString `entry ++ ": " ++ message) (fromJson? (toJson entry) : Except String PortRef)
      let ids ← Except.mapError (fun message => toString `Suimon.Input ++ "." ++ toString `items ++ ": " ++ message) (fromJson? (toJson items) : Except String (List ItemId))
      pure (Input.mk ref ids)) = .ok (Input.mk entry items)
    rw [json_portRef_roundtrip, json_list_roundtrip json_string_roundtrip]
    rfl

@[simp] theorem json_output_roundtrip (output : Output) : fromJson? (toJson output) = Except.ok output := by
  cases output with
  | mk port items =>
    change (do
      let name ← Except.mapError (fun message => toString `Suimon.Output ++ "." ++ toString `port ++ ": " ++ message) (fromJson? (toJson port) : Except String PortName)
      let ids ← Except.mapError (fun message => toString `Suimon.Output ++ "." ++ toString `items ++ ": " ++ message) (fromJson? (toJson items) : Except String (List ItemId))
      pure (Output.mk name ids)) = .ok (Output.mk port items)
    rw [json_string_roundtrip, json_list_roundtrip json_string_roundtrip]
    rfl


@[simp] theorem json_tag_singleton (tag : String) (value : Json) : (Json.mkObj [(tag, value)]).getTag? = some tag := by
  simp [Json.mkObj, Json.getTag?]
  rw [Std.TreeMap.Raw.size_insert Std.TreeMap.Raw.WF.emptyc,
    Std.TreeMap.Raw.minKey?_insert_of_isEmpty Std.TreeMap.Raw.WF.emptyc (by simp)]
  simp
  rfl

@[simp] theorem json_op_roundtrip (op : Op) : fromJson? (toJson op) = Except.ok op := by
  cases op with
  | start inputs =>
    have fields : (toJson (Op.start inputs)).parseCtorFields "start" 1 (some #[`inputs]) = .ok #[toJson inputs] := by
      simp only [ToJson.toJson, instToJsonOp.toJson]
      simp [Json.parseCtorFields]
      rfl
    simp only [FromJson.fromJson?, instFromJsonOp.fromJson, ToJson.toJson, instToJsonOp.toJson, json_tag_singleton]
    simp only [ToJson.toJson, instToJsonOp.toJson] at fields
    rw [fields]
    change (do
      let v0 ← (fromJson? (toJson inputs) : Except String (List Input))
      pure (Op.start v0)) = .ok (Op.start inputs)
    simp only [json_list_roundtrip json_input_roundtrip, json_list_roundtrip json_output_roundtrip,
      json_path_roundtrip, json_credentials_roundtrip, json_string_roundtrip, json_nat_roundtrip, json_bool_roundtrip,
      bind, Except.bind, pure, Except.pure]
  | activate path node =>
    have fields : (toJson (Op.activate path node)).parseCtorFields "activate" 2 (some #[`path, `node]) = .ok #[toJson path, toJson node] := by
      simp only [ToJson.toJson, instToJsonOp.toJson]
      simp [Json.parseCtorFields]
      rfl
    simp only [FromJson.fromJson?, instFromJsonOp.fromJson, ToJson.toJson, instToJsonOp.toJson, json_tag_singleton]
    simp only [ToJson.toJson, instToJsonOp.toJson] at fields
    rw [fields]
    change (do
      let v0 ← (fromJson? (toJson path) : Except String (Path))
      let v1 ← (fromJson? (toJson node) : Except String (NodeId))
      pure (Op.activate v0 v1)) = .ok (Op.activate path node)
    simp only [json_list_roundtrip json_input_roundtrip, json_list_roundtrip json_output_roundtrip,
      json_path_roundtrip, json_credentials_roundtrip, json_string_roundtrip, json_nat_roundtrip, json_bool_roundtrip,
      bind, Except.bind, pure, Except.pure]
  | spawn path node item =>
    have fields : (toJson (Op.spawn path node item)).parseCtorFields "spawn" 3 (some #[`path, `node, `item]) = .ok #[toJson path, toJson node, toJson item] := by
      simp only [ToJson.toJson, instToJsonOp.toJson]
      simp [Json.parseCtorFields]
      rfl
    simp only [FromJson.fromJson?, instFromJsonOp.fromJson, ToJson.toJson, instToJsonOp.toJson, json_tag_singleton]
    simp only [ToJson.toJson, instToJsonOp.toJson] at fields
    rw [fields]
    change (do
      let v0 ← (fromJson? (toJson path) : Except String (Path))
      let v1 ← (fromJson? (toJson node) : Except String (NodeId))
      let v2 ← (fromJson? (toJson item) : Except String (ItemId))
      pure (Op.spawn v0 v1 v2)) = .ok (Op.spawn path node item)
    simp only [json_list_roundtrip json_input_roundtrip, json_list_roundtrip json_output_roundtrip,
      json_path_roundtrip, json_credentials_roundtrip, json_string_roundtrip, json_nat_roundtrip, json_bool_roundtrip,
      bind, Except.bind, pure, Except.pure]
  | claim auth worker =>
    have fields : (toJson (Op.claim auth worker)).parseCtorFields "claim" 2 (some #[`auth, `worker]) = .ok #[toJson auth, toJson worker] := by
      simp only [ToJson.toJson, instToJsonOp.toJson]
      simp [Json.parseCtorFields]
      rfl
    simp only [FromJson.fromJson?, instFromJsonOp.fromJson, ToJson.toJson, instToJsonOp.toJson, json_tag_singleton]
    simp only [ToJson.toJson, instToJsonOp.toJson] at fields
    rw [fields]
    change (do
      let v0 ← (fromJson? (toJson auth) : Except String (Credentials))
      let v1 ← (fromJson? (toJson worker) : Except String (String))
      pure (Op.claim v0 v1)) = .ok (Op.claim auth worker)
    simp only [json_list_roundtrip json_input_roundtrip, json_list_roundtrip json_output_roundtrip,
      json_path_roundtrip, json_credentials_roundtrip, json_string_roundtrip, json_nat_roundtrip, json_bool_roundtrip,
      bind, Except.bind, pure, Except.pure]
  | renew auth =>
    have fields : (toJson (Op.renew auth)).parseCtorFields "renew" 1 (some #[`auth]) = .ok #[toJson auth] := by
      simp only [ToJson.toJson, instToJsonOp.toJson]
      simp [Json.parseCtorFields]
      rfl
    simp only [FromJson.fromJson?, instFromJsonOp.fromJson, ToJson.toJson, instToJsonOp.toJson, json_tag_singleton]
    simp only [ToJson.toJson, instToJsonOp.toJson] at fields
    rw [fields]
    change (do
      let v0 ← (fromJson? (toJson auth) : Except String (Credentials))
      pure (Op.renew v0)) = .ok (Op.renew auth)
    simp only [json_list_roundtrip json_input_roundtrip, json_list_roundtrip json_output_roundtrip,
      json_path_roundtrip, json_credentials_roundtrip, json_string_roundtrip, json_nat_roundtrip, json_bool_roundtrip,
      bind, Except.bind, pure, Except.pure]
  | expireLease inst now =>
    have fields : (toJson (Op.expireLease inst now)).parseCtorFields "expireLease" 2 (some #[`inst, `now]) = .ok #[toJson inst, toJson now] := by
      simp only [ToJson.toJson, instToJsonOp.toJson]
      simp [Json.parseCtorFields]
      rfl
    simp only [FromJson.fromJson?, instFromJsonOp.fromJson, ToJson.toJson, instToJsonOp.toJson, json_tag_singleton]
    simp only [ToJson.toJson, instToJsonOp.toJson] at fields
    rw [fields]
    change (do
      let v0 ← (fromJson? (toJson inst) : Except String (InstanceId))
      let v1 ← (fromJson? (toJson now) : Except String (Time))
      pure (Op.expireLease v0 v1)) = .ok (Op.expireLease inst now)
    simp only [json_list_roundtrip json_input_roundtrip, json_list_roundtrip json_output_roundtrip,
      json_path_roundtrip, json_credentials_roundtrip, json_string_roundtrip, json_nat_roundtrip, json_bool_roundtrip,
      bind, Except.bind, pure, Except.pure]
  | promoteRetry inst now =>
    have fields : (toJson (Op.promoteRetry inst now)).parseCtorFields "promoteRetry" 2 (some #[`inst, `now]) = .ok #[toJson inst, toJson now] := by
      simp only [ToJson.toJson, instToJsonOp.toJson]
      simp [Json.parseCtorFields]
      rfl
    simp only [FromJson.fromJson?, instFromJsonOp.fromJson, ToJson.toJson, instToJsonOp.toJson, json_tag_singleton]
    simp only [ToJson.toJson, instToJsonOp.toJson] at fields
    rw [fields]
    change (do
      let v0 ← (fromJson? (toJson inst) : Except String (InstanceId))
      let v1 ← (fromJson? (toJson now) : Except String (Time))
      pure (Op.promoteRetry v0 v1)) = .ok (Op.promoteRetry inst now)
    simp only [json_list_roundtrip json_input_roundtrip, json_list_roundtrip json_output_roundtrip,
      json_path_roundtrip, json_credentials_roundtrip, json_string_roundtrip, json_nat_roundtrip, json_bool_roundtrip,
      bind, Except.bind, pure, Except.pure]
  | emit auth port item =>
    have fields : (toJson (Op.emit auth port item)).parseCtorFields "emit" 3 (some #[`auth, `port, `item]) = .ok #[toJson auth, toJson port, toJson item] := by
      simp only [ToJson.toJson, instToJsonOp.toJson]
      simp [Json.parseCtorFields]
      rfl
    simp only [FromJson.fromJson?, instFromJsonOp.fromJson, ToJson.toJson, instToJsonOp.toJson, json_tag_singleton]
    simp only [ToJson.toJson, instToJsonOp.toJson] at fields
    rw [fields]
    change (do
      let v0 ← (fromJson? (toJson auth) : Except String (Credentials))
      let v1 ← (fromJson? (toJson port) : Except String (PortName))
      let v2 ← (fromJson? (toJson item) : Except String (ItemId))
      pure (Op.emit v0 v1 v2)) = .ok (Op.emit auth port item)
    simp only [json_list_roundtrip json_input_roundtrip, json_list_roundtrip json_output_roundtrip,
      json_path_roundtrip, json_credentials_roundtrip, json_string_roundtrip, json_nat_roundtrip, json_bool_roundtrip,
      bind, Except.bind, pure, Except.pure]
  | complete auth outputs =>
    have fields : (toJson (Op.complete auth outputs)).parseCtorFields "complete" 2 (some #[`auth, `outputs]) = .ok #[toJson auth, toJson outputs] := by
      simp only [ToJson.toJson, instToJsonOp.toJson]
      simp [Json.parseCtorFields]
      rfl
    simp only [FromJson.fromJson?, instFromJsonOp.fromJson, ToJson.toJson, instToJsonOp.toJson, json_tag_singleton]
    simp only [ToJson.toJson, instToJsonOp.toJson] at fields
    rw [fields]
    change (do
      let v0 ← (fromJson? (toJson auth) : Except String (Credentials))
      let v1 ← (fromJson? (toJson outputs) : Except String (List Output))
      pure (Op.complete v0 v1)) = .ok (Op.complete auth outputs)
    simp only [json_list_roundtrip json_input_roundtrip, json_list_roundtrip json_output_roundtrip,
      json_path_roundtrip, json_credentials_roundtrip, json_string_roundtrip, json_nat_roundtrip, json_bool_roundtrip,
      bind, Except.bind, pure, Except.pure]
  | fail auth code retryable =>
    have fields : (toJson (Op.fail auth code retryable)).parseCtorFields "fail" 3 (some #[`auth, `code, `retryable]) = .ok #[toJson auth, toJson code, toJson retryable] := by
      simp only [ToJson.toJson, instToJsonOp.toJson]
      simp [Json.parseCtorFields]
      rfl
    simp only [FromJson.fromJson?, instFromJsonOp.fromJson, ToJson.toJson, instToJsonOp.toJson, json_tag_singleton]
    simp only [ToJson.toJson, instToJsonOp.toJson] at fields
    rw [fields]
    change (do
      let v0 ← (fromJson? (toJson auth) : Except String (Credentials))
      let v1 ← (fromJson? (toJson code) : Except String (String))
      let v2 ← (fromJson? (toJson retryable) : Except String (Bool))
      pure (Op.fail v0 v1 v2)) = .ok (Op.fail auth code retryable)
    simp only [json_list_roundtrip json_input_roundtrip, json_list_roundtrip json_output_roundtrip,
      json_path_roundtrip, json_credentials_roundtrip, json_string_roundtrip, json_nat_roundtrip, json_bool_roundtrip,
      bind, Except.bind, pure, Except.pure]
  | fireWaitAll path node =>
    have fields : (toJson (Op.fireWaitAll path node)).parseCtorFields "fireWaitAll" 2 (some #[`path, `node]) = .ok #[toJson path, toJson node] := by
      simp only [ToJson.toJson, instToJsonOp.toJson]
      simp [Json.parseCtorFields]
      rfl
    simp only [FromJson.fromJson?, instFromJsonOp.fromJson, ToJson.toJson, instToJsonOp.toJson, json_tag_singleton]
    simp only [ToJson.toJson, instToJsonOp.toJson] at fields
    rw [fields]
    change (do
      let v0 ← (fromJson? (toJson path) : Except String (Path))
      let v1 ← (fromJson? (toJson node) : Except String (NodeId))
      pure (Op.fireWaitAll v0 v1)) = .ok (Op.fireWaitAll path node)
    simp only [json_list_roundtrip json_input_roundtrip, json_list_roundtrip json_output_roundtrip,
      json_path_roundtrip, json_credentials_roundtrip, json_string_roundtrip, json_nat_roundtrip, json_bool_roundtrip,
      bind, Except.bind, pure, Except.pure]
  | fireBranch path node arm =>
    have fields : (toJson (Op.fireBranch path node arm)).parseCtorFields "fireBranch" 3 (some #[`path, `node, `arm]) = .ok #[toJson path, toJson node, toJson arm] := by
      simp only [ToJson.toJson, instToJsonOp.toJson]
      simp [Json.parseCtorFields]
      rfl
    simp only [FromJson.fromJson?, instFromJsonOp.fromJson, ToJson.toJson, instToJsonOp.toJson, json_tag_singleton]
    simp only [ToJson.toJson, instToJsonOp.toJson] at fields
    rw [fields]
    change (do
      let v0 ← (fromJson? (toJson path) : Except String (Path))
      let v1 ← (fromJson? (toJson node) : Except String (NodeId))
      let v2 ← (fromJson? (toJson arm) : Except String (PortName))
      pure (Op.fireBranch v0 v1 v2)) = .ok (Op.fireBranch path node arm)
    simp only [json_list_roundtrip json_input_roundtrip, json_list_roundtrip json_output_roundtrip,
      json_path_roundtrip, json_credentials_roundtrip, json_string_roundtrip, json_nat_roundtrip, json_bool_roundtrip,
      bind, Except.bind, pure, Except.pure]
  | fireCoalesce path node edge item =>
    have fields : (toJson (Op.fireCoalesce path node edge item)).parseCtorFields "fireCoalesce" 4 (some #[`path, `node, `edge, `item]) = .ok #[toJson path, toJson node, toJson edge, toJson item] := by
      simp only [ToJson.toJson, instToJsonOp.toJson]
      simp [Json.parseCtorFields]
      rfl
    simp only [FromJson.fromJson?, instFromJsonOp.fromJson, ToJson.toJson, instToJsonOp.toJson, json_tag_singleton]
    simp only [ToJson.toJson, instToJsonOp.toJson] at fields
    rw [fields]
    change (do
      let v0 ← (fromJson? (toJson path) : Except String (Path))
      let v1 ← (fromJson? (toJson node) : Except String (NodeId))
      let v2 ← (fromJson? (toJson edge) : Except String (String))
      let v3 ← (fromJson? (toJson item) : Except String (ItemId))
      pure (Op.fireCoalesce v0 v1 v2 v3)) = .ok (Op.fireCoalesce path node edge item)
    simp only [json_list_roundtrip json_input_roundtrip, json_list_roundtrip json_output_roundtrip,
      json_path_roundtrip, json_credentials_roundtrip, json_string_roundtrip, json_nat_roundtrip, json_bool_roundtrip,
      bind, Except.bind, pure, Except.pure]
  | fireCollect path node =>
    have fields : (toJson (Op.fireCollect path node)).parseCtorFields "fireCollect" 2 (some #[`path, `node]) = .ok #[toJson path, toJson node] := by
      simp only [ToJson.toJson, instToJsonOp.toJson]
      simp [Json.parseCtorFields]
      rfl
    simp only [FromJson.fromJson?, instFromJsonOp.fromJson, ToJson.toJson, instToJsonOp.toJson, json_tag_singleton]
    simp only [ToJson.toJson, instToJsonOp.toJson] at fields
    rw [fields]
    change (do
      let v0 ← (fromJson? (toJson path) : Except String (Path))
      let v1 ← (fromJson? (toJson node) : Except String (NodeId))
      pure (Op.fireCollect v0 v1)) = .ok (Op.fireCollect path node)
    simp only [json_list_roundtrip json_input_roundtrip, json_list_roundtrip json_output_roundtrip,
      json_path_roundtrip, json_credentials_roundtrip, json_string_roundtrip, json_nat_roundtrip, json_bool_roundtrip,
      bind, Except.bind, pure, Except.pure]
  | fireFilter path node item keep =>
    have fields : (toJson (Op.fireFilter path node item keep)).parseCtorFields "fireFilter" 4 (some #[`path, `node, `item, `keep]) = .ok #[toJson path, toJson node, toJson item, toJson keep] := by
      simp only [ToJson.toJson, instToJsonOp.toJson]
      simp [Json.parseCtorFields]
      rfl
    simp only [FromJson.fromJson?, instFromJsonOp.fromJson, ToJson.toJson, instToJsonOp.toJson, json_tag_singleton]
    simp only [ToJson.toJson, instToJsonOp.toJson] at fields
    rw [fields]
    change (do
      let v0 ← (fromJson? (toJson path) : Except String (Path))
      let v1 ← (fromJson? (toJson node) : Except String (NodeId))
      let v2 ← (fromJson? (toJson item) : Except String (ItemId))
      let v3 ← (fromJson? (toJson keep) : Except String (Bool))
      pure (Op.fireFilter v0 v1 v2 v3)) = .ok (Op.fireFilter path node item keep)
    simp only [json_list_roundtrip json_input_roundtrip, json_list_roundtrip json_output_roundtrip,
      json_path_roundtrip, json_credentials_roundtrip, json_string_roundtrip, json_nat_roundtrip, json_bool_roundtrip,
      bind, Except.bind, pure, Except.pure]
  | fireMerge path node edge item =>
    have fields : (toJson (Op.fireMerge path node edge item)).parseCtorFields "fireMerge" 4 (some #[`path, `node, `edge, `item]) = .ok #[toJson path, toJson node, toJson edge, toJson item] := by
      simp only [ToJson.toJson, instToJsonOp.toJson]
      simp [Json.parseCtorFields]
      rfl
    simp only [FromJson.fromJson?, instFromJsonOp.fromJson, ToJson.toJson, instToJsonOp.toJson, json_tag_singleton]
    simp only [ToJson.toJson, instToJsonOp.toJson] at fields
    rw [fields]
    change (do
      let v0 ← (fromJson? (toJson path) : Except String (Path))
      let v1 ← (fromJson? (toJson node) : Except String (NodeId))
      let v2 ← (fromJson? (toJson edge) : Except String (String))
      let v3 ← (fromJson? (toJson item) : Except String (ItemId))
      pure (Op.fireMerge v0 v1 v2 v3)) = .ok (Op.fireMerge path node edge item)
    simp only [json_list_roundtrip json_input_roundtrip, json_list_roundtrip json_output_roundtrip,
      json_path_roundtrip, json_credentials_roundtrip, json_string_roundtrip, json_nat_roundtrip, json_bool_roundtrip,
      bind, Except.bind, pure, Except.pure]
  | propagateEos path node =>
    have fields : (toJson (Op.propagateEos path node)).parseCtorFields "propagateEos" 2 (some #[`path, `node]) = .ok #[toJson path, toJson node] := by
      simp only [ToJson.toJson, instToJsonOp.toJson]
      simp [Json.parseCtorFields]
      rfl
    simp only [FromJson.fromJson?, instFromJsonOp.fromJson, ToJson.toJson, instToJsonOp.toJson, json_tag_singleton]
    simp only [ToJson.toJson, instToJsonOp.toJson] at fields
    rw [fields]
    change (do
      let v0 ← (fromJson? (toJson path) : Except String (Path))
      let v1 ← (fromJson? (toJson node) : Except String (NodeId))
      pure (Op.propagateEos v0 v1)) = .ok (Op.propagateEos path node)
    simp only [json_list_roundtrip json_input_roundtrip, json_list_roundtrip json_output_roundtrip,
      json_path_roundtrip, json_credentials_roundtrip, json_string_roundtrip, json_nat_roundtrip, json_bool_roundtrip,
      bind, Except.bind, pure, Except.pure]
  | finishSubworkflow inst =>
    have fields : (toJson (Op.finishSubworkflow inst)).parseCtorFields "finishSubworkflow" 1 (some #[`inst]) = .ok #[toJson inst] := by
      simp only [ToJson.toJson, instToJsonOp.toJson]
      simp [Json.parseCtorFields]
      rfl
    simp only [FromJson.fromJson?, instFromJsonOp.fromJson, ToJson.toJson, instToJsonOp.toJson, json_tag_singleton]
    simp only [ToJson.toJson, instToJsonOp.toJson] at fields
    rw [fields]
    change (do
      let v0 ← (fromJson? (toJson inst) : Except String (InstanceId))
      pure (Op.finishSubworkflow v0)) = .ok (Op.finishSubworkflow inst)
    simp only [json_list_roundtrip json_input_roundtrip, json_list_roundtrip json_output_roundtrip,
      json_path_roundtrip, json_credentials_roundtrip, json_string_roundtrip, json_nat_roundtrip, json_bool_roundtrip,
      bind, Except.bind, pure, Except.pure]
  | loopIterate inst done =>
    have fields : (toJson (Op.loopIterate inst done)).parseCtorFields "loopIterate" 2 (some #[`inst, `done]) = .ok #[toJson inst, toJson done] := by
      simp only [ToJson.toJson, instToJsonOp.toJson]
      simp [Json.parseCtorFields]
      rfl
    simp only [FromJson.fromJson?, instFromJsonOp.fromJson, ToJson.toJson, instToJsonOp.toJson, json_tag_singleton]
    simp only [ToJson.toJson, instToJsonOp.toJson] at fields
    rw [fields]
    change (do
      let v0 ← (fromJson? (toJson inst) : Except String (InstanceId))
      let v1 ← (fromJson? (toJson done) : Except String (Bool))
      pure (Op.loopIterate v0 v1)) = .ok (Op.loopIterate inst done)
    simp only [json_list_roundtrip json_input_roundtrip, json_list_roundtrip json_output_roundtrip,
      json_path_roundtrip, json_credentials_roundtrip, json_string_roundtrip, json_nat_roundtrip, json_bool_roundtrip,
      bind, Except.bind, pure, Except.pure]
  | skip path node =>
    have fields : (toJson (Op.skip path node)).parseCtorFields "skip" 2 (some #[`path, `node]) = .ok #[toJson path, toJson node] := by
      simp only [ToJson.toJson, instToJsonOp.toJson]
      simp [Json.parseCtorFields]
      rfl
    simp only [FromJson.fromJson?, instFromJsonOp.fromJson, ToJson.toJson, instToJsonOp.toJson, json_tag_singleton]
    simp only [ToJson.toJson, instToJsonOp.toJson] at fields
    rw [fields]
    change (do
      let v0 ← (fromJson? (toJson path) : Except String (Path))
      let v1 ← (fromJson? (toJson node) : Except String (NodeId))
      pure (Op.skip v0 v1)) = .ok (Op.skip path node)
    simp only [json_list_roundtrip json_input_roundtrip, json_list_roundtrip json_output_roundtrip,
      json_path_roundtrip, json_credentials_roundtrip, json_string_roundtrip, json_nat_roundtrip, json_bool_roundtrip,
      bind, Except.bind, pure, Except.pure]
  | idle => rfl
  | cancel => rfl
  | manualRetry inst =>
    have fields : (toJson (Op.manualRetry inst)).parseCtorFields "manualRetry" 1 (some #[`inst]) = .ok #[toJson inst] := by
      simp only [ToJson.toJson, instToJsonOp.toJson]
      simp [Json.parseCtorFields]
      rfl
    simp only [FromJson.fromJson?, instFromJsonOp.fromJson, ToJson.toJson, instToJsonOp.toJson, json_tag_singleton]
    simp only [ToJson.toJson, instToJsonOp.toJson] at fields
    rw [fields]
    change (do
      let v0 ← (fromJson? (toJson inst) : Except String (InstanceId))
      pure (Op.manualRetry v0)) = .ok (Op.manualRetry inst)
    simp only [json_list_roundtrip json_input_roundtrip, json_list_roundtrip json_output_roundtrip,
      json_path_roundtrip, json_credentials_roundtrip, json_string_roundtrip, json_nat_roundtrip, json_bool_roundtrip,
      bind, Except.bind, pure, Except.pure]


theorem json_op_not_null (op : Op) : toJson op ≠ Json.null := by
  cases op <;> simp [ToJson.toJson, instToJsonOp.toJson, Json.mkObj]

@[simp] theorem json_optional_op_roundtrip (op : Option Op) : fromJson? (toJson op) = Except.ok op := by
  cases op with
  | none => rfl
  | some op =>
    have h := json_op_roundtrip op
    have nonnull := json_op_not_null op
    change Lean.Option.fromJson? (toJson op) = .ok (some op)
    cases encoded : toJson op <;> simp only [encoded, Lean.Option.fromJson?] at *
    all_goals first | contradiction | (rw [h]; rfl)

@[simp] theorem json_event_roundtrip (event : Event) : fromJson? (toJson event) = Except.ok event := by
  cases event with
  | mk version sequence txn recordedAt type op data =>
    change (do
      let version' ← Except.mapError (fun message => toString `Suimon.Trace.Event ++ "." ++ toString `schema_version ++ ": " ++ message)
        (fromJson? (toJson version) : Except String Nat)
      let sequence' ← Except.mapError (fun message => toString `Suimon.Trace.Event ++ "." ++ toString `sequence ++ ": " ++ message)
        (fromJson? (toJson sequence) : Except String Nat)
      let txn' ← Except.mapError (fun message => toString `Suimon.Trace.Event ++ "." ++ toString `txn ++ ": " ++ message)
        (fromJson? (toJson txn) : Except String String)
      let recordedAt' ← Except.mapError (fun message => toString `Suimon.Trace.Event ++ "." ++ toString `recorded_at ++ ": " ++ message)
        (fromJson? (toJson recordedAt) : Except String Nat)
      let type' ← Except.mapError (fun message => toString `Suimon.Trace.Event ++ "." ++ toString `type ++ ": " ++ message)
        (fromJson? (toJson type) : Except String String)
      let op' ← Except.mapError (fun message => toString `Suimon.Trace.Event ++ "." ++ toString `op ++ ": " ++ message)
        (fromJson? (toJson op) : Except String (Option Op))
      let data' ← Except.mapError (fun message => toString `Suimon.Trace.Event ++ "." ++ toString `data ++ ": " ++ message)
        (fromJson? (toJson data) : Except String Json)
      pure (Event.mk version' sequence' txn' recordedAt' type' op' data')) = .ok (Event.mk version sequence txn recordedAt type op data)
    rw [json_nat_roundtrip, json_nat_roundtrip, json_string_roundtrip, json_nat_roundtrip,
      json_string_roundtrip, json_optional_op_roundtrip]
    rfl

/-- Every v2 event survives its actual typed JSON codec and canonical-schema check. --/
theorem parseEventJson_roundtrip (event : Event) (version : event.schema_version = 2) :
    parseEventJson (toJson event) = .ok event := by
  simp [parseEventJson, json_event_roundtrip, version, bind, Except.bind, pure, Except.pure]

end Suimon.Trace
