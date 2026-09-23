export type JsonValue = null | boolean | number | string | JsonValue[] | { [key: string]: JsonValue };

/* Program: schema/program.schema.json. Optional arrays are normalized to [] by parseProgram. */

/** A type name, or `{ list: type }` for List<type>. */
export type ValueType = string | { list: ValueType };
/** The output of one call: return one value, or yield each element. */
export type Contract = { single: ValueType } | { stream: ValueType };
export type Policy = 'stop' | 'continue';
export interface Timeout { callMs?: number; elementMs?: number }

export interface FunctionDecl { id: string; input?: ValueType; output: Contract }
export interface JudgeDecl { id: string; input: ValueType }
export interface TransformDecl { id: string; input: ValueType; output: ValueType }

export interface FunctionBody { type: 'function'; function: string }
/** `output` names the endpoint of the called workflow whose result is the call's output. */
export interface SubworkflowBody { type: 'subworkflow'; workflow: string; output: string }
export type Body = FunctionBody | SubworkflowBody;

/** A concurrency task. Without outputTransform, its results are left out of the output. */
export interface Task {
  name: string;
  body: Body;
  inputTransform?: string;
  outputTransform?: string;
  policy: Policy;
  timeout?: Timeout;
}
export interface BranchControl { type: 'branch'; judge: string; arms: string[] }
export interface WaitStreamControl { type: 'waitStream'; element: ValueType }
export interface MergeControl { type: 'merge'; element: ValueType }
export interface ConcurrencyControl {
  type: 'concurrency';
  input?: ValueType;
  limit: number;
  tasks: Task[];
  output: 'list' | 'stream';
  element: ValueType;
}
export type Control = FunctionBody | SubworkflowBody | BranchControl | WaitStreamControl | MergeControl | ConcurrencyControl;
export type ControlType = Control['type'];

export interface Placement { name: string; node: Control; policy: Policy; timeout?: Timeout }
/** `arm` is present exactly when the source is a branch. `transform` may be the library's `discard`. */
export interface Connection { source: string; arm?: string; target: string; transform: string }
export interface WorkflowInput { type: ValueType; placement: string }
export interface Workflow { id: string; input?: WorkflowInput; placements: Placement[]; connections: Connection[] }
export interface Program {
  main: string;
  functions: FunctionDecl[];
  judges: JudgeDecl[];
  transforms: TransformDecl[];
  workflows: Workflow[];
}

/* Runtime state: Suimon/State.lean in its derived JSON form. Option fields are normalized to null. */

/** A run: [] is the root run; a sub-workflow call appends one opaque segment. */
export type Path = string[];
export type Cause = 'error' | 'timeout' | 'lost' | 'transform';
export type Outcome = 'normal' | 'skipped' | 'failed' | 'upstreamFailed';
export type Status = 'running' | 'stopping' | 'succeeded' | 'failed' | 'cancelled' | 'skipped';
export type CallStatus = 'running' | 'fetching' | 'cancelling' | 'returned' | 'failed' | 'lost' | 'cancelled';
export type InvocationStatus = 'active' | 'succeeded' | 'skipped' | 'failed' | 'upstreamFailed' | 'cancelled';
export type TaskStatus = 'pending' | 'ready' | 'active' | 'succeeded' | 'skipped' | 'failed' | 'upstreamFailed' | 'notStarted' | 'cancelled';

export interface Run {
  path: Path;
  workflow: string;
  input: string | null;
  /** The invocation, or the execution of `task`, that called this workflow; null for the root. */
  owner: string | null;
  task: string | null;
  complete: boolean;
}
export interface Invocation {
  id: string;
  run: Path;
  placement: string;
  trigger: string | null;
  input: string | null;
  status: InvocationStatus;
  arm: string | null;
}
export type CallTarget = { function: { id: string } } | { judge: { id: string } };
export interface CallTimeout { callMs: number | null; elementMs: number | null }
/** A call of a user process. Its owner is an invocation, or (with `task`) an execution. */
export interface Call {
  id: string;
  owner: string;
  task: string | null;
  target: CallTarget;
  input: string | null;
  stream: boolean;
  status: CallStatus;
  yields: number;
  timeout: CallTimeout;
  policy: Policy;
}
export interface TaskState { name: string; input: string | null; status: TaskStatus }
/** One execution of a concurrency placement; its id is the id of the invocation it runs for. */
export interface Execution { id: string; run: Path; placement: string; input: string | null; tasks: TaskState[]; complete: boolean }
/** The output transform applied to one task result: not yet, the transformed value, or a failure. */
export type TaskOutput = 'pending' | { value: { v: string } } | 'failed';
/** A result of a task body; `output` stays pending for a task without an output transform. */
export interface TaskResult { execution: string; task: string; index: number; value: string; output: TaskOutput }
/**
 * An accepted result of a placement. `producer` is the call for a call result, the execution for a
 * concurrency result (Stream items and List results), the invocation for a sub-workflow call result,
 * and the aggregate key of the run and placement for the list of a waitStream or Merge.
 */
export interface Result { id: string; run: Path; placement: string; producer: string; arm: string | null; value: string }
export type Delivered = { value: { v: string } } | 'trigger' | 'failed';
export interface Delivery { run: Path; connection: number; source: string; outcome: Delivered }
export interface Settled { run: Path; placement: string; outcome: Outcome; arms: [string, Outcome][] }
export interface Failure { run: Path; placement: string; task: string | null; cause: Cause }
export interface RuntimeState {
  status: Status;
  started: boolean;
  cancelled: boolean;
  runs: Run[];
  invocations: Invocation[];
  calls: Call[];
  executions: Execution[];
  results: Result[];
  taskResults: TaskResult[];
  deliveries: Delivery[];
  settled: Settled[];
  failures: Failure[];
}

/* Execution records: schema/trace.schema.json. Value fields hold value identities, which stay opaque. */

export type CallOp =
  | { type: 'fetch' | 'ended' | 'failed' | 'lost' | 'terminated'; call: string }
  | { type: 'returned' | 'yielded'; call: string; value: string }
  | { type: 'judged'; call: string; arm: string }
  | { type: 'timedOut'; call: string; element: boolean };
export type TaskOp =
  | { type: 'taskInput'; execution: string; task: string; value?: string }
  | { type: 'taskInputFailed' | 'beginTask'; execution: string; task: string }
  | { type: 'taskOutput'; execution: string; task: string; index: number; value: string }
  | { type: 'taskOutputFailed'; execution: string; task: string; index: number };
export type Op =
  | { type: 'start'; input?: string }
  | { type: 'invoke'; run: Path; placement: string; trigger?: string }
  | CallOp
  | { type: 'deliver'; run: Path; connection: number; source: string; value?: string }
  | { type: 'transformFailed'; run: Path; connection: number; source: string }
  | TaskOp
  | { type: 'settle'; run: Path; placement: string }
  | { type: 'closeExecution'; execution: string }
  | { type: 'closeRun'; run: Path }
  | { type: 'cancel' | 'conclude' };
export type OpType = Op['type'];
/** `values` maps value identities to the payload strings the runtime serialized. */
export interface OpRecord { seq: number; op: Op; values?: Record<string, string> }
export interface CommitRecord { seq: number; commit: true }
export type ExecutionRecord = OpRecord | CommitRecord;
/**
 * The complete lines of a record, and the text after the last newline. The tail is what a crash
 * leaves: it is never parsed and never committed, even when it would parse.
 */
export interface RecordLog { records: ExecutionRecord[]; tail: string }
/** One op record; only an op followed by its commit is an accepted transition. */
export interface Transition { seq: number; op: Op; values: Record<string, string>; committed: boolean }

/* Presentation hints supplied by the host. */

export interface PlacementPresentation { label?: string; description?: string; accent?: string; position?: { x: number; y: number } }
/** Hints for the placements of one workflow, by placement name. */
export type PlacementPresentations = Record<string, PlacementPresentation>;
/** Hints by workflow id, then placement name. */
export type WorkflowPresentations = Record<string, PlacementPresentations>;
