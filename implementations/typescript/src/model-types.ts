export type ValueType = string | { list: ValueType };
export type Kind = 'single' | 'stream';
export type Policy = 'stop' | 'continue';
export interface Timeout { callMs?: bigint; elementMs?: bigint }
export type Contract = { single: ValueType } | { stream: ValueType };
export interface FunctionDecl { id: string; input?: ValueType; output: Contract }
export interface JudgeDecl { id: string; input: ValueType }
export interface TransformDecl { id: string; input: ValueType; output: ValueType }
export type Body = { type: 'function'; function: string } | { type: 'subworkflow'; workflow: string; output: string };
export interface TaskSpec { name: string; body: Body; inputTransform?: string; outputTransform?: string; policy: Policy; timeout?: Timeout }
export interface Concurrency { type: 'concurrency'; input?: ValueType; limit: bigint; tasks: TaskSpec[]; output: 'list' | 'stream'; element: ValueType }
export type Control = Body | { type: 'branch'; judge: string; arms: string[] }
  | { type: 'waitStream' | 'merge'; element: ValueType } | Concurrency;
export interface Placement { name: string; node: Control; policy: Policy; timeout?: Timeout }
export interface Connection { source: string; arm?: string; target: string; transform: string }
export interface Workflow { id: string; input?: { type: ValueType; placement: string }; placements: Placement[]; connections: Connection[] }
export interface Definition { main: string; functions: FunctionDecl[]; judges: JudgeDecl[]; transforms: TransformDecl[]; workflows: Workflow[] }

export type Path = string[];
export type Cause = 'error' | 'timeout' | 'lost' | 'transform';
export type Outcome = 'normal' | 'skipped' | 'failed' | 'upstreamFailed';
export type Status = 'running' | 'stopping' | 'succeeded' | 'failed' | 'cancelled' | 'skipped';
export type CallStatus = 'running' | 'fetching' | 'cancelling' | 'returned' | 'failed' | 'lost' | 'cancelled';
export type InvocationStatus = 'active' | 'succeeded' | 'skipped' | 'failed' | 'upstreamFailed' | 'cancelled';
export type TaskStatus = 'pending' | 'ready' | 'active' | 'succeeded' | 'skipped' | 'failed' | 'upstreamFailed' | 'notStarted' | 'cancelled';
export interface Run { path: Path; workflow: string; input: string | null; owner: string | null; task: string | null; complete: boolean }
export interface Invocation { id: string; run: Path; placement: string; trigger: string | null; input: string | null; status: InvocationStatus; arm: string | null }
export interface Call { id: string; owner: string; task: string | null; target: { kind: 'function' | 'judge'; id: string }; input: string | null; stream: boolean; status: CallStatus; yields: number; timeout: Timeout; policy: Policy }
export interface TaskState { name: string; input: string | null; status: TaskStatus }
export interface ConcurrencyExecution { id: string; run: Path; placement: string; input: string | null; tasks: TaskState[]; complete: boolean }
export type TaskOutput = { kind: 'pending' | 'failed' } | { kind: 'value'; value: string };
export interface TaskResult { execution: string; task: string; index: number; value: string; output: TaskOutput }
export interface Result { id: string; run: Path; placement: string; producer: string; arm: string | null; value: string }
export type Delivered = { kind: 'trigger' | 'failed' } | { kind: 'value'; value: string };
export interface Delivery { run: Path; connection: number; source: string; outcome: Delivered }
export interface Settled { run: Path; placement: string; outcome: Outcome; arms: { arm: string; outcome: Outcome }[] }
export interface Failure { run: Path; placement: string; task: string | null; cause: Cause }
export interface State {
  status: Status; started: boolean; cancelled: boolean;
  runs: Run[]; invocations: Invocation[]; calls: Call[]; executions: ConcurrencyExecution[];
  results: Result[]; taskResults: TaskResult[]; deliveries: Delivery[]; settled: Settled[]; failures: Failure[];
}

export type Op =
  | { type: 'start'; input?: string }
  | { type: 'invoke'; run: Path; placement: string; trigger?: string }
  | { type: 'fetch' | 'ended' | 'failed' | 'lost' | 'terminated'; call: string }
  | { type: 'returned' | 'yielded'; call: string; value: string }
  | { type: 'judged'; call: string; arm: string }
  | { type: 'timedOut'; call: string; element: boolean }
  | { type: 'deliver'; run: Path; connection: number; source: string; value?: string }
  | { type: 'transformFailed'; run: Path; connection: number; source: string }
  | { type: 'taskInput'; execution: string; task: string; value?: string }
  | { type: 'taskInputFailed' | 'beginTask'; execution: string; task: string }
  | { type: 'taskOutput'; execution: string; task: string; index: number; value: string }
  | { type: 'taskOutputFailed'; execution: string; task: string; index: number }
  | { type: 'settle'; run: Path; placement: string }
  | { type: 'closeExecution'; execution: string }
  | { type: 'closeRun'; run: Path }
  | { type: 'cancel' | 'conclude' };

export interface Payload { value: string; payload: string }
export type TraceRecord = { seq: number; op: Op; values: Payload[] } | { seq: number; commit: true };
export interface CheckedTrace { definition: Definition | null; validated: boolean; state: State; values: Payload[]; committed: number; length: number }
