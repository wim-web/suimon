import type { Call, Definition, Execution, Failure, Invocation, InvocationStatus, Path, Result, Run, RuntimeState, Settled, TaskOutput, TaskStatus } from '../types';
import { findWorkflow } from './definition';
import { dictionary } from './dictionary';
import { createRuntimeIndex, ownerKey, placementKey } from './runtime-index';
import type { RuntimeIndex } from './runtime-index';

export function samePath(a: readonly string[], b: readonly string[]): boolean {
  return a.length === b.length && a.every((segment, i) => segment === b[i]);
}
/** A key for maps and React keys; path segments stay opaque. */
export function pathKey(path: readonly string[]): string { return JSON.stringify(path); }

export function findRun(state: RuntimeState, path: readonly string[], index?: RuntimeIndex): Run | undefined {
  return index ? index.runs.get(pathKey(path)) : state.runs.find(r => samePath(r.path, path));
}
export function findInvocation(state: RuntimeState, id: string, index?: RuntimeIndex): Invocation | undefined { return index ? index.invocations.get(id) : state.invocations.find(i => i.id === id); }
export function findExecution(state: RuntimeState, id: string, index?: RuntimeIndex): Execution | undefined { return index ? index.executions.get(id) : state.executions.find(e => e.id === id); }

/** The transformed value of a task result, or null while pending and after a failure. */
export function taskOutputValue(output: TaskOutput): string | null { return typeof output === 'object' ? output.value.v : null; }
export type TaskOutputState = 'pending' | 'value' | 'failed';
export function taskOutputState(output: TaskOutput): TaskOutputState { return typeof output === 'object' ? 'value' : output; }

/**
 * What produced a result, from its producer: a call (and the invocation that owns it), an
 * execution of a concurrency placement (with its invocation, which has the same id), the
 * invocation of a sub-workflow call, or the aggregate of a waitStream or Merge, which no single
 * invocation produced.
 */
export type ResultSource =
  | { kind: 'call'; call: Call; invocation?: Invocation }
  | { kind: 'execution'; execution: Execution; invocation?: Invocation }
  | { kind: 'invocation'; invocation: Invocation }
  | { kind: 'aggregate'; invocation?: undefined };

export function resultSource(state: RuntimeState, result: Result, index?: RuntimeIndex): ResultSource {
  const call = index ? index.calls.get(result.producer) : state.calls.find(c => c.id === result.producer);
  if (call) return { kind: 'call', call, ...(call.task === null && { invocation: findInvocation(state, call.owner, index) }) };
  const execution = findExecution(state, result.producer, index);
  if (execution) return { kind: 'execution', execution, invocation: findInvocation(state, execution.id, index) };
  const invocation = findInvocation(state, result.producer, index);
  return invocation ? { kind: 'invocation', invocation } : { kind: 'aggregate' };
}

/** The results produced for one invocation: by its calls, its execution, or its sub-workflow call. */
export function invocationResults(state: RuntimeState, invocation: Invocation, index: RuntimeIndex = createRuntimeIndex(state)): Result[] {
  return (index.resultsByInvocation.get(invocation.id) ?? []).filter(r => samePath(r.run, invocation.run) && r.placement === invocation.placement);
}

const taskEnded = (status: TaskStatus) => status !== 'pending' && status !== 'ready' && status !== 'active';

/** Where a child run was called from: an invocation, or one task of a concurrency execution. */
export interface RunOwner { run: Path; placement: string; invocation?: Invocation; execution?: Execution; task: string | null }

export function runOwner(state: RuntimeState, run: Run, index?: RuntimeIndex): RunOwner | undefined {
  if (run.owner === null) return undefined;
  if (run.task !== null) {
    const execution = findExecution(state, run.owner, index);
    return execution && { run: execution.run, placement: execution.placement, execution, task: run.task };
  }
  const invocation = findInvocation(state, run.owner, index);
  return invocation && { run: invocation.run, placement: invocation.placement, invocation, task: null };
}

/** Child runs called by one invocation, or by one task of the execution with that id. */
export function childRuns(state: RuntimeState, owner: string, task: string | null = null, index?: RuntimeIndex): Run[] {
  return index ? index.childRunsByOwner.get(ownerKey(owner, task)) ?? [] : state.runs.filter(r => r.owner === owner && r.task === task);
}

export interface RunNode {
  run: Run;
  depth: number;
  owner?: RunOwner;
  /** 1-based position among the runs called from the same placement (and task) of the parent run. */
  ordinal: number;
  status: 'running' | 'complete';
}

/** Runs in tree order: each child run follows the run that owns its caller. Orphans come last. */
export function runTree(state: RuntimeState, index: RuntimeIndex = createRuntimeIndex(state)): RunNode[] {
  const byParent = new Map<string, { run: Run; owner?: RunOwner }[]>();
  const roots: { run: Run; owner?: RunOwner }[] = [];
  for (const run of state.runs) {
    const owner = runOwner(state, run, index);
    if (!run.path.length || !owner) roots.push({ run, owner });
    else {
      const key = pathKey(owner.run), siblings = byParent.get(key);
      if (siblings) siblings.push({ run, owner }); else byParent.set(key, [{ run, owner }]);
    }
  }
  roots.sort((a, b) => a.run.path.length - b.run.path.length);
  const nodes: RunNode[] = [];
  const visit = (item: { run: Run; owner?: RunOwner }, depth: number, ordinal: number) => {
    nodes.push({ run: item.run, depth, owner: item.owner, ordinal, status: item.run.complete ? 'complete' : 'running' });
    const counts = new Map<string, number>();
    for (const child of byParent.get(pathKey(item.run.path)) ?? []) {
      const key = ownerKey(child.owner!.placement, child.owner!.task);
      counts.set(key, (counts.get(key) ?? 0) + 1);
      visit(child, depth + 1, counts.get(key)!);
    }
  };
  roots.forEach(root => visit(root, 0, 1));
  return nodes;
}

export function runLabel(node: RunNode): string {
  if (!node.owner) return node.run.path.length ? `${node.run.workflow} (unknown owner)` : node.run.workflow;
  return `${node.owner.placement}${node.owner.task ? `.${node.owner.task}` : ''} #${node.ordinal} → ${node.run.workflow}`;
}

export type PlacementPhase = 'idle' | 'active' | 'waiting' | 'settled';
export interface PlacementStatus {
  placement: string;
  invocations: Invocation[];
  /** Invocation counts by status. */
  counts: Partial<Record<InvocationStatus, number>>;
  /** Calls of the placement or its tasks that have not ended, including cancelled ones still running. */
  runningCalls: number;
  /** Concurrency: executions and the counts of their tasks by status. */
  executions: Execution[];
  taskCounts: Partial<Record<TaskStatus, number>>;
  /** Concurrency: the output transforms of the results of tasks that have one, by state. */
  taskOutputs: Partial<Record<TaskOutputState, number>>;
  settled: Settled | null;
  results: number;
  failures: Failure[];
  phase: PlacementPhase;
}
export interface ConnectionStatus { values: number; triggers: number; failed: number }
export interface RunOverlay {
  run: Run;
  /** The status of each placement of the run's workflow, by name; runOverlay builds it without a prototype. */
  placements: Record<string, PlacementStatus>;
  /** Deliveries on each connection of the run, by connection index. */
  connections: Record<number, ConnectionStatus>;
  failures: Failure[];
}

function count<T extends string>(values: T[]): Partial<Record<T, number>> {
  const counts: Partial<Record<T, number>> = {};
  for (const value of values) counts[value] = (counts[value] ?? 0) + 1;
  return counts;
}

/** The status of every placement in one run of the state. */
export function runOverlay(definition: Definition, state: RuntimeState, path: readonly string[], index: RuntimeIndex = createRuntimeIndex(state)): RunOverlay | null {
  const run = findRun(state, path, index);
  const workflow = run && findWorkflow(definition, run.workflow);
  if (!run || !workflow) return null;
  const failures = index.failuresByRun.get(pathKey(path)) ?? [];
  const placements = dictionary<PlacementStatus>();
  for (const p of workflow.placements) {
    const key = placementKey(path, p.name);
    const own = index.invocationsByPlacement.get(key) ?? [];
    const ownExecutions = index.executionsByPlacement.get(key) ?? [];
    const runningCalls = own.reduce((n, i) => n + (index.runningInvocationCalls.get(i.id) ?? 0), 0)
      + ownExecutions.reduce((n, e) => n + (index.runningExecutionCalls.get(e.id) ?? 0), 0);
    const tasks = ownExecutions.flatMap(e => e.tasks.map(t => t.status));
    const transformed = new Set(p.node.type === 'concurrency' ? p.node.tasks.filter(t => t.outputTransform).map(t => t.name) : []);
    const outputs = ownExecutions.flatMap(e => (index.taskResultsByExecution.get(e.id) ?? []).filter(r => transformed.has(r.task)).map(r => taskOutputState(r.output)));
    const settledOne = index.settledByPlacement.get(key)?.[0] ?? null;
    const busy = runningCalls > 0 || own.some(i => i.status === 'active') || ownExecutions.some(e => !e.complete) || tasks.some(s => !taskEnded(s))
      || own.some(i => index.activeChildInvocations.has(i.id)) || ownExecutions.some(e => index.activeChildExecutions.has(e.id));
    placements[p.name] = {
      placement: p.name, invocations: own, counts: count(own.map(i => i.status)), runningCalls,
      executions: ownExecutions, taskCounts: count(tasks), taskOutputs: count(outputs), settled: settledOne,
      results: index.resultsByPlacement.get(key)?.length ?? 0,
      failures: index.failuresByPlacement.get(key) ?? [],
      phase: settledOne ? 'settled' : busy ? 'active' : own.length ? 'waiting' : 'idle',
    };
  }
  const connections: Record<number, ConnectionStatus> = {};
  for (const d of index.deliveriesByRun.get(pathKey(path)) ?? []) {
    const c = connections[d.connection] ??= { values: 0, triggers: 0, failed: 0 };
    if (d.outcome === 'trigger') c.triggers++; else if (d.outcome === 'failed') c.failed++; else c.values++;
  }
  return { run, placements, connections, failures };
}

/** The outcome of one arm of a settled branch; other placements settle as a whole. */
export function armOutcome(settled: Settled, arm: string | null | undefined) {
  return (arm && settled.arms.find(([name]) => name === arm)?.[1]) || settled.outcome;
}
