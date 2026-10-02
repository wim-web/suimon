import type { Path, RuntimeState } from '../types';

/** Tuple keys keep opaque identifiers (including separators and empty names) distinct. */
export const placementKey = (run: readonly string[], placement: string) => JSON.stringify([run, placement]);
export const ownerKey = (owner: string, task: string | null) => JSON.stringify([owner, task]);
export const connectionKey = (run: readonly string[], connection: number) => JSON.stringify([run, connection]);

function byId<T extends { id: string }>(items: T[]): Map<string, T> {
  const result = new Map<string, T>();
  // Preserve Array.find's first-match behavior for unchecked input.
  for (const item of items) if (!result.has(item.id)) result.set(item.id, item);
  return result;
}

function group<T>(items: T[], key: (item: T) => string): Map<string, T[]> {
  const result = new Map<string, T[]>();
  for (const item of items) {
    const k = key(item), bucket = result.get(k);
    if (bucket) bucket.push(item); else result.set(k, [item]);
  }
  return result;
}

/** Build once per immutable state snapshot and share across all views of that snapshot. */
export function createRuntimeIndex(state: RuntimeState) {
  const placed = (item: { run: Path; placement: string }) => placementKey(item.run, item.placement);
  const calls = byId(state.calls), invocations = byId(state.invocations), executions = byId(state.executions);
  const runs = new Map<string, RuntimeState['runs'][number]>();
  for (const run of state.runs) {
    const key = JSON.stringify(run.path);
    if (!runs.has(key)) runs.set(key, run);
  }
  const activeChildInvocations = new Set<string>(), activeChildExecutions = new Set<string>();
  for (const run of state.runs) if (!run.complete && run.owner !== null) {
    (run.task === null ? activeChildInvocations : activeChildExecutions).add(run.owner);
  }
  const runningInvocationCalls = new Map<string, number>(), runningExecutionCalls = new Map<string, number>();
  for (const call of state.calls) if (call.status === 'running' || call.status === 'fetching' || call.status === 'cancelling') {
    const counts = call.task === null ? runningInvocationCalls : runningExecutionCalls;
    counts.set(call.owner, (counts.get(call.owner) ?? 0) + 1);
  }
  const resultInvocation = (result: RuntimeState['results'][number]) => {
    const call = calls.get(result.producer);
    return call ? (call.task === null ? invocations.get(call.owner) : undefined) : invocations.get(result.producer);
  };
  const resultsByInvocation = group(state.results.filter(r => resultInvocation(r) !== undefined), r => resultInvocation(r)!.id);
  return {
    state, runs, calls, invocations, executions, results: byId(state.results),
    invocationsByPlacement: group(state.invocations, placed),
    executionsByPlacement: group(state.executions, placed),
    resultsByPlacement: group(state.results, placed),
    settledByPlacement: group(state.settled, placed),
    failuresByPlacement: group(state.failures, placed),
    failuresByRun: group(state.failures, f => JSON.stringify(f.run)),
    deliveriesByRun: group(state.deliveries, d => JSON.stringify(d.run)),
    deliveriesByConnection: group(state.deliveries, d => connectionKey(d.run, d.connection)),
    callsByOwner: group(state.calls, c => ownerKey(c.owner, c.task)),
    taskResultsByExecution: group(state.taskResults, r => r.execution),
    childRunsByOwner: group(state.runs.filter(r => r.owner !== null), r => ownerKey(r.owner!, r.task)),
    activeChildInvocations, activeChildExecutions, runningInvocationCalls, runningExecutionCalls, resultsByInvocation,
  };
}

export type RuntimeIndex = ReturnType<typeof createRuntimeIndex>;
