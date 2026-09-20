import { createWorkflowView } from '@suimon/ui-kit';
import type { WorkflowSnapshot, WorkflowView } from '@suimon/ui-kit';

export interface Timings { firstWorker: number | null; total: number | null }
export const emptyTimings = (): Timings => ({ firstWorker: null, total: null });

export function progress(data: WorkflowSnapshot | WorkflowView) {
  const view = 'index' in data ? data : createWorkflowView(data.graph, data.events, data.values);
  const activity = view.activity;
  const ports = (id: string) => view.io[id] ?? { inputs: [], outputs: [] };
  const source = ports('source'), filter = ports('filter'), collect = ports('collect');
  const received = source.outputs.find(port => port.port.name === 'items')?.items.length ?? 0;
  const accepted = filter.outputs[0]?.items.length ?? 0;
  const evaluated = filter.inputs[0]?.items.filter(item => item.consumed === true).length ?? 0;
  return { emitted: received, filtered: evaluated - accepted, active: activity.each?.running ?? 0, complete: activity.each?.succeeded ?? 0,
    sourceDone: (activity.source?.succeeded ?? 0) > 0, collected: (collect.outputs[0]?.items.length ?? 0) > 0,
    collectArrived: collect.inputs[0]?.items.length ?? 0,
    collectWaiting: collect.inputs[0]?.items.filter(item => item.consumed === false).length ?? 0 };
}

export function observeTimings(previous: Timings, state: ReturnType<typeof progress>, elapsed: number, done: boolean): Timings {
  return {
    firstWorker: previous.firstWorker ?? (state.active + state.complete > 0 ? elapsed : null),
    total: done ? elapsed : previous.total,
  };
}
