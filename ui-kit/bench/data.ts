import type { Definition, ExecutionRecord, RuntimeState } from '../src/types';

// Synthetic calls with small payloads isolate indexing and rendering from transport/JSON costs.
export const definition: Definition = {
  main: 'large-run', functions: [{ id: 'process', output: { single: 'Item' } }], judges: [], transforms: [],
  workflows: [{ id: 'large-run', placements: [{ name: 'work', node: { type: 'function', function: 'process' }, policy: 'continue' }], connections: [] }],
};

export function largeRun(count: number) {
  const state: RuntimeState = {
    status: 'running', started: true, cancelled: false,
    runs: [{ path: [], workflow: 'large-run', input: null, owner: null, task: null, complete: false }],
    invocations: [], calls: [], results: [], deliveries: [], executions: [], taskResults: [], settled: [], failures: [],
  };
  const records: ExecutionRecord[] = [];
  for (let i = 0; i < count; i++) {
    const id = `inv-${i}`, call = `call-${i}`, value = `value-${i}`;
    state.invocations.push({ id, run: [], placement: 'work', trigger: `trigger-${i}`, input: null, status: 'succeeded', arm: null });
    state.calls.push({ id: call, owner: id, task: null, target: { function: { id: 'process' } }, input: null, stream: false, status: 'returned', yields: 0, timeout: { callMs: null, elementMs: null }, policy: 'continue' });
    state.results.push({ id: `result-${i}`, run: [], placement: 'work', producer: call, arm: null, value });
    records.push({ seq: i * 2 + 1, op: { type: 'returned', call, value }, values: { [value]: `{"item":${i}}` } }, { seq: i * 2 + 2, commit: true });
  }
  return { state, records };
}

export const listDefinition: Definition = {
  main: 'large-list', functions: [{ id: 'items', output: { stream: 'Item' } }], judges: [],
  transforms: [{ id: 'item', input: 'Item', output: 'Item' }],
  workflows: [{ id: 'large-list', placements: [
    { name: 'items', node: { type: 'function', function: 'items' }, policy: 'continue' },
    { name: 'collected', node: { type: 'waitStream', element: 'Item' }, policy: 'continue' },
  ], connections: [{ source: 'items', target: 'collected', transform: 'item' }] }],
};

/** A stream collected into one list, shown through the same workbench as the other fixtures. */
export function largeListRun(count: number) {
  const { state, records } = largeRun(0);
  state.status = 'succeeded';
  state.runs[0] = { path: [], workflow: 'large-list', input: null, owner: null, task: null, complete: true };
  state.invocations.push({ id: 'stream', run: [], placement: 'items', trigger: null, input: null, status: 'succeeded', arm: null });
  state.calls.push({ id: 'stream-call', owner: 'stream', task: null, target: { function: { id: 'items' } }, input: null, stream: true, status: 'returned', yields: count, timeout: { callMs: null, elementMs: null }, policy: 'continue' });
  for (let i = 0; i < count; i++) {
    const value = `item-${i}`, result = `result-${i}`;
    state.results.push({ id: result, run: [], placement: 'items', producer: 'stream-call', arm: null, value });
    state.deliveries.push({ run: [], connection: 0, source: result, outcome: { value: { v: value } } });
    records.push({ seq: i * 2 + 1, op: { type: 'yielded', call: 'stream-call', value }, values: { [value]: `{"item":${i}}` } }, { seq: i * 2 + 2, commit: true });
  }
  state.results.push({ id: 'collected-result', run: [], placement: 'collected', producer: 'aggregate', arm: null, value: 'list' });
  state.settled = ['items', 'collected'].map(placement => ({ run: [], placement, outcome: 'normal', arms: [] }));
  return { state, records };
}
