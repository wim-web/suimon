import { expect, it } from 'vitest';
import type { JsonObject, TraceEvent, WorkflowSnapshot } from '@suimon/ui-kit';
import { progress } from '../src/progress';

it('shows queued Collect input without treating unevaluated filter input as skipped', () => {
  const data: WorkflowSnapshot = { graph: {
    nodes: [
      { id: 'filter', kind: { type: 'filter' }, inputs: [{ name: 'in', kind: 'stream' }], outputs: [{ name: 'out', kind: 'stream' }] },
      { id: 'collect', kind: { type: 'collect' }, inputs: [{ name: 'in', kind: 'stream' }], outputs: [{ name: 'out', kind: 'plain' }] },
    ],
    edges: [{ src: { node: 'filter', port: 'out' }, dst: { node: 'collect', port: 'in' } }],
    entries: [{ node: 'filter', port: 'in' }], exits: [{ node: 'collect', port: 'out' }],
  }, events: [], values: { item: 'hello' } };
  const event = (sequence: number, type: string, facts: JsonObject, txn: string): TraceEvent => ({ schema_version: 2, sequence, txn, recorded_at: 0, type, op: null, data: facts });
  data.events = [
    event(1, 'token.placed', { edge: '["entry","0"]', token: { item: { id: 'item' } }, by_instance: '$execution' }, 'arrival'),
    event(2, 'transaction.committed', {}, 'arrival'),
  ];
  expect(progress(data).filtered).toBe(0);
  data.events.push(
    event(3, 'instance.created', { id: 'f', node: 'filter', path: [] }, 'filter'),
    event(4, 'token.placed', { edge: '["edge","0"]', token: { item: { id: 'item' } }, by_instance: 'f' }, 'filter'),
    event(5, 'token.consumed', { channel: '["entry","0"]', index: 0, item: 'item', by_instance: 'f' }, 'filter'),
    event(6, 'transaction.committed', {}, 'filter'),
  );
  expect(progress(data)).toMatchObject({ filtered: 0, collectArrived: 1, collectWaiting: 1, collected: false });
});
