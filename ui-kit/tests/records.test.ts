import { expect, it } from 'vitest';
import { filterTransitions, recordRelation, recordTransitions, recordValues, relationLabel } from '../src/lib/records';
import { resolveValue, valueIndex, previewValue } from '../src/lib/values';
import { parseRecordLog, parseRecords } from '../src/lib/parse';
import { runTree } from '../src/lib/status';
import { definition, recordText, records, state } from './helpers';

it('marks an op without its commit as uncommitted', () => {
  const all = recordTransitions(records('users-a'));
  expect(all).toHaveLength(50);
  expect(all.every(t => t.committed)).toBe(true);
  const lines = recordText('users-a').split('\n');
  const torn = recordTransitions(parseRecords(lines.slice(0, 6).join('\n') + '\n'));
  expect(torn.map(t => [t.seq, t.op.type, t.committed])).toEqual([[1, 'start', true], [3, 'invoke', true], [5, 'fetch', false]]);
  expect(Object.keys(recordValues(torn))).toEqual(['5:value5:input']);
  // users-c ends with an op and a tail that would commit it: the op stays uncommitted.
  const c = recordTransitions(parseRecordLog(recordText('users-c')).records);
  expect(c.at(-1)).toMatchObject({ seq: 81, committed: false, op: { type: 'taskOutput' } });
  expect(c.filter(t => !t.committed)).toHaveLength(1);
  expect(Object.keys(recordValues(c))).not.toContain(Object.keys(c.at(-1)!.values)[0]);
  expect(Object.keys(recordValues(c, true))).toContain(Object.keys(c.at(-1)!.values)[0]);
});

it('relates every op of a completed run to a run and placement through the state', () => {
  const p = definition('users'), s = state('users-a');
  const transitions = recordTransitions(records('users-a'));
  const relations = new Map(transitions.map(t => [t.seq, recordRelation(t.op, p, s)]));
  const byType = (type: string) => transitions.filter(t => t.op.type === type).map(t => relations.get(t.seq)!);
  expect(byType('start')).toEqual([{ run: [], placement: 'fetchAllUsers' }]);
  for (const type of ['fetch', 'yielded', 'returned', 'ended', 'taskInput', 'beginTask', 'taskOutput', 'closeExecution', 'closeRun', 'invoke', 'settle'])
    expect(byType(type).every(r => r.placement !== undefined), type).toBe(true);
  expect(byType('deliver')[0]).toEqual({ run: [], placement: 'perUser', source: 'fetchAllUsers', connection: 0 });
  expect(relationLabel(byType('deliver')[0])).toBe('fetchAllUsers → perUser');
  expect(byType('taskInput')[0]).toMatchObject({ run: [], placement: 'perUser', task: 'profile' });
  const child = runTree(s)[1]!.run.path;
  expect(byType('closeRun').find(r => r.childRun?.[0] === child[0])).toMatchObject({ run: [], placement: 'perUser', task: 'profile' });
  const fetch = byType('returned').find(r => r.placement === 'fetch')!;
  expect(fetch.run).toHaveLength(1);
  // Without the state only ops that name their run and placement are related.
  const bare = recordRelation(transitions.find(t => t.op.type === 'fetch')!.op, p);
  expect(bare).toEqual({});
  expect(relationLabel(bare)).toBe('—');
  expect(recordRelation({ type: 'deliver', run: [], connection: 1, source: 'x' }, p)).toMatchObject({ placement: 'all', source: 'perUser' });

  const inChild = filterTransitions(transitions, relations, { run: child });
  expect(inChild.map(t => t.op.type)).toContain('closeRun');
  expect(inChild.filter(t => t.op.type === 'invoke')).toHaveLength(2);
  const format = filterTransitions(transitions, relations, { run: child, placement: 'format' });
  expect(format.length).toBeGreaterThan(0);
  expect(format.every(t => relations.get(t.seq)!.placement === 'format')).toBe(true);
  expect(filterTransitions(transitions, relations, { run: [], placement: 'format' })).toEqual([]);
  expect(filterTransitions(transitions, relations, { uncommittedOnly: true })).toEqual([]);
});

it('shows the payloads of engine-built lists from the records', () => {
  const p = definition('branch'), s = state('branch-a');
  const payloads = recordValues(recordTransitions(records('branch-a')));
  const receipts = s.results.find(r => r.placement === 'receipts')!;
  expect(resolveValue(valueIndex(p, s, payloads), receipts.value)).toEqual({ kind: 'payload', id: receipts.value, payload: receipts.value });
  // Every value a committed state names has a payload in the records.
  for (const name of ['users-a', 'users-b', 'branch-a', 'merge-a']) {
    const known = recordValues(recordTransitions(records(name)));
    const st = state(name);
    const named = [...st.results.map(r => r.value), ...st.taskResults.flatMap(r => typeof r.output === 'object' ? [r.value, r.output.value.v] : [r.value])];
    expect(named.filter(v => !Object.hasOwn(known, v)), name).toEqual([]);
  }
  const branchResult = s.results.find(r => r.placement === 'paid')!;
  expect(resolveValue(valueIndex(p, s, payloads), branchResult.value).kind).toBe('payload');
  expect(resolveValue(valueIndex(p, s, payloads), 'unknown')).toEqual({ kind: 'missing', id: 'unknown' });
});

it('derives the members of engine-built lists from the state when no payload is at hand', () => {
  const p = definition('branch'), s = state('branch-a');
  const payloads = recordValues(recordTransitions(records('branch-a')));
  const receipts = s.results.find(r => r.placement === 'receipts')!;
  delete payloads[receipts.value];
  const list = resolveValue(valueIndex(p, s, payloads), receipts.value);
  expect(list.kind === 'list' && list.items.map(i => i.kind)).toEqual(['payload']);
  expect(previewValue(list)).toMatch(/^\[5:value/);
  const merge = definition('merge'), ms = state('merge-a');
  const widgets = ms.results.find(r => r.placement === 'widgets')!;
  const members = resolveValue(valueIndex(merge, ms), widgets.value);
  expect(members.kind === 'list' && members.items.map(i => i.kind)).toEqual(['missing', 'missing']);
  // Two executions of one concurrency placement: each List result is attributed by its producer.
  const users = definition('users'), ub = state('users-b');
  const index = valueIndex(users, ub);
  const lists = ub.results.filter(r => r.placement === 'perUser').map(r => {
    const value = resolveValue(index, r.value);
    const outputs = ub.taskResults.filter(t => t.execution === r.producer && typeof t.output === 'object');
    return [value.kind === 'list' ? value.items.length : -1, outputs.length];
  });
  expect(lists.sort()).toEqual([[0, 0], [2, 2]]);
});
