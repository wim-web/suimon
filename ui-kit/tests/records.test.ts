import { expect, it } from 'vitest';
import { filterTransitions, recordRelation, recordTransitions, recordValues, relationLabel } from '../src/lib/records';
import type { RecordRelation } from '../src/lib/records';
import type { Op } from '../src/types';
import { resolveValue, valueIndex, previewValue } from '../src/lib/values';
import { parseRecordLog, parseRecords } from '../src/lib/parse';
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
  expect(c.at(-1)).toMatchObject({ seq: 79, committed: false, op: { type: 'taskOutput' } });
  expect(c.filter(t => !t.committed)).toHaveLength(1);
  expect(Object.keys(recordValues(c))).not.toContain(Object.keys(c.at(-1)!.values)[0]);
  expect(Object.keys(recordValues(c, true))).toContain(Object.keys(c.at(-1)!.values)[0]);
});

it('relates every op of a completed run to a run and placement through the state', () => {
  const p = definition('users'), s = state('users-a');
  const transitions = recordTransitions(records('users-a'));
  const relations = new Map(transitions.map(t => [t.seq, recordRelation(t.op, p, s)]));
  const byType = (type: string) => transitions.filter(t => t.op.type === type).map(t => relations.get(t.seq)!);
  const child = s.runs[1]!.path, secondChild = s.runs[2]!.path;
  const source = { run: [], placement: 'fetchAllUsers' }, perUser = { run: [], placement: 'perUser' };
  const profile = { ...perUser, task: 'profile' }, orders = { ...perUser, task: 'orders' };
  const fetch = { run: child, placement: 'fetch' }, format = { run: child, placement: 'format' };
  const secondFetch = { run: secondChild, placement: 'fetch' }, secondFormat = { run: secondChild, placement: 'format' };
  const all = { run: [], placement: 'all' };
  const expected: Record<string, RecordRelation[]> = {
    start: [source],
    invoke: [source, perUser, perUser, fetch, secondFetch, format, secondFormat],
    fetch: [source, source, source], yielded: [source, source], ended: [source],
    deliver: [
      { ...perUser, source: 'fetchAllUsers', connection: 0 }, { ...perUser, source: 'fetchAllUsers', connection: 0 },
      { ...format, source: 'fetch', connection: 0 }, { ...secondFormat, source: 'fetch', connection: 0 },
      { ...all, source: 'perUser', connection: 1 }, { ...all, source: 'perUser', connection: 1 },
    ],
    taskInput: [profile, orders, profile, orders], beginTask: [profile, orders, orders, profile],
    returned: [fetch, orders, orders, secondFetch, format, secondFormat],
    taskOutput: [orders, orders, profile, profile],
    settle: [fetch, source, format, secondFetch, secondFormat, perUser, all],
    closeRun: [{ ...profile, childRun: child }, { ...profile, childRun: secondChild }],
    closeExecution: [perUser, perUser], conclude: [{ run: [] }],
  };
  expect([...new Set(transitions.map(t => t.op.type))].sort()).toEqual(Object.keys(expected).sort());
  for (const [type, expectedRelations] of Object.entries(expected)) expect(byType(type), type).toEqual(expectedRelations);
  expect(relationLabel(byType('deliver')[0])).toBe('fetchAllUsers → perUser');
  // Without the state only ops that name their run and placement are related.
  const bare = recordRelation(transitions.find(t => t.op.type === 'fetch')!.op, p);
  expect(bare).toEqual({});
  expect(relationLabel(bare)).toBe('—');
  expect(recordRelation({ type: 'deliver', run: [], connection: 1, source: 'x' }, p)).toMatchObject({ placement: 'all', source: 'perUser' });

  const inChild = filterTransitions(transitions, relations, { run: child });
  expect(inChild.map(t => t.op.type)).toContain('closeRun');
  expect(inChild.filter(t => t.op.type === 'invoke')).toHaveLength(2);
  const formatRecords = filterTransitions(transitions, relations, { run: child, placement: 'format' });
  expect(formatRecords.map(t => [t.seq, t.op.type])).toEqual([[47, 'deliver'], [63, 'invoke'], [65, 'returned'], [67, 'settle']]);
  expect(filterTransitions(transitions, relations, { run: [], placement: 'format' })).toEqual([]);
  expect(filterTransitions(transitions, relations, { uncommittedOnly: true })).toEqual([]);
});

it('relates failure reports to their actual call, execution and connection owners', () => {
  const p = definition('users'), s = state('users-b');
  const failures = recordTransitions(records('users-b')).filter(t => ['timedOut', 'terminated', 'taskOutputFailed'].includes(t.op.type));
  expect(failures.map(t => t.op.type)).toEqual(['timedOut', 'terminated', 'taskOutputFailed']);
  expect(failures.map(t => recordRelation(t.op, p, s))).toEqual([
    { run: [], placement: 'perUser', task: 'orders' },
    { run: [], placement: 'perUser', task: 'orders' },
    { run: [], placement: 'perUser', task: 'profile' },
  ]);

  // The resolver reads identities from a snapshot; report acceptance belongs to the
  // engine. Exercise the other failure op variants with these known owner links.
  const timeout = failures[0]!.op;
  if (timeout.type !== 'timedOut') throw new Error('expected the recorded orders timeout');
  const childInvocation = s.invocations.find(invocation => invocation.placement === 'fetch' && invocation.run[0] === s.runs[1]!.path[0])!;
  const childCall = s.calls.find(call => call.owner === childInvocation.id)!;
  expect(childCall).toBeDefined();
  expect(childCall.target).toEqual({ function: { id: 'fetchProfile' } });
  const cases: [Op, RecordRelation][] = [
    [{ type: 'failed', call: timeout.call }, { run: [], placement: 'perUser', task: 'orders' }],
    [{ type: 'lost', call: childCall.id }, { run: s.runs[1]!.path, placement: 'fetch' }],
    [{ type: 'taskInputFailed', execution: s.executions[0]!.id, task: 'profile' }, { run: [], placement: 'perUser', task: 'profile' }],
    [{ type: 'transformFailed', run: s.runs[1]!.path, connection: 0, source: 'unknown' }, { run: s.runs[1]!.path, placement: 'format', source: 'fetch', connection: 0 }],
    [{ type: 'failed', call: 'unknown' }, {}],
    [{ type: 'cancel' }, { run: [] }],
  ];
  for (const [op, expected] of cases) expect(recordRelation(op, p, s), op.type).toEqual(expected);
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
  expect(list.kind === 'list' && list.items.map(i => i.kind)).toEqual(['payload', 'payload']);
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
