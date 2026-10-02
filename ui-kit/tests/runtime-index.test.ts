import { expect, it } from 'vitest';
import { createRuntimeIndex, ownerKey, placementKey } from '../src/lib/runtime-index';
import { recordRelation } from '../src/lib/records';
import { childRuns, findInvocation, findRun, invocationResults, runOverlay, runTree } from '../src/lib/status';
import { valueIndex } from '../src/lib/values';
import { definition as largeDefinition, largeRun } from '../bench/data';
import { definition, state } from './helpers';

it('keeps lookups, call ownership, list members and run order consistent across snapshots', () => {
  for (const fixture of ['users-a', 'users-b', 'users-c', 'branch-a', 'merge-a']) {
    const s = state(fixture), d = definition(fixture.split('-')[0]!), index = createRuntimeIndex(s);
    expect(runTree(s, index)).toEqual(runTree(s));
    expect(valueIndex(d, s, {}, index)).toEqual(valueIndex(d, s));
    for (const run of s.runs) {
      expect(findRun(s, run.path, index)).toBe(run);
      expect(runOverlay(d, s, run.path, index)).toEqual(runOverlay(d, s, run.path));
      if (run.owner) expect(childRuns(s, run.owner, run.task, index)).toEqual(childRuns(s, run.owner, run.task));
    }
    for (const inv of s.invocations) {
      expect(findInvocation(s, inv.id, index)).toBe(inv);
      expect(invocationResults(s, inv, index)).toEqual(invocationResults(s, inv));
    }
  }
  const a = state('users-a'), b = structuredClone(a);
  b.invocations[0]!.status = 'active';
  const ai = createRuntimeIndex(a), bi = createRuntimeIndex(b);
  expect(runOverlay(definition('users'), a, [], ai)!.placements.fetchAllUsers!.counts).toEqual({ succeeded: 1 });
  expect(runOverlay(definition('users'), b, [], bi)!.placements.fetchAllUsers!.counts).toEqual({ active: 1 });
});

it('does not conflate opaque paths, empty task names, separators or prototype names', () => {
  expect(new Set([placementKey(['a', 'b'], '__proto__'), placementKey(['a,b'], '__proto__'), placementKey([], 'constructor')]).size).toBe(3);
  expect(new Set([ownerKey('a', null), ownerKey('a', ''), ownerKey('a\u0000b', 'c'), ownerKey('a', 'b\u0000c')]).size).toBe(4);
  const { state: s } = largeRun(1);
  s.invocations[0]!.id = '';
  s.calls[0]!.owner = '';
  s.calls[0]!.task = '';
  const index = createRuntimeIndex(s);
  expect(invocationResults(s, s.invocations[0]!, index)).toEqual([]); // A task call is not its owner's direct result.
});

it('resolves a large record batch with linear identifier reads, including building the index', () => {
  const count = 10_000, { state: s, records } = largeRun(count);
  let reads = 0;
  for (const item of [...s.invocations, ...s.calls]) {
    const id = item.id;
    Object.defineProperty(item, 'id', { get: () => { reads++; return id; } });
  }
  const index = createRuntimeIndex(s);
  for (const record of records) if ('op' in record) expect(recordRelation(record.op, largeDefinition, s, index)).toEqual({ run: [], placement: 'work' });
  expect(reads).toBeLessThan(count * 30);
});
