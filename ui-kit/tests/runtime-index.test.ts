import { expect, it } from 'vitest';
import { createRuntimeIndex, ownerKey, placementKey } from '../src/lib/runtime-index';
import { recordRelation } from '../src/lib/records';
import { childRuns, findInvocation, findRun, invocationResults, runOverlay, runTree } from '../src/lib/status';
import { valueIndex } from '../src/lib/values';
import { definition as largeDefinition, largeRun } from '../bench/data';
import { definition, state } from './helpers';

it('matches fixture expectations and direct scans across immutable snapshots', () => {
  for (const fixture of ['users-a', 'users-b', 'users-c', 'branch-a', 'merge-a']) {
    const s = state(fixture), d = definition(fixture.split('-')[0]!), index = createRuntimeIndex(s);
    const sameRun = (left: string[], right: string[]) => JSON.stringify(left) === JSON.stringify(right);
    const tree = runTree(s, index);
    expect(tree.map(node => node.run.path)).toEqual(s.runs.map(run => run.path));
    expect(tree.map(node => [node.run.workflow, node.depth, node.ordinal, node.owner?.task ?? null]))
      .toEqual(fixture.startsWith('users')
        ? [['users', 0, 1, null], ['profileFlow', 1, 1, 'profile'], ['profileFlow', 1, 2, 'profile']]
        : [[fixture === 'branch-a' ? 'shipping' : 'dashboard', 0, 1, null]]);

    // These member positions are expectations for the recorded fixtures, not another
    // call to valueIndex with its default (identical) index implementation.
    const output = (i: number) => {
      const value = s.taskResults[i]!.output;
      if (typeof value !== 'object') throw new Error(`expected transformed output ${i}`);
      return value.value.v;
    };
    const delivered = (i: number) => {
      const value = s.deliveries[i]!.outcome;
      if (typeof value !== 'object') throw new Error(`expected delivered value ${i}`);
      return value.value.v;
    };
    const list = (result: number, items: string[]): [string, string[]] => [s.results[result]!.value, items];
    const expectedLists = fixture === 'users-a' ? [list(6, [output(1), output(2)]), list(7, [output(0), output(3)]), list(8, [delivered(4), delivered(5)])]
      : fixture === 'users-b' ? [list(6, []), list(7, [output(0), output(2)]), list(8, [delivered(4), delivered(5)])]
      : fixture === 'branch-a' ? [list(6, [delivered(3), delivered(5)])]
      : fixture === 'merge-a' ? [list(3, [delivered(3), delivered(0)])] : [];
    expect([...valueIndex(d, s, {}, index).lists], fixture).toEqual(expectedLists);

    for (const run of s.runs) {
      expect(findRun(s, run.path, index)).toBe(run);
      const overlay = runOverlay(d, s, run.path, index)!;
      expect(overlay.run).toBe(run);
      const workflow = d.workflows.find(w => w.id === run.workflow)!;
      expect(Object.keys(overlay.placements)).toEqual(workflow.placements.map(p => p.name));
      for (const placement of workflow.placements) {
        const at = (item: { run: string[]; placement: string }) => sameRun(item.run, run.path) && item.placement === placement.name;
        expect(overlay.placements[placement.name]).toMatchObject({
          invocations: s.invocations.filter(at), executions: s.executions.filter(at),
          results: s.results.filter(at).length, failures: s.failures.filter(at),
        });
      }
      if (run.owner) expect(childRuns(s, run.owner, run.task, index)).toEqual(childRuns(s, run.owner, run.task));
    }
    for (const inv of s.invocations) {
      expect(findInvocation(s, inv.id, index)).toBe(inv);
      // Scan the raw producer links without calling another indexed accessor.
      const directCalls = s.calls.filter(call => call.owner === inv.id && call.task === null).map(call => call.id);
      const expected = s.results.filter(result => sameRun(result.run, inv.run) && result.placement === inv.placement
        && (directCalls.includes(result.producer) || (result.producer === inv.id && !s.calls.some(call => call.id === result.producer))));
      expect(invocationResults(s, inv, index)).toEqual(expected);
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
