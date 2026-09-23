import { expect, it } from 'vitest';
import type { RuntimeState } from '../src/types';
import { armOutcome, childRuns, invocationResults, resultSource, runLabel, runOverlay, runTree, taskOutputValue } from '../src/lib/status';
import { program, state } from './helpers';

it('summarizes each placement of the root run', () => {
  const overlay = runOverlay(program('users'), state('users-a'), [])!;
  expect(overlay.run.workflow).toBe('users');
  const perUser = overlay.placements.perUser!;
  expect(perUser.counts).toEqual({ succeeded: 2 });
  expect(perUser.executions).toHaveLength(2);
  expect(perUser.taskCounts).toEqual({ succeeded: 4 });
  expect(perUser.taskOutputs).toEqual({ value: 4 });
  expect(perUser.settled?.outcome).toBe('normal');
  expect(perUser.phase).toBe('settled');
  expect(perUser.results).toBe(2);
  expect(overlay.placements.fetchAllUsers!.results).toBe(2);
  expect(overlay.placements.all!.results).toBe(1);
  expect(overlay.connections).toEqual({ 0: { values: 2, triggers: 0, failed: 0 }, 1: { values: 2, triggers: 0, failed: 0 } });
  expect(runOverlay(program('merge'), state('merge-a'), [])!.connections[2]).toEqual({ values: 0, triggers: 1, failed: 0 });
});

it('nests child runs under the run that called them, through the execution of a task', () => {
  const s = state('users-a');
  const tree = runTree(s);
  expect(tree.map(n => [n.depth, runLabel(n)])).toEqual([[0, 'users'], [1, 'perUser.profile #1 → profileFlow'], [1, 'perUser.profile #2 → profileFlow']]);
  const child = tree[1]!;
  expect(child.owner?.execution?.placement).toBe('perUser');
  expect(childRuns(s, child.run.owner!, 'profile')).toEqual([child.run]);
  const overlay = runOverlay(program('users'), s, child.run.path)!;
  expect(overlay.run.workflow).toBe('profileFlow');
  expect(Object.values(overlay.placements).map(p => [p.placement, p.counts.succeeded, p.settled?.outcome])).toEqual([['fetch', 1, 'normal'], ['format', 1, 'normal']]);
  expect(runOverlay(program('users'), s, ['nope'])).toBeNull();
});

it('distinguishes running, waiting, skipped and failed placements', () => {
  const branch = program('branch');
  const s: RuntimeState = {
    status: 'running', started: true, cancelled: false,
    runs: [{ path: [], workflow: 'shipping', input: null, owner: null, task: null, complete: false }],
    invocations: [
      { id: 'i1', run: [], placement: 'list', trigger: null, input: null, status: 'active', arm: null },
      { id: 'i2', run: [], placement: 'paid', trigger: 'r1', input: 'v1', status: 'failed', arm: null },
      { id: 'i3', run: [], placement: 'paid', trigger: 'r2', input: 'v2', status: 'succeeded', arm: 'unpaid' },
    ],
    calls: [{ id: 'i1', owner: 'i1', task: null, target: { function: { id: 'listOrders' } }, input: null, stream: true, status: 'fetching', yields: 2, timeout: { callMs: 60000, elementMs: 5000 }, policy: 'stop' }],
    executions: [], taskResults: [],
    results: [{ id: 'r1', run: [], placement: 'list', producer: 'i1', arm: null, value: 'v0' }, { id: 'r2', run: [], placement: 'list', producer: 'i1', arm: null, value: 'v0b' }, { id: 'r3', run: [], placement: 'paid', producer: 'i3', arm: 'unpaid', value: 'v2' }],
    deliveries: [{ run: [], connection: 0, source: 'r1', outcome: { value: { v: 'v1' } } }, { run: [], connection: 0, source: 'r2', outcome: 'failed' }],
    settled: [{ run: [], placement: 'ship', outcome: 'skipped', arms: [] }],
    failures: [{ run: [], placement: 'paid', task: null, cause: 'timeout' }],
  };
  const overlay = runOverlay(branch, s, [])!;
  expect(overlay.placements.list).toMatchObject({ phase: 'active', runningCalls: 1, counts: { active: 1 } });
  expect(overlay.placements.paid).toMatchObject({ phase: 'waiting', counts: { failed: 1, succeeded: 1 }, results: 1 });
  expect(overlay.placements.paid!.failures).toEqual([{ run: [], placement: 'paid', task: null, cause: 'timeout' }]);
  expect(overlay.placements.ship).toMatchObject({ phase: 'settled', settled: { outcome: 'skipped' } });
  expect(overlay.placements.receipts!.phase).toBe('idle');
  expect(overlay.connections[0]).toEqual({ values: 1, triggers: 0, failed: 1 });
  expect(armOutcome({ run: [], placement: 'paid', outcome: 'normal', arms: [['paid', 'skipped'], ['unpaid', 'normal']] }, 'paid')).toBe('skipped');
  expect(armOutcome({ run: [], placement: 'x', outcome: 'failed', arms: [] }, null)).toBe('failed');
});

it('counts task outputs by state and attributes results to their producer', () => {
  const p = program('users');
  const failed = runOverlay(p, state('users-b'), [])!.placements.perUser!;
  expect(failed.taskOutputs).toEqual({ value: 2, failed: 1 });
  expect(failed.failures.map(f => [f.task, f.cause]).sort()).toEqual([['orders', 'timeout'], ['profile', 'transform']]);
  const running = runOverlay(p, state('users-c'), [])!.placements.perUser!;
  expect(running.taskOutputs).toEqual({ value: 2, pending: 1 });
  expect(running.phase).toBe('active');
  expect(running.results).toBe(0);

  const s = state('users-b');
  for (const r of s.results) {
    const source = resultSource(s, r);
    const expected = r.placement === 'perUser' ? 'execution' : r.placement === 'all' ? 'aggregate' : 'call';
    expect(source.kind, r.placement).toBe(expected);
    if (source.kind !== 'aggregate') expect(source.invocation?.placement).toBe(r.placement);
  }
  const perUser = s.invocations.filter(i => i.placement === 'perUser');
  expect(perUser.map(i => invocationResults(s, i).map(r => r.producer))).toEqual(perUser.map(i => [i.id]));
  const fetchAll = s.invocations.find(i => i.placement === 'fetchAllUsers')!;
  expect(invocationResults(s, fetchAll)).toHaveLength(2);
  const m = state('merge-a');
  expect(resultSource(m, m.results.find(r => r.placement === 'widgets')!).kind).toBe('aggregate');
  const page = m.results.find(r => r.placement === 'page')!;
  expect(resultSource(m, page)).toMatchObject({ kind: 'call', invocation: { placement: 'page' } });
  expect(taskOutputValue('pending')).toBeNull();
  expect(taskOutputValue({ value: { v: 'x' } })).toBe('x');
});

it('attributes a sub-workflow call result to the invocation that called the workflow', () => {
  const base = state('users-a');
  const invocation = { id: 'inv', run: [], placement: 'call', trigger: null, input: null, status: 'succeeded' as const, arm: null };
  const s: RuntimeState = { ...base, invocations: [...base.invocations, invocation], results: [...base.results, { id: 'ret', run: [], placement: 'call', producer: 'inv', arm: null, value: 'v' }] };
  const result = s.results.at(-1)!;
  expect(resultSource(s, result)).toEqual({ kind: 'invocation', invocation });
  expect(invocationResults(s, invocation)).toEqual([result]);
});
