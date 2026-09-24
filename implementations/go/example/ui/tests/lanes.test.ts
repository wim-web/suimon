import { expect, it } from 'vitest';
import type { RunView, Scenario } from '../src/api';
import { latestRun, runKey, timelineLanes } from '../src/lanes';

// timelineLanes reads the id, title and compare of a scenario, and the unit, spans and times of a run.
const scenario = (id: string, compare?: string) => ({ id, title: id, description: '', compare }) as Scenario;
const scenarios = [scenario('stream', 'batch'), scenario('batch', 'stream'), scenario('merge')];
const run = (id: string, unitMs: number) => ({ id, unitMs, elapsedMs: 7 * unitMs, done: true,
  spans: [{ function: 'produce', detail: id, startMs: 0, endMs: 5 * unitMs, marks: [], outcome: 'ok' }] }) as unknown as RunView;
const runs = { [runKey('stream', 600)]: run('stream@600', 600), [runKey('batch', 600)]: run('batch@600', 600), [runKey('batch', 200)]: run('batch@200', 200) };
/** Each lane as [scenario, unit, the run it shows]. */
const lanes = (id: string, latest: Record<string, number>, unit: number) =>
  timelineLanes(scenarios, scenarios.find(s => s.id === id)!, runs, latest, unit).map(l => [l.key, l.unitMs, l.run?.spans[0]?.detail ?? null]);

it('compares the latest run of the scenario with the run of the other scenario that has the same unit', () => {
  const latest = { stream: 600, batch: 200 };
  expect(latestRun(runs, latest, 'batch')?.id).toBe('batch@200');
  // Batch last ran with 200ms, and Stream never did; the chosen unit is for the next run.
  expect(lanes('batch', latest, 1000)).toEqual([['stream', 200, null], ['batch', 200, 'batch@200']]);
  // Stream last ran with 600ms, as Batch did before its latest run.
  expect(lanes('stream', latest, 1000)).toEqual([['stream', 600, 'stream@600'], ['batch', 600, 'batch@600']]);
});

it('shows the runs with the chosen unit before the scenario has run', () => {
  expect(latestRun(runs, { batch: 200 }, 'stream')).toBeUndefined();
  expect(lanes('stream', { batch: 200 }, 600)).toEqual([['stream', 600, null], ['batch', 600, 'batch@600']]);
  expect(lanes('stream', { batch: 200 }, 200)).toEqual([['stream', 200, null], ['batch', 200, 'batch@200']]);
  expect(lanes('merge', {}, 1000)).toEqual([['merge', 1000, null]]);
});
