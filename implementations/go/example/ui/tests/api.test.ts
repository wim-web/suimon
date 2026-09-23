import { readFileSync } from 'node:fs';
import { expect, it } from 'vitest';
import { applyProgress, parseProgress, parseReport, parseScenarios } from '../src/api';

// branch.progress.json is the response of GET /api/runs/{id} for a finished run of the branch
// scenario, as the Go server wrote it.
const fixture = JSON.parse(readFileSync(new URL('./fixtures/branch.progress.json', import.meta.url), 'utf8')) as Record<string, unknown>;
const program = JSON.parse(readFileSync(new URL('../../programs/branch.json', import.meta.url), 'utf8')) as unknown;

it('parses the scenarios with their programs', () => {
  const [scenario] = parseScenarios([{ id: 'branch', title: 'Branch and Merge', description: 'd', program, input: { id: 'A-1', amount: 1 } }]);
  expect(scenario!.program.workflows[0]!.placements.map(p => p.name)).toEqual(['route', 'review', 'approve', 'decide']);
  expect(scenario!.input).toEqual({ id: 'A-1', amount: 1 });
  expect(() => parseScenarios([{ id: 'x', title: 't', description: 'd', program: {} }])).toThrow(/main/);
});

it('accumulates the records of progress messages and rejects a gap', () => {
  const full = parseProgress(fixture);
  expect(full.done).toBe(true);
  expect(full.state.status).toBe('succeeded');
  expect(full.state.settled.find(s => s.placement === 'review')?.outcome).toBe('skipped');
  const head = parseProgress({ ...fixture, done: false, records: full.records.slice(0, 4) });
  const tail = parseProgress({ ...fixture, offset: 4, records: full.records.slice(4) });
  const view = applyProgress(applyProgress(null, head), tail);
  expect(view.lines).toEqual(full.records);
  expect(view.records.length).toBe(full.records.length);
  expect(view.done).toBe(true);
  expect(() => applyProgress(applyProgress(null, head), { ...tail, offset: 5 })).toThrow(/record 5/);
  // A new run starts over.
  expect(applyProgress(view, { ...head, id: 'other' }).lines).toHaveLength(4);
});

it('parses a report', () => {
  const report = parseReport({ status: 'failed', outputs: { collect: [1] }, endpoints: { collect: 'normal' }, failures: [{ run: [], placement: 'lookup', cause: 'timeout', error: 'suimon: timed out' }] });
  expect(report.failures[0]).toEqual({ run: [], placement: 'lookup', cause: 'timeout', error: 'suimon: timed out' });
  expect(() => parseReport({ status: 'x', outputs: {}, endpoints: { a: 1 }, failures: [] })).toThrow(/endpoints/);
});
