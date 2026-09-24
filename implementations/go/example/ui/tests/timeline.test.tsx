import { renderToStaticMarkup } from 'react-dom/server';
import { expect, it } from 'vitest';
import type { Span } from '../src/api';
import { Timeline } from '../src/Timeline';
import type { TimelineLane, TimelineRun } from '../src/Timeline';

const span = (fn: string, detail: string, startMs: number, endMs: number | null, marks: number[] = []): Span =>
  ({ function: fn, detail, startMs, endMs, marks, outcome: endMs === null ? 'running' : 'ok' });

/** The text of each lane header. */
const headers = (html: string) => [...html.matchAll(/<div class="app-lane-header">(.*?)<\/div>/g)].map(m => m[1]!.replace(/<[^>]+>/g, ' ').replace(/\s+/g, ' ').trim());
const lane = (key: string, label: string, run: TimelineRun | null): TimelineLane => ({ key, label, unitMs: 100, run });

it('marks the first downstream start in each lane, and shows a lane that has not run', () => {
  const html = renderToStaticMarkup(<Timeline highlight="process" lanes={[
    { key: 'stream', label: 'Stream', unitMs: 50, run: { label: 'Stream', elapsedMs: 152, done: true, spans: [
      span('produce', '2 items', 0, 100, [50, 100]),
      span('process', 'alpha', 51, 151),
    ] } },
    { key: 'batch', label: 'Batch', unitMs: 50, run: null },
  ]} />);
  // Both lanes are for runs with the same unit.
  expect(html.match(/unit <b>50ms<\/b>/g)).toHaveLength(2);
  expect(html).toContain('first process at <b>51ms</b>');
  expect(html).toContain('not run yet');
  expect(html.match(/class="app-mark"/g)).toHaveLength(2);
  // The marker runs through every row of the lane.
  expect(html.match(/class="app-marker"/g)).toHaveLength(2);
});

it('compares when downstream work starts, when the first result appears and the total time of the runs', () => {
  // One unit is 100ms: fetching takes a unit per item, and processing alpha 3 units, bravo 1 and charlie 0.5.
  const stream: TimelineRun = { label: 'Stream', elapsedMs: 401, done: true, spans: [
    span('produce', '3 items', 0, 300, [100, 200, 300]), span('process', 'alpha', 100, 400), span('process', 'bravo', 200, 300), span('process', 'charlie', 300, 350),
  ] };
  const batch: TimelineRun = { label: 'Batch', elapsedMs: 601, done: true, spans: [
    span('produceAll', '3 items', 0, 300), span('split', '3 items', 300, 300, [300, 300, 300]),
    span('process', 'alpha', 300, 600), span('process', 'bravo', 300, 400), span('process', 'charlie', 300, 350),
  ] };
  const html = renderToStaticMarkup(<Timeline highlight="process" lanes={[lane('stream', 'Stream', stream), lane('batch', 'Batch', batch)]} />);
  expect(headers(html)).toEqual([
    'Stream unit 100ms first process at 100ms first result at 300ms total 401ms',
    'Batch unit 100ms first process at 300ms first result at 350ms total 601ms',
  ]);
  // While a run is in progress it has no total, and no result before its first process call returns.
  const running: TimelineRun = { ...batch, elapsedMs: 320, done: false, spans: [
    span('produceAll', '3 items', 0, 300), span('split', '3 items', 300, 300, [300, 300, 300]),
    span('process', 'alpha', 300, null), span('process', 'bravo', 300, null), span('process', 'charlie', 300, null),
  ] };
  expect(headers(renderToStaticMarkup(<Timeline highlight="process" lanes={[lane('stream', 'Stream', stream), lane('batch', 'Batch', running)]} />))[1])
    .toBe('Batch unit 100ms first process at 300ms first result at — running · 320ms');
  // Without a downstream function to compare, a lane gives only the total.
  const merge: TimelineRun = { label: 'Merge', elapsedMs: 301, done: true, spans: [span('loadUser', 'u-1', 0, 100), span('fetch profile', 'u-1', 100, 300)] };
  expect(headers(renderToStaticMarkup(<Timeline lanes={[lane('merge', 'Merge', merge)]} />))).toEqual(['Merge unit 100ms total 301ms']);
});
