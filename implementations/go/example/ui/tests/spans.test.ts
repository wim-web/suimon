import { expect, it } from 'vitest';
import type { Span } from '../src/api';
import { firstResult, firstStart, formatMs, packSpans, ticks } from '../src/spans';

const span = (fn: string, detail: string, startMs: number, endMs: number | null): Span => ({ function: fn, detail, startMs, endMs, marks: [], outcome: endMs === null ? 'running' : 'ok' });

it('packs overlapping spans of a function into separate rows, and reuses a row once it is free', () => {
  const spans = [span('process', 'b', 50, 150), span('produce', '5 items', 0, 250), span('process', 'a', 10, 60), span('process', 'c', 60, 100)];
  const groups = packSpans(spans, 300);
  expect(groups.map(g => g.function)).toEqual(['produce', 'process']);
  expect(groups[1]!.rows.map(row => row.map(s => s.detail))).toEqual([['a', 'c'], ['b']]);
});

it('draws a running span up to now', () => {
  const groups = packSpans([span('lookup', 'stuck', 10, null), span('lookup', 'next', 40, 60)], 80);
  expect(groups[0]!.rows).toHaveLength(2);
  expect(packSpans([span('lookup', 'stuck', 10, null), span('lookup', 'next', 40, 60)], 20)[0]!.rows).toHaveLength(1);
});

it('finds the first start of downstream work and its first result', () => {
  const spans = [span('produceAll', '5 items', 0, 250), span('process', 'a', 251, 300), span('process', 'b', 250.5, 310), span('process', 'c', 252, null)];
  expect(firstStart(spans, 'process')).toBe(250.5);
  expect(firstStart(spans, 'missing')).toBeNull();
  // The first result is the first call to return, whichever started first.
  expect(firstResult(spans, 'process')).toBe(300);
  expect(firstResult(spans, 'missing')).toBeNull();
  // A running call has no result yet, and a call that failed or was cancelled has none.
  const unfinished: Span[] = [span('process', 'c', 252, null), { ...span('process', 'd', 251, 260), outcome: 'cancelled' }, { ...span('process', 'e', 251, 270), outcome: 'error' }];
  expect(firstResult(unfinished, 'process')).toBeNull();
  expect(firstResult([...unfinished, ...spans], 'process')).toBe(300);
});

it('chooses round ticks and formats durations', () => {
  expect(ticks(1000)).toEqual([0, 200, 400, 600, 800, 1000]);
  expect(ticks(1234)).toEqual([0, 500, 1000]);
  expect(ticks(1)).toEqual([0, 1]);
  expect(formatMs(52.4)).toBe('52ms');
  expect(formatMs(1500)).toBe('1.50s');
  expect(formatMs(null)).toBe('—');
});
