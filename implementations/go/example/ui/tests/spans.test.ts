import { expect, it } from 'vitest';
import type { Span } from '../src/api';
import { firstStart, formatMs, lastEnd, packSpans, ticks } from '../src/spans';

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

it('finds the first start of downstream work and the end of user code', () => {
  const spans = [span('produceAll', '5 items', 0, 250), span('process', 'a', 251, 300), span('process', 'b', 250.5, 310)];
  expect(firstStart(spans, 'process')).toBe(250.5);
  expect(firstStart(spans, 'missing')).toBeNull();
  expect(lastEnd(spans)).toBe(310);
  expect(lastEnd([...spans, span('ship', 'x', 1, null)])).toBeNull();
});

it('chooses round ticks and formats durations', () => {
  expect(ticks(1000)).toEqual([0, 200, 400, 600, 800, 1000]);
  expect(ticks(1234)).toEqual([0, 500, 1000]);
  expect(ticks(1)).toEqual([0, 1]);
  expect(formatMs(52.4)).toBe('52ms');
  expect(formatMs(1500)).toBe('1.50s');
  expect(formatMs(null)).toBe('—');
});
