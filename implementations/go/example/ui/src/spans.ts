import type { Span } from './api';

/** The spans of one function, packed into rows so that spans in a row never overlap. */
export interface SpanGroup { function: string; rows: Span[][] }

/** The end of a span for drawing; a running span ends now. */
export function spanEnd(span: Span, now: number): number { return span.endMs ?? Math.max(now, span.startMs); }

/** Groups spans by function, in order of first start, and packs each group greedily into rows. */
export function packSpans(spans: readonly Span[], now: number): SpanGroup[] {
  const groups = new Map<string, Span[][]>();
  for (const span of [...spans].sort((a, b) => a.startMs - b.startMs)) {
    let rows = groups.get(span.function);
    if (!rows) { rows = []; groups.set(span.function, rows); }
    const row = rows.find(r => spanEnd(r[r.length - 1]!, now) <= span.startMs);
    if (row) row.push(span); else rows.push([span]);
  }
  return [...groups].map(([fn, rows]) => ({ function: fn, rows }));
}

/** When the first span of the function started, if any did. */
export function firstStart(spans: readonly Span[], fn: string): number | null {
  const starts = spans.filter(s => s.function === fn).map(s => s.startMs);
  return starts.length ? Math.min(...starts) : null;
}

/** When the last span ended, or null while one is running. */
export function lastEnd(spans: readonly Span[]): number | null {
  if (!spans.length || spans.some(s => s.endMs === null)) return null;
  return Math.max(...spans.map(s => s.endMs!));
}

/** Tick positions for an axis of `max` milliseconds: a round step of at least 1ms giving about `count` ticks. */
export function ticks(max: number, count = 6): number[] {
  if (max <= 0) return [0];
  const raw = max / count, power = 10 ** Math.floor(Math.log10(raw));
  const step = Math.max(1, [1, 2, 5, 10].map(m => m * power).find(s => s >= raw)!);
  const out: number[] = [];
  for (let i = 0; i * step <= max; i++) out.push(i * step);
  return out;
}

export function formatMs(ms: number | null): string {
  if (ms === null) return '—';
  return ms >= 1000 ? `${(ms / 1000).toFixed(2)}s` : `${Math.round(ms)}ms`;
}
