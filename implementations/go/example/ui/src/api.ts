import { parseDefinition, parseRecords, parseState } from '@suimon/ui-kit';
import type { Definition, ExecutionRecord, JsonValue, RuntimeState } from '@suimon/ui-kit';

/* The JSON API of the example server (implementations/go/example/server.go). */

export interface Scenario { id: string; title: string; description: string; definition: Definition; input?: JsonValue; compare?: string }
export interface Span { function: string; detail: string; startMs: number; endMs: number | null; marks: number[]; outcome: 'running' | 'ok' | 'error' | 'cancelled' }
/** One progress message: the records from `offset` on, and the state they establish. */
export interface Progress { id: string; scenario: string; state: RuntimeState; offset: number; records: string[]; spans: Span[]; elapsedMs: number; done: boolean; error?: string }
export interface FailureReport { run: string[]; placement: string; task?: string; cause: string; error?: string }
export interface Report { status: string; outputs: Record<string, JsonValue>; endpoints: Record<string, string>; failures: FailureReport[] }

type Obj = Record<string, unknown>;
function object(value: unknown, at: string): Obj {
  if (value === null || typeof value !== 'object' || Array.isArray(value)) throw new TypeError(`${at}: expected an object`);
  return value as Obj;
}
function string(value: unknown, at: string): string {
  if (typeof value !== 'string') throw new TypeError(`${at}: expected a string`);
  return value;
}
function number(value: unknown, at: string): number {
  if (typeof value !== 'number' || !Number.isFinite(value) || value < 0) throw new TypeError(`${at}: expected a non-negative number`);
  return value;
}
function array(value: unknown, at: string): unknown[] {
  if (!Array.isArray(value)) throw new TypeError(`${at}: expected an array`);
  return value;
}
const outcomes = ['running', 'ok', 'error', 'cancelled'] as const;

export function parseScenarios(value: unknown): Scenario[] {
  return array(value, 'scenarios').map((item, i) => {
    const at = `scenarios[${i}]`, o = object(item, at);
    const scenario: Scenario = { id: string(o.id, `${at}.id`), title: string(o.title, `${at}.title`), description: string(o.description, `${at}.description`), definition: parseDefinition(o.definition) };
    if (o.input !== undefined) scenario.input = o.input as JsonValue;
    if (o.compare !== undefined) scenario.compare = string(o.compare, `${at}.compare`);
    return scenario;
  });
}

export function parseSpan(value: unknown, at: string): Span {
  const o = object(value, at);
  const outcome = string(o.outcome, `${at}.outcome`);
  if (!(outcomes as readonly string[]).includes(outcome)) throw new TypeError(`${at}.outcome: unknown outcome ${outcome}`);
  return {
    function: string(o.function, `${at}.function`), detail: string(o.detail, `${at}.detail`), startMs: number(o.startMs, `${at}.startMs`),
    endMs: o.endMs === null ? null : number(o.endMs, `${at}.endMs`),
    marks: o.marks === undefined ? [] : array(o.marks, `${at}.marks`).map((m, j) => number(m, `${at}.marks[${j}]`)),
    outcome: outcome as Span['outcome'],
  };
}

export function parseProgress(value: unknown): Progress {
  const o = object(value, 'progress');
  const progress: Progress = {
    id: string(o.id, 'progress.id'), scenario: string(o.scenario, 'progress.scenario'), state: parseState(o.state),
    offset: number(o.offset, 'progress.offset'), records: array(o.records, 'progress.records').map((r, i) => string(r, `progress.records[${i}]`)),
    spans: array(o.spans, 'progress.spans').map((s, i) => parseSpan(s, `progress.spans[${i}]`)),
    elapsedMs: number(o.elapsedMs, 'progress.elapsedMs'), done: o.done === true,
  };
  if (o.error !== undefined) progress.error = string(o.error, 'progress.error');
  return progress;
}

export function parseReport(value: unknown): Report {
  const o = object(value, 'report');
  return {
    status: string(o.status, 'report.status'),
    outputs: object(o.outputs, 'report.outputs') as Record<string, JsonValue>,
    endpoints: Object.fromEntries(Object.entries(object(o.endpoints, 'report.endpoints')).map(([k, v]) => [k, string(v, `report.endpoints.${k}`)])),
    failures: array(o.failures, 'report.failures').map((f, i) => {
      const at = `report.failures[${i}]`, x = object(f, at);
      const failure: FailureReport = { run: array(x.run, `${at}.run`).map((s, j) => string(s, `${at}.run[${j}]`)), placement: string(x.placement, `${at}.placement`), cause: string(x.cause, `${at}.cause`) };
      if (x.task !== undefined) failure.task = string(x.task, `${at}.task`);
      if (x.error !== undefined) failure.error = string(x.error, `${at}.error`);
      return failure;
    }),
  };
}

/** The accumulated view of one run: every line so far, the header first, and the records after it, parsed. */
export interface RunView { id: string; scenario: string; state: RuntimeState; lines: string[]; records: ExecutionRecord[]; spans: Span[]; elapsedMs: number; done: boolean; error?: string }

/**
 * Applies one progress message. Its records must continue the lines received so far, or start
 * over at offset 0 (a new run, or an event stream that reconnected).
 */
export function applyProgress(previous: RunView | null, p: Progress): RunView {
  const base = previous?.id === p.id && p.offset > 0 ? previous : null;
  const lines = base?.lines ?? [];
  if (p.offset !== lines.length) throw new Error(`progress at record ${p.offset}, but ${lines.length} records were received`);
  const all = p.records.length || !base ? [...lines, ...p.records] : lines;
  // parseRecords checks the header, the first line, and the sequence from 1, so the whole record is parsed again.
  const view: RunView = {
    id: p.id, scenario: p.scenario, state: p.state, lines: all, records: all === lines && base ? base.records : parseRecords(all),
    spans: p.spans, elapsedMs: p.elapsedMs, done: p.done,
  };
  if (p.error !== undefined) view.error = p.error;
  return view;
}

async function json(response: Response): Promise<unknown> {
  if (!response.ok) throw new Error((await response.text()).trim() || `${response.status} ${response.statusText}`);
  return response.json();
}

export async function loadScenarios(signal?: AbortSignal): Promise<Scenario[]> {
  return parseScenarios(await json(await fetch('/api/scenarios', { signal })));
}

export async function startRun(scenario: string, input: JsonValue | undefined): Promise<string> {
  const body = input === undefined ? { scenario } : { scenario, input };
  const o = object(await json(await fetch('/api/runs', { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify(body) })), 'run');
  return string(o.id, 'run.id');
}

export async function loadReport(id: string): Promise<Report> {
  return parseReport(await json(await fetch(`/api/runs/${encodeURIComponent(id)}/report`)));
}

export async function cancelRun(id: string): Promise<void> {
  const response = await fetch(`/api/runs/${encodeURIComponent(id)}/cancel`, { method: 'POST' });
  if (!response.ok) throw new Error(await response.text());
}

/** Follows a run through server-sent events until it is done; returns a function that stops. */
export function followRun(id: string, onProgress: (p: Progress) => void, onError: (error: Error) => void): () => void {
  const source = new EventSource(`/api/runs/${encodeURIComponent(id)}/events`);
  const stop = () => source.close();
  source.onmessage = event => {
    try {
      const p = parseProgress(JSON.parse(event.data as string));
      if (p.done) stop();
      onProgress(p);
    } catch (error) { stop(); onError(error instanceof Error ? error : new Error(String(error))); }
  };
  source.addEventListener('failure', event => { stop(); onError(new Error(String(JSON.parse((event as MessageEvent<string>).data)))); });
  source.onerror = () => { if (source.readyState === EventSource.CLOSED) onError(new Error('the event stream closed')); };
  return stop;
}
