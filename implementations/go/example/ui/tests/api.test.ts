import { readFileSync } from 'node:fs';
import { afterEach, expect, it, vi } from 'vitest';
import { applyProgress, cancelRun, parseProgress, parseReport, parseScenarios, startRun } from '../src/api';

// branch.progress.json is the response of GET /api/runs/{id} for a finished run of the branch
// scenario with a unit of 10ms, as the Go server wrote it: its records start with the header.
const fixture = JSON.parse(readFileSync(new URL('./fixtures/branch.progress.json', import.meta.url), 'utf8')) as Record<string, unknown>;
const definition = JSON.parse(readFileSync(new URL('../../definitions/branch.json', import.meta.url), 'utf8')) as unknown;

it('parses the scenarios with their definitions', () => {
  const [scenario] = parseScenarios([{ id: 'branch', title: 'Branch and Merge', description: 'd', definition, input: { id: 'A-1', amount: 1 } }]);
  expect(scenario!.definition.workflows[0]!.placements.map(p => p.name)).toEqual(['route', 'review', 'approve', 'decide']);
  expect(scenario!.input).toEqual({ id: 'A-1', amount: 1 });
  expect(() => parseScenarios([{ id: 'x', title: 't', description: 'd', definition: {} }])).toThrow(/main/);
});

it('accumulates the records of progress messages and rejects a gap', () => {
  const full = parseProgress(fixture);
  expect(full.done).toBe(true);
  expect(full.unitMs).toBe(10);
  expect(full.state.status).toBe('succeeded');
  expect(full.state.settled.find(s => s.placement === 'review')?.outcome).toBe('skipped');
  const head = parseProgress({ ...fixture, done: false, records: full.records.slice(0, 4) });
  const tail = parseProgress({ ...fixture, offset: 4, records: full.records.slice(4) });
  const view = applyProgress(applyProgress(null, head), tail);
  expect(view.lines).toEqual(full.records);
  // The header holds the definition of the scenario, which the engine validated; the records follow it.
  expect(JSON.parse(full.records[0]!)).toEqual({ definition, validated: true });
  expect(view.records.length).toBe(full.records.length - 1);
  expect(view.records[0]).toMatchObject({ seq: 1, op: { type: 'start' } });
  expect(view.done).toBe(true);
  expect(view.unitMs).toBe(10);
  expect(() => applyProgress(applyProgress(null, head), { ...tail, offset: 5 })).toThrow(/record 5/);
  // A new run starts over.
  expect(applyProgress(view, { ...head, id: 'other' }).lines).toHaveLength(4);
});

it('requires the unit of the run in a progress message', () => {
  expect(() => parseProgress({ ...fixture, unitMs: undefined })).toThrow(/progress\.unitMs/);
});

afterEach(() => { vi.unstubAllGlobals(); });

it('sends the unit and a fresh CSRF capability with each run request', async () => {
  let token = 0;
  const fetch = vi.fn(async (url: string, _init: RequestInit) => url === '/api/csrf'
    ? Response.json({ token: `token-${++token}` })
    : Response.json({ id: 'r1' }, { status: 201 }));
  vi.stubGlobal('fetch', fetch);
  expect(await startRun('stream', { names: ['alpha'] }, 600)).toBe('r1');
  await startRun('merge', undefined, 1000);
  expect(fetch.mock.calls.map(([url]) => url)).toEqual(['/api/csrf', '/api/runs', '/api/csrf', '/api/runs']);
  expect(fetch.mock.calls.filter(([url]) => url === '/api/runs').map(([url, init]) => [
    url, init.method, JSON.parse(init.body as string), new Headers(init.headers).get('X-CSRF-Token'), new Headers(init.headers).get('Content-Type'), init.mode,
  ])).toEqual([
    ['/api/runs', 'POST', { scenario: 'stream', input: { names: ['alpha'] }, unitMs: 600 }, 'token-1', 'application/json', 'same-origin'],
    ['/api/runs', 'POST', { scenario: 'merge', unitMs: 1000 }, 'token-2', 'application/json', 'same-origin'],
  ]);
  expect(fetch.mock.calls.filter(([url]) => url === '/api/csrf').every(([, init]) => init.cache === 'no-store' && init.mode === 'same-origin')).toBe(true);
});

it('protects cancellation even though the POST body is empty', async () => {
  const fetch = vi.fn(async (url: string, _init: RequestInit) => url === '/api/csrf'
    ? Response.json({ token: 'cancel-token' }) : new Response(null, { status: 204 }));
  vi.stubGlobal('fetch', fetch);
  await cancelRun('r1');
  const [url, init] = fetch.mock.calls[1]!;
  expect(url).toBe('/api/runs/r1/cancel');
  expect(init.method).toBe('POST');
  expect(new Headers(init.headers).get('Content-Type')).toBe('application/json');
  expect(new Headers(init.headers).get('X-CSRF-Token')).toBe('cancel-token');
});

it('does not send a write when the CSRF bootstrap fails', async () => {
  const fetch = vi.fn(async () => new Response('unexpected Origin', { status: 403 }));
  vi.stubGlobal('fetch', fetch);
  await expect(startRun('stream', undefined, 600)).rejects.toThrow('unexpected Origin');
  expect(fetch).toHaveBeenCalledTimes(1);
});

it('keeps the WASM transport independent of HTTP capabilities', async () => {
  vi.stubEnv('MODE', 'wasm');
  vi.resetModules();
  const fetch = vi.fn();
  vi.stubGlobal('fetch', fetch);
  const wasm = await import('../src/wasm');
  const request = vi.spyOn(wasm, 'wasmRequest').mockResolvedValue(Response.json({ id: 'r1' }, { status: 201 }));
  try {
    const api = await import('../src/api');
    expect(await api.startRun('stream', undefined, 600)).toBe('r1');
    request.mockResolvedValue(new Response(null, { status: 204 }));
    await api.cancelRun('r1');
    expect(request.mock.calls.map(([path]) => path)).toEqual(['/api/runs', '/api/runs/r1/cancel']);
    expect(fetch).not.toHaveBeenCalled();
  } finally {
    request.mockRestore();
    vi.unstubAllEnvs();
    vi.resetModules();
  }
});

it('parses a report', () => {
  const report = parseReport({ status: 'failed', outputs: { collect: '[1]' }, endpoints: { collect: 'normal' }, failures: [{ run: [], placement: 'lookup', cause: 'timeout', error: 'suimon: timed out' }] });
  expect(report.failures[0]).toEqual({ run: [], placement: 'lookup', cause: 'timeout', error: 'suimon: timed out' });
  expect(() => parseReport({ status: 'x', outputs: {}, endpoints: { a: 1 }, failures: [] })).toThrow(/endpoints/);
});
