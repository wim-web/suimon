import { describe, expect, it } from 'vitest';
import { parseOutputs, readRunFrames } from '../src/api';

const graph = { nodes: [], edges: [], entries: [], exits: [] };
const frame = (done: boolean) => ({ ...done ? { outputs: [] } : { graph }, event_offset: 0, events: [], values: done ? {} : { input: '日本語' }, elapsed_ms: done ? 500 : 0, done });
const committed = (sequence: number) => ({ schema_version: 2, sequence, txn: `tx:${sequence}`, recorded_at: 0, type: 'transaction.committed', op: null, data: {} });
const response = (...frames: unknown[]) => new Response(frames.map(frame => JSON.stringify(frame)).join('\n'));
async function collect(response: Response) { const frames = []; for await (const value of readRunFrames(response)) frames.push(value); return frames; }

describe('live run transport', () => {
  it('decodes JSON and multibyte UTF-8 split across arbitrary network chunks', async () => {
    const bytes = new TextEncoder().encode(JSON.stringify(frame(false)) + '\n' + JSON.stringify(frame(true)));
    const stream = new ReadableStream<Uint8Array>({ start(controller) {
      for (let i = 0; i < bytes.length; i++) controller.enqueue(bytes.slice(i, i + 1));
      controller.close();
    } });
    const frames = await collect(new Response(stream));
    expect(frames.map(frame => frame.done)).toEqual([false, true]);
    expect(frames[1]?.snapshot.values?.input).toBe('日本語');
  });
  it('does not turn an interrupted connection into a successful execution', async () => {
    await expect(collect(new Response(JSON.stringify(frame(false)) + '\n'))).rejects.toThrow('接続が終了');
  });
  it('rejects invalid progress and surfaces HTTP errors', async () => {
    await expect(collect(response({ ...frame(true), graph, elapsed_ms: 'soon' }))).rejects.toThrow('progress');
    await expect(collect(new Response('invalid scenario', { status: 400 }))).rejects.toThrow('invalid scenario');
  });
  it('keeps every exit, item and falsy value', async () => {
    const outputs = [
      { port: { node: 'a', port: 'out' }, items: [{ id: 'one', value: 0 }, { id: 'two', value: '' }] },
      { port: { node: 'b', port: 'out' }, items: [{ id: 'three', value: null }, { id: 'four', value: false }] },
    ];
    const frames = await collect(response({ ...frame(true), graph, outputs }));
    expect(frames[0]?.outputs).toEqual(outputs);
  });
  it.each([null, {}, [{ port: 'bad', items: [] }], [{ port: { node: 'a', port: 'out' }, items: [{}] }], [{ port: { node: 'a', port: 'out' }, items: [{ id: 'x' }] }]])('rejects malformed outputs: %j', outputs => {
    expect(() => parseOutputs(outputs)).toThrow();
  });
  it('rejects non-JSON output values', () => {
    for (const value of [undefined, Infinity, NaN, () => null]) expect(() => parseOutputs([{ port: { node: 'a', port: 'out' }, items: [{ id: 'x', value }] }])).toThrow();
  });
  it('appends deltas while preserving earlier snapshots and parsed event identities', async () => {
    const frames = await collect(response(
      { ...frame(false), events: [committed(1)] },
      { event_offset: 1, events: [committed(2)], values: { output: false }, elapsed_ms: 100, done: false },
      { ...frame(true), event_offset: 2 },
    ));
    expect(frames.map(frame => frame.snapshot.events.length)).toEqual([1, 2, 2]);
    expect(frames[1]!.snapshot.events[0]).toBe(frames[0]!.snapshot.events[0]);
    expect(frames[1]!.snapshot.graph).toBe(frames[0]!.snapshot.graph);
    expect(frames[2]!.snapshot.events).toBe(frames[1]!.snapshot.events);
    expect(frames[0]!.snapshot.values).toEqual({ input: '日本語' });
    expect(frames[2]!.snapshot.values).toEqual({ input: '日本語', output: false });
    // Readers never share the accumulator between executions.
    expect((await collect(response({ ...frame(true), graph })))[0]!.snapshot.events).toEqual([]);
  });
  it.each([
    { event_offset: -1 }, { event_offset: 2 }, { event_offset: 0 }, { event_offset: 1.5 }, { event_offset: Number.MAX_SAFE_INTEGER + 1 },
    { events: [committed(1)] }, { events: [committed(3)] }, { events: [committed(2), committed(4)] },
  ])('rejects missing, repeated or out-of-order deltas: %j', invalid => {
    return expect(collect(response({ ...frame(false), events: [committed(1)] }, { ...frame(true), event_offset: 1, ...invalid }))).rejects.toThrow(/offset|sequence/);
  });
  it('rejects a delta without the initial graph or a repeated graph', async () => {
    await expect(collect(response(frame(true)))).rejects.toThrow('graph');
    await expect(collect(response(frame(false), { ...frame(true), graph }))).rejects.toThrow('Graph');
  });
  it('rejects invalid or repeated values and uncommitted event suffixes', async () => {
    await expect(collect(response(frame(false), { ...frame(true), values: { input: 'overwritten' } }))).rejects.toThrow('already received');
    await expect(collect(response({ ...frame(true), graph, values: null }))).rejects.toThrow('values');
    await expect(collect(response({ ...frame(true), graph, events: [{ ...committed(1), type: 'token.placed' }] }))).rejects.toThrow('uncommitted');
    await expect(collect(response({ ...frame(true), graph, events: [{ ...committed(1), schema_version: 1 }] }))).rejects.toThrow('schema');
  });
  it('rejects early outcomes, decreasing elapsed time, and records after completion', async () => {
    await expect(collect(response({ ...frame(false), outputs: [] }))).rejects.toThrow('before the final');
    await expect(collect(response({ ...frame(false), elapsed_ms: 600 }, frame(true)))).rejects.toThrow('backwards');
    await expect(collect(response({ ...frame(true), graph }, frame(true)))).rejects.toThrow('after the final');
    await expect(collect(response({ ...frame(true), graph, outputs: undefined }))).rejects.toThrow('outputs');
  });
  it('delivers execution failures in the final delta without discarding prior history', async () => {
    const frames = await collect(response({ ...frame(false), events: [committed(1)] }, { ...frame(true), event_offset: 1, error: 'worker failed' }));
    expect(frames[1]!.error).toBe('worker failed');
    expect(frames[1]!.snapshot.events).toHaveLength(1);
  });
});
