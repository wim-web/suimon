import { readFileSync } from 'node:fs';
import { describe, expect, it } from 'vitest';
import { parseSnapshot } from '../src/lib/parse';
import { eventNode, eventValues, operation, traceIndex } from '../src/lib/trace';
import { layoutGraph } from '../src/lib/layout';
import type { Graph, TraceEvent } from '../src/types';

const fixture = (path: string) => readFileSync(new URL(`../../Test/${path}`, import.meta.url), 'utf8');
const graph: unknown = JSON.parse(fixture('graphs/minimal.json'));
const events: TraceEvent[] = fixture('traces/minimal.jsonl').trim().split('\n').map(line => JSON.parse(line) as TraceEvent);

describe('public trace contract', () => {
  it('uses shared Lean fixtures and distinguishes commands from facts', () => {
    const data = parseSnapshot({ graph, events });
    const index = traceIndex(data.events);
    expect(index.status).toBe('succeeded');
    expect(index.transactions).toHaveLength(5);
    expect(index.transactions.every(tx => tx.committed)).toBe(true);
    const claims = events.filter(event => event.type === 'attempt.started');
    expect(operation(claims[0]!)?.kind).toBe('claim');
    expect(operation(claims[1]!)).toBeNull();
    for (const event of claims) expect(eventNode(event, index.instances)).toBe('work');
    expect(eventNode(events.find(event => event.type === 'attempt.finished' && !event.op)!, index.instances)).toBe('work');
  });
  it('keeps the last committed status when the final transaction is incomplete', () => {
    const index = traceIndex(events.slice(0, -1));
    expect(index.status).toBe('running');
    expect(index.transactions.at(-1)?.committed).toBe(false);
    expect(traceIndex(events.slice(0, 3)).status).toBe('ready');
  });
  it('preserves empty and zero payloads, and distinguishes absent values', () => {
    const complete = events.find(event => operation(event)?.kind === 'complete')!;
    expect(eventValues(complete, { result: '' })).toEqual([{ id: 'result', available: true, value: '' }]);
    expect(eventValues(complete)).toEqual([{ id: 'result', available: false, value: undefined }]);
    const placed = events.find(event => event.type === 'token.placed' && eventValues(event).some(value => value.id === 'result'))!;
    expect(eventValues(placed, { result: 0 })[0]?.value).toBe(0);
  });
  it.each([['loop-retry', 'loop'], ['coalesce', 'coalesce']])('accepts %s fixtures across nested / retry operations', (name, graphName) => {
    const data = parseSnapshot({ graph: JSON.parse(fixture(`graphs/${graphName}.json`)), events: fixture(`traces/${name}.jsonl`).trim().split('\n').map(line => JSON.parse(line)) });
    const index = traceIndex(data.events);
    expect(index.status).toBe('succeeded');
    expect(index.transactions.flatMap(tx => tx.events)).toHaveLength(data.events.length);
    for (const event of data.events) { operation(event); eventNode(event, index.instances); eventValues(event); }
  });
  it('rejects bad versions, unsafe naturals, malformed ports and operations', () => {
    expect(() => parseSnapshot({ graph, events: [{ ...events[0], schema_version: 1 }] })).toThrow(/v2/);
    expect(() => parseSnapshot({ graph, events: [{ ...events[0], recorded_at: 2 ** 53 }] })).toThrow(/safe/);
    expect(() => parseSnapshot({ graph, events: [{ ...events[0], op: {} }] })).toThrow(/operation/);
    expect(() => parseSnapshot({ graph: { nodes: [{ id: 'x', kind: { type: 'leaf' }, inputs: null }], edges: [], entries: [], exits: [] }, events: [] })).toThrow(/node/);
  });
});

it('lays out unordered branching DAGs and disconnected nodes without overlap', () => {
  const source = parseSnapshot({ graph, events }).graph.nodes[0]!;
  const edge = (src: string, dst: string) => ({ src: { node: src, port: 'out' }, dst: { node: dst, port: 'in' } });
  const dag: Graph = { nodes: ['end', 'b', 'a', 'start', 'other'].map(id => ({ ...source, id })), edges: [edge('start', 'a'), edge('start', 'b'), edge('a', 'end'), edge('b', 'end')], entries: [], exits: [] };
  const positions = layoutGraph(dag);
  expect(positions.get('start')!.y).toBeLessThan(positions.get('a')!.y);
  expect(positions.get('a')!.y).toBeLessThan(positions.get('end')!.y);
  expect(positions.get('a')!.y).toBe(positions.get('b')!.y);
  expect(positions.get('a')!.x).not.toBe(positions.get('b')!.x);
  expect(new Set([...positions.values()].map(point => `${point.x},${point.y}`)).size).toBe(5);
});
