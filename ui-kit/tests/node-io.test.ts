import { readFileSync } from 'node:fs';
import { expect, it } from 'vitest';
import { nodeIO, portPreview } from '../src/lib/node-io';
import { parseGraph, parseSnapshot } from '../src/lib/parse';
import type { Graph, GraphNode, JsonObject, TraceEvent } from '../src/types';

const read = (path: string) => readFileSync(new URL(`../../Test/${path}`, import.meta.url), 'utf8');
function fixture(graph: string, trace: string) {
  return parseSnapshot({ graph: JSON.parse(read(`graphs/${graph}.json`)), events: read(`traces/${trace}.jsonl`).trim().split('\n').map(line => JSON.parse(line)) });
}

it('shows each committed input and output from shared Lean trace with its value', () => {
  const data = fixture('minimal', 'minimal');
  const inputID = data.events.find(event => event.type === 'token.consumed')!.data.item as string;
  const io = nodeIO(data.graph, data.graph.nodes[0]!, data.events, { [inputID]: 'hello suimon', result: 'HELLO SUIMON' });
  expect(io.inputs[0]?.port.name).toBe('in');
  expect(io.inputs[0]?.items.map(item => item.value)).toEqual(['hello suimon']);
  expect(io.outputs[0]?.items.map(item => item.value)).toEqual(['HELLO SUIMON']);
  expect(io.inputs[0]?.connections).toEqual(['Workflow input']);
  expect(io.outputs[0]?.connections).toEqual(['Workflow output']);
});

it('does not display uncommitted output as a completed result', () => {
  const data = fixture('minimal', 'minimal');
  const marker = data.events.findIndex(event => event.type === 'transaction.committed' && event.txn === 'txn-3');
  const io = nodeIO(data.graph, data.graph.nodes[0]!, data.events.slice(0, marker), { result: 'not committed' });
  expect(io.inputs[0]?.items).toHaveLength(1);
  expect(io.outputs[0]?.items).toHaveLength(0);
});

it('shows an arriving input before the receiving instance is created', () => {
  const data = fixture('minimal', 'minimal');
  const beforeActivation = data.events.slice(0, 4);
  const inputID = data.events.find(event => event.type === 'token.consumed')!.data.item as string;
  const io = nodeIO(data.graph, data.graph.nodes[0]!, beforeActivation, { [inputID]: 'queued' });
  expect(io.inputs[0]?.items).toMatchObject([{ id: inputID, consumed: false, value: 'queued' }]);
  expect(io.inputs[0]?.items[0]?.instance).toBeUndefined();
  expect(io.outputs[0]?.items).toHaveLength(0);
  expect(io.inputs[0]?.channels).toEqual([{ id: '["entry","0"]', closed: true }]);
  expect(nodeIO(data.graph, data.graph.nodes[0]!, beforeActivation.slice(0, -1)).inputs[0]?.items).toHaveLength(0);
});

it('accumulates Collect input while open and updates consumption without duplicating arrivals', () => {
  const graph = parseGraph(JSON.parse(read('graphs/streaming.json')));
  const collect = graph.nodes.find(node => node.id === 'collect')!;
  const event = (sequence: number, type: string, data: JsonObject, txn = 'tx'): TraceEvent => ({ schema_version: 2, txn, sequence, recorded_at: 0, type, op: null, data });
  const channel = '["edge","1"]';
  const first = [event(1, 'token.placed', { by_instance: 'child', edge: channel, token: { item: { id: 'a' } } }), event(2, 'transaction.committed', {})];
  const values = { a: 'ONE', b: 'TWO', result: ['ONE', 'TWO'] };
  const pending = nodeIO(graph, collect, first, values);
  expect(pending.inputs[0]?.items).toMatchObject([{ id: 'a', value: 'ONE', consumed: false, tokenIndex: 0 }]);
  expect(pending.inputs[0]?.channels?.[0]?.closed).toBe(false);
  expect(pending.outputs[0]?.items).toHaveLength(0);

  const closed = [...first,
    event(3, 'token.placed', { by_instance: 'child', edge: channel, token: { item: { id: 'b' } } }, 'close'),
    event(4, 'token.placed', { by_instance: 'child', edge: channel, token: 'eos' }, 'close'),
    event(5, 'transaction.committed', {}, 'close')];
  const waiting = nodeIO(graph, collect, closed, values);
  expect(waiting.inputs[0]?.items.map(item => item.consumed)).toEqual([false, false]);
  expect(waiting.inputs[0]?.channels?.[0]?.closed).toBe(true);
  expect(waiting.outputs[0]?.items).toHaveLength(0);

  const finished = [...closed,
    event(6, 'instance.created', { id: 'collector', node: 'collect', path: [] }, 'collect'),
    event(7, 'token.placed', { by_instance: 'collector', edge: '["exit","0"]', token: { item: { id: 'result' } } }, 'collect'),
    event(8, 'token.consumed', { by_instance: 'collector', channel, item: 'a', index: 0 }, 'collect'),
    event(9, 'token.consumed', { by_instance: 'collector', channel, item: 'b', index: 1 }, 'collect'),
    event(10, 'transaction.committed', {}, 'collect')];
  const complete = nodeIO(graph, collect, finished, values);
  expect(complete.inputs[0]?.items).toMatchObject([
    { id: 'a', consumed: true, sequence: 1, consumedSequence: 8, instance: 'collector' },
    { id: 'b', consumed: true, sequence: 3, consumedSequence: 9, instance: 'collector' },
  ]);
  expect(complete.inputs[0]?.items).toHaveLength(2);
  expect(complete.outputs[0]?.items[0]?.value).toEqual(['ONE', 'TWO']);
});

it('retains falsy payloads and distinguishes missing values from no recorded data', () => {
  const data = fixture('minimal', 'minimal');
  for (const value of ['', 0, false, null]) {
    const io = nodeIO(data.graph, data.graph.nodes[0]!, data.events, { result: value });
    expect(portPreview(io.outputs[0])).toBe(JSON.stringify(value));
  }
  expect(portPreview(nodeIO(data.graph, data.graph.nodes[0]!, data.events).outputs[0])).toBe('値は未提供');
  expect(portPreview(nodeIO(data.graph, data.graph.nodes[0]!, []).outputs[0])).toBe('未記録');
});

it('separates a loop body from its owner and groups repeated instances without losing values', () => {
  const data = fixture('loop', 'loop-retry');
  const loop = data.graph.nodes[0]!;
  if (!('body' in loop.kind)) throw new Error('expected loop body');
  const body = loop.kind.body;
  const inner = nodeIO(body, body.nodes[0]!, data.events, {}, ['loop']);
  expect(inner.inputs[0]?.items.map(item => item.id)).toEqual(['["input","loop","in"]', 'result-1', 'result-2']);
  expect(inner.outputs[0]?.items.map(item => item.id)).toEqual(['result-1', 'result-2', 'result-3']);
  const outer = nodeIO(data.graph, loop, data.events);
  expect(outer.inputs[0]?.items).toHaveLength(1);
  expect(outer.outputs[0]?.items.map(item => item.id)).toEqual(['result-3']);
  expect(nodeIO(body, body.nodes[0]!, data.events).inputs[0]?.items).toHaveLength(0);
  const waitingForChild = nodeIO(body, body.nodes[0]!, data.events.slice(0, 10), {}, ['loop']);
  expect(waitingForChild.inputs[0]?.items).toHaveLength(1);
  expect(waitingForChild.inputs[0]?.items[0]?.consumed).toBe(false);
});

it('maps multiple input ports by channel, not by equal payloads or event order', () => {
  const template = parseGraph(JSON.parse(read('graphs/minimal.json'))).nodes[0]!;
  const node: GraphNode = { ...template, id: 'join', inputs: [{ name: 'left', kind: 'plain' }, { name: 'right', kind: 'plain' }] };
  const graph: Graph = { nodes: [node], edges: [], entries: [{ node: 'join', port: 'left' }, { node: 'join', port: 'right' }], exits: [{ node: 'join', port: 'out' }, { node: 'join', port: 'out' }] };
  const event = (sequence: number, type: string, data: JsonObject): TraceEvent => ({ schema_version: 2, txn: 'tx', sequence, recorded_at: 0, type, op: null, data });
  const events = [
    event(1, 'instance.created', { id: 'opaque-instance', node: 'join', path: [] }),
    event(2, 'token.consumed', { by_instance: 'opaque-instance', channel: '["entry","1"]', item: 'right-value', index: 0 }),
    event(3, 'token.consumed', { by_instance: 'opaque-instance', channel: '["entry","0"]', item: 'left-value', index: 0 }),
    event(4, 'token.placed', { by_instance: 'opaque-instance', edge: '["exit","0"]', token: { item: { id: 'result' } } }),
    event(5, 'token.placed', { by_instance: 'opaque-instance', edge: '["exit","1"]', token: { item: { id: 'result' } } }),
    event(6, 'transaction.committed', {}),
  ];
  const io = nodeIO(graph, node, events, { 'left-value': 0, 'right-value': 0, result: 0 });
  expect(io.inputs.map(port => [port.port.name, port.items[0]?.id])).toEqual([['left', 'left-value'], ['right', 'right-value']]);
  expect(io.outputs[0]?.items).toHaveLength(1);
});

it('keeps control-node output values and the actual chosen input port', () => {
  const data = fixture('coalesce', 'coalesce');
  const join = data.graph.nodes.find(node => node.id === 'join')!;
  const io = nodeIO(data.graph, join, data.events, { chosen: 'chosen value' });
  expect(io.inputs.flatMap(port => port.items).map(item => item.value)).toEqual(['chosen value']);
  expect(io.outputs.flatMap(port => port.items).map(item => item.value)).toEqual(['chosen value']);
});
