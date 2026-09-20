import { expect, it } from 'vitest';
import { decorateNodes } from '../src/components/canvas-nodes';
import type { CanvasNode } from '../src/components/canvas-nodes';
import type { NodeIOData } from '../src/lib/node-io';

const node = (id: string): CanvasNode => ({ id, type: 'workflow', position: { x: 0, y: 0 }, data: { definition: { id, kind: { type: 'collect' }, inputs: [], outputs: [] }, eventCount: 0 } });
const io: NodeIOData = { inputs: [], outputs: [{ port: { name: 'out', kind: 'plain' }, connections: [], items: [{ id: 'result', instance: 'instance', sequence: 1, available: true, value: { text: 'same' } }] }] };

it('retains unchanged node objects across transport snapshots and updates only affected nodes', () => {
  const nodes = [node('a'), node('b')];
  const options = { presentations: {}, eventCounts: { a: 1, b: 0 }, nodeIO: { a: io } };
  const first = decorateNodes(nodes, [], options);
  const second = decorateNodes(nodes, first, { ...options, nodeIO: structuredClone(options.nodeIO) });
  expect(second[0]).toBe(first[0]);
  expect(second[1]).toBe(first[1]);
  const selected = decorateNodes(nodes, second, { ...options, selectedNode: 'a' });
  expect(selected[0]).not.toBe(second[0]);
  expect(selected[1]).toBe(second[1]);
  const moved = decorateNodes([{ ...nodes[0]!, position: { x: 30, y: 50 } }, nodes[1]!], first, options);
  expect(moved[0]?.position).toEqual({ x: 30, y: 50 });
  expect(moved[1]).toBe(first[1]);
});
