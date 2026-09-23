import type { Connection, Placement, Program, ValueType, Workflow } from '../types';
import { deriveKinds, findWorkflow, isEndpoint, isEntry } from './program';
import type { Kind } from './program';

export interface Point { x: number; y: number }
export interface LayoutNode { name: string; placement: Placement; kind: Kind | null; entry: boolean; endpoint: boolean; position: Point; height: number }
/** An edge is one connection; `kind` is the Single/Stream kind of its source's output. */
export interface LayoutEdge { index: number; connection: Connection; kind: Kind | null }
export interface WorkflowLayout {
  workflow: Workflow;
  nodes: LayoutNode[];
  edges: LayoutEdge[];
  /** Where the value passed to run enters, when the workflow takes an input. */
  input?: { type: ValueType; placement: string; position: Point };
}

export const NODE_WIDTH = 280;
const COLUMN = NODE_WIDTH + 64, GAP = 92, ROW = 22;

/** Estimated rendered height of a placement node, used to space ranks before React Flow measures. */
export function placementHeight(placement: Placement): number {
  const node = placement.node;
  const rows = node.type === 'concurrency' ? 1 + node.tasks.length : node.type === 'branch' ? 1 + node.arms.length : 1;
  return 62 + 12 + rows * ROW + 30;
}

/** A layered top-down layout of one workflow; `positions` overrides computed positions by placement name. */
export function layoutWorkflow(program: Program, workflow: Workflow | string, positions: Record<string, Point | undefined> = {}): WorkflowLayout {
  const w = typeof workflow === 'string' ? findWorkflow(program, workflow) : workflow;
  if (!w) throw new TypeError(`unknown workflow ${String(workflow)}`);
  const names = w.placements.map(p => p.name);
  const rank = new Map(names.map(n => [n, 0]));
  const indegree = new Map(names.map(n => [n, 0]));
  const next = new Map(names.map(n => [n, [] as string[]]));
  const previous = new Map(names.map(n => [n, [] as string[]]));
  for (const c of w.connections) {
    if (!rank.has(c.source) || !rank.has(c.target)) continue;
    indegree.set(c.target, indegree.get(c.target)! + 1);
    next.get(c.source)!.push(c.target);
    previous.get(c.target)!.push(c.source);
  }
  const queue = names.filter(n => indegree.get(n) === 0);
  for (let i = 0; i < queue.length; i++) {
    const source = queue[i]!;
    for (const target of next.get(source)!) {
      rank.set(target, Math.max(rank.get(target)!, rank.get(source)! + 1));
      indegree.set(target, indegree.get(target)! - 1);
      if (indegree.get(target) === 0) queue.push(target);
    }
  }
  const layers = new Map<number, string[]>();
  for (const n of names) { const r = rank.get(n)!; layers.set(r, [...layers.get(r) ?? [], n]); }
  const order = [...layers.keys()].sort((a, b) => a - b);
  const column = new Map<string, number>();
  for (const r of order) {
    const layer = layers.get(r)!;
    const center = (n: string) => {
      const from = previous.get(n)!.filter(p => column.has(p));
      return from.length ? from.reduce((sum, p) => sum + column.get(p)!, 0) / from.length : Number.NaN;
    };
    const sorted = layer.map((n, i) => ({ n, i, c: center(n) })).sort((a, b) => (Number.isNaN(a.c) || Number.isNaN(b.c) ? a.i - b.i : a.c - b.c || a.i - b.i));
    sorted.forEach(({ n }, i) => column.set(n, i - (sorted.length - 1) / 2));
  }
  const placements = new Map(w.placements.map(p => [p.name, p]));
  const offset = new Map<number, number>();
  let y = 0;
  for (const r of order) { offset.set(r, y); y += Math.max(...layers.get(r)!.map(n => placementHeight(placements.get(n)!))) + GAP; }
  const kinds = deriveKinds(program, w);
  const nodes: LayoutNode[] = w.placements.map(p => ({
    name: p.name, placement: p, kind: kinds[p.name] ?? null, entry: isEntry(w, p.name), endpoint: isEndpoint(w, p.name), height: placementHeight(p),
    position: positions[p.name] ?? { x: column.get(p.name)! * COLUMN, y: offset.get(rank.get(p.name)!)! },
  }));
  const edges = w.connections.map((connection, index) => ({ index, connection, kind: kinds[connection.source] ?? null }));
  const layout: WorkflowLayout = { workflow: w, nodes, edges };
  const entry = w.input && nodes.find(n => n.name === w.input!.placement);
  if (w.input && entry) layout.input = { type: w.input.type, placement: w.input.placement, position: { x: entry.position.x, y: entry.position.y - 96 } };
  return layout;
}
