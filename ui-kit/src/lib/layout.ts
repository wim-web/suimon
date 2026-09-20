import type { Graph, GraphNode } from '../types';

export function nodeDisplayHeight(node: GraphNode) { return 100 + (node.inputs.length + node.outputs.length) * 24; }

export function layoutGraph(graph: Graph): Map<string, { x: number; y: number }> {
  const ranks = new Map(graph.nodes.map(node => [node.id, 0]));
  const incoming = new Map(graph.nodes.map(node => [node.id, 0]));
  const outgoing = new Map(graph.nodes.map(node => [node.id, [] as string[]]));
  for (const edge of graph.edges) {
    if (!incoming.has(edge.dst.node) || !outgoing.has(edge.src.node)) continue;
    incoming.set(edge.dst.node, (incoming.get(edge.dst.node) ?? 0) + 1);
    outgoing.get(edge.src.node)?.push(edge.dst.node);
  }
  const queue = graph.nodes.filter(node => incoming.get(node.id) === 0).map(node => node.id);
  for (let i = 0; i < queue.length; i++) {
    const source = queue[i]!;
    for (const target of outgoing.get(source) ?? []) {
      ranks.set(target, Math.max(ranks.get(target) ?? 0, (ranks.get(source) ?? 0) + 1));
      incoming.set(target, (incoming.get(target) ?? 0) - 1);
      if (incoming.get(target) === 0) queue.push(target);
    }
  }
  const columns = new Map<number, number>();
  const counts = new Map<number, number>();
  const heights = new Map<number, number>();
  for (const node of graph.nodes) {
    const rank = ranks.get(node.id) ?? 0;
    heights.set(rank, Math.max(heights.get(rank) ?? 0, nodeDisplayHeight(node)));
  }
  const offsets = new Map<number, number>();
  let y = 0;
  for (const rank of [...heights.keys()].sort((a, b) => a - b)) { offsets.set(rank, y); y += heights.get(rank)! + 72; }
  for (const rank of ranks.values()) counts.set(rank, (counts.get(rank) ?? 0) + 1);
  return new Map(graph.nodes.map(node => {
    const rank = ranks.get(node.id) ?? 0;
    const column = columns.get(rank) ?? 0;
    columns.set(rank, column + 1);
    return [node.id, { x: (column - ((counts.get(rank) ?? 1) - 1) / 2) * 320, y: offsets.get(rank) ?? 0 }];
  }));
}
