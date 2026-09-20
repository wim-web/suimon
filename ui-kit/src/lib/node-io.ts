import type { Graph, GraphNode, JsonValue, Port, TraceEvent, TraceIndex } from '../types';
import { asTraceIndex, object, operation } from './trace';
import { instanceDefinitionPath, resolveChannel, sameScope } from './routing';
import type { ResolvedChannel } from './routing';
export { instanceDefinitionPath } from './routing';

export interface NodeIOItem {
  id: string; instance?: string; sequence: number; available: boolean; value?: JsonValue;
  channel?: string; tokenIndex?: number; consumed?: boolean; consumedSequence?: number;
}
export interface NodeIOPort { port: Port; connections: string[]; items: NodeIOItem[]; channels?: { id: string; closed: boolean }[] }
export interface NodeIOData { inputs: NodeIOPort[]; outputs: NodeIOPort[] }

function emptyIO(graph: Graph, node: GraphNode): NodeIOData {
  return {
    inputs: node.inputs.map(port => ({ port, items: [], connections: [
      ...graph.edges.filter(edge => edge.dst.node === node.id && edge.dst.port === port.name).map(edge => `${edge.src.node}.${edge.src.port}`),
      ...graph.entries.filter(entry => entry.node === node.id && entry.port === port.name).map(() => 'Workflow input'),
    ] })),
    outputs: node.outputs.map(port => ({ port, items: [], connections: [
      ...graph.edges.filter(edge => edge.src.node === node.id && edge.src.port === port.name).map(edge => `${edge.dst.node}.${edge.dst.port}`),
      ...graph.exits.filter(exit => exit.node === node.id && exit.port === port.name).map(() => 'Workflow output'),
    ] })),
  };
}

// Traverse the committed trace once for every node in this graph scope.
export function graphIO(graph: Graph, source: TraceEvent[] | TraceIndex, values: Record<string, JsonValue> = {}, scope: string[] = []): Record<string, NodeIOData> {
  const index = asTraceIndex(source);
  const result: Record<string, NodeIOData> = Object.create(null) as Record<string, NodeIOData>;
  for (const node of graph.nodes) result[node.id] = emptyIO(graph, node);
  const channels = new Map<string, ResolvedChannel | null>();
  const resolve = (channel: string) => {
    if (!channels.has(channel)) channels.set(channel, resolveChannel(graph, channel, index, scope));
    return channels.get(channel);
  };
  const placedIndices = new Map<string, number>(), received = new Map<string, NodeIOItem>();
  const outputKeys = new Map<NodeIOPort, Set<string>>();
  const addOutput = (node: string, port: string, id: string, instance: string, sequence: number) => {
    const target = result[node]?.outputs.find(output => output.port.name === port);
    if (!target) return;
    const keys = outputKeys.get(target) ?? new Set<string>(), key = JSON.stringify([id, instance]);
    if (keys.has(key)) return;
    keys.add(key); outputKeys.set(target, keys);
    target.items.push({ id, instance, sequence, available: Object.hasOwn(values, id), value: values[id] });
  };
  for (const event of index.committedEvents) {
    if (event.op === null && event.type === 'token.placed' && typeof event.data.edge === 'string') {
      const channel = event.data.edge, resolved = resolve(channel);
      const tokenIndex = placedIndices.get(channel) ?? 0;
      placedIndices.set(channel, tokenIndex + 1); // EOS also occupies an index.
      const target = resolved?.destination ? result[resolved.destination.node]?.inputs.find(input => input.port.name === resolved.destination!.port) : undefined;
      const id = object(object(event.data.token).item).id;
      if (target) {
        target.channels ??= [];
        let stream = target.channels.find(stream => stream.id === channel);
        if (!stream) { stream = { id: channel, closed: false }; target.channels.push(stream); }
        if (event.data.token === 'eos') stream.closed = true;
        if (typeof id === 'string') {
          const item: NodeIOItem = { id, sequence: event.sequence, available: Object.hasOwn(values, id), value: values[id], channel, tokenIndex, consumed: false };
          target.items.push(item); received.set(JSON.stringify([channel, tokenIndex]), item);
        }
      }
      const instance = typeof event.data.by_instance === 'string' ? index.instances.get(event.data.by_instance) : undefined;
      if (resolved?.source && instance && typeof id === 'string' && instance.node === resolved.source.node && sameScope(instance.path, resolved.runtimePath)) {
        addOutput(resolved.source.node, resolved.source.port, id, instance.id, event.sequence);
      }
    }
    if (event.op === null && event.type === 'token.consumed' && typeof event.data.channel === 'string' && typeof event.data.index === 'number' && typeof event.data.item === 'string') {
      const { channel, index: tokenIndex, item: id, by_instance } = event.data;
      const ref = resolve(channel)?.destination;
      const target = ref ? result[ref.node]?.inputs.find(input => input.port.name === ref.port) : undefined;
      if (target) {
        const key = JSON.stringify([channel, tokenIndex]);
        let item = received.get(key);
        if (!item) {
          item = { id, sequence: event.sequence, available: Object.hasOwn(values, id), value: values[id], channel, tokenIndex };
          target.items.push(item); received.set(key, item);
        }
        if (item.id === id) {
          item.consumed = true; item.consumedSequence = event.sequence;
          if (typeof by_instance === 'string') item.instance = by_instance;
        }
      }
    }
    // Successful outputs with no outgoing channel are still observable.
    if (!index.successfulCompletions.has(event.sequence)) continue;
    const op = operation(event), auth = object(op?.args.auth);
    const instance = typeof auth.instance === 'string' ? index.instances.get(auth.instance) : undefined;
    const definition = instance ? instanceDefinitionPath(instance, index.instances) : null;
    if (!instance || !definition || !sameScope(definition, scope) || !Array.isArray(op?.args.outputs)) continue;
    for (const output of op.args.outputs) {
      const { port, items } = object(output);
      if (typeof port !== 'string' || !Array.isArray(items)) continue;
      for (const id of items) if (typeof id === 'string') addOutput(instance.node, port, id, instance.id, event.sequence);
    }
  }
  return result;
}

export function nodeIO(graph: Graph, node: GraphNode, source: TraceEvent[] | TraceIndex, values: Record<string, JsonValue> = {}, scope: string[] = []): NodeIOData {
  return graphIO(graph, source, values, scope)[node.id] ?? emptyIO(graph, node);
}
export function portPreview(port?: NodeIOPort): string {
  if (!port?.items.length) return '未記録';
  const item = port.items.at(-1)!;
  const value = item.available ? JSON.stringify(item.value) ?? '値なし' : '値は未提供';
  return port.items.length > 1 ? `${value} (+${port.items.length - 1})` : value;
}
