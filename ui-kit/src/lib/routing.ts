import type { Graph, InstanceInfo, PortRef, TraceEvent, TraceIndex } from '../types';
import { object, operation } from './trace';

export interface ScopedNode { node: string; scope: string[] }
export interface ResolvedChannel { runtimePath: string[]; source?: PortRef; destination?: PortRef }
export interface EventRelation { actor?: ScopedNode; source?: ScopedNode & { port: string }; destination?: ScopedNode & { port: string } }

function strings(encoded: unknown): string[] | null {
  if (typeof encoded !== 'string') return null;
  try { const parts: unknown = JSON.parse(encoded); return Array.isArray(parts) && parts.every(part => typeof part === 'string') ? parts : null; }
  catch { return null; }
}
export function sameScope(a: string[], b: string[]) { return a.length === b.length && a.every((part, i) => part === b[i]); }

export function frameDefinitionPath(runtimePath: string[], instances: Map<string, InstanceInfo>): string[] | null {
  const path: string[] = [];
  for (const segment of runtimePath) {
    const owner = strings(segment)?.[0], parent = owner ? instances.get(owner) : undefined;
    if (!parent) return null;
    path.push(parent.node);
  }
  return path;
}
export function instanceDefinitionPath(instance: InstanceInfo, instances: Map<string, InstanceInfo>): string[] | null {
  return frameDefinitionPath(instance.path, instances);
}

// One channel resolver is shared by port values and trace filtering.
export function resolveChannel(graph: Graph, channel: unknown, index: TraceIndex, scope: string[] = []): ResolvedChannel | null {
  const parts = strings(channel);
  if (!parts || parts.length < 2) return null;
  const runtimePath = parts.slice(0, -2), definition = frameDefinitionPath(runtimePath, index.instances);
  if (!definition || !sameScope(definition, scope)) return null;
  const ordinal = parts.at(-1)!;
  if (!/^(0|[1-9][0-9]*)$/.test(ordinal) || !Number.isSafeInteger(Number(ordinal))) return null;
  const position = Number(ordinal);
  switch (parts.at(-2)) {
    case 'edge': { const edge = graph.edges[position]; return edge ? { runtimePath, source: edge.src, destination: edge.dst } : null; }
    case 'entry': {
      const destination = graph.entries[position];
      if (!destination || (!runtimePath.length && index.executionInputs && !index.executionInputs.has(JSON.stringify([destination.node, destination.port])))) return null;
      return { runtimePath, destination };
    }
    case 'exit': { const source = graph.exits[position]; return source ? { runtimePath, source } : null; }
    default: return null;
  }
}

export function eventRelation(event: TraceEvent, graph: Graph, index: TraceIndex, scope: string[] = []): EventRelation {
  const op = operation(event);
  const declaration = typeof op?.args.node === 'string' ? op.args : event.op === null && event.type === 'instance.created' ? event.data : null;
  let actor: ScopedNode | undefined;
  if (declaration && typeof declaration.node === 'string' && Array.isArray(declaration.path) && declaration.path.every(part => typeof part === 'string')) {
    const definition = frameDefinitionPath(declaration.path, index.instances);
    if (definition) actor = { node: declaration.node, scope: definition };
  } else {
    const id = object(op?.args.auth).instance ?? op?.args.inst ?? event.data.by_instance ?? event.data.instance ?? object(event.data.attempt).instance;
    const instance = typeof id === 'string' ? index.instances.get(id) : undefined;
    const definition = instance ? instanceDefinitionPath(instance, index.instances) : null;
    if (instance && definition) actor = { node: instance.node, scope: definition };
  }
  const channel = event.op === null && (event.type === 'token.placed' || event.type === 'token.consumed')
    ? resolveChannel(graph, event.type === 'token.placed' ? event.data.edge : event.data.channel, index, scope) : null;
  return { actor, source: channel?.source ? { ...channel.source, scope } : undefined, destination: channel?.destination ? { ...channel.destination, scope } : undefined };
}

export function relatedNodes(relation: EventRelation, scope: string[]): string[] {
  return [...new Set([relation.actor, relation.source, relation.destination].filter((node): node is ScopedNode => !!node && sameScope(node.scope, scope)).map(node => node.node))];
}
export function relationLabel(relation?: EventRelation): string {
  if (!relation) return '—';
  const label = (node: ScopedNode & { port?: string }) => [...node.scope, node.node].join('/') + (node.port ? `.${node.port}` : '');
  if (relation.destination) {
    const from = relation.source ?? relation.actor;
    return `${from ? label(from) : 'input'} → ${label(relation.destination)}`;
  }
  return relation.actor ? label(relation.actor) : relation.source ? label(relation.source) : '—';
}
