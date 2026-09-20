import type { Graph, JsonValue, TraceEvent, TraceIndex } from '../types';
import { nodeActivity } from './activity';
import { graphIO } from './node-io';
import { asTraceIndex } from './trace';
import { eventRelation, relatedNodes } from './routing';
import type { EventRelation } from './routing';

export function createWorkflowView(graph: Graph, source: TraceEvent[] | TraceIndex, values?: Record<string, JsonValue>, scope: string[] = []) {
  const index = asTraceIndex(source);
  const relations = new Map<number, EventRelation>();
  const eventsByNode = new Map<string, TraceEvent[]>();
  for (const event of index.events) {
    const relation = eventRelation(event, graph, index, scope);
    relations.set(event.sequence, relation);
    if (!index.committedSequences.has(event.sequence)) continue;
    for (const node of relatedNodes(relation, scope)) {
      const events = eventsByNode.get(node) ?? [];
      events.push(event); eventsByNode.set(node, events);
    }
  }
  return { graph, index, values, scope, relations, eventsByNode, io: graphIO(graph, index, values, scope), activity: nodeActivity(index, scope),
    counts: Object.fromEntries([...eventsByNode].map(([node, events]) => [node, events.length])) };
}
export type WorkflowView = ReturnType<typeof createWorkflowView>;
