import type { WorkflowFlowNode, BoundaryFlowNode } from './WorkflowNode';
import type { NodePresentations } from '../types';
import type { NodeIOData } from '../lib/node-io';
import type { NodeActivity } from '../lib/activity';
import { equalData } from '../lib/equal';

export type CanvasNode = WorkflowFlowNode | BoundaryFlowNode;
export function decorateNodes(nodes: CanvasNode[], previous: CanvasNode[], options: {
  selectedNode?: string | null; presentations: NodePresentations; eventCounts: Record<string, number>;
  nodeIO?: Record<string, NodeIOData>; activity?: Record<string, NodeActivity>; onOpenScope?: (id: string) => void;
}): CanvasNode[] {
  const old = new Map(previous.map(node => [node.id, node]));
  return nodes.map(node => {
    if (node.type !== 'workflow') return node;
    const id = node.data.definition.id, selected = options.selectedNode === id;
    const data = { ...node.data, presentation: options.presentations[id], eventCount: options.eventCounts[id] ?? 0, io: options.nodeIO?.[id], activity: options.activity?.[id], onOpenScope: options.onOpenScope };
    const prior = old.get(node.id);
    // Keep the whole React Flow node object when neither geometry nor visible
    // data changed. Moving/selecting one node need not re-render its siblings.
    if (prior?.type === 'workflow' && prior.selected === selected && equalData(prior.position, node.position) &&
      equalData(prior.measured, node.measured) && prior.dragging === node.dragging && prior.data.definition === data.definition &&
      prior.data.onOpenScope === data.onOpenScope && equalData(prior.data.presentation, data.presentation) &&
      prior.data.eventCount === data.eventCount && equalData(prior.data.activity, data.activity) && equalData(prior.data.io, data.io)) return prior;
    return { ...node, selected, data };
  });
}
