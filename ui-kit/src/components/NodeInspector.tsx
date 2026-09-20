import { ArrowUpRight, ListTree } from 'lucide-react';
import type { GraphNode, NodePresentation, TraceEvent } from '../types';
import type { NodeIOData } from '../lib/node-io';
import { NodeIcon } from './NodeIcon';
import { NodeIOPanel } from './NodeIOPanel';

export interface NodeInspectorProps {
  node: GraphNode;
  presentation?: NodePresentation;
  events?: TraceEvent[];
  io?: NodeIOData;
  onShowTrace?: () => void;
  onOpenScope?: () => void;
}
export function NodeInspector({ node, presentation, events = [], io, onShowTrace, onOpenScope }: NodeInspectorProps) {
  return <div className="sui-node-inspector"><NodeIcon kind={node.kind.type} accent={presentation?.accent} size={24} /><h2>{presentation?.label ?? node.id}</h2><p className="sui-description">{presentation?.description ?? `${node.kind.type} node`}</p>
    <NodeIOPanel data={io ?? { inputs: node.inputs.map(port => ({ port, connections: [], items: [] })), outputs: node.outputs.map(port => ({ port, connections: [], items: [] })) }} />
    <dl className="sui-metadata"><dt>Node ID</dt><dd>{node.id}</dd><dt>Type</dt><dd>{node.kind.type}</dd>{node.kind.type === 'leaf' && <><dt>Concurrency</dt><dd>{node.kind.concurrency}</dd><dt>Max attempts</dt><dd>{node.kind.retry.maxAttempts}</dd></>}</dl>
    {onShowTrace && <button className="sui-button sui-wide-button" onClick={onShowTrace}><ListTree size={14} />View trace<span>{events.length}</span></button>}
    {'body' in node.kind && onOpenScope && <button className="sui-button sui-wide-button" onClick={onOpenScope}>内側のグラフを開く<ArrowUpRight size={14} /></button>}
  </div>;
}
