import { Handle, Position } from '@xyflow/react';
import { memo } from 'react';
import type { Node, NodeProps } from '@xyflow/react';
import { ArrowUpRight, Ellipsis } from 'lucide-react';
import type { GraphNode, NodePresentation } from '../types';
import { portPreview } from '../lib/node-io';
import type { NodeIOData } from '../lib/node-io';
import type { NodeActivity } from '../lib/activity';
import { NodeIcon } from './NodeIcon';

export type WorkflowFlowNode = Node<{
  definition: GraphNode;
  presentation?: NodePresentation;
  eventCount: number;
  io?: NodeIOData;
  activity?: NodeActivity;
  onOpenScope?: (id: string) => void;
}, 'workflow'>;

export const WorkflowNode = memo(function WorkflowNode({ data, selected }: NodeProps<WorkflowFlowNode>) {
  const { definition, presentation, eventCount } = data;
  const inputSide = presentation?.inputSide ?? 'top', outputSide = presentation?.outputSide ?? 'bottom';
  const position = { top: Position.Top, bottom: Position.Bottom, left: Position.Left, right: Position.Right };
  const offset = (side: string, i: number, count: number, row: number) => side === 'left' || side === 'right'
    ? { top: `calc(var(--sui-node-header-height) + 5px + var(--sui-node-port-height) * ${row + 0.5})` }
    : { left: `${(i + 1) / (count + 1) * 100}%` };
  return <div className={`sui-workflow-node ${selected ? 'is-selected' : ''} ${data.activity?.running ? 'is-running' : ''}`}>
    {definition.inputs.map((port, i) => <Handle key={port.name} id={`in:${port.name}`} type="target" position={position[inputSide]} style={offset(inputSide, i, definition.inputs.length, i)} title={`IN ${port.name}`} />)}
    <div className="sui-node-header"><NodeIcon kind={definition.kind.type} accent={presentation?.accent} size={20} />
    <div className="sui-node-copy"><span>{presentation?.description ?? definition.kind.type}</span><strong>{presentation?.label ?? definition.id}</strong></div></div>
    <div className="sui-node-io-preview">{(['inputs', 'outputs'] as const).flatMap(direction => definition[direction].map(port => {
      const io = data.io?.[direction].find(item => item.port.name === port.name);
      const preview = portPreview(io);
      const waiting = direction === 'inputs' ? io?.items.filter(item => item.consumed === false).length ?? 0 : 0;
      return <div key={`${direction}:${port.name}`} className={`sui-preview-${direction}`}><span title={port.name}>{direction === 'inputs' ? 'IN' : 'OUT'} <b>{port.name}</b></span><code title={preview}>{preview}</code>{waiting > 0 && <em className="sui-port-pending">待機 {waiting}</em>}</div>;
    }))}</div>
    <Ellipsis className="sui-node-dots" size={15} />
    <span className="sui-node-count">{eventCount > 0 ? data.activity ? `${data.activity.running} running · ${data.activity.succeeded} done` : `${eventCount} events` : '\u00a0'}</span>
    {'body' in definition.kind && <button type="button" className="sui-node-body nodrag" title="内側のグラフを開く" onClick={event => { event.stopPropagation(); data.onOpenScope?.(definition.id); }}><ArrowUpRight size={14} /></button>}
    {definition.outputs.map((port, i) => <Handle key={port.name} id={`out:${port.name}`} type="source" position={position[outputSide]} style={offset(outputSide, i, definition.outputs.length, definition.inputs.length + i)} title={`OUT ${port.name}`} />)}
  </div>;
});

export type BoundaryFlowNode = Node<{ kind: 'entry' | 'exit'; label: string; port: string }, 'boundary'>;
export function BoundaryNode({ data }: NodeProps<BoundaryFlowNode>) {
  return <div className="sui-boundary-node"><NodeIcon kind={data.kind} size={15} /><div><span>{data.kind === 'entry' ? 'WORKFLOW INPUT' : 'WORKFLOW OUTPUT'}</span><strong>{data.label}</strong></div>
    <Handle id={data.port} type={data.kind === 'entry' ? 'source' : 'target'} position={data.kind === 'entry' ? Position.Bottom : Position.Top} />
  </div>;
}
