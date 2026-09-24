import { memo } from 'react';
import type { MouseEvent, ReactNode } from 'react';
import { Handle, Position } from '@xyflow/react';
import type { Node, NodeProps } from '@xyflow/react';
import { ArrowUpRight, Timer } from 'lucide-react';
import type { InvocationStatus, Placement, PlacementPresentation, TaskStatus, ValueType } from '../types';
import type { Kind } from '../lib/definition';
import { bodyLabel, renderValueType } from '../lib/definition';
import type { PlacementStatus } from '../lib/status';
import { armOutcome } from '../lib/status';
import { NodeIcon } from './NodeIcon';
import { StatusBadge, StatusCounts } from './StatusBadge';

export const invocationOrder: readonly InvocationStatus[] = ['active', 'succeeded', 'skipped', 'upstreamFailed', 'failed', 'cancelled'];
export const taskOrder: readonly TaskStatus[] = ['pending', 'ready', 'active', 'succeeded', 'skipped', 'upstreamFailed', 'failed', 'notStarted', 'cancelled'];

export type PlacementNodeData = {
  workflow: string;
  placement: Placement;
  kind: Kind | null;
  entry: boolean;
  endpoint: boolean;
  /** Whether a connection or the workflow input reaches the placement. */
  hasInput: boolean;
  presentation?: PlacementPresentation;
  status?: PlacementStatus;
  highlighted?: boolean;
  onOpenWorkflow?: (workflow: string, placement: string, task?: string) => void;
};
export type PlacementFlowNode = Node<PlacementNodeData, 'placement'>;

export const controlLabels: Record<Placement['node']['type'], string> = {
  function: 'Function', subworkflow: 'Sub-workflow', branch: 'Branch', waitStream: 'waitStream', merge: 'Merge', concurrency: 'Concurrency',
};
export const kindLabel = (kind: Kind | null) => kind === 'single' ? 'Single' : kind === 'stream' ? 'Stream' : 'kind ?';
const list = (type: ValueType) => `List<${renderValueType(type)}>`;

function Row({ label, children }: { label: string; children: ReactNode }) {
  return <div className="sui-node-row"><span>{label}</span><div>{children}</div></div>;
}

export const PlacementNode = memo(function PlacementNode({ data, selected }: NodeProps<PlacementFlowNode>) {
  const { placement, presentation, status } = data;
  const node = placement.node;
  const open = (workflow: string, task?: string) => (event: MouseEvent) => { event.stopPropagation(); data.onOpenWorkflow?.(workflow, placement.name, task); };
  const phase = status?.settled ? status.settled.outcome : status?.phase;
  const invocations = status?.invocations.length ?? 0;
  return <div className={`sui-placement-node ${selected ? 'is-selected' : ''} ${data.highlighted ? 'is-highlighted' : ''} ${status?.phase === 'active' ? 'is-running' : ''}`}>
    {data.hasInput && <Handle type="target" position={Position.Top} isConnectable={false} />}
    <div className="sui-node-header">
      <NodeIcon kind={node.type} accent={presentation?.accent} size={19} />
      <div className="sui-node-copy"><span>{presentation?.description ?? controlLabels[node.type]}</span><strong title={placement.name}>{presentation?.label ?? placement.name}</strong></div>
      <div className="sui-node-marks">{data.entry && <em className="sui-mark">entry</em>}{data.endpoint && <em className="sui-mark">endpoint</em>}</div>
    </div>
    <div className="sui-node-detail">
      {node.type === 'function' && <Row label="call"><code>{node.function}</code></Row>}
      {node.type === 'subworkflow' && <Row label="calls"><button type="button" className="sui-link nodrag" title={`Open workflow ${node.workflow}`} onClick={open(node.workflow)}>{bodyLabel(node)}<ArrowUpRight size={12} /></button></Row>}
      {node.type === 'waitStream' && <Row label="collects"><code>{list(node.element)}</code></Row>}
      {node.type === 'merge' && <Row label="merges"><code>{list(node.element)}</code></Row>}
      {node.type === 'branch' && <>
        <Row label="judge"><code>{node.judge}</code></Row>
        {node.arms.map(arm => {
          const chosen = status?.invocations.filter(i => i.arm === arm).length ?? 0;
          return <Row key={arm} label="arm"><code>{arm}</code>{status && chosen > 0 && <b className="sui-count">{chosen}</b>}{status?.settled && <StatusBadge status={armOutcome(status.settled, arm)} />}</Row>;
        })}
      </>}
      {node.type === 'concurrency' && <>
        <Row label="limit"><code>{node.limit} · {node.output === 'list' ? list(node.element) : `Stream<${renderValueType(node.element)}>`}</code></Row>
        {node.tasks.map(task => {
          const counts: Partial<Record<TaskStatus, number>> = {};
          for (const e of status?.executions ?? []) for (const t of e.tasks) if (t.name === task.name) counts[t.status] = (counts[t.status] ?? 0) + 1;
          return <div key={task.name} className="sui-node-row is-task">
            <div className={`sui-task ${task.outputTransform ? '' : 'is-excluded'}`} title={task.outputTransform ? 'In the output' : 'Left out of the output'}><strong>{task.name}</strong>{task.body.type === 'subworkflow'
              ? <button type="button" className="sui-link nodrag" title={`Open workflow ${task.body.workflow}`} onClick={open(task.body.workflow, task.name)}>{task.body.workflow}<ArrowUpRight size={12} /></button>
              : <code>{task.body.function}</code>}</div>
            <StatusCounts counts={counts} order={taskOrder} />
          </div>;
        })}
      </>}
    </div>
    <div className="sui-node-footer">
      <span className="sui-node-contract">{kindLabel(data.kind)} · {placement.policy}{placement.timeout && <Timer size={11} aria-label="timeout" />}</span>
      {status && <span className="sui-node-status">{invocations > 0 && <span className="sui-muted" title="Invocations">{invocations}×</span>}{status.failures.length > 0 && <StatusBadge status="failed" count={status.failures.length} title="Failure records" />}{phase && <StatusBadge status={phase} />}</span>}
    </div>
    {!data.endpoint && <Handle type="source" position={Position.Bottom} isConnectable={false} />}
  </div>;
});

export type InputFlowNode = Node<{ type: ValueType; placement: string }, 'workflowInput'>;
export function InputNode({ data }: NodeProps<InputFlowNode>) {
  return <div className="sui-input-node"><NodeIcon kind="input" size={14} /><div><span>WORKFLOW INPUT</span><strong>{renderValueType(data.type)}</strong></div>
    <Handle type="source" position={Position.Bottom} />
  </div>;
}
