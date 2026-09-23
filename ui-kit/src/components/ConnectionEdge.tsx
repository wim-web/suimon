import { BaseEdge, EdgeLabelRenderer, getSmoothStepPath } from '@xyflow/react';
import type { Edge, EdgeProps } from '@xyflow/react';
import type { Connection } from '../types';
import type { Kind } from '../lib/program';
import type { ConnectionStatus } from '../lib/status';

export type ConnectionEdgeData = { index: number; connection: Connection; kind: Kind | null; status?: ConnectionStatus; highlighted?: boolean };
export type ConnectionFlowEdge = Edge<ConnectionEdgeData, 'connection'>;

/** A connection labelled with its branch arm, transform and Single/Stream kind, and deliveries in the run. */
export function ConnectionEdge({ id, sourceX, sourceY, targetX, targetY, sourcePosition, targetPosition, data, markerEnd }: EdgeProps<ConnectionFlowEdge>) {
  const [path, labelX, labelY] = getSmoothStepPath({ sourceX, sourceY, targetX, targetY, sourcePosition, targetPosition, borderRadius: 10 });
  const status = data?.status;
  return <>
    <BaseEdge id={id} path={path} markerEnd={markerEnd} className={`${data?.kind === 'stream' ? 'sui-edge-stream' : ''} ${data?.highlighted ? 'sui-edge-highlighted' : ''}`} />
    {data && <EdgeLabelRenderer>
      <div className={`sui-edge-label nodrag nopan ${data.highlighted ? 'is-highlighted' : ''}`} style={{ transform: `translate(-50%, -50%) translate(${labelX}px, ${labelY}px)` }}>
        {data.connection.arm && <em className="sui-edge-arm">{data.connection.arm}</em>}
        <code title="transform">{data.connection.transform}</code>
        {data.kind && <span className="sui-edge-kind">{data.kind === 'single' ? 'Single' : 'Stream'}</span>}
        {status && (status.values + status.triggers > 0) && <b className="sui-tone-success" title="Delivered">{status.values + status.triggers}</b>}
        {status && status.failed > 0 && <b className="sui-tone-danger" title="Transform failed">{status.failed}</b>}
      </div>
    </EdgeLabelRenderer>}
  </>;
}
