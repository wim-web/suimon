import { useEffect, useMemo, useRef } from 'react';
import { Background, BackgroundVariant, MarkerType, Panel, ReactFlow, ReactFlowProvider, useNodesState, useReactFlow, useViewport } from '@xyflow/react';
import type { Edge } from '@xyflow/react';
import { Maximize, Minus, Plus } from 'lucide-react';
import type { Definition, PlacementPresentations } from '../types';
import { lookup } from '../lib/dictionary';
import { layoutWorkflow } from '../lib/layout';
import type { RunOverlay } from '../lib/status';
import { equalData } from '../lib/equal';
import { ConnectionEdge } from './ConnectionEdge';
import type { ConnectionEdgeData, ConnectionFlowEdge } from './ConnectionEdge';
import { InputNode, PlacementNode } from './PlacementNode';
import type { InputFlowNode, PlacementFlowNode } from './PlacementNode';

const nodeTypes = { placement: PlacementNode, workflowInput: InputNode };
const edgeTypes = { connection: ConnectionEdge };
const emptyPresentations: PlacementPresentations = {};
// Room at the top for the canvas label and a host's breadcrumbs.
const fitOptions = { padding: { top: '84px', bottom: '48px', x: '40px' }, maxZoom: 1 } as const;
type CanvasNode = PlacementFlowNode | InputFlowNode;

export interface WorkflowCanvasProps {
  definition: Definition;
  /** The workflow to draw, by id. */
  workflow: string;
  /** Status of one run of this workflow; without it the canvas shows the definition only. */
  overlay?: RunOverlay | null;
  selectedPlacement?: string | null;
  /** A placement and connection to emphasize, such as those of a selected record. */
  highlightedPlacement?: string | null;
  highlightedConnection?: number | null;
  onSelectPlacement?: (placement: string | null) => void;
  /** A sub-workflow placement or task asks to open the workflow it calls. */
  onOpenWorkflow?: (workflow: string, placement: string, task?: string) => void;
  presentations?: PlacementPresentations;
  theme?: 'dark' | 'light';
}

function CanvasControls() {
  const { zoomIn, zoomOut, fitView } = useReactFlow();
  const { zoom } = useViewport();
  return <Panel position="bottom-right"><div className="sui-canvas-controls">
    <button aria-label="Zoom out" title="Zoom out" onClick={() => void zoomOut({ duration: 180 })}><Minus size={14} /></button>
    <span>{Math.round(zoom * 100)}%</span>
    <button aria-label="Zoom in" title="Zoom in" onClick={() => void zoomIn({ duration: 180 })}><Plus size={14} /></button>
    <i /><button aria-label="Fit view" title="Fit view" onClick={() => void fitView({ ...fitOptions, duration: 240 })}><Maximize size={14} /></button>
  </div></Panel>;
}

function Canvas({ definition, workflow, overlay, selectedPlacement, highlightedPlacement, highlightedConnection, onSelectPlacement, onOpenWorkflow, presentations = emptyPresentations, theme = 'dark' }: WorkflowCanvasProps) {
  const layout = useMemo(() => {
    const positions = Object.fromEntries(Object.entries(presentations).map(([name, p]) => [name, p.position]));
    const result = layoutWorkflow(definition, workflow, positions);
    const nodes: CanvasNode[] = result.nodes.map(n => ({ id: `placement:${n.name}`, type: 'placement', position: n.position,
      data: { workflow: result.workflow.id, placement: n.placement, kind: n.kind, entry: n.entry, endpoint: n.endpoint, hasInput: n.entry || result.edges.some(e => e.connection.target === n.name) } }));
    if (result.input) nodes.push({ id: 'input', type: 'workflowInput', selectable: false, position: result.input.position, data: { type: result.input.type, placement: result.input.placement } });
    const edges: Edge[] = result.edges.map(e => ({ id: `connection:${e.index}`, type: 'connection', source: `placement:${e.connection.source}`, target: `placement:${e.connection.target}`,
      markerEnd: { type: MarkerType.ArrowClosed, width: 14, height: 14 }, data: { index: e.index, connection: e.connection, kind: e.kind } } satisfies ConnectionFlowEdge));
    if (result.input) edges.push({ id: 'input', source: 'input', target: `placement:${result.input.placement}`, markerEnd: { type: MarkerType.ArrowClosed, width: 14, height: 14 } });
    return { nodes, edges, workflow: result.workflow };
  }, [definition, workflow, presentations]);
  const [nodes, setNodes, onNodesChange] = useNodesState<CanvasNode>(layout.nodes);
  useEffect(() => { setNodes(layout.nodes); }, [layout, setNodes]);
  const previous = useRef(new Map<string, CanvasNode>());
  const decorated = useMemo(() => nodes.map((node): CanvasNode => {
    if (node.type !== 'placement') return node;
    const name = node.data.placement.name, prior = previous.current.get(node.id);
    const data = { ...node.data, presentation: lookup(presentations, name), status: lookup(overlay?.placements, name), highlighted: highlightedPlacement === name, onOpenWorkflow };
    const selected = selectedPlacement === name;
    // Keep an unchanged node object so a new state snapshot re-renders only the placements it changed.
    if (prior?.type === 'placement' && prior.selected === selected && prior.position === node.position && prior.measured === node.measured && prior.dragging === node.dragging
      && prior.data.placement === data.placement && prior.data.onOpenWorkflow === onOpenWorkflow && prior.data.highlighted === data.highlighted
      && equalData(prior.data.presentation, data.presentation) && equalData(prior.data.status, data.status)) return prior;
    return { ...node, selected, data };
  }), [nodes, presentations, overlay, highlightedPlacement, selectedPlacement, onOpenWorkflow]);
  useEffect(() => { previous.current = new Map(decorated.map(node => [node.id, node])); }, [decorated]);
  const edges = useMemo(() => layout.edges.map((edge): Edge => {
    if (edge.type !== 'connection') return edge;
    const data = edge.data as ConnectionEdgeData;
    return { ...edge, data: { ...data, status: overlay?.connections[data.index], highlighted: highlightedConnection === data.index } };
  }), [layout, overlay, highlightedConnection]);
  return <ReactFlow<CanvasNode, Edge> nodes={decorated} edges={edges} nodeTypes={nodeTypes} edgeTypes={edgeTypes} onNodesChange={onNodesChange}
    onNodeClick={(_, node) => { if (node.type === 'placement') onSelectPlacement?.(node.data.placement.name); }}
    onPaneClick={() => onSelectPlacement?.(null)} nodesConnectable={false} edgesReconnectable={false} deleteKeyCode={null}
    fitView fitViewOptions={fitOptions} minZoom={0.2} maxZoom={1.75} colorMode={theme} proOptions={{ hideAttribution: true }}>
    <Background variant={BackgroundVariant.Dots} gap={18} size={1} color="var(--sui-grid)" />
    <Panel position="top-left"><div className="sui-canvas-label"><span className="sui-live-dot" />{layout.workflow.id.toUpperCase()} <span>{layout.workflow.placements.length} placements · {layout.workflow.connections.length} connections{overlay ? '' : ' · definition'}</span></div></Panel>
    <CanvasControls />
  </ReactFlow>;
}

/** One workflow as a graph: placements as nodes, connections as edges, with an optional run overlay. */
export function WorkflowCanvas(props: WorkflowCanvasProps) {
  return <div className="sui-canvas"><ReactFlowProvider><Canvas {...props} /></ReactFlowProvider></div>;
}
