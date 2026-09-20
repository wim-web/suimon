import { useEffect, useMemo, useRef } from 'react';
import { Background, BackgroundVariant, Panel, ReactFlow, ReactFlowProvider, useNodesState, useReactFlow, useViewport } from '@xyflow/react';
import type { Edge } from '@xyflow/react';
import { Maximize, Minus, Plus } from 'lucide-react';
import type { Graph, NodePresentations } from '../types';
import { layoutGraph, nodeDisplayHeight } from '../lib/layout';
import type { NodeIOData } from '../lib/node-io';
import type { NodeActivity } from '../lib/activity';
import { BoundaryNode, WorkflowNode } from './WorkflowNode';
import { decorateNodes } from './canvas-nodes';
import type { CanvasNode } from './canvas-nodes';
const nodeTypes = { workflow: WorkflowNode, boundary: BoundaryNode };
const emptyPresentations: NodePresentations = {};
const emptyCounts: Record<string, number> = {};

export interface WorkflowCanvasProps {
  graph: Graph;
  selectedNode?: string | null;
  onSelectNode?: (nodeId: string | null) => void;
  onOpenScope?: (nodeId: string) => void;
  presentations?: NodePresentations;
  eventCounts?: Record<string, number>;
  nodeIO?: Record<string, NodeIOData>;
  activity?: Record<string, NodeActivity>;
  showBoundaryNodes?: boolean;
  theme?: 'dark' | 'light';
}

function CanvasControls() {
  const { zoomIn, zoomOut, fitView } = useReactFlow();
  const { zoom } = useViewport();
  return <Panel position="bottom-right"><div className="sui-canvas-controls">
    <button aria-label="縮小" title="縮小" onClick={() => void zoomOut({ duration: 180 })}><Minus size={14} /></button>
    <span>{Math.round(zoom * 100)}%</span>
    <button aria-label="拡大" title="拡大" onClick={() => void zoomIn({ duration: 180 })}><Plus size={14} /></button>
    <i /><button aria-label="全体を表示" title="全体を表示" onClick={() => void fitView({ padding: 0.22, maxZoom: 1, duration: 240 })}><Maximize size={14} /></button>
  </div></Panel>;
}

function Canvas({ graph, selectedNode, onSelectNode, onOpenScope, presentations = emptyPresentations, eventCounts = emptyCounts, nodeIO, activity, showBoundaryNodes = true, theme = 'dark' }: WorkflowCanvasProps) {
  const layout = useMemo(() => {
    const positions = layoutGraph(graph);
    for (const node of graph.nodes) { const position = presentations[node.id]?.position; if (position) positions.set(node.id, position); }
    const nodes: CanvasNode[] = graph.nodes.map(node => ({ id: `node:${node.id}`, type: 'workflow', position: positions.get(node.id) ?? { x: 0, y: 0 }, data: { definition: node, eventCount: 0 } }));
    const edges: Edge[] = graph.edges.map((edge, index) => ({ id: `edge:${index}`, source: `node:${edge.src.node}`, target: `node:${edge.dst.node}`, sourceHandle: `out:${edge.src.port}`, targetHandle: `in:${edge.dst.port}`, type: 'smoothstep' }));
    const points = [...positions.values()];
    const centerX = points.length ? (Math.min(...points.map(point => point.x)) + Math.max(...points.map(point => point.x))) / 2 : 0;
    const minY = Math.min(0, ...points.map(point => point.y));
    const bottom = Math.max(0, ...graph.nodes.map(node => (positions.get(node.id)?.y ?? 0) + nodeDisplayHeight(node)));
    for (const [kind, refs] of [['entry', graph.entries], ['exit', graph.exits]] as const) {
      if (!showBoundaryNodes) continue;
      for (const [index, ref] of refs.entries()) {
        const id = `${kind}:${index}`;
        nodes.push({ id, type: 'boundary', selectable: false, position: { x: centerX + (index - (refs.length - 1) / 2) * 280, y: kind === 'entry' ? minY - 110 : bottom + 64 }, data: { kind, label: `${ref.node}.${ref.port}`, port: ref.port } });
        edges.push(kind === 'entry' ? { id, source: id, target: `node:${ref.node}`, sourceHandle: ref.port, targetHandle: `in:${ref.port}`, type: 'smoothstep' } : { id, source: `node:${ref.node}`, target: id, sourceHandle: `out:${ref.port}`, targetHandle: ref.port, type: 'smoothstep' });
      }
    }
    return { nodes, edges };
  }, [graph, presentations, showBoundaryNodes]);
  const [nodes, setNodes, onNodesChange] = useNodesState<CanvasNode>(layout.nodes);
  useEffect(() => { setNodes(layout.nodes); }, [layout, setNodes]);
  const lastNodes = useRef<CanvasNode[]>([]);
  const decorated = useMemo(() => decorateNodes(nodes, lastNodes.current, { selectedNode, presentations, eventCounts, nodeIO, activity, onOpenScope }), [nodes, selectedNode, presentations, eventCounts, nodeIO, activity, onOpenScope]);
  useEffect(() => { lastNodes.current = decorated; }, [decorated]);
  return <ReactFlow<CanvasNode> nodes={decorated} edges={layout.edges} nodeTypes={nodeTypes} onNodesChange={onNodesChange}
    onNodeClick={(_, node) => { if (node.type === 'workflow') onSelectNode?.(node.data.definition.id); }}
    onPaneClick={() => onSelectNode?.(null)} nodesConnectable={false} edgesReconnectable={false} deleteKeyCode={null}
    fitView fitViewOptions={{ padding: 0.16, maxZoom: 1 }} minZoom={0.25} maxZoom={1.75} colorMode={theme}
    proOptions={{ hideAttribution: true }} ariaLabelConfig={{ 'node.a11yDescription.default': 'ノードを選択すると詳細を表示します。矢印キーで表示位置を移動できます。' }}>
    <Background variant={BackgroundVariant.Dots} gap={18} size={1} color="var(--sui-grid)" />
    <Panel position="top-left"><div className="sui-canvas-label"><span className="sui-live-dot" />WORKFLOW CANVAS <span>{graph.nodes.length} nodes · {graph.edges.length} connections</span></div></Panel>
    <Panel position="bottom-left"><span className="sui-canvas-hint">ドラッグで移動 · スクロールでズーム</span></Panel>
    <CanvasControls />
  </ReactFlow>;
}

export function WorkflowCanvas(props: WorkflowCanvasProps) {
  return <div className="sui-canvas"><ReactFlowProvider><Canvas {...props} /></ReactFlowProvider></div>;
}
