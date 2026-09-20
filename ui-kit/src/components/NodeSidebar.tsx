import { useState } from 'react';
import type { ReactNode } from 'react';
import { ChevronDown, Layers, Search, SlidersHorizontal } from 'lucide-react';
import type { Graph, NodePresentations } from '../types';
import { NodeIcon } from './NodeIcon';

export interface NodeSidebarProps {
  graph: Graph;
  selectedNode?: string | null;
  onSelectNode: (id: string) => void;
  presentations?: NodePresentations;
  children?: ReactNode;
}
export function NodeSidebar({ graph, selectedNode, onSelectNode, presentations = {}, children }: NodeSidebarProps) {
  const [query, setQuery] = useState('');
  const [kind, setKind] = useState('all');
  const [showFilter, setShowFilter] = useState(false);
  const nodes = graph.nodes.filter(node => (kind === 'all' || node.kind.type === kind) && `${node.id} ${presentations[node.id]?.label ?? ''} ${node.kind.type}`.toLowerCase().includes(query.toLowerCase()));
  return <aside className="sui-sidebar">
    <div className="sui-sidebar-title"><span>Workflow</span><span className="sui-small-badge">{graph.nodes.length}</span></div>
    <div className="sui-search-row"><label className="sui-search"><Search size={14} /><input aria-label="ノードを検索" placeholder="Search nodes…" value={query} onChange={event => setQuery(event.target.value)} /></label><button className={`sui-icon-button ${showFilter ? 'is-active' : ''}`} aria-label="ノード種別フィルタ" aria-expanded={showFilter} onClick={() => setShowFilter(!showFilter)}><SlidersHorizontal size={14} /></button></div>
    {showFilter && <select className="sui-select" aria-label="ノード種別" value={kind} onChange={event => setKind(event.target.value)}><option value="all">すべての種別</option>{[...new Set(graph.nodes.map(node => node.kind.type))].map(type => <option key={type}>{type}</option>)}</select>}
    <div className="sui-sidebar-group"><Layers size={13} /><span>Nodes</span><ChevronDown size={12} /></div>
    <div className="sui-node-list">{nodes.map(node => <button key={node.id} className={`sui-sidebar-node ${selectedNode === node.id ? 'is-selected' : ''}`} aria-pressed={selectedNode === node.id} onClick={() => onSelectNode(node.id)}>
      <NodeIcon kind={node.kind.type} accent={presentations[node.id]?.accent} size={15} /><span><strong>{presentations[node.id]?.label ?? node.id}</strong><small>{node.id}</small></span><span className="sui-sidebar-node-kind">{node.kind.type}</span>
    </button>)}{nodes.length === 0 && <p className="sui-empty-small">一致するノードがありません</p>}</div>
    <details className="sui-connections"><summary className="sui-sidebar-group"><span>Connections</span><span className="sui-muted">{graph.edges.length}</span><ChevronDown size={12} /></summary>
    <div className="sui-connection-list">{graph.edges.map((edge, i) => <button key={i} onClick={() => onSelectNode(edge.dst.node)}><span>{edge.src.node}<small>.{edge.src.port}</small></span><span className="sui-connection-line" /><span>{edge.dst.node}<small>.{edge.dst.port}</small></span></button>)}</div></details>
    {children && <div className="sui-sidebar-slot">{children}</div>}
    <div className="sui-sidebar-footer"><span className="sui-live-dot" /><div>Graph inspector<small>ノードを選んで詳細と trace を確認</small></div></div>
  </aside>;
}
