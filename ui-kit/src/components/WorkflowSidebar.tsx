import { useState } from 'react';
import type { ReactNode } from 'react';
import { ChevronDown, Search } from 'lucide-react';
import type { PlacementPresentations, Workflow } from '../types';
import type { RunOverlay } from '../lib/status';
import { NodeIcon } from './NodeIcon';
import { controlLabels } from './PlacementNode';
import { StatusBadge } from './StatusBadge';

export interface WorkflowSidebarProps {
  workflow: Workflow;
  overlay?: RunOverlay | null;
  selectedPlacement?: string | null;
  onSelectPlacement: (placement: string) => void;
  presentations?: PlacementPresentations;
  /** Sections placed above the placements, such as a RunSelector. */
  header?: ReactNode;
  children?: ReactNode;
}
export function WorkflowSidebar({ workflow, overlay, selectedPlacement, onSelectPlacement, presentations = {}, header, children }: WorkflowSidebarProps) {
  const [query, setQuery] = useState('');
  const placements = workflow.placements.filter(p => `${p.name} ${presentations[p.name]?.label ?? ''} ${p.node.type}`.toLowerCase().includes(query.toLowerCase()));
  return <aside className="sui-sidebar">
    {header}
    <div className="sui-sidebar-title"><span>{workflow.id}</span><span className="sui-small-badge">{workflow.placements.length}</span></div>
    <div className="sui-search-row"><label className="sui-search"><Search size={14} /><input aria-label="Search placements" placeholder="Search placements…" value={query} onChange={event => setQuery(event.target.value)} /></label></div>
    <div className="sui-node-list">{placements.map(p => {
      const status = overlay?.placements[p.name];
      const phase = status?.settled?.outcome ?? status?.phase;
      return <button key={p.name} className={`sui-sidebar-node ${selectedPlacement === p.name ? 'is-selected' : ''}`} aria-pressed={selectedPlacement === p.name} onClick={() => onSelectPlacement(p.name)}>
        <NodeIcon kind={p.node.type} accent={presentations[p.name]?.accent} size={15} />
        <span><strong>{presentations[p.name]?.label ?? p.name}</strong><small>{controlLabels[p.node.type]}</small></span>
        {phase && phase !== 'idle' && <StatusBadge status={phase} />}
      </button>;
    })}{placements.length === 0 && <p className="sui-empty-small">No matching placements</p>}</div>
    <details className="sui-connections"><summary className="sui-sidebar-group"><span>Connections</span><span className="sui-muted">{workflow.connections.length}</span><ChevronDown size={12} /></summary>
      <div className="sui-connection-list">{workflow.connections.map((c, i) => <button key={i} onClick={() => onSelectPlacement(c.target)}>
        <span>{c.source}{c.arm && <small> [{c.arm}]</small>}</span><span className="sui-connection-line" /><span>{c.target}<small> · {c.transform}</small></span>
      </button>)}</div></details>
    {children && <div className="sui-sidebar-slot">{children}</div>}
  </aside>;
}
