import { useCallback, useMemo, useState } from 'react';
import type { ReactNode } from 'react';
import { ChevronRight, CircleDot, ListTree, PanelLeft, PanelRight, X } from 'lucide-react';
import type { Graph, NodePresentations, TraceEvent, WorkflowSnapshot } from '../types';
import { downloadJSON, eventCategory, traceIndex } from '../lib/trace';
import { createWorkflowView } from '../lib/view';
import type { WorkflowView } from '../lib/view';
import { sameScope } from '../lib/routing';
import { EventInspector } from './EventInspector';
import { NodeInspector } from './NodeInspector';
import { NodeSidebar } from './NodeSidebar';
import { TracePanel } from './TracePanel';
import type { TraceCategory } from './TracePanel';
import { WorkflowCanvas } from './WorkflowCanvas';
import { WorkflowToolbar } from './WorkflowToolbar';

export interface WorkflowWorkbenchProps {
  data: WorkflowSnapshot;
  view?: WorkflowView;
  title?: string;
  subtitle?: string;
  presentations?: NodePresentations;
  actions?: ReactNode;
  sidebarContent?: ReactNode;
  notice?: ReactNode;
  running?: boolean;
  showBoundaryNodes?: boolean;
  theme?: 'dark' | 'light';
  onSelectEvent?: (event: TraceEvent) => void;
}
export function WorkflowWorkbench({ data, view: suppliedView, title = 'Workflow', subtitle, presentations, actions, sidebarContent, notice, running, showBoundaryNodes, theme = 'dark', onSelectEvent }: WorkflowWorkbenchProps) {
  const [scope, setScope] = useState<string[]>([]);
  const [selectedNode, setSelectedNode] = useState<string | null>(null);
  const [selectedSequence, setSelectedSequence] = useState<number | null>(null);
  const [sidebar, setSidebar] = useState(true);
  const [inspector, setInspector] = useState(false);
  const [trace, setTrace] = useState(false);
  const [nodeFilter, setNodeFilter] = useState<string | null>(null);
  const [category, setCategory] = useState<TraceCategory>('all');
  const index = useMemo(() => suppliedView?.index.events === data.events ? suppliedView.index : traceIndex(data.events), [data.events, suppliedView]);
  const graph = useMemo(() => scope.reduce<Graph>((current, id) => {
    const node = current.nodes.find(node => node.id === id);
    return node && 'body' in node.kind ? node.kind.body : current;
  }, data.graph), [data.graph, scope]);
  const view = useMemo(() => suppliedView && suppliedView.graph === graph && suppliedView.values === data.values && suppliedView.index === index && sameScope(suppliedView.scope, scope)
    ? suppliedView : createWorkflowView(graph, index, data.values, scope), [suppliedView, graph, index, data.values, scope]);
  const currentNode = graph.nodes.find(node => node.id === selectedNode);
  const currentEvent = data.events.find(event => event.sequence === selectedSequence);
  const visibleEvents = useMemo(() => (nodeFilter ? view.eventsByNode.get(nodeFilter) ?? [] : data.events).filter(event => category === 'all' || eventCategory(event) === category), [view, nodeFilter, category, data.events]);
  const eventPosition = visibleEvents.findIndex(event => event.sequence === selectedSequence);
  const selectNode = useCallback((id: string | null) => { setSelectedNode(id); setSelectedSequence(null); setNodeFilter(id); if (id) setInspector(true); }, []);
  const selectEvent = useCallback((event: TraceEvent) => {
    const relation = view.relations.get(event.sequence);
    const node = nodeFilter && view.eventsByNode.get(nodeFilter)?.includes(event) ? nodeFilter
      : relation?.actor && sameScope(relation.actor.scope, scope) ? relation.actor.node : relation?.destination?.node ?? null;
    setSelectedSequence(event.sequence); setSelectedNode(node); setInspector(true); onSelectEvent?.(event);
  }, [view, nodeFilter, scope, onSelectEvent]);
  const openScope = useCallback((id: string) => { setScope(previous => [...previous, id]); selectNode(null); }, [selectNode]);
  const goScope = useCallback((length: number) => { setScope(previous => previous.slice(0, length)); selectNode(null); }, [selectNode]);
  return <div className="suimon-ui sui-workbench" data-theme={theme}>
    <WorkflowToolbar title={title} subtitle={subtitle} status={running ? 'running' : index.status} actions={actions} onExport={kind => downloadJSON(`${kind}.${kind === 'trace' ? 'jsonl' : 'json'}`, kind === 'graph' ? data.graph : kind === 'trace' ? data.events : data, kind === 'trace')} />
    {notice}
    <div className="sui-workspace">
      <nav className="sui-rail" aria-label="ワークスペースのパネル">
        <button className={sidebar ? 'is-active' : ''} aria-label="ノード一覧" title="ノード一覧" aria-pressed={sidebar} onClick={() => setSidebar(!sidebar)}><PanelLeft size={18} /></button>
        <button className={trace ? 'is-active' : ''} aria-label="実行履歴" title="実行履歴" aria-pressed={trace} onClick={() => setTrace(!trace)}><ListTree size={18} /></button>
        <button className={inspector ? 'is-active' : ''} aria-label="詳細パネル" title="詳細パネル" aria-pressed={inspector} onClick={() => setInspector(!inspector)}><PanelRight size={18} /></button>
      </nav>
      {sidebar && <NodeSidebar key={scope.join('/')} graph={graph} selectedNode={selectedNode} onSelectNode={selectNode} presentations={presentations}>{sidebarContent}</NodeSidebar>}
      <main className="sui-main"><div className="sui-canvas-area">
        {scope.length > 0 && <nav className="sui-breadcrumbs" aria-label="グラフ階層"><button onClick={() => goScope(0)}>Workflow</button>{scope.map((id, i) => <span key={i}><ChevronRight size={11} /><button onClick={() => goScope(i + 1)}>{id}</button></span>)}</nav>}
        <WorkflowCanvas key={scope.join('/')} graph={graph} selectedNode={selectedNode} onSelectNode={selectNode} onOpenScope={openScope} presentations={presentations} eventCounts={view.counts} nodeIO={view.io} activity={view.activity} showBoundaryNodes={showBoundaryNodes} theme={theme} />
      </div>
      {trace && <TracePanel events={data.events} index={index} view={view} selectedSequence={selectedSequence} nodeFilter={nodeFilter} category={category} onCategoryChange={next => { setCategory(next); if (currentEvent && next !== 'all' && eventCategory(currentEvent) !== next) setSelectedSequence(null); }} onSelectEvent={selectEvent} onClearFilter={() => setNodeFilter(null)} onClose={() => setTrace(false)} />}
      <footer className="sui-statusbar"><span><CircleDot size={11} />{running ? 'Running workflow…' : index.status === 'ready' ? 'Ready to run' : index.status}</span><button onClick={() => setTrace(!trace)} aria-expanded={trace}><ListTree size={12} />Trace <b>{data.events.length}</b><span>{index.transactions.length} transactions</span></button></footer>
      </main>
      {inspector && <aside className="sui-inspector" aria-label="詳細"><div className="sui-inspector-header"><span>{currentEvent ? 'Event details' : 'Node details'}</span><button className="sui-icon-button" aria-label="詳細を閉じる" onClick={() => setInspector(false)}><X size={15} /></button></div>
        {currentEvent ? <EventInspector event={currentEvent} values={data.values} onPrevious={eventPosition > 0 ? () => selectEvent(visibleEvents[eventPosition - 1]!) : undefined} onNext={eventPosition >= 0 && eventPosition < visibleEvents.length - 1 ? () => selectEvent(visibleEvents[eventPosition + 1]!) : undefined} /> : currentNode ? <NodeInspector node={currentNode} presentation={presentations?.[currentNode.id]} io={view.io[currentNode.id]} events={view.eventsByNode.get(currentNode.id)} onShowTrace={() => { setNodeFilter(currentNode.id); setTrace(true); }} onOpenScope={() => openScope(currentNode.id)} /> : <div className="sui-empty-inspector"><PanelRight size={28} /><p>ノードやイベントを選択すると、詳細が表示されます。</p></div>}
      </aside>}
    </div>
  </div>;
}
