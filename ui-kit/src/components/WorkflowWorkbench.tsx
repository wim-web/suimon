import { useCallback, useMemo, useState } from 'react';
import type { ReactNode } from 'react';
import { ChevronRight, CircleDot, ListTree, PanelLeft, PanelRight, X } from 'lucide-react';
import type { ExecutionRecord, Failure, Path, Program, RuntimeState, Transition, WorkflowPresentations } from '../types';
import { findWorkflow } from '../lib/program';
import { recordTransitions, recordValues, filterTransitions } from '../lib/records';
import type { RecordFilter, RecordRelation } from '../lib/records';
import { childRuns, findRun, pathKey, runLabel, runOverlay, runOwner, runTree, samePath } from '../lib/status';
import { valueIndex } from '../lib/values';
import { FailureList } from './FailureList';
import { PlacementInspector } from './PlacementInspector';
import { RecordInspector } from './RecordInspector';
import { RecordPanel, relationsOf } from './RecordPanel';
import { RunSelector } from './RunSelector';
import { WorkflowCanvas } from './WorkflowCanvas';
import { WorkflowSidebar } from './WorkflowSidebar';
import { WorkflowToolbar } from './WorkflowToolbar';

export interface WorkflowWorkbenchProps {
  program: Program;
  state?: RuntimeState;
  records?: readonly ExecutionRecord[];
  /** The text after the last newline of the record (RecordLog.tail), which is never committed. */
  recordTail?: string;
  presentations?: WorkflowPresentations;
  title?: string;
  subtitle?: string;
  actions?: ReactNode;
  sidebarContent?: ReactNode;
  notice?: ReactNode;
  theme?: 'dark' | 'light';
  /** The selected run; the workbench keeps its own selection when omitted. */
  run?: Path;
  onRunChange?: (run: Path) => void;
  onSelectRecord?: (transition: Transition, relation: RecordRelation) => void;
}

/** Either a run of the state, or workflow definitions opened in turn (from a run, if any). */
type View = { run: Path } | { workflow: string; trail: string[]; from?: Path };
const emptyRecords: readonly ExecutionRecord[] = [];

export function WorkflowWorkbench({ program, state, records = emptyRecords, recordTail = '', presentations, title, subtitle, actions, sidebarContent, notice, theme = 'dark', run: controlledRun, onRunChange, onSelectRecord }: WorkflowWorkbenchProps) {
  const [localView, setView] = useState<View>({ run: [] });
  const [selectedPlacement, setSelectedPlacement] = useState<string | null>(null);
  const [selectedSeq, setSelectedSeq] = useState<number | null>(null);
  const [highlight, setHighlight] = useState<RecordRelation | null>(null);
  const [sidebar, setSidebar] = useState(true);
  const [inspector, setInspector] = useState(false);
  const [recordsOpen, setRecordsOpen] = useState(false);
  const [filter, setFilter] = useState<RecordFilter>({});
  const view: View = controlledRun && 'run' in localView ? { run: controlledRun } : localView;

  const transitions = useMemo(() => recordTransitions(records), [records]);
  const relations = useMemo(() => relationsOf(transitions, program, state), [transitions, program, state]);
  const values = useMemo(() => valueIndex(program, state, recordValues(transitions)), [program, state, transitions]);
  const tree = useMemo(() => state ? runTree(state) : [], [state]);
  const labels = useMemo(() => new Map(tree.map(node => [pathKey(node.run.path), runLabel(node)])), [tree]);
  const labelOf = useCallback((path: string[]) => labels.get(pathKey(path)) ?? (path.length ? 'unknown run' : 'root'), [labels]);

  const currentRun = 'run' in view && state ? findRun(state, view.run) ?? findRun(state, []) : undefined;
  const runPath = currentRun?.path ?? null;
  const workflowId = currentRun?.workflow ?? ('workflow' in view ? view.workflow : program.main);
  const workflow = findWorkflow(program, workflowId) ?? findWorkflow(program, program.main)!;
  const overlay = useMemo(() => state && runPath ? runOverlay(program, state, runPath) : null, [program, state, runPath]);

  const selectRun = useCallback((path: Path) => {
    setView({ run: path }); onRunChange?.(path);
    setSelectedPlacement(null); setSelectedSeq(null); setHighlight(null);
    setFilter(previous => previous.run ? { ...previous, run: path, placement: null } : previous);
  }, [onRunChange]);
  const selectPlacement = useCallback((name: string | null) => {
    setSelectedPlacement(name); setSelectedSeq(null); setHighlight(null);
    if (name) { setInspector(true); setFilter(previous => ({ ...previous, run: runPath, placement: name })); }
  }, [runPath]);
  const openWorkflow = useCallback((called: string, placement: string, task?: string) => {
    if (state && runPath) {
      const owners = task ? state.executions.filter(e => samePath(e.run, runPath) && e.placement === placement).map(e => e.id)
        : state.invocations.filter(i => samePath(i.run, runPath) && i.placement === placement).map(i => i.id);
      const runs = owners.flatMap(owner => childRuns(state, owner, task ?? null));
      if (runs.length === 1) { selectRun(runs[0]!.path); return; }
      if (runs.length > 1) { selectPlacement(placement); return; }
    }
    setView(previous => 'workflow' in previous && !runPath ? { ...previous, workflow: called, trail: [...previous.trail, called] }
      : { workflow: called, trail: runPath ? [called] : [workflowId, called], ...(runPath ? { from: runPath } : {}) });
    setSelectedPlacement(null); setSelectedSeq(null); setHighlight(null);
  }, [state, runPath, workflowId, selectRun, selectPlacement]);
  const openTrail = useCallback((length: number) => {
    setView(previous => 'workflow' in previous ? { ...previous, workflow: previous.trail[length - 1]!, trail: previous.trail.slice(0, length) } : previous);
    setSelectedPlacement(null); setSelectedSeq(null); setHighlight(null);
  }, []);
  const visible = useMemo(() => filterTransitions(transitions, relations, filter), [transitions, relations, filter]);
  const selectRecord = useCallback((transition: Transition, relation: RecordRelation = relations.get(transition.seq) ?? {}) => {
    if (relation.run && state && findRun(state, relation.run) && !(runPath && samePath(relation.run, runPath))) { setView({ run: relation.run }); onRunChange?.(relation.run); }
    setSelectedSeq(transition.seq); setSelectedPlacement(relation.placement ?? null); setHighlight(relation); setInspector(true);
    onSelectRecord?.(transition, relation);
  }, [relations, state, runPath, onRunChange, onSelectRecord]);
  const selectFailure = useCallback((failure: Failure) => {
    if (state && findRun(state, failure.run)) { setView({ run: failure.run }); onRunChange?.(failure.run); }
    setSelectedPlacement(failure.placement); setSelectedSeq(null); setHighlight(null); setInspector(true);
  }, [state, onRunChange]);

  const currentRecord = selectedSeq === null ? undefined : transitions.find(t => t.seq === selectedSeq);
  const position = currentRecord ? visible.indexOf(currentRecord) : -1;
  const breadcrumbs: { label: string; path: Path }[] = [];
  if (state && currentRun) {
    for (let r: typeof currentRun | undefined = currentRun; r; ) {
      breadcrumbs.unshift({ label: r.path.length ? labelOf(r.path) : r.workflow, path: r.path });
      const owner: ReturnType<typeof runOwner> = runOwner(state, r);
      r = owner && r.path.length ? findRun(state, owner.run) : undefined;
    }
  }
  const uncommitted = transitions.filter(t => !t.committed).length;
  const placementRecords = selectedPlacement ? filterTransitions(transitions, relations, { run: runPath, placement: selectedPlacement }).length : 0;

  return <div className="suimon-ui sui-workbench" data-theme={theme}>
    <WorkflowToolbar title={title ?? program.main} subtitle={subtitle} status={state ? state.status : 'definition'} failures={state?.failures.length}
      onShowFailures={() => setSidebar(true)} actions={actions} />
    {notice}
    <div className="sui-workspace">
      <nav className="sui-rail" aria-label="Workbench panels">
        <button className={sidebar ? 'is-active' : ''} aria-label="Workflow panel" title="Workflow panel" aria-pressed={sidebar} onClick={() => setSidebar(!sidebar)}><PanelLeft size={18} /></button>
        <button className={recordsOpen ? 'is-active' : ''} aria-label="Execution records" title="Execution records" aria-pressed={recordsOpen} onClick={() => setRecordsOpen(!recordsOpen)}><ListTree size={18} /></button>
        <button className={inspector ? 'is-active' : ''} aria-label="Inspector" title="Inspector" aria-pressed={inspector} onClick={() => setInspector(!inspector)}><PanelRight size={18} /></button>
      </nav>
      {sidebar && <WorkflowSidebar key={workflow.id} workflow={workflow} overlay={overlay} selectedPlacement={selectedPlacement} onSelectPlacement={selectPlacement} presentations={presentations?.[workflow.id]}
        header={state && <section className="sui-sidebar-section"><div className="sui-sidebar-group"><span>Runs</span><span className="sui-muted">{state.runs.length}</span></div><RunSelector state={state} run={runPath} onSelectRun={selectRun} /></section>}>
        {state && state.failures.length > 0 && <section className="sui-sidebar-section"><div className="sui-sidebar-group"><span>Failures</span><span className="sui-muted">{state.failures.length}</span></div><FailureList state={state} onSelectFailure={selectFailure} /></section>}
        {sidebarContent}
      </WorkflowSidebar>}
      <main className="sui-main"><div className="sui-canvas-area">
        <nav className="sui-breadcrumbs" aria-label="Run path">
          {breadcrumbs.map((crumb, i) => <span key={pathKey(crumb.path)}>{i > 0 && <ChevronRight size={11} />}<button onClick={() => selectRun(crumb.path)} aria-current={i === breadcrumbs.length - 1 ? 'page' : undefined}>{crumb.label}</button></span>)}
          {!currentRun && <span className="sui-muted">definition</span>}
          {!currentRun && ('workflow' in view ? view.trail : [workflow.id]).map((id, i, trail) => <span key={i}><ChevronRight size={11} /><button onClick={() => openTrail(i + 1)} aria-current={i === trail.length - 1 ? 'page' : undefined}>{id}</button></span>)}
          {'workflow' in view && view.from && <button className="sui-link" onClick={() => selectRun(view.from!)}>back to run</button>}
        </nav>
        <WorkflowCanvas key={workflow.id} program={program} workflow={workflow.id} overlay={overlay} selectedPlacement={selectedPlacement}
          highlightedPlacement={highlight?.placement ?? null} highlightedConnection={highlight?.connection ?? null}
          onSelectPlacement={selectPlacement} onOpenWorkflow={openWorkflow} presentations={presentations?.[workflow.id]} theme={theme} />
      </div>
      {recordsOpen && <RecordPanel transitions={transitions} tail={recordTail} program={program} state={state} relations={relations} selectedSeq={selectedSeq} filter={filter} onFilterChange={setFilter} onSelectRecord={selectRecord} onClose={() => setRecordsOpen(false)} />}
      <footer className="sui-statusbar"><span><CircleDot size={11} />{state ? `${state.status} · ${state.runs.length} runs` : 'No runtime state'}</span>
        <button onClick={() => setRecordsOpen(!recordsOpen)} aria-expanded={recordsOpen}><ListTree size={12} />Records <b>{transitions.length}</b>{uncommitted > 0 && <span>{uncommitted} uncommitted</span>}{recordTail && <span>partial last line</span>}</button></footer>
      </main>
      {inspector && <aside className="sui-inspector" aria-label="Inspector"><div className="sui-inspector-header"><span>{currentRecord ? 'Record' : 'Placement'}</span><button className="sui-icon-button" aria-label="Close inspector" onClick={() => setInspector(false)}><X size={15} /></button></div>
        {currentRecord ? <RecordInspector transition={currentRecord} relation={relations.get(currentRecord.seq)} values={values} runLabel={labelOf}
          onPrevious={position > 0 ? () => selectRecord(visible[position - 1]!) : undefined} onNext={position >= 0 && position < visible.length - 1 ? () => selectRecord(visible[position + 1]!) : undefined} />
          : selectedPlacement ? <PlacementInspector program={program} workflow={workflow} placement={selectedPlacement} state={state} run={runPath} values={values} presentation={presentations?.[workflow.id]?.[selectedPlacement]}
            onOpenWorkflow={openWorkflow} onSelectRun={selectRun} onShowRecords={transitions.length ? () => { setFilter({ run: runPath, placement: selectedPlacement }); setRecordsOpen(true); } : undefined} recordCount={placementRecords} />
            : <div className="sui-empty-inspector"><PanelRight size={28} /><p>Select a placement or a record to see its details.</p></div>}
      </aside>}
    </div>
  </div>;
}
