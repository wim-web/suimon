import type { ReactNode } from 'react';
import { ArrowUpRight, ListTree } from 'lucide-react';
import type { Execution, Invocation, Path, PlacementPresentation, Program, Result, Run, RuntimeState, Timeout, Workflow } from '../types';
import { bodyLabel, deriveKinds, findPlacement, findWorkflow, incoming, isEndpoint, isEntry, outgoing, renderValueType } from '../lib/program';
import type { IndexedConnection } from '../lib/program';
import { armOutcome, childRuns, invocationResults, resultSource, runOverlay, samePath } from '../lib/status';
import type { ValueIndex } from '../lib/values';
import { resolveValue } from '../lib/values';
import { NodeIcon } from './NodeIcon';
import { controlLabels, invocationOrder, kindLabel, taskOrder } from './PlacementNode';
import { StatusBadge, StatusCounts } from './StatusBadge';
import { ValueView } from './ValueView';

export interface PlacementInspectorProps {
  program: Program;
  workflow: Workflow | string;
  placement: string;
  /** With a state and a run of this workflow, the inspector adds the placement's status in that run. */
  state?: RuntimeState;
  run?: Path | null;
  /** Payloads for value identities, from valueIndex. */
  values?: ValueIndex;
  presentation?: PlacementPresentation;
  onOpenWorkflow?: (workflow: string, placement: string, task?: string) => void;
  onSelectRun?: (path: Path) => void;
  onShowRecords?: () => void;
  recordCount?: number;
  /** Invocations and results listed before the rest is summarized. */
  limit?: number;
}

const timeoutText = (t?: Timeout) => t && (t.callMs !== undefined || t.elementMs !== undefined)
  ? [t.callMs !== undefined && `call ${t.callMs} ms`, t.elementMs !== undefined && `element ${t.elementMs} ms`].filter(Boolean).join(' · ') : '—';

function Section({ title, count, children }: { title: string; count?: number; children: ReactNode }) {
  return <section className="sui-inspector-section"><h3>{title}{count !== undefined && <span> {count}</span>}</h3>{children}</section>;
}
function More({ total, shown }: { total: number; shown: number }) {
  return total > shown ? <p className="sui-empty-small">{total - shown} more not shown</p> : null;
}

function RunLinks({ runs, onSelectRun }: { runs: Run[]; onSelectRun?: (path: Path) => void }) {
  return runs.length ? <div className="sui-run-links">{runs.map((r, i) => <button key={i} className="sui-link" disabled={!onSelectRun} onClick={() => onSelectRun?.(r.path)}>
    run {r.workflow}<StatusBadge status={r.complete ? 'complete' : 'running'} /><ArrowUpRight size={12} />
  </button>)}</div> : null;
}

export function PlacementInspector({ program, workflow: workflowRef, placement: name, state, run, values, presentation, onOpenWorkflow, onSelectRun, onShowRecords, recordCount, limit = 50 }: PlacementInspectorProps) {
  const workflow = typeof workflowRef === 'string' ? findWorkflow(program, workflowRef) : workflowRef;
  const placement = findPlacement(workflow, name);
  if (!workflow || !placement) return <div className="sui-empty-inspector"><p>Unknown placement {name}</p></div>;
  const node = placement.node;
  const kind = deriveKinds(program, workflow)[name] ?? null;
  const overlay = state && run ? runOverlay(program, state, run) : null;
  const status = overlay?.run.workflow === workflow.id ? overlay.placements[name] : undefined;
  const connectionStatus = status ? overlay!.connections : undefined;
  const results = status && state ? state.results.filter(r => r.placement === name && samePath(r.run, overlay!.run.path)) : [];
  const fn = node.type === 'function' ? program.functions.find(f => f.id === node.function) : undefined;
  const connectionRow = (c: IndexedConnection, direction: 'in' | 'out') => {
    const deliveries = connectionStatus?.[c.index];
    return <li key={c.index} className="sui-connection-row">
      <span>{direction === 'in' ? c.source : c.target}{c.arm && <em className="sui-edge-arm">{c.arm}</em>}</span>
      <code>{c.transform}</code>
      {deliveries && <span className="sui-badges">{deliveries.values + deliveries.triggers > 0 && <StatusBadge status="succeeded" count={deliveries.values + deliveries.triggers} title="Delivered" />}{deliveries.failed > 0 && <StatusBadge status="failed" count={deliveries.failed} title="Transform failed" />}</span>}
    </li>;
  };
  const inbound = incoming(workflow, name), outbound = outgoing(workflow, name);
  const value = (id: string | null, label?: string) => id === null ? null : <ValueView value={resolveValue(values, id)} label={label} />;
  const triggerSource = (trigger: string | null) => {
    const source = trigger === null ? undefined : state?.results.find(r => r.id === trigger);
    return source ? `${source.placement}${source.arm ? ` [${source.arm}]` : ''}` : trigger === null ? 'start of run' : 'unknown result';
  };
  const executionView = (e: Execution) => node.type === 'concurrency' && state ? <div className="sui-execution">
    {e.tasks.map(t => {
      const spec = node.tasks.find(s => s.name === t.name);
      const outputs = state.taskResults.filter(r => r.execution === e.id && r.task === t.name);
      return <div key={t.name} className="sui-execution-task">
        <div className="sui-row-title"><strong>{t.name}</strong><StatusBadge status={t.status} /></div>
        {value(t.input, 'input')}
        {outputs.map(r => <div key={r.index}>
          {value(r.value, `result ${r.index}`)}
          {spec?.outputTransform && (typeof r.output === 'object' ? value(r.output.value.v, `output ${r.index}`)
            : <p className="sui-value-missing">output transform {r.output}</p>)}
        </div>)}
        <RunLinks runs={childRuns(state, e.id, t.name)} onSelectRun={onSelectRun} />
      </div>;
    })}
  </div> : null;
  const ordinal = new Map(status?.invocations.map((i, n) => [i.id, n + 1]));
  const resultLabel = (r: Result) => {
    if (!state) return undefined;
    const source = resultSource(state, r), n = source.invocation && ordinal.get(source.invocation.id);
    const from = source.kind === 'aggregate' ? 'aggregate' : n !== undefined ? `#${n}` : source.kind;
    return r.arm ? `${from} · arm ${r.arm}` : from;
  };
  const invocationView = (i: Invocation) => {
    const calls = state?.calls.filter(c => c.owner === i.id && c.task === null) ?? [];
    const execution = state?.executions.find(e => e.id === i.id);
    const produced = state ? invocationResults(state, i) : [];
    return <li key={i.id} className="sui-invocation">
      <div className="sui-row-title"><span className="sui-muted">#{ordinal.get(i.id)}</span><StatusBadge status={i.status} />{i.arm && <em className="sui-edge-arm">{i.arm}</em>}<small title={i.trigger ?? undefined}>from {triggerSource(i.trigger)}</small></div>
      {value(i.input, 'input')}
      {calls.map(c => <div key={c.id} className="sui-call"><span>{'function' in c.target ? c.target.function.id : c.target.judge.id}</span><StatusBadge status={c.status} />{c.stream && <small>{c.yields} yielded</small>}</div>)}
      {state && <RunLinks runs={childRuns(state, i.id)} onSelectRun={onSelectRun} />}
      {execution && executionView(execution)}
      {produced.length > 0 && <div className="sui-invocation-results">{produced.slice(0, limit).map(r => <ValueView key={r.id} value={resolveValue(values, r.value)} label={r.arm ? `result · arm ${r.arm}` : 'result'} />)}<More total={produced.length} shown={limit} /></div>}
    </li>;
  };
  return <div className="sui-placement-inspector">
    <NodeIcon kind={node.type} accent={presentation?.accent} size={22} />
    <h2>{presentation?.label ?? name}</h2>
    <p className="sui-description">{presentation?.description ?? `${controlLabels[node.type]} placement in ${workflow.id}`}</p>
    <div className="sui-badges">{isEntry(workflow, name) && <em className="sui-mark">entry</em>}{isEndpoint(workflow, name) && <em className="sui-mark">endpoint</em>}</div>
    <dl className="sui-metadata">
      <dt>Placement</dt><dd>{name}</dd>
      <dt>Control</dt><dd>{controlLabels[node.type]}</dd>
      {node.type === 'function' && <><dt>Function</dt><dd>{node.function}</dd>
        {fn && <><dt>Input</dt><dd>{fn.input ? renderValueType(fn.input) : 'none'}</dd><dt>Contract</dt><dd>{'single' in fn.output ? `Single<${renderValueType(fn.output.single)}>` : `Stream<${renderValueType(fn.output.stream)}>`}</dd></>}</>}
      {node.type === 'subworkflow' && <><dt>Workflow</dt><dd><button className="sui-link" disabled={!onOpenWorkflow} onClick={() => onOpenWorkflow?.(node.workflow, name)}>{node.workflow}<ArrowUpRight size={12} /></button></dd><dt>Output</dt><dd>{node.output}</dd></>}
      {node.type === 'branch' && <><dt>Judge</dt><dd>{node.judge}</dd><dt>Arms</dt><dd>{node.arms.join(', ')}</dd></>}
      {(node.type === 'waitStream' || node.type === 'merge') && <><dt>Element</dt><dd>{renderValueType(node.element)}</dd></>}
      {node.type === 'concurrency' && <><dt>Input</dt><dd>{node.input ? renderValueType(node.input) : 'none'}</dd><dt>Limit</dt><dd>{node.limit}</dd><dt>Output</dt><dd>{node.output === 'list' ? 'List' : 'Stream'} of {renderValueType(node.element)}</dd></>}
      <dt>Output kind</dt><dd>{kindLabel(kind)}</dd>
      <dt>Policy</dt><dd>{placement.policy}</dd>
      <dt>Timeout</dt><dd>{timeoutText(placement.timeout)}</dd>
    </dl>
    {node.type === 'concurrency' && <Section title="Tasks" count={node.tasks.length}><ul className="sui-plain-list">{node.tasks.map(t => <li key={t.name} className="sui-task-spec">
      <div className="sui-row-title"><strong>{t.name}</strong>{t.body.type === 'subworkflow'
        ? <button className="sui-link" disabled={!onOpenWorkflow} onClick={() => onOpenWorkflow?.((t.body as { workflow: string }).workflow, name, t.name)}>{bodyLabel(t.body)}<ArrowUpRight size={12} /></button>
        : <code>{t.body.function}</code>}</div>
      <small>in {t.inputTransform ?? '—'} · out {t.outputTransform ?? 'not in output'} · {t.policy}{t.timeout ? ` · ${timeoutText(t.timeout)}` : ''}</small>
    </li>)}</ul></Section>}
    <Section title="Incoming" count={inbound.length}>{inbound.length ? <ul className="sui-plain-list">{inbound.map(c => connectionRow(c, 'in'))}</ul> : <p className="sui-empty-small">{isEntry(workflow, name) ? 'Receives the workflow input' : 'No input connection'}</p>}</Section>
    <Section title="Outgoing" count={outbound.length}>{outbound.length ? <ul className="sui-plain-list">{outbound.map(c => connectionRow(c, 'out'))}</ul> : <p className="sui-empty-small">Endpoint of {workflow.id}</p>}</Section>
    {status && <>
      <Section title="Status">
        <div className="sui-badges">{status.settled ? <StatusBadge status={status.settled.outcome} title="Settled outcome" /> : <StatusBadge status={status.phase} />}<StatusCounts counts={status.counts} order={invocationOrder} /></div>
        {status.settled && status.settled.arms.length > 0 && <ul className="sui-plain-list">{status.settled.arms.map(([arm]) => <li key={arm} className="sui-connection-row"><em className="sui-edge-arm">{arm}</em><StatusBadge status={armOutcome(status.settled!, arm)} /></li>)}</ul>}
        {Object.keys(status.taskCounts).length > 0 && <div className="sui-badges"><small className="sui-muted">tasks</small><StatusCounts counts={status.taskCounts} order={taskOrder} /></div>}
        {Object.keys(status.taskOutputs).length > 0 && <div className="sui-badges"><small className="sui-muted">outputs</small><StatusCounts counts={{ pending: status.taskOutputs.pending, transformed: status.taskOutputs.value, failed: status.taskOutputs.failed }} order={['pending', 'transformed', 'failed']} /></div>}
        {status.failures.map((f, i) => <p key={i} className="sui-failure-line">failed{f.task ? ` in task ${f.task}` : ''} · {f.cause}</p>)}
      </Section>
      <Section title="Invocations" count={status.invocations.length}>{status.invocations.length ? <ul className="sui-plain-list">{status.invocations.slice(0, limit).map(invocationView)}</ul> : <p className="sui-empty-small">Not invoked in this run</p>}<More total={status.invocations.length} shown={limit} /></Section>
      <Section title="Results" count={results.length}>{results.slice(0, limit).map(r => <ValueView key={r.id} value={resolveValue(values, r.value)} label={resultLabel(r)} />)}{!results.length && <p className="sui-empty-small">No results</p>}<More total={results.length} shown={limit} /></Section>
    </>}
    {onShowRecords && <button className="sui-button sui-wide-button" onClick={onShowRecords}><ListTree size={14} />Show records<span>{recordCount ?? ''}</span></button>}
  </div>;
}
