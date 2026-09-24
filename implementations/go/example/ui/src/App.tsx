import { useCallback, useEffect, useRef, useState } from 'react';
import { ChartGantt, LoaderCircle, Play, Square } from 'lucide-react';
import { WorkflowWorkbench, formatPayload } from '@suimon/ui-kit';
import type { JsonValue } from '@suimon/ui-kit';
import { applyProgress, cancelRun, followRun, loadReport, loadScenarios, startRun } from './api';
import type { Progress, Report, RunView, Scenario } from './api';
import { latestRun, runKey, timelineLanes, shownUnit } from './lanes';
import { Timeline } from './Timeline';

/** The downstream function of the stream and batch scenarios: the timeline compares when its first call starts and when its first result appears. */
const downstream = 'process';

/** The choices of one unit of simulated I/O for a run, in milliseconds. */
const units = [{ ms: 200, label: '200ms · fast' }, { ms: 600, label: '600ms · normal' }, { ms: 1000, label: '1000ms · slow' }] as const;
const defaultUnit = 600;

const message = (error: unknown) => error instanceof Error ? error.message : String(error);

export function App() {
  const [scenarios, setScenarios] = useState<Scenario[] | null>(null);
  const [error, setError] = useState('');

  useEffect(() => {
    const controller = new AbortController();
    loadScenarios(controller.signal).then(list => {
      if (!list.length) throw new Error('The server has no scenarios.');
      setScenarios(list);
    }).catch(e => { if (!controller.signal.aborted) setError(message(e)); });
    return () => controller.abort();
  }, []);

  if (!scenarios) {
    return <div className="suimon-ui app-loading" data-theme="dark">{error ? <><strong>Could not load the scenarios</strong><p role="alert">{error}</p><button onClick={() => location.reload()}>Reload</button></>
      : <><LoaderCircle className="app-spin" size={22} /><span>Loading scenarios…</span></>}</div>;
  }
  return <Playground scenarios={scenarios} />;
}

/** The playground for the scenarios of the server, of which there is at least one. */
export function Playground({ scenarios }: { scenarios: readonly Scenario[] }) {
  const [selected, setSelected] = useState(scenarios[0]!.id);
  const [unit, setUnit] = useState<number>(defaultUnit);
  const [inputs, setInputs] = useState<Record<string, string>>(() => Object.fromEntries(scenarios.map(s => [s.id, s.input === undefined ? '' : JSON.stringify(s.input, null, 2)])));
  /** The latest run of each scenario with each unit, by runKey. */
  const [runs, setRuns] = useState<Record<string, RunView>>({});
  /** The unit of the latest run of each scenario. */
  const [latest, setLatest] = useState<Record<string, number>>({});
  const [reports, setReports] = useState<Record<string, Report>>({});
  const [error, setError] = useState('');
  const [timeline, setTimeline] = useState(true);
  const followers = useRef(new Map<string, () => void>());
  // Choosing a scenario mounts the workbench again, and the select in its header with it.
  const scenarioSelect = useRef<HTMLSelectElement>(null);
  const refocus = useRef(false);

  useEffect(() => {
    const active = followers.current;
    return () => { for (const stop of active.values()) stop(); };
  }, []);
  useEffect(() => {
    if (refocus.current) { refocus.current = false; scenarioSelect.current?.focus(); }
  }, [selected]);

  const onProgress = useCallback((p: Progress) => {
    const key = runKey(p.scenario, p.unitMs);
    setRuns(previous => {
      try { return { ...previous, [key]: applyProgress(previous[key] ?? null, p) }; }
      catch (e) {
        // Stop following: later messages cannot continue a record that missed one.
        followers.current.get(p.id)?.(); followers.current.delete(p.id);
        queueMicrotask(() => setError(message(e))); return previous;
      }
    });
    setLatest(previous => previous[p.scenario] === p.unitMs ? previous : { ...previous, [p.scenario]: p.unitMs });
    if (p.done) {
      followers.current.delete(p.id);
      if (p.error) setError(p.error);
      else loadReport(p.id).then(report => setReports(previous => ({ ...previous, [p.id]: report }))).catch(e => setError(message(e)));
    }
  }, []);

  const scenario = scenarios.find(s => s.id === selected) ?? scenarios[0]!;
  const current = latestRun(runs, latest, scenario.id);
  const running = current !== undefined && !current.done;

  async function run() {
    setError('');
    let input: JsonValue | undefined;
    if (scenario.input !== undefined) {
      try { input = JSON.parse(inputs[scenario.id] ?? '') as JsonValue; }
      catch { setError('The input is not valid JSON.'); return; }
    }
    try {
      const id = await startRun(scenario.id, input, unit);
      followers.current.set(id, followRun(id, onProgress, e => { followers.current.delete(id); setError(message(e)); }));
    } catch (e) { setError(message(e)); }
  }

  const report = current ? reports[current.id] : undefined;

  return <WorkflowWorkbench key={scenario.id} definition={scenario.definition} state={current?.state} records={current?.records}
    title={scenario.title} subtitle="suimon Go runtime · playground"
    actions={<>
      <button className="sui-button" aria-pressed={timeline} onClick={() => setTimeline(!timeline)}><ChartGantt size={13} />Timeline</button>
      <select ref={scenarioSelect} className="app-select" aria-label="Scenario" value={scenario.id}
        onChange={event => { refocus.current = true; setSelected(event.target.value); }}>
        {scenarios.map(s => <option key={s.id} value={s.id}>{s.title}</option>)}
      </select>
      {running && <button className="sui-button" onClick={() => void cancelRun(current.id).catch(e => setError(message(e)))}><Square size={12} />Cancel</button>}
      <button className="sui-button sui-button-primary" onClick={() => void run()} disabled={running}>{running ? <LoaderCircle className="app-spin" size={14} /> : <Play size={13} fill="currentColor" />}{running ? 'Running…' : 'Run'}</button>
    </>}
    notice={<>
      {error && <div className="app-error" role="alert">{error}</div>}
      {timeline && <Timeline lanes={timelineLanes(scenarios, scenario, runs, latest, unit)} highlight={scenario.compare ? downstream : undefined} />}
    </>}
    sidebarContent={<div className="app-side">
      <section className="sui-sidebar-section">
        <div className="sui-sidebar-group"><span>Scenario</span></div>
        <p className="app-description">{scenario.description}</p>
      </section>
      <section className="sui-sidebar-section">
        <label className="sui-sidebar-group" htmlFor="run-unit"><span>Unit</span>
          <select id="run-unit" className="app-select" value={shownUnit(current, unit)} disabled={running} onChange={event => setUnit(Number(event.target.value))}>
            {units.map(u => <option key={u.ms} value={u.ms}>{u.label}</option>)}
          </select></label>
        <p className="app-description">How long one unit lasts: every simulated wait is counted in units.</p>
      </section>
      {scenario.input !== undefined && <section className="sui-sidebar-section">
        <label className="sui-sidebar-group" htmlFor="scenario-input"><span>Input</span></label>
        <textarea id="scenario-input" className="app-input" spellCheck={false} value={inputs[scenario.id] ?? ''} disabled={running}
          onChange={event => setInputs(previous => ({ ...previous, [scenario.id]: event.target.value }))} />
      </section>}
      {report && <section className="sui-sidebar-section">
        <div className="sui-sidebar-group"><span>Report</span><span className="sui-muted">{report.status}</span></div>
        {Object.entries(report.outputs).map(([name, value]) => <div key={name} className="app-output"><b>{name}</b><pre>{formatPayload(value)}</pre></div>)}
        {Object.keys(report.outputs).length === 0 && <p className="app-description">No endpoint has a value.</p>}
        {report.failures.map((f, i) => <p key={i} className="app-failure">{f.placement}{f.task ? `/${f.task}` : ''}: {f.cause}{f.error ? ` · ${f.error}` : ''}</p>)}
      </section>}
    </div>}
  />;
}
