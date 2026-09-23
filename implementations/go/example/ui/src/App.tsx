import { useCallback, useEffect, useRef, useState } from 'react';
import { ChartGantt, LoaderCircle, Play, Square } from 'lucide-react';
import { WorkflowWorkbench } from '@suimon/ui-kit';
import type { JsonValue } from '@suimon/ui-kit';
import { applyProgress, cancelRun, followRun, loadReport, loadScenarios, startRun } from './api';
import type { Progress, Report, RunView, Scenario } from './api';
import { Timeline } from './Timeline';
import type { TimelineLane } from './Timeline';

/** The function whose start times the stream and batch scenarios compare. */
const downstream = 'process';

const message = (error: unknown) => error instanceof Error ? error.message : String(error);

export function App() {
  const [scenarios, setScenarios] = useState<Scenario[] | null>(null);
  const [selected, setSelected] = useState('');
  const [inputs, setInputs] = useState<Record<string, string>>({});
  /** The latest run of each scenario. */
  const [runs, setRuns] = useState<Record<string, RunView>>({});
  const [reports, setReports] = useState<Record<string, Report>>({});
  const [error, setError] = useState('');
  const [timeline, setTimeline] = useState(true);
  const followers = useRef(new Map<string, () => void>());

  useEffect(() => {
    const controller = new AbortController();
    loadScenarios(controller.signal).then(list => {
      setScenarios(list); setSelected(list[0]?.id ?? '');
      setInputs(Object.fromEntries(list.map(s => [s.id, s.input === undefined ? '' : JSON.stringify(s.input, null, 2)])));
    }).catch(e => { if (!controller.signal.aborted) setError(message(e)); });
    const active = followers.current;
    return () => { controller.abort(); for (const stop of active.values()) stop(); };
  }, []);

  const onProgress = useCallback((p: Progress) => {
    setRuns(previous => {
      try { return { ...previous, [p.scenario]: applyProgress(previous[p.scenario] ?? null, p) }; }
      catch (e) {
        // Stop following: later messages cannot continue a record that missed one.
        followers.current.get(p.id)?.(); followers.current.delete(p.id);
        queueMicrotask(() => setError(message(e))); return previous;
      }
    });
    if (p.done) {
      followers.current.delete(p.id);
      if (p.error) setError(p.error);
      else loadReport(p.id).then(report => setReports(previous => ({ ...previous, [p.id]: report }))).catch(e => setError(message(e)));
    }
  }, []);

  const scenario = scenarios?.find(s => s.id === selected);
  const current = scenario ? runs[scenario.id] : undefined;
  const running = current !== undefined && !current.done;

  async function run() {
    if (!scenario) return;
    setError('');
    let input: JsonValue | undefined;
    if (scenario.input !== undefined) {
      try { input = JSON.parse(inputs[scenario.id] ?? '') as JsonValue; }
      catch { setError('The input is not valid JSON.'); return; }
    }
    try {
      const id = await startRun(scenario.id, input);
      followers.current.set(id, followRun(id, onProgress, e => { followers.current.delete(id); setError(message(e)); }));
    } catch (e) { setError(message(e)); }
  }

  if (!scenarios || !scenario) {
    return <div className="suimon-ui app-loading" data-theme="dark">{error ? <><strong>Could not load the scenarios</strong><p role="alert">{error}</p><button onClick={() => location.reload()}>Reload</button></>
      : <><LoaderCircle className="app-spin" size={22} /><span>Loading scenarios…</span></>}</div>;
  }

  const compared = scenario.compare ? scenarios.filter(s => s.id === scenario.id || s.id === scenario.compare) : [scenario];
  const lanes: TimelineLane[] = compared.map(s => {
    const r = runs[s.id];
    return { key: s.id, label: s.title, run: r ? { label: s.title, spans: r.spans, elapsedMs: r.elapsedMs, done: r.done } : null };
  });
  const report = current ? reports[current.id] : undefined;

  return <WorkflowWorkbench key={scenario.id} program={scenario.program} state={current?.state} records={current?.records}
    title={scenario.title} subtitle="suimon Go runtime · playground"
    actions={<>
      <button className="sui-button" aria-pressed={timeline} onClick={() => setTimeline(!timeline)}><ChartGantt size={13} />Timeline</button>
      {running && <button className="sui-button" onClick={() => void cancelRun(current.id).catch(e => setError(message(e)))}><Square size={12} />Cancel</button>}
      <button className="sui-button sui-button-primary" onClick={() => void run()} disabled={running}>{running ? <LoaderCircle className="app-spin" size={14} /> : <Play size={13} fill="currentColor" />}{running ? 'Running…' : 'Run'}</button>
    </>}
    notice={<>
      {error && <div className="app-error" role="alert">{error}</div>}
      {timeline && <Timeline lanes={lanes} highlight={scenario.compare ? downstream : undefined} />}
    </>}
    sidebarContent={<div className="app-side">
      <section className="sui-sidebar-section">
        <div className="sui-sidebar-group"><span>Scenarios</span><span className="sui-muted">{scenarios.length}</span></div>
        <ul className="app-scenarios">{scenarios.map(s => {
          const r = runs[s.id];
          return <li key={s.id}><button aria-current={s.id === scenario.id ? 'true' : undefined} onClick={() => setSelected(s.id)}>
            <span>{s.title}</span>{r && <span className="sui-muted">{r.done ? r.state.status : 'running'}</span>}
          </button></li>;
        })}</ul>
        <p className="app-description">{scenario.description}</p>
      </section>
      {scenario.input !== undefined && <section className="sui-sidebar-section">
        <label className="sui-sidebar-group" htmlFor="scenario-input"><span>Input</span></label>
        <textarea id="scenario-input" className="app-input" spellCheck={false} value={inputs[scenario.id] ?? ''} disabled={running}
          onChange={event => setInputs(previous => ({ ...previous, [scenario.id]: event.target.value }))} />
      </section>}
      {report && <section className="sui-sidebar-section">
        <div className="sui-sidebar-group"><span>Report</span><span className="sui-muted">{report.status}</span></div>
        {Object.entries(report.outputs).map(([name, value]) => <div key={name} className="app-output"><b>{name}</b><pre>{JSON.stringify(value, null, 2)}</pre></div>)}
        {Object.keys(report.outputs).length === 0 && <p className="app-description">No endpoint has a value.</p>}
        {report.failures.map((f, i) => <p key={i} className="app-failure">{f.placement}{f.task ? `/${f.task}` : ''}: {f.cause}{f.error ? ` · ${f.error}` : ''}</p>)}
      </section>}
    </div>}
  />;
}
