import { useEffect, useRef, useState } from 'react';
import { LoaderCircle, Play, Terminal, Type } from 'lucide-react';
import { createWorkflowView, WorkflowWorkbench } from '@suimon/ui-kit';
import type { NodePresentations, WorkflowSnapshot, WorkflowView } from '@suimon/ui-kit';
import { loadSamples, readRunFrames } from './api';
import type { RunOutput, Sample } from './api';
import { LiveProgress, seconds } from './LiveProgress';
import { emptyTimings, observeTimings, progress } from './progress';
import type { Timings } from './progress';
import { RunOutputs } from './RunOutputs';

const presentations: NodePresentations = {
  source: { label: 'Generate & emit', description: 'Leaf · time-delayed stream', accent: '#a26aff', position: { x: 0, y: 0 }, outputSide: 'right' },
  filter: { label: 'Skip #comments', description: 'Filter · per item', accent: '#cb9b50', position: { x: 330, y: 0 }, inputSide: 'left' },
  each: { label: 'Process in parallel', description: 'ForEach · open to inspect workers', accent: '#dc68b5', position: { x: 330, y: 250 }, outputSide: 'left' },
  collect: { label: 'Collect all results', description: 'AllWait · stream completion', accent: '#5b9ab4', position: { x: 0, y: 250 }, inputSide: 'right' },
  trim: { label: 'Trim whitespace', description: 'Text processing', accent: '#a26aff' },
  uppercase: { label: 'Convert to uppercase', description: 'Leaf · simulated work', accent: '#dc68b5' },
};

export function App() {
  const [samples, setSamples] = useState<Sample[]>([]);
  const [selected, setSelected] = useState('streaming');
  const [data, setData] = useState<WorkflowSnapshot | null>(null);
  const [view, setView] = useState<WorkflowView | null>(null);
  const [live, setLive] = useState<ReturnType<typeof progress> | null>(null);
  const [input, setInput] = useState('');
  const [delay, setDelay] = useState(600);
  const [running, setRunning] = useState(false);
  const [error, setError] = useState('');
  const [outputs, setOutputs] = useState<RunOutput[] | undefined>(undefined);
  const [elapsed, setElapsed] = useState(0);
  const [timings, setTimings] = useState<Timings>(emptyTimings);
  const [history, setHistory] = useState<Record<string, Timings>>({});
  const request = useRef<AbortController | null>(null);
  const sample = samples.find(sample => sample.id === selected);
  const comparisonKey = JSON.stringify([input, delay]);

  function display(snapshot: WorkflowSnapshot) {
    const view = createWorkflowView(snapshot.graph, snapshot.events, snapshot.values);
    const live = progress(view);
    setData(snapshot); setView(view); setLive(live);
    return live;
  }

  useEffect(() => {
    const controller = new AbortController();
    void loadSamples(controller.signal).then(list => {
      const first = list[0];
      if (!first) throw new Error('サンプルがありません');
      setSamples(list); setSelected(first.id); setInput(first.input);
      display({ graph: first.graph, events: [], values: {} });
    }).catch((err: unknown) => { if (!controller.signal.aborted) setError(err instanceof Error ? err.message : String(err)); });
    return () => { controller.abort(); request.current?.abort(); };
  }, []);

  function changeSample(id: string) {
    const next = samples.find(sample => sample.id === id);
    if (!next) return;
    const keepInput = selected !== 'basic' && id !== 'basic';
    setSelected(id); if (!keepInput) setInput(next.input);
    display({ graph: next.graph, events: [], values: {} });
    setOutputs(undefined); setTimings(emptyTimings()); setElapsed(0); setError('');
  }

  async function run() {
    if (!sample) return;
    const controller = new AbortController(); request.current = controller;
    setRunning(true); setError(''); setOutputs(undefined); setElapsed(0); setTimings(emptyTimings());
    display({ graph: sample.graph, events: [], values: {} });
    let measured = emptyTimings();
    try {
      const response = await fetch('/api/run', { method: 'POST', signal: controller.signal,
        headers: { 'Content-Type': 'application/json', Accept: 'application/x-ndjson' },
        body: JSON.stringify({ scenario: selected, input, delay_ms: delay }) });
      for await (const frame of readRunFrames(response)) {
        // Keep this scenario's topology identity, including across reruns, so
        // new data does not reset positions the user dragged on the canvas.
        const snapshot = { ...frame.snapshot, graph: sample.graph };
        const state = display(snapshot); setElapsed(frame.elapsedMS);
        measured = observeTimings(measured, state, frame.elapsedMS, frame.done);
        setTimings(measured);
        if (frame.done) {
          if (frame.error) throw new Error(frame.error);
          setOutputs(frame.outputs);
          setHistory(previous => ({ ...previous, [`${selected}:${comparisonKey}`]: measured }));
        }
      }
    } catch (err) { if (!controller.signal.aborted) setError(err instanceof Error ? err.message : String(err)); }
    finally { if (!controller.signal.aborted) setRunning(false); request.current = null; }
  }

  if (!data || !sample || !view || !live) return <div className="suimon-ui app-loading">{error ? <><strong>サンプルを読み込めませんでした</strong><p role="alert">{error}</p><button onClick={() => location.reload()}>再読み込み</button></> : <><LoaderCircle className="app-spin" size={22} /><span>Loading samples…</span></>}</div>;
  const streaming = selected !== 'basic';
  return <WorkflowWorkbench key={selected} data={data} view={view} title={sample.title} subtitle="Examples / Go runtime" presentations={presentations} running={running} showBoundaryNodes={!streaming}
    actions={<><select className="app-sample-select" aria-label="サンプル" disabled={running} value={selected} onChange={event => changeSample(event.target.value)}>{samples.map(sample => <option key={sample.id} value={sample.id}>{sample.title}</option>)}</select><button className="sui-button sui-button-primary" onClick={() => void run()} disabled={running}>{running ? <LoaderCircle className="app-spin" size={14} /> : <Play size={13} fill="currentColor" />}{running ? 'Running…' : 'Run workflow'}</button></>}
    notice={<>{error && <div className="app-error" role="alert">{error}</div>}{streaming && <LiveProgress state={live} total={input.trim() ? input.trim().split(/\s+/).length : 0} running={running} elapsed={elapsed} timings={timings} />}</>}
    sidebarContent={<div className="app-run-input"><p className="app-sample-description">{sample.description}</p><div className="app-section-label"><Type size={13} /><label htmlFor="workflow-input">WORKFLOW INPUT</label></div><textarea id="workflow-input" aria-label="入力テキスト" spellCheck={false} value={input} onChange={event => setInput(event.target.value)} disabled={running} />
      {streaming ? <><span className="app-input-hint">空白区切り・最大12件。# で始まる項目を除外します。</span><label className="app-delay">待ち時間の基準<select aria-label="待ち時間" value={delay} disabled={running} onChange={event => setDelay(Number(event.target.value))}><option value={200}>200ms · fast</option><option value={600}>600ms · normal</option><option value={1000}>1000ms · slow</option></select></label><p className="app-input-hint">生成: 1倍 / 加工: 2〜4倍。ForEach の内側で実行中の値を確認できます。</p>
        <div className="app-comparison"><strong>同じ入力・待ち時間の比較</strong><table><thead><tr><th>方式</th><th>下流開始</th><th>全体</th></tr></thead><tbody>{['streaming', 'batch'].map(id => { const past = history[`${id}:${comparisonKey}`]; return <tr key={id}><th>{id === 'streaming' ? 'Stream' : 'Batch'}</th><td>{seconds(past?.firstWorker ?? null)}</td><td>{seconds(past?.total ?? null)}</td></tr>; })}</tbody></table><small>方式を切り替えて実行すると比較できます。</small></div>
      </> : <span className="app-input-hint">前後の空白を除去して、大文字に変換します。</span>}
      {outputs !== undefined && <RunOutputs outputs={outputs} />}
      <div className="app-runtime"><Terminal size={13} /><span>Go runtime</span><span className="app-local">LOCAL</span></div>
    </div>}
  />;
}
