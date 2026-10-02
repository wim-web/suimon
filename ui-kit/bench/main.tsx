import { useState } from 'react';
import { createRoot } from 'react-dom/client';
import { WorkflowWorkbench } from '../src/components/WorkflowWorkbench';
import '../src/styles.css';
import { definition, largeRun, listDefinition, largeListRun } from './data';

const paint = () => new Promise<void>(resolve => requestAnimationFrame(() => requestAnimationFrame(() => resolve())));
async function measure(action: () => void) { const start = performance.now(); action(); await paint(); return performance.now() - start; }

function Benchmark() {
  const [listMode, setListMode] = useState(false);
  const [data, setData] = useState(() => largeRun(0));
  const load = (count: number) => { const next = largeRun(count); return measure(() => { setListMode(false); setData(next); }); };
  const list = (count = 100_000) => { const next = largeListRun(count); return measure(() => { setListMode(true); setData(next); }); };
  window.bench = {
    load, measure,
    payload: (payload = '{"id":9007199254740993,"items":[' + Array(150_000).fill('"large result value with extra text"').join(',') + ']}') => {
      const next = largeRun(1);
      const record = next.records[0]!;
      if ('op' in record) record.values = { 'value-0': payload };
      return measure(() => { setListMode(false); setData(next); });
    },
    list,
    append: () => (listMode ? list : load)(data.records.length / 2 + 100),
    snapshot: () => { const next = structuredClone(data); return measure(() => setData(next)); },
    tear: () => measure(() => setData({ ...data, records: data.records.slice(0, -1) })),
  };
  return <div style={{ height: '100vh', display: 'flex', flexDirection: 'column' }}>
    <div style={{ padding: 8 }}><button onClick={() => void load(10_000)}>Load 10,000</button> <button onClick={() => void load(100_000)}>Load 100,000</button> <button onClick={() => void window.bench.append()}>Append 100</button> <button onClick={() => void window.bench.payload()}>Large JSON</button> <button onClick={() => void window.bench.list()}>Large list</button></div>
    <div style={{ flex: 1, minHeight: 0 }}><WorkflowWorkbench key={listMode ? 'list' : 'calls'} definition={listMode ? listDefinition : definition} state={data.state} records={data.records}
      notice={listMode ? <div className="sui-bench-notice">Select “collected” to inspect the {data.records.length / 2} items as a list result.</div> : undefined} /></div>
  </div>;
}

declare global {
  interface Window { bench: { load: (count: number) => Promise<number>; payload: (payload?: string) => Promise<number>; list: (count?: number) => Promise<number>; append: () => Promise<number>; snapshot: () => Promise<number>; tear: () => Promise<number>; measure: typeof measure } }
}
createRoot(document.getElementById('root')!).render(<Benchmark />);
