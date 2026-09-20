import { Check, Clock3, Radio } from 'lucide-react';
import type { Timings, progress } from './progress';

export function seconds(value: number | null) { return value === null ? '—' : `${(value / 1000).toFixed(1)}s`; }

export function LiveProgress({ state, total, running, elapsed, timings }: { state: ReturnType<typeof progress>; total: number; running: boolean; elapsed: number; timings: Timings }) {
  return <section className="app-live-progress" aria-label="ライブ実行状況">
    <div className="app-live-title"><Radio size={13} /><strong>{running ? 'LIVE' : timings.total !== null ? 'FINISHED' : 'READY'}</strong><span>{seconds(elapsed)}</span></div>
    <div className="app-progress-stage"><small>Source · Emit</small><strong>{state.emitted} / {total}</strong><span>{state.sourceDone ? 'EOS · 生成完了' : running ? '時間差で生成中' : '待機中'}</span></div>
    <div className="app-progress-stage"><small>Filter</small><strong>{state.filtered} skipped</strong><span># で始まる項目を除外</span></div>
    <div className="app-progress-stage"><small>ForEach · concurrency 2</small><strong className={state.active ? 'app-active' : ''}>{state.active} running · {state.complete} done</strong><span>所要時間が異なる worker</span></div>
    <div className="app-progress-stage"><small>Collect · AllWait</small><strong>{state.collected ? <><Check size={12} />Complete</> : `${state.collectArrived} arrived · ${state.collectWaiting} waiting`}</strong><span>{state.collected ? '全件を配列で出力' : '入力を蓄積し、EOS を待つ'}</span></div>
    <div className="app-progress-timings"><span><Clock3 size={12} />下流の開始 <b>{seconds(timings.firstWorker)}</b></span><span>全体所要時間 <b>{seconds(timings.total)}</b></span></div>
  </section>;
}
