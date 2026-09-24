import type { Span } from './api';
import { firstResult, firstStart, formatMs, packSpans, spanEnd, ticks } from './spans';

/** The spans of user code in one run, in milliseconds from its start, and the time since its start, which stops at its end. */
export interface TimelineRun { label: string; spans: Span[]; elapsedMs: number; done: boolean }
/** A lane of a run, if there is one, whose unit of simulated I/O is `unitMs`. */
export interface TimelineLane { key: string; label: string; unitMs: number; run: TimelineRun | null }

const palette = ['--sui-kind-function', '--sui-kind-concurrency', '--sui-kind-branch', '--sui-kind-collect', '--sui-kind-subworkflow', '--sui-accent'];
function colorOf(fn: string): string {
  let h = 0;
  for (const c of fn) h = (h * 31 + c.charCodeAt(0)) >>> 0;
  return `var(${palette[h % palette.length]!})`;
}

/**
 * Lanes of runs on one time axis, so that runs of different scenarios can be compared; each lane
 * shows its unit and the total time of its run. `highlight` names the downstream function: each lane
 * also shows when its first call started, marked across the lane, and when its first result appeared.
 */
export function Timeline({ lanes, highlight }: { lanes: TimelineLane[]; highlight?: string }) {
  const extent = Math.max(100, ...lanes.map(l => l.run ? Math.max(l.run.elapsedMs, ...l.run.spans.map(s => spanEnd(s, l.run!.elapsedMs))) : 0));
  const scale = ticks(extent);
  const max = Math.max(extent, scale[scale.length - 1]!);
  const pct = (ms: number) => `${(ms / max) * 100}%`;
  return <section className="app-timeline" aria-label="Timeline">
    {lanes.map(({ key, label, unitMs, run }) => {
      const unit = <span>unit <b>{unitMs}ms</b></span>;
      if (!run) return <div key={key} className="app-lane"><div className="app-lane-header"><strong>{label}</strong>{unit}<span className="sui-muted">not run yet</span></div></div>;
      const first = highlight ? firstStart(run.spans, highlight) : null;
      return <div key={key} className="app-lane">
        <div className="app-lane-header"><strong>{label}</strong>{unit}
          {highlight && <><span>first {highlight} at <b>{formatMs(first)}</b></span><span>first result at <b>{formatMs(firstResult(run.spans, highlight))}</b></span></>}
          <span>{run.done ? <>total <b>{formatMs(run.elapsedMs)}</b></> : <>running · {formatMs(run.elapsedMs)}</>}</span>
        </div>
        <div className="app-lane-body">
          {packSpans(run.spans, run.elapsedMs).map(group => group.rows.map((row, i) => <div key={`${group.function}/${i}`} className="app-row">
            <span className="app-row-label">{i === 0 ? group.function : ''}</span>
            <div className="app-track">
              {row.map(span => {
                const stop = spanEnd(span, run.elapsedMs);
                return <div key={`${span.startMs}/${span.detail}`} className={`app-bar is-${span.outcome}`} style={{ left: pct(span.startMs), width: `max(2px, ${pct(stop - span.startMs)})`, background: colorOf(span.function) }}
                  title={`${span.function} ${span.detail}: ${formatMs(span.startMs)} – ${span.endMs === null ? 'running' : formatMs(span.endMs)} (${span.outcome})`}>
                  <span>{span.detail}</span>
                  {span.marks.map((m, j) => <i key={j} className="app-mark" style={{ left: `${((m - span.startMs) / Math.max(stop - span.startMs, 1e-9)) * 100}%` }} />)}
                </div>;
              })}
              {first !== null && <div className="app-marker" style={{ left: pct(first) }} />}
            </div>
          </div>))}
        </div>
      </div>;
    })}
    <div className="app-row app-axis"><span className="app-row-label" /><div className="app-track">{scale.map(t => <span key={t} style={{ left: pct(t) }}>{formatMs(t)}</span>)}</div></div>
  </section>;
}
