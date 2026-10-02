import { Fragment, useMemo } from 'react';
import { ChevronLeft, ChevronRight, Code2 } from 'lucide-react';
import type { Transition } from '../types';
import { opValues, relationLabel } from '../lib/records';
import type { RecordRelation } from '../lib/records';
import type { ValueIndex } from '../lib/values';
import { StatusBadge } from './StatusBadge';
import { PayloadText, ValueView } from './ValueView';
import { LazyDetails } from './LazyDetails';
import { PagedContent } from './PagedContent';

export interface RecordInspectorProps {
  transition: Transition;
  relation?: RecordRelation;
  /** Payloads from other records; the record's own payloads take precedence. */
  values?: ValueIndex;
  runLabel?: (path: string[]) => string;
  onPrevious?: () => void;
  onNext?: () => void;
}
export function RecordInspector({ transition, relation, values, runLabel, onPrevious, onNext }: RecordInspectorProps) {
  const { op } = transition;
  const fields = Object.entries(op).filter(([key]) => key !== 'type');
  const ids = [...new Set([...opValues(op), ...Object.keys(transition.values)])];

  return <div className="sui-record-inspector">
    <div className="sui-inspector-kicker"><span>RECORD {transition.seq}</span><div>
      <button className="sui-icon-button" aria-label="Previous record" disabled={!onPrevious} onClick={onPrevious}><ChevronLeft size={15} /></button>
      <button className="sui-icon-button" aria-label="Next record" disabled={!onNext} onClick={onNext}><ChevronRight size={15} /></button>
    </div></div>
    <h2>{op.type}</h2>
    <StatusBadge status={transition.committed ? 'committed' : 'uncommitted'} title={transition.committed ? 'Followed by its commit' : 'No commit follows; recovery discards it'} />
    <dl className="sui-metadata">
      {relation?.run && <><dt>Run</dt><dd>{runLabel?.(relation.run) ?? (relation.run.length ? relation.run.join(' / ') : 'root')}</dd></>}
      <dt>Relates to</dt><dd>{relationLabel(relation)}</dd>
      {relation?.childRun && <><dt>Child run</dt><dd>{runLabel?.(relation.childRun) ?? relation.childRun.join(' / ')}</dd></>}
      {fields.map(([key, value]) => <Fragment key={key}><dt>{key}</dt><dd className={typeof value === 'string' ? 'sui-id' : undefined} title={typeof value === 'string' ? value : undefined}>{Array.isArray(value) ? (value.length ? value.join(' / ') : '[] (root)') : String(value)}</dd></Fragment>)}
    </dl>
    {ids.length > 0 && <section className="sui-inspector-section"><h3>Values <span>{ids.length}</span></h3><PagedContent key={transition.seq} count={ids.length} label="Record values">{(start, end) => ids.slice(start, end).map(id => Object.hasOwn(transition.values, id)
      ? <ValueView key={id} value={{ kind: 'payload', id, payload: transition.values[id]! }} label={id} />
      : <ValueView key={id} valueId={id} values={values} label={id} />)}</PagedContent></section>}
    <LazyDetails key={transition.seq} className="sui-json" summary={<><Code2 size={13} />Record JSON</>}>{() => <RecordJson transition={transition} />}</LazyDetails>
  </div>;
}

function RecordJson({ transition }: { transition: Transition }) {
  const payload = useMemo(() => JSON.stringify({ seq: transition.seq, op: transition.op, values: transition.values }, null, 2), [transition]);
  return <PayloadText payload={payload} />;
}
