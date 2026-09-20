import { ChevronLeft, ChevronRight, Code2 } from 'lucide-react';
import type { JsonValue, TraceEvent } from '../types';
import { eventCategory, eventValues, operation } from '../lib/trace';

export interface EventInspectorProps {
  event: TraceEvent;
  values?: Record<string, JsonValue>;
  onPrevious?: () => void;
  onNext?: () => void;
}
export function EventInspector({ event, values, onPrevious, onNext }: EventInspectorProps) {
  const items = eventValues(event, values);
  return <div className="sui-event-inspector">
    <div className="sui-inspector-kicker"><span>EVENT {String(event.sequence).padStart(2, '0')}</span><div><button className="sui-icon-button" aria-label="前のイベント" disabled={!onPrevious} onClick={onPrevious}><ChevronLeft size={15} /></button><button className="sui-icon-button" aria-label="次のイベント" disabled={!onNext} onClick={onNext}><ChevronRight size={15} /></button></div></div>
    <h2>{operation(event)?.kind ?? event.type}</h2><span className={`sui-event-kind sui-event-${eventCategory(event)}`}>{eventCategory(event)}</span>
    <dl className="sui-metadata"><dt>Transaction</dt><dd>{event.txn}</dd><dt>Logical time</dt><dd>{event.recorded_at}</dd><dt>Event type</dt><dd>{event.type}</dd></dl>
    {items.length > 0 && <section className="sui-inspector-section"><h3>Values <span>{items.length}</span></h3>{items.map(item => <div className="sui-value" key={item.id}><span title={item.id}>{item.id}</span><pre>{item.available ? JSON.stringify(item.value, null, 2) : '値は未提供'}</pre></div>)}</section>}
    <details className="sui-json" open><summary><Code2 size={13} />Event JSON</summary><pre>{JSON.stringify(event, null, 2)}</pre></details>
  </div>;
}
