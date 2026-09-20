import { useState } from 'react';
import { Check, ListTree, X } from 'lucide-react';
import type { TraceEvent, TraceIndex } from '../types';
import { eventCategory, eventNode, operation } from '../lib/trace';
import { relationLabel } from '../lib/routing';
import type { WorkflowView } from '../lib/view';

export type TraceCategory = 'all' | 'command' | 'fact' | 'commit';
export interface TracePanelProps {
  events: TraceEvent[];
  index: TraceIndex;
  view?: WorkflowView;
  selectedSequence?: number | null;
  nodeFilter?: string | null;
  onSelectEvent: (event: TraceEvent) => void;
  onClearFilter?: () => void;
  onClose?: () => void;
  category?: TraceCategory;
  onCategoryChange?: (category: TraceCategory) => void;
}
export function TracePanel({ events, index, view, selectedSequence, nodeFilter, onSelectEvent, onClearFilter, onClose, category: controlledCategory, onCategoryChange }: TracePanelProps) {
  const [localCategory, setLocalCategory] = useState<TraceCategory>('all');
  const category = controlledCategory ?? localCategory;
  const relevant = nodeFilter ? view ? view.eventsByNode.get(nodeFilter) ?? [] : events.filter(event => eventNode(event, index.instances) === nodeFilter) : events;
  const filtered = relevant.filter(event => category === 'all' || category === eventCategory(event));
  return <section className="sui-trace-panel" aria-label="実行 trace">
    <div className="sui-trace-header"><span><ListTree size={14} />Execution trace <b>{events.length}</b></span>
      <div className="sui-trace-actions">{nodeFilter && <button className="sui-filter-chip" onClick={onClearFilter}>{nodeFilter}<X size={11} /></button>}
        <select aria-label="イベント種別" value={category} onChange={event => { const next = event.target.value as TraceCategory; setLocalCategory(next); onCategoryChange?.(next); }}><option value="all">All events</option><option value="command">Commands</option><option value="fact">Facts</option><option value="commit">Commits</option></select>
        {onClose && <button className="sui-icon-button" aria-label="trace を閉じる" onClick={onClose}><X size={15} /></button>}
      </div>
    </div>
    <div className="sui-trace-table"><div className="sui-trace-columns"><span>#</span><span>Event</span><span>Node / route</span><span>Transaction</span><span>Type</span></div>
      {filtered.map(event => <button className={`sui-trace-row ${selectedSequence === event.sequence ? 'is-selected' : ''}`} key={event.sequence} onClick={() => onSelectEvent(event)} aria-pressed={selectedSequence === event.sequence}>
        <span className="sui-muted">{String(event.sequence).padStart(2, '0')}</span><span className="sui-trace-name">{eventCategory(event) === 'commit' && <Check size={12} />}{operation(event)?.kind ?? event.type}</span><span title={view ? relationLabel(view.relations.get(event.sequence)) : undefined}>{view ? relationLabel(view.relations.get(event.sequence)) : eventNode(event, index.instances) ?? '—'}</span><span className="sui-muted">{event.txn}{!index.committedSequences.has(event.sequence) && ' · 未確定'}</span><span className={`sui-event-kind sui-event-${eventCategory(event)}`}>{eventCategory(event)}</span>
      </button>)}
      {filtered.length === 0 && <div className="sui-empty-trace"><ListTree size={22} /><span>{events.length ? '一致するイベントがありません' : 'ワークフローを実行すると履歴が表示されます'}</span></div>}
    </div>
  </section>;
}
