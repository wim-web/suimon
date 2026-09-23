import { useMemo, useState } from 'react';
import { Check, ListTree, X } from 'lucide-react';
import type { Program, RuntimeState, Transition } from '../types';
import { filterTransitions, recordRelation, relationLabel } from '../lib/records';
import type { RecordFilter, RecordRelation } from '../lib/records';
import { pathKey, runLabel, runTree } from '../lib/status';

export interface RecordPanelProps {
  transitions: readonly Transition[];
  program: Program;
  /** The text after the last newline of the record (RecordLog.tail); shown as never committed. */
  tail?: string;
  /** Resolves call, task and execution ops to their run and placement. */
  state?: RuntimeState;
  /** Relations by seq; computed from the program and state when omitted. */
  relations?: ReadonlyMap<number, RecordRelation>;
  selectedSeq?: number | null;
  /** A controlled filter; without it the panel keeps its own. */
  filter?: RecordFilter;
  onFilterChange?: (filter: RecordFilter) => void;
  onSelectRecord?: (transition: Transition, relation: RecordRelation) => void;
  onClose?: () => void;
}

export function relationsOf(transitions: readonly Transition[], program: Program, state?: RuntimeState): Map<number, RecordRelation> {
  return new Map(transitions.map(t => [t.seq, recordRelation(t.op, program, state)]));
}

/** Execution records in order, each op marked committed or uncommitted, filterable by run and placement. */
export function RecordPanel({ transitions, program, tail = '', state, relations: supplied, selectedSeq, filter: controlled, onFilterChange, onSelectRecord, onClose }: RecordPanelProps) {
  const [local, setLocal] = useState<RecordFilter>({});
  const filter = controlled ?? local;
  const change = (next: RecordFilter) => { setLocal(next); onFilterChange?.(next); };
  const relations = useMemo(() => supplied ?? relationsOf(transitions, program, state), [supplied, transitions, program, state]);
  const runs = useMemo(() => state ? runTree(state) : [], [state]);
  const labels = useMemo(() => new Map(runs.map(node => [pathKey(node.run.path), runLabel(node)])), [runs]);
  const visible = useMemo(() => filterTransitions(transitions, relations, filter), [transitions, relations, filter]);
  const uncommitted = transitions.filter(t => !t.committed).length;
  const runValue = filter.run ? pathKey(filter.run) : '';
  return <section className="sui-record-panel" aria-label="Execution records">
    <div className="sui-record-header"><span><ListTree size={14} />Execution records <b>{transitions.length}</b>{uncommitted > 0 && <em className="sui-tone-warning">{uncommitted} uncommitted</em>}{tail && <em className="sui-tone-warning">partial last line</em>}</span>
      <div className="sui-record-actions">
        {filter.placement && <button className="sui-filter-chip" onClick={() => change({ ...filter, placement: null })} title="Clear placement filter">{filter.placement}<X size={11} /></button>}
        <select aria-label="Run" value={runValue} onChange={event => change({ ...filter, run: event.target.value ? runs.find(n => pathKey(n.run.path) === event.target.value)?.run.path ?? null : null, placement: null })}>
          <option value="">All runs</option>
          {runs.map(node => <option key={pathKey(node.run.path)} value={pathKey(node.run.path)}>{' '.repeat(node.depth * 2)}{runLabel(node)}</option>)}
          {filter.run && !labels.has(runValue) && <option value={runValue}>selected run</option>}
        </select>
        <select aria-label="Commit state" value={filter.uncommittedOnly ? 'uncommitted' : 'all'} onChange={event => change({ ...filter, uncommittedOnly: event.target.value === 'uncommitted' })}>
          <option value="all">All records</option><option value="uncommitted">Uncommitted</option>
        </select>
        {onClose && <button className="sui-icon-button" aria-label="Close records" onClick={onClose}><X size={15} /></button>}
      </div>
    </div>
    <div className="sui-record-table"><div className="sui-record-columns"><span>#</span><span>Op</span><span>Run</span><span>Placement</span><span>State</span></div>
      {visible.map(t => {
        const relation = relations.get(t.seq);
        return <button key={t.seq} className={`sui-record-row ${selectedSeq === t.seq ? 'is-selected' : ''} ${t.committed ? '' : 'is-uncommitted'}`} aria-pressed={selectedSeq === t.seq} onClick={() => onSelectRecord?.(t, relation ?? {})}>
          <span className="sui-muted">{t.seq}</span>
          <span className="sui-record-name">{t.committed && <Check size={12} aria-hidden="true" />}{t.op.type}</span>
          <span title={relation?.run?.join(' / ')}>{relation?.run ? labels.get(pathKey(relation.run)) ?? (relation.run.length ? 'child run' : 'root') : '—'}</span>
          <span title={relationLabel(relation)}>{relationLabel(relation)}</span>
          <span className={`sui-badge sui-tone-${t.committed ? 'success' : 'warning'}`}>{t.committed ? 'committed' : 'uncommitted'}</span>
        </button>;
      })}
      {tail && <div className="sui-record-tail" title={tail}><span className="sui-badge sui-tone-warning">tail</span>Text after the last newline ({tail.length} characters); recovery discards it, so it is never committed.</div>}
      {visible.length === 0 && !tail && <div className="sui-empty-records"><ListTree size={22} /><span>{transitions.length ? 'No matching records' : 'No execution records'}</span></div>}
    </div>
  </section>;
}
