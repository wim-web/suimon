import { useLayoutEffect, useMemo, useRef, useState } from 'react';
import type { CSSProperties, KeyboardEvent, ReactNode } from 'react';
import type { Transition } from '../types';

const rowHeight = 34, headerHeight = 30, overscan = 6;

/** Fixed-height rows keep DOM work bounded even when the entire trace is retained. */
export function VirtualRecordList({ records, selectedSeq, renderRow, children }: {
  records: readonly Transition[];
  selectedSeq?: number | null;
  renderRow: (record: Transition) => ReactNode;
  children: ReactNode;
}) {
  const table = useRef<HTMLDivElement>(null);
  const [viewport, setViewport] = useState({ top: 0, height: 218 });
  const [focusSeq, setFocusSeq] = useState<number | null>(null);
  const selectedIndex = useMemo(() => selectedSeq == null ? -1 : records.findIndex(t => t.seq === selectedSeq), [records, selectedSeq]);
  const maxTop = Math.max(0, headerHeight + records.length * rowHeight - viewport.height);
  const top = Math.min(viewport.top, maxTop);
  const start = Math.max(0, Math.floor(top / rowHeight) - overscan);
  const end = Math.min(records.length, Math.ceil((top + viewport.height) / rowHeight) + overscan);

  useLayoutEffect(() => {
    const element = table.current!;
    const measure = () => setViewport({ top: element.scrollTop, height: element.clientHeight });
    measure();
    const observer = new ResizeObserver(measure);
    observer.observe(element);
    return () => observer.disconnect();
  }, []);

  const reveal = (index: number) => {
    const element = table.current!;
    const first = index * rowHeight, last = first + rowHeight + headerHeight;
    if (first < element.scrollTop) element.scrollTop = first;
    else if (last > element.scrollTop + element.clientHeight) element.scrollTop = last - element.clientHeight;
    setViewport({ top: element.scrollTop, height: element.clientHeight });
  };
  useLayoutEffect(() => { if (selectedIndex >= 0) reveal(selectedIndex); }, [selectedIndex]);
  useLayoutEffect(() => {
    const row = focusSeq === null ? null : table.current?.querySelector<HTMLButtonElement>(`[data-record-seq="${focusSeq}"]`);
    if (row) { row.focus({ preventScroll: true }); setFocusSeq(null); }
  }, [focusSeq, start, end]);

  const navigate = (event: KeyboardEvent<HTMLDivElement>) => {
    const seq = (event.target as HTMLElement).closest<HTMLElement>('[data-record-seq]')?.dataset.recordSeq;
    const current = seq === undefined ? Math.max(0, Math.ceil(top / rowHeight)) - 1 : records.findIndex(t => t.seq === Number(seq));
    const page = Math.max(1, Math.floor((viewport.height - headerHeight) / rowHeight));
    let next: number;
    switch (event.key) {
      case 'ArrowDown': next = current + 1; break;
      case 'ArrowUp': next = current - 1; break;
      case 'PageDown': next = current + page; break;
      case 'PageUp': next = current - page; break;
      case 'Home': next = 0; break;
      case 'End': next = records.length - 1; break;
      default: return;
    }
    if (!records.length) return;
    event.preventDefault();
    next = Math.max(0, Math.min(records.length - 1, next));
    reveal(next);
    setFocusSeq(records[next]!.seq);
  };

  return <div className="sui-record-table" ref={table} tabIndex={0} aria-label="Execution record list" onKeyDown={navigate}
    style={{ '--sui-row-height': `${rowHeight}px`, '--sui-record-header-height': `${headerHeight}px` } as CSSProperties}
    onScroll={event => { const element = event.currentTarget; setViewport({ top: element.scrollTop, height: element.clientHeight }); }}>
    <div className="sui-record-columns"><span>#</span><span>Op</span><span>Run</span><span>Placement</span><span>State</span></div>
    <div aria-hidden="true" style={{ height: start * rowHeight }} />
    {records.slice(start, end).map(renderRow)}
    <div aria-hidden="true" style={{ height: (records.length - end) * rowHeight }} />
    {children}
  </div>;
}
