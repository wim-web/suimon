import type { ReactNode } from 'react';
import { LazyDetails } from './LazyDetails';

/** Like browser developer tools: large containers expand through bounded index ranges. */
export function TreeChildren({ count, renderItem, rangeLabel = (start, end) => `[${start} … ${end - 1}]` }: {
  count: number; renderItem: (index: number) => ReactNode; rangeLabel?: (start: number, end: number) => string;
}) {
  const range = (start: number, end: number): ReactNode => {
    if (end - start <= 100) return Array.from({ length: end - start }, (_, i) => renderItem(start + i));
    let size = 100;
    while (size * 100 < end - start) size *= 100;
    return Array.from({ length: Math.ceil((end - start) / size) }, (_, i) => {
      const from = start + i * size, to = Math.min(end, from + size);
      return <LazyDetails key={from} className="sui-tree-branch sui-tree-range" summary={rangeLabel(from, to)}>
        {() => <div className="sui-tree-children">{range(from, to)}</div>}
      </LazyDetails>;
    });
  };
  return <div className="sui-tree-children">{range(0, count)}</div>;
}
