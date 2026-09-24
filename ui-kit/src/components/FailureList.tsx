import { useMemo } from 'react';
import { TriangleAlert } from 'lucide-react';
import type { Failure, RuntimeState } from '../types';
import { pathKey, runLabel, runTree } from '../lib/status';

export interface FailureListProps { state: RuntimeState; onSelectFailure?: (failure: Failure) => void }
/** Failure records of the whole execution; a failure keeps the overall status failed (§11.4). */
export function FailureList({ state, onSelectFailure }: FailureListProps) {
  const labels = useMemo(() => new Map(runTree(state).map(node => [pathKey(node.run.path), runLabel(node)])), [state]);
  return <div className="sui-failure-list">
    {state.failures.map((f, i) => <button key={i} className="sui-failure" onClick={() => onSelectFailure?.(f)}>
      <TriangleAlert size={13} aria-hidden="true" />
      <span><strong>{f.placement}{f.task ? `.${f.task}` : ''}</strong><small>{f.cause} · {labels.get(pathKey(f.run)) ?? 'unknown run'}</small></span>
    </button>)}
    {state.failures.length === 0 && <p className="sui-empty-small">No failures</p>}
  </div>;
}
