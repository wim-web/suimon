import { useMemo } from 'react';
import type { Path, RuntimeState } from '../types';
import { pathKey, runLabel, runTree, samePath } from '../lib/status';
import { StatusBadge } from './StatusBadge';

export interface RunSelectorProps {
  state: RuntimeState;
  /** The selected run; [] is the root run. */
  run?: Path | null;
  onSelectRun: (path: Path) => void;
}
/** The root run and the child runs of sub-workflow calls, nested under the run that called them. */
export function RunSelector({ state, run, onSelectRun }: RunSelectorProps) {
  const nodes = useMemo(() => runTree(state), [state]);
  return <div className="sui-run-list" aria-label="Runs">
    {nodes.map(node => {
      const selected = !!run && samePath(run, node.run.path);
      return <button key={pathKey(node.run.path)} className={`sui-run ${selected ? 'is-selected' : ''}`} aria-pressed={selected}
        style={{ paddingLeft: 8 + node.depth * 14 }} onClick={() => onSelectRun(node.run.path)} title={node.run.path.length ? node.run.path.join(' / ') : 'root run'}>
        <span><strong>{runLabel(node)}</strong><small>{node.run.path.length ? node.owner?.invocation ? 'sub-workflow call' : 'concurrency task' : 'root run'}</small></span>
        <StatusBadge status={node.status} />
      </button>;
    })}
    {nodes.length === 0 && <p className="sui-empty-small">No runs yet</p>}
  </div>;
}
