import type { Path, RuntimeState } from '../types';
import type { RuntimeIndex } from '../lib/runtime-index';
import { pathKey, runLabel, samePath } from '../lib/status';
import { InvalidRuntimeState, useRunTree } from './RuntimeRuns';
import { StatusBadge } from './StatusBadge';

export interface RunSelectorProps {
  state: RuntimeState;
  /** Optional lookup index; ownership is always checked against the source state. */
  runtimeIndex?: RuntimeIndex;
  /** The selected run; [] is the root run. */
  run?: Path | null;
  onSelectRun: (path: Path) => void;
}
/** The root run and the child runs of sub-workflow calls, nested under the run that called them. */
export function RunSelector({ state, run, onSelectRun }: RunSelectorProps) {
  const { nodes, invalid } = useRunTree(state);
  if (invalid) return <InvalidRuntimeState />;
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
