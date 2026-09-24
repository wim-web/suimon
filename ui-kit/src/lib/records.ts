import type { Definition, ExecutionRecord, Op, Path, RuntimeState, Transition } from '../types';
import { findWorkflow } from './definition';
import { findExecution, findInvocation, findRun, runOwner, samePath } from './status';

/** Op records with whether their commit followed; an op without its commit is uncommitted. */
export function recordTransitions(records: readonly ExecutionRecord[]): Transition[] {
  const transitions: Transition[] = [];
  records.forEach((record, i) => {
    if ('commit' in record) return;
    const next = records[i + 1];
    transitions.push({ seq: record.seq, op: record.op, values: record.values ?? {}, committed: !!next && 'commit' in next && next.seq === record.seq + 1 });
  });
  return transitions;
}

/** Payloads by value identity from the committed transitions (or all, for inspecting a torn tail). */
export function recordValues(transitions: readonly Transition[], includeUncommitted = false): Record<string, string> {
  const values: Record<string, string> = {};
  for (const t of transitions) if (t.committed || includeUncommitted) Object.assign(values, t.values);
  return values;
}

/** The value identities an op refers to. */
export function opValues(op: Op): string[] {
  switch (op.type) {
    case 'start': return op.input === undefined ? [] : [op.input];
    case 'returned': case 'yielded': case 'taskOutput': return [op.value];
    case 'deliver': case 'taskInput': return op.value === undefined ? [] : [op.value];
    default: return [];
  }
}

/** What a record is about, as far as the op and the state tell. */
export interface RecordRelation {
  run?: Path;
  placement?: string;
  task?: string;
  connection?: number;
  /** The source placement of a delivery's connection. */
  source?: string;
  /** The child run a closeRun ends; `run` and `placement` are then its caller. */
  childRun?: Path;
}

function callRelation(state: RuntimeState | undefined, id: string): RecordRelation {
  const call = state?.calls.find(c => c.id === id);
  if (!state || !call) return {};
  if (call.task !== null) {
    const execution = findExecution(state, call.owner);
    return execution ? { run: execution.run, placement: execution.placement, task: call.task } : {};
  }
  const invocation = findInvocation(state, call.owner);
  return invocation ? { run: invocation.run, placement: invocation.placement } : {};
}

/**
 * Relates an op to a run and placement. invoke and settle name them; call, task and execution ops
 * are resolved through the state, so they stay unrelated when the state does not know the call yet.
 */
export function recordRelation(op: Op, definition: Definition, state?: RuntimeState): RecordRelation {
  const workflowOf = (run: Path) => {
    const found = state && findRun(state, run);
    return findWorkflow(definition, found ? found.workflow : run.length ? '' : definition.main);
  };
  switch (op.type) {
    case 'start': {
      const main = findWorkflow(definition, definition.main);
      return main?.input ? { run: [], placement: main.input.placement } : { run: [] };
    }
    case 'invoke': case 'settle': return { run: op.run, placement: op.placement };
    case 'deliver': case 'transformFailed': {
      const c = workflowOf(op.run)?.connections[op.connection];
      return c ? { run: op.run, placement: c.target, source: c.source, connection: op.connection } : { run: op.run, connection: op.connection };
    }
    case 'taskInput': case 'taskInputFailed': case 'beginTask': case 'taskOutput': case 'taskOutputFailed': case 'closeExecution': {
      const execution = state && findExecution(state, op.execution);
      if (!execution) return {};
      return { run: execution.run, placement: execution.placement, ...(op.type === 'closeExecution' ? {} : { task: op.task }) };
    }
    case 'closeRun': {
      const run = state && findRun(state, op.run), owner = run && runOwner(state, run);
      return owner ? { run: owner.run, placement: owner.placement, childRun: op.run, ...(owner.task ? { task: owner.task } : {}) } : { childRun: op.run };
    }
    case 'cancel': case 'conclude': return { run: [] };
    default: return callRelation(state, op.call);
  }
}

export function relationLabel(relation: RecordRelation | undefined): string {
  if (!relation || (!relation.placement && relation.connection === undefined)) return '—';
  const target = relation.placement ? `${relation.placement}${relation.task ? `.${relation.task}` : ''}` : `connection ${relation.connection}`;
  return relation.source ? `${relation.source} → ${target}` : target;
}

export interface RecordFilter { run?: Path | null; placement?: string | null; uncommittedOnly?: boolean }

/** Transitions related to a run (and placement of that run); child runs are other runs. */
export function filterTransitions(transitions: readonly Transition[], relations: ReadonlyMap<number, RecordRelation>, filter: RecordFilter): Transition[] {
  return transitions.filter(t => {
    const relation = relations.get(t.seq);
    if (filter.uncommittedOnly && t.committed) return false;
    const inRun = !filter.run || (!!relation?.run && samePath(relation.run, filter.run));
    if (filter.placement) return inRun && relation?.placement === filter.placement;
    return inRun || (!!filter.run && !!relation?.childRun && samePath(relation.childRun, filter.run));
  });
}
