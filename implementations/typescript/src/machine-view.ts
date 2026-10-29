import { deriveKinds } from './definition.js';
import { keyAggregate, listValue, samePath } from './identity.js';
import type {
  Body, CallStatus, Concurrency, ConcurrencyExecution, Connection, Definition, Invocation,
  InvocationStatus, Kind, Outcome, Path, Placement, Result, Run, Settled, State, TaskSpec, TaskState, Workflow,
} from './model-types.js';

export class Rejection extends Error {
  constructor(readonly code: string) { super(code); this.name = 'Rejection'; }
}

export function requireCondition(condition: boolean, code: string): asserts condition {
  if (!condition) throw new Rejection(code);
}

export function requireValue<T>(value: T | undefined, code: string): T {
  if (value === undefined) throw new Rejection(code);
  return value;
}

export const callEnded = (status: CallStatus): boolean => !['running', 'fetching', 'cancelling'].includes(status);

type IndexedConnection = { index: number; connection: Connection };
export type Shape = { kind: 'none' | 'entry' } | ({ kind: 'single' | 'stream' } & IndexedConnection)
  | { kind: 'merge'; merged: IndexedConnection[] };
type Resolution = { kind: 'pending' | 'transformFailed' | 'skipped' | 'failure' }
  | { kind: 'value'; source: string; input: string | null };
type Settlement = { settled: Settled; result?: Result };

export class View {
  private derived: ReturnType<typeof deriveKinds> | undefined;
  constructor(readonly def: Definition, readonly state: State) {}

  workflowByID(id: string): Workflow | undefined { return this.def.workflows.find(w => w.id === id); }
  run(path: Path): Run | undefined { return this.state.runs.find(r => samePath(r.path, path)); }
  workflow(path: Path): Workflow | undefined {
    const run = this.run(path);
    return run === undefined ? undefined : this.workflowByID(run.workflow);
  }
  invocation(id: string): Invocation | undefined { return this.state.invocations.find(i => i.id === id); }
  invocationsOf(path: Path, name: string): Invocation[] {
    return this.state.invocations.filter(i => samePath(i.run, path) && i.placement === name);
  }
  findInvocation(path: Path, name: string, trigger: string | null): Invocation | undefined {
    return this.invocationsOf(path, name).find(i => i.trigger === trigger);
  }
  call(id: string) { return this.state.calls.find(c => c.id === id); }
  execution(id: string) { return this.state.executions.find(e => e.id === id); }
  result(id: string) { return this.state.results.find(r => r.id === id); }
  resultsOf(path: Path, name: string): Result[] {
    return this.state.results.filter(r => samePath(r.run, path) && r.placement === name);
  }
  settledOf(path: Path, name: string): Settled | undefined {
    return this.state.settled.find(x => samePath(x.run, path) && x.placement === name);
  }
  delivery(path: Path, index: number, source: string) {
    return this.state.deliveries.find(d => samePath(d.run, path) && d.connection === index && d.source === source);
  }
  deliveriesOn(path: Path, index: number) {
    return this.state.deliveries.filter(d => samePath(d.run, path) && d.connection === index);
  }
  taskResult(execution: string, task: string, index: number) {
    return this.state.taskResults.find(r => r.execution === execution && r.task === task && r.index === index);
  }
  kinds(workflow: Workflow): Map<string, Kind> {
    this.derived ??= deriveKinds(this.def);
    return this.derived.get(workflow.id) ?? new Map();
  }
  shape(workflow: Workflow, name: string): Shape | undefined {
    const placement = workflow.placements.find(p => p.name === name);
    if (placement === undefined) return undefined;
    const inputs = workflow.connections.flatMap((connection, index) => connection.target === name ? [{ index, connection }] : []);
    if (placement.node.type === 'merge') return { kind: 'merge', merged: inputs };
    if (workflow.input?.placement === name) return { kind: 'entry' };
    if (inputs.length === 0) return { kind: 'none' };
    const only = inputs[0];
    if (inputs.length !== 1 || only === undefined) return undefined;
    const sourceKind = this.kinds(workflow).get(only.connection.source);
    return sourceKind === undefined ? undefined : { kind: sourceKind, ...only };
  }
  placementOf(path: Path, name: string): Placement {
    const workflow = requireValue(this.workflow(path), 'UNKNOWN_RUN');
    return requireValue(workflow.placements.find(p => p.name === name), 'UNKNOWN_PLACEMENT');
  }
  concurrencyOf(execution: ConcurrencyExecution): Concurrency {
    const node = this.placementOf(execution.run, execution.placement).node;
    if (node.type !== 'concurrency') throw new Rejection('NOT_CONCURRENCY');
    return node;
  }
  taskSpec(execution: ConcurrencyExecution, name: string): TaskSpec {
    return requireValue(this.concurrencyOf(execution).tasks.find(t => t.name === name), 'UNKNOWN_TASK');
  }
  task(execution: ConcurrencyExecution, name: string): TaskState {
    return requireValue(execution.tasks.find(t => t.name === name), 'UNKNOWN_TASK');
  }
  invocationEnded(invocation: Invocation): boolean {
    const { state } = this;
    return invocation.status !== 'active'
      && !state.calls.some(c => c.owner === invocation.id && c.task === null && !callEnded(c.status))
      && !state.runs.some(r => r.owner === invocation.id && r.task === null && !r.complete)
      && !state.executions.some(e => e.id === invocation.id && !e.complete);
  }
  eligible(path: Path, connection: Connection): Result[] {
    return this.resultsOf(path, connection.source).filter(r => connection.arm === undefined || r.arm === connection.arm);
  }
  armOutcome(settled: Settled, arm: string | undefined): Outcome {
    return arm === undefined ? settled.outcome : settled.arms.find(a => a.arm === arm)?.outcome ?? settled.outcome;
  }
  resolveSingle(path: Path, index: number, connection: Connection): Resolution {
    const delivery = this.deliveriesOn(path, index)[0];
    if (delivery !== undefined) {
      switch (delivery.outcome.kind) {
        case 'value': return { kind: 'value', source: delivery.source, input: delivery.outcome.value };
        case 'trigger': return { kind: 'value', source: delivery.source, input: null };
        case 'failed': return { kind: 'transformFailed' };
      }
    }
    const settled = this.settledOf(path, connection.source);
    if (settled === undefined) return { kind: 'pending' };
    switch (this.armOutcome(settled, connection.arm)) {
      case 'normal': return { kind: 'pending' };
      case 'skipped': return { kind: 'skipped' };
      default: return { kind: 'failure' };
    }
  }
  streamEnd(path: Path, index: number, connection: Connection): Outcome | undefined {
    const settled = this.settledOf(path, connection.source);
    if (settled === undefined || this.eligible(path, connection).some(r => this.delivery(path, index, r.id) === undefined)) return undefined;
    return this.armOutcome(settled, connection.arm);
  }
  holdsSlot(execution: ConcurrencyExecution, task: TaskState): boolean {
    return task.status === 'active' || this.state.calls.some(c => c.owner === execution.id && c.task === task.name && c.status === 'cancelling');
  }
  taskEnded(execution: ConcurrencyExecution, task: TaskState): boolean {
    return !['pending', 'ready', 'active'].includes(task.status) && !this.holdsSlot(execution, task)
      && !this.state.runs.some(r => r.owner === execution.id && r.task === task.name && !r.complete);
  }
  slotsHeld(execution: ConcurrencyExecution): number {
    return execution.tasks.filter(task => this.holdsSlot(execution, task)).length;
  }
  designatedOutput(run: Run): string {
    if (run.owner === null) throw new Rejection('ROOT_RUN');
    let body: Body;
    if (run.task === null) {
      const invocation = requireValue(this.invocation(run.owner), 'UNKNOWN_INVOCATION');
      const node = this.placementOf(invocation.run, invocation.placement).node;
      if (node.type !== 'function' && node.type !== 'subworkflow') throw new Rejection('NOT_A_CALL');
      body = node;
    } else {
      const execution = requireValue(this.execution(run.owner), 'UNKNOWN_EXECUTION');
      body = this.taskSpec(execution, run.task).body;
    }
    if (body.type !== 'subworkflow') throw new Rejection('NOT_A_WORKFLOW_CALL');
    return body.output;
  }

  settleOutcome(path: Path, placement: Placement, shape: Shape, kind: Kind): Settlement | undefined {
    const invocations = this.invocationsOf(path, placement.name);
    if (invocations.some(i => !this.invocationEnded(i))) return undefined;
    const done = (outcome: Outcome): Settlement => ({ settled: { run: path, placement: placement.name, outcome, arms: [] } });
    const aggregate = (values: string[]): Settlement => {
      const key = keyAggregate(path, placement.name);
      return { ...done('normal'), result: { id: key, run: path, placement: placement.name, producer: key, arm: null, value: listValue(values) } };
    };
    const triggered = (index: number): boolean => this.deliveriesOn(path, index).every(d =>
      d.outcome.kind === 'failed' || this.findInvocation(path, placement.name, d.source) !== undefined);
    const ownFailures = (index: number): number => this.deliveriesOn(path, index).filter(d => d.outcome.kind === 'failed').length
      + invocations.filter(i => i.status === 'failed' || i.status === 'cancelled').length;
    const control = placement.node;
    switch (control.type) {
      case 'waitStream': {
        if (shape.kind !== 'stream') return undefined;
        const ended = this.streamEnd(path, shape.index, shape.connection);
        if (ended === undefined) return undefined;
        if (ended === 'skipped') return done('skipped');
        return aggregate(this.deliveriesOn(path, shape.index).flatMap(d => d.outcome.kind === 'value' ? [d.outcome.value] : []));
      }
      case 'merge': {
        if (shape.kind !== 'merge') return undefined;
        const resolutions = shape.merged.map(input => this.resolveSingle(path, input.index, input.connection));
        if (resolutions.some(r => r.kind === 'pending')) return undefined;
        if (resolutions.every(r => r.kind === 'skipped')) return done('skipped');
        return aggregate(resolutions.flatMap(r => r.kind === 'value' && r.input !== null ? [r.input] : []));
      }
      case 'branch': {
        const arms = (outcome: Outcome, arm: (name: string) => Outcome = () => outcome): Settlement => ({
          settled: { run: path, placement: placement.name, outcome, arms: control.arms.map(name => ({ arm: name, outcome: arm(name) })) },
        });
        const byInvocation = (invocation: Invocation | undefined): Settlement | undefined => {
          if (invocation === undefined) return undefined;
          switch (invocation.status) {
            case 'succeeded': return arms('normal', name => invocation.arm === name ? 'normal' : 'skipped');
            case 'skipped': return arms('skipped');
            case 'upstreamFailed': return arms('upstreamFailed');
            default: return arms('failed');
          }
        };
        switch (shape.kind) {
          case 'entry': return byInvocation(this.findInvocation(path, placement.name, null));
          case 'single': {
            const resolution = this.resolveSingle(path, shape.index, shape.connection);
            switch (resolution.kind) {
              case 'pending': return undefined;
              case 'value': return byInvocation(this.findInvocation(path, placement.name, resolution.source));
              case 'transformFailed': return arms('failed');
              case 'skipped': return arms('skipped');
              case 'failure': return arms('upstreamFailed');
            }
          }
          case 'stream': {
            const ended = this.streamEnd(path, shape.index, shape.connection);
            if (ended === undefined || !triggered(shape.index)) return undefined;
            if (ended === 'skipped') return arms('skipped');
            const chosen = new Set(this.resultsOf(path, placement.name).flatMap(r => r.arm === null ? [] : [r.arm]));
            const failures = ownFailures(shape.index);
            return arms('normal', name => chosen.size > 0 && !chosen.has(name) && failures === 0 ? 'skipped' : 'normal');
          }
          default: return undefined;
        }
      }
      case 'function': case 'subworkflow': case 'concurrency': {
        switch (shape.kind) {
          case 'none': case 'entry': {
            const invocation = this.findInvocation(path, placement.name, null);
            return invocation === undefined ? undefined : done(invocationOutcome(kind, invocation.status));
          }
          case 'single': {
            const resolution = this.resolveSingle(path, shape.index, shape.connection);
            switch (resolution.kind) {
              case 'pending': return undefined;
              case 'value': {
                const invocation = this.findInvocation(path, placement.name, resolution.source);
                return invocation === undefined ? undefined : done(invocationOutcome(kind, invocation.status));
              }
              case 'transformFailed': return done(missingOutcome(kind, 'failed'));
              case 'skipped': return done('skipped');
              case 'failure': return done(missingOutcome(kind, 'upstreamFailed'));
            }
          }
          case 'stream': {
            const ended = this.streamEnd(path, shape.index, shape.connection);
            if (ended === undefined || !triggered(shape.index)) return undefined;
            if (ended === 'skipped') return done('skipped');
            return done(invocations.length > 0 && invocations.every(i => i.status === 'skipped') && ownFailures(shape.index) === 0 ? 'skipped' : 'normal');
          }
          case 'merge': return undefined;
        }
      }
      default: {
        const exhaustive: never = control;
        return exhaustive;
      }
    }
  }
}

function invocationOutcome(kind: Kind, status: InvocationStatus): Outcome {
  switch (status) {
    case 'succeeded': return 'normal';
    case 'skipped': return 'skipped';
    case 'upstreamFailed': return kind === 'stream' ? 'normal' : 'upstreamFailed';
    default: return kind === 'stream' ? 'normal' : 'failed';
  }
}

function missingOutcome(kind: Kind, reason: Outcome): Outcome {
  return kind === 'stream' && reason !== 'skipped' ? 'normal' : reason;
}
