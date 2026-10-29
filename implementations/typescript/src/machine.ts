import {
  exploreValue, keyCallResult, keyChild, keyInvocation, keyList, keyReturned, keyTask,
  keyTaskOutput, listValue, samePath,
} from './identity.js';
import { callEnded, Rejection, requireCondition as require, requireValue, View } from './machine-view.js';
import type {
  Call, CallStatus, Cause, ConcurrencyExecution, Definition, Failure, Invocation, InvocationStatus,
  Op, Path, Policy, Result, State, TaskOutput, TaskResult, TaskState, TaskStatus, Workflow,
} from './model-types.js';

export { Rejection } from './machine-view.js';

export function initialState(): State {
  return { status: 'running', started: false, cancelled: false, runs: [], invocations: [], calls: [],
    executions: [], results: [], taskResults: [], deliveries: [], settled: [], failures: [] };
}

export function stateValues(state: State): string[] {
  const values: string[] = [];
  const add = (value: string | null): void => { if (value !== null) values.push(value); };
  for (const run of state.runs) add(run.input);
  for (const invocation of state.invocations) add(invocation.input);
  for (const call of state.calls) add(call.input);
  for (const execution of state.executions) {
    add(execution.input);
    for (const task of execution.tasks) add(task.input);
  }
  for (const result of state.results) values.push(result.value);
  for (const delivery of state.deliveries) if (delivery.outcome.kind === 'value') values.push(delivery.outcome.value);
  for (const result of state.taskResults) {
    values.push(result.value);
    if (result.output.kind === 'value') values.push(result.output.value);
  }
  return values;
}

export function step(definition: Definition, state: State, op: Op): State {
  const next = { ...state };
  new Stepper(definition, next).apply(op);
  return next;
}

type Owner = { kind: 'invocation'; invocation: Invocation }
  | { kind: 'task'; execution: ConcurrencyExecution; task: TaskState };
type Acceptance = { kind: 'result'; result: Result } | { kind: 'taskResult'; result: TaskResult };

class Stepper extends View {
  private running(): void { require(this.state.started && this.state.status === 'running', 'NOT_RUNNING'); }
  private getCall(id: string): Call { return requireValue(this.call(id), 'UNKNOWN_CALL'); }
  private getExecution(id: string): ConcurrencyExecution { return requireValue(this.execution(id), 'UNKNOWN_EXECUTION'); }
  private setCall(call: Call, status: CallStatus, yields = call.yields): void {
    this.state.calls = this.state.calls.map(c => c.id === call.id ? { ...c, status, yields } : c);
  }
  private setInvocation(invocation: Invocation, status: InvocationStatus, arm = invocation.arm): void {
    this.state.invocations = this.state.invocations.map(i => i.id === invocation.id ? { ...i, status, arm } : i);
  }
  private setTask(execution: ConcurrencyExecution, task: TaskState): void {
    const next = { ...execution, tasks: execution.tasks.map(t => t.name === task.name ? task : t) };
    this.state.executions = this.state.executions.map(e => e.id === execution.id ? next : e);
  }
  private completeRun(path: Path): void {
    this.state.runs = this.state.runs.map(r => samePath(r.path, path) ? { ...r, complete: true } : r);
  }
  private completeExecution(id: string): void {
    const next = { ...this.getExecution(id), complete: true };
    this.state.executions = this.state.executions.map(e => e.id === id ? next : e);
  }
  private setTaskOutput(result: TaskResult, output: TaskOutput): void {
    this.state.taskResults = this.state.taskResults.map(r => r.execution === result.execution && r.task === result.task && r.index === result.index
      ? { ...r, output } : r);
  }
  private addResult(result: Result): void { this.state.results = [...this.state.results, result]; }
  private addTaskResult(result: TaskResult): void { this.state.taskResults = [...this.state.taskResults, result]; }
  private stop(): void {
    this.state.status = 'stopping';
    this.state.calls = this.state.calls.map(c => c.status === 'running' || c.status === 'fetching' ? { ...c, status: 'cancelling' } : c);
    this.state.executions = this.state.executions.map(e => ({ ...e, tasks: e.tasks.map(t =>
      t.status === 'pending' || t.status === 'ready' ? { ...t, status: 'notStarted' } : t) }));
  }
  private endUnfinished(): void {
    this.state.invocations = this.state.invocations.map(i => i.status === 'active' ? { ...i, status: 'cancelled' } : i);
    this.state.executions = this.state.executions.map(e => ({ ...e, tasks: e.tasks.map(t => {
      if (t.status === 'active') return { ...t, status: 'cancelled' };
      if (t.status === 'pending' || t.status === 'ready') return { ...t, status: 'notStarted' };
      return t;
    }) }));
  }
  private fail(failure: Failure, policy: Policy): void {
    this.state.failures = [...this.state.failures, failure];
    if (policy === 'stop') this.stop();
  }
  private ownerOf(call: Call): Owner {
    if (call.task === null) return { kind: 'invocation', invocation: requireValue(this.invocation(call.owner), 'UNKNOWN_INVOCATION') };
    const execution = this.getExecution(call.owner);
    return { kind: 'task', execution, task: this.task(execution, call.task) };
  }
  private callFailure(call: Call, cause: Cause): Failure {
    if (call.task === null) {
      const invocation = requireValue(this.invocation(call.owner), 'UNKNOWN_INVOCATION');
      return { run: invocation.run, placement: invocation.placement, task: null, cause };
    }
    const execution = this.getExecution(call.owner);
    return { run: execution.run, placement: execution.placement, task: call.task, cause };
  }
  private accept(call: Call, index: number, value: string, arm: string | null): Acceptance {
    if (call.task === null) {
      const invocation = requireValue(this.invocation(call.owner), 'UNKNOWN_INVOCATION');
      const result: Result = { id: keyCallResult(call.id, index), run: invocation.run, placement: invocation.placement,
        producer: call.id, arm, value };
      require(this.result(result.id) === undefined, 'DUPLICATE_RESULT');
      return { kind: 'result', result };
    }
    require(this.taskResult(call.owner, call.task, index) === undefined, 'DUPLICATE_RESULT');
    return { kind: 'taskResult', result: { execution: call.owner, task: call.task, index, value, output: { kind: 'pending' } } };
  }
  private addAccepted(acceptance: Acceptance): void {
    if (acceptance.kind === 'result') this.addResult(acceptance.result);
    else this.addTaskResult(acceptance.result);
  }
  private settleOwner(owner: Owner, invocation: InvocationStatus, task: TaskStatus): void {
    if (owner.kind === 'invocation') this.setInvocation(owner.invocation, invocation);
    else this.setTask(owner.execution, { ...owner.task, status: task });
  }
  private cancelOwner(owner: Owner): void {
    if (owner.kind === 'invocation') {
      if (owner.invocation.status === 'active') this.setInvocation(owner.invocation, 'cancelled');
    } else if (owner.task.status === 'active') this.setTask(owner.execution, { ...owner.task, status: 'cancelled' });
  }
  private failCall(call: Call, status: CallStatus, cause: Cause): void {
    const failure = this.callFailure(call, cause);
    const owner = this.ownerOf(call);
    this.setCall(call, status);
    this.settleOwner(owner, 'failed', 'failed');
    this.fail(failure, call.policy);
  }

  apply(op: Op): void {
    switch (op.type) {
      case 'start': return this.start(op.input ?? null);
      case 'invoke': return this.invoke(op.run, op.placement, op.trigger ?? null);
      case 'fetch': return this.fetch(op.call);
      case 'returned': return this.returned(op.call, op.value);
      case 'judged': return this.judged(op.call, op.arm);
      case 'yielded': return this.yielded(op.call, op.value);
      case 'ended': return this.ended(op.call);
      case 'failed': return this.failed(op.call);
      case 'timedOut': return this.timedOut(op.call, op.element);
      case 'lost': return this.lost(op.call);
      case 'terminated': return this.terminated(op.call);
      case 'deliver': return this.deliver(op.run, op.connection, op.source, op.value ?? null);
      case 'transformFailed': return this.transformFailed(op.run, op.connection, op.source);
      case 'taskInput': return this.taskInput(op.execution, op.task, op.value ?? null);
      case 'taskInputFailed': return this.taskInputFailed(op.execution, op.task);
      case 'beginTask': return this.beginTask(op.execution, op.task);
      case 'taskOutput': return this.taskOutput(op.execution, op.task, op.index, op.value);
      case 'taskOutputFailed': return this.taskOutputFailed(op.execution, op.task, op.index);
      case 'settle': return this.settle(op.run, op.placement);
      case 'closeExecution': return this.closeExecution(op.execution);
      case 'closeRun': return this.closeRun(op.run);
      case 'cancel': return this.cancel();
      case 'conclude': return this.conclude();
      default: { const exhaustive: never = op; return exhaustive; }
    }
  }

  private start(input: string | null): void {
    require(!this.state.started && this.state.status === 'running', 'ALREADY_STARTED');
    const workflow = requireValue(this.workflowByID(this.def.main), 'UNKNOWN_MAIN');
    require((workflow.input !== undefined) === (input !== null), 'INPUT_MISMATCH');
    this.state.started = true;
    this.state.runs = [{ path: [], workflow: this.def.main, input, owner: null, task: null, complete: false }];
  }
  private invocationInput(path: Path, input: string | null, workflow: Workflow, name: string, trigger: string | null): string | null {
    const shape = requireValue(this.shape(workflow, name), 'INVALID_SHAPE');
    if (shape.kind === 'none' && trigger === null) return null;
    if (shape.kind === 'entry' && trigger === null) return input;
    if (shape.kind === 'single' && trigger !== null) {
      const resolution = this.resolveSingle(path, shape.index, shape.connection);
      require(resolution.kind === 'value', 'INPUT_NOT_READY');
      require(resolution.source === trigger, 'WRONG_TRIGGER');
      return resolution.input;
    }
    if (shape.kind === 'stream' && trigger !== null) {
      const delivery = this.delivery(path, shape.index, trigger);
      if (delivery?.outcome.kind === 'value') return delivery.outcome.value;
      if (delivery?.outcome.kind === 'trigger') return null;
      throw new Rejection('INPUT_NOT_READY');
    }
    throw new Rejection('INVALID_TRIGGER');
  }
  private invoke(path: Path, name: string, trigger: string | null): void {
    this.running();
    const run = requireValue(this.run(path), 'UNKNOWN_RUN');
    require(!run.complete, 'RUN_COMPLETE');
    const workflow = requireValue(this.workflowByID(run.workflow), 'UNKNOWN_WORKFLOW');
    const placement = requireValue(workflow.placements.find(p => p.name === name), 'UNKNOWN_PLACEMENT');
    const input = this.invocationInput(path, run.input, workflow, name, trigger);
    const id = keyInvocation(path, name, trigger);
    require(this.findInvocation(path, name, trigger) === undefined && this.invocation(id) === undefined, 'DUPLICATE_INVOCATION');
    const invocation: Invocation = { id, run: path, placement: name, trigger, input, status: 'active', arm: null };
    const node = placement.node;
    switch (node.type) {
      case 'function': {
        const declaration = requireValue(this.def.functions.find(f => f.id === node.function), 'UNKNOWN_FUNCTION');
        require(this.call(id) === undefined, 'DUPLICATE_CALL');
        this.state.invocations = [...this.state.invocations, invocation];
        this.state.calls = [...this.state.calls, { id, owner: id, task: null, target: { kind: 'function', id: node.function }, input,
          stream: 'stream' in declaration.output, status: 'running', yields: 0, timeout: placement.timeout ?? {}, policy: placement.policy }];
        return;
      }
      case 'subworkflow': {
        const child = keyChild(id);
        require(this.run(child) === undefined, 'DUPLICATE_RUN');
        this.state.invocations = [...this.state.invocations, invocation];
        this.state.runs = [...this.state.runs, { path: child, workflow: node.workflow, input, owner: id, task: null, complete: false }];
        return;
      }
      case 'branch': {
        require(this.call(id) === undefined, 'DUPLICATE_CALL');
        this.state.invocations = [...this.state.invocations, invocation];
        this.state.calls = [...this.state.calls, { id, owner: id, task: null, target: { kind: 'judge', id: node.judge }, input,
          stream: false, status: 'running', yields: 0, timeout: placement.timeout ?? {}, policy: placement.policy }];
        return;
      }
      case 'concurrency': {
        require(this.execution(id) === undefined, 'DUPLICATE_EXECUTION');
        const tasks: TaskState[] = node.tasks.map(task => ({ name: task.name, input: null, status: node.input === undefined ? 'ready' : 'pending' }));
        this.state.invocations = [...this.state.invocations, invocation];
        this.state.executions = [...this.state.executions, { id, run: path, placement: name, input, tasks, complete: false }];
        return;
      }
      default: throw new Rejection('NOT_INVOCABLE');
    }
  }
  private fetch(id: string): void {
    this.running();
    const call = this.getCall(id);
    require(call.stream && call.status === 'running', 'NOT_FETCHABLE');
    this.setCall(call, 'fetching');
  }
  private returned(id: string, value: string): void {
    this.running();
    const call = this.getCall(id);
    require(!call.stream && call.status === 'running' && call.target.kind !== 'judge', 'NOT_RETURNABLE');
    const accepted = this.accept(call, 0, value, null);
    const owner = this.ownerOf(call);
    this.addAccepted(accepted);
    this.setCall(call, 'returned');
    this.settleOwner(owner, 'succeeded', 'succeeded');
  }
  private judged(id: string, arm: string): void {
    this.running();
    const call = this.getCall(id);
    require(call.status === 'running' && call.target.kind === 'judge' && call.task === null, 'NOT_JUDGING');
    const invocation = requireValue(this.invocation(call.owner), 'UNKNOWN_INVOCATION');
    const node = this.placementOf(invocation.run, invocation.placement).node;
    require(node.type === 'branch', 'NOT_BRANCH');
    require(node.arms.includes(arm), 'UNKNOWN_ARM');
    const accepted = this.accept(call, 0, invocation.input ?? '', arm);
    this.addAccepted(accepted);
    this.setCall(call, 'returned');
    this.setInvocation(invocation, 'succeeded', arm);
  }
  private yielded(id: string, value: string): void {
    this.running();
    const call = this.getCall(id);
    require(call.stream && call.status === 'fetching', 'NOT_FETCHING');
    const accepted = this.accept(call, call.yields, value, null);
    this.addAccepted(accepted);
    this.setCall(call, 'running', call.yields + 1);
  }
  private ended(id: string): void {
    this.running();
    const call = this.getCall(id);
    require(call.stream && call.status === 'fetching', 'NOT_FETCHING');
    const owner = this.ownerOf(call);
    this.setCall(call, 'returned');
    this.settleOwner(owner, 'succeeded', 'succeeded');
  }
  private failed(id: string): void {
    this.running();
    const call = this.getCall(id);
    require(call.status === 'running' || call.status === 'fetching', 'NOT_RUNNING');
    this.failCall(call, 'failed', 'error');
  }
  private timedOut(id: string, element: boolean): void {
    this.running();
    const call = this.getCall(id);
    require(element ? call.status === 'fetching' && call.timeout.elementMs !== undefined
      : (call.status === 'running' || call.status === 'fetching') && call.timeout.callMs !== undefined, 'NO_TIMEOUT');
    this.failCall(call, 'cancelling', 'timeout');
  }
  private lost(id: string): void {
    require(this.state.started && (this.state.status === 'running' || this.state.status === 'stopping'), 'TERMINAL');
    const call = this.getCall(id);
    if (call.status === 'running' || call.status === 'fetching') return this.failCall(call, 'lost', 'lost');
    if (call.status === 'cancelling') return this.cancelled(call);
    throw new Rejection('NOT_RUNNING');
  }
  private cancelled(call: Call): void {
    const owner = this.ownerOf(call);
    this.setCall(call, 'cancelled');
    this.cancelOwner(owner);
  }
  private terminated(id: string): void {
    require(this.state.started && (this.state.status === 'running' || this.state.status === 'stopping'), 'TERMINAL');
    const call = this.getCall(id);
    require(call.status === 'cancelling', 'NOT_CANCELLING');
    this.cancelled(call);
  }
  private deliveryTarget(path: Path, index: number, source: string) {
    const workflow = requireValue(this.workflow(path), 'UNKNOWN_RUN');
    const connection = requireValue(workflow.connections[index], 'UNKNOWN_CONNECTION');
    const result = requireValue(this.result(source), 'UNKNOWN_RESULT');
    require(samePath(result.run, path) && result.placement === connection.source
      && (connection.arm === undefined || result.arm === connection.arm), 'NOT_ELIGIBLE');
    require(this.delivery(path, index, source) === undefined, 'DUPLICATE_DELIVERY');
    return { workflow, connection };
  }
  private deliver(path: Path, index: number, source: string, value: string | null): void {
    this.running();
    const { connection } = this.deliveryTarget(path, index, source);
    require((connection.transform === 'discard') === (value === null), 'TRANSFORM_MISMATCH');
    this.state.deliveries = [...this.state.deliveries, { run: path, connection: index, source,
      outcome: value === null ? { kind: 'trigger' } : { kind: 'value', value } }];
  }
  private transformFailed(path: Path, index: number, source: string): void {
    this.running();
    const { workflow, connection } = this.deliveryTarget(path, index, source);
    require(connection.transform !== 'discard', 'DISCARD_CANNOT_FAIL');
    const target = requireValue(workflow.placements.find(p => p.name === connection.target), 'UNKNOWN_PLACEMENT');
    this.state.deliveries = [...this.state.deliveries, { run: path, connection: index, source, outcome: { kind: 'failed' } }];
    this.fail({ run: path, placement: connection.target, task: null, cause: 'transform' }, target.policy);
  }
  private taskInput(id: string, name: string, value: string | null): void {
    this.running();
    const execution = this.getExecution(id);
    const task = this.task(execution, name);
    require(task.status === 'pending', 'NOT_PENDING');
    const spec = this.taskSpec(execution, name);
    require(spec.inputTransform !== undefined && (spec.inputTransform === 'discard') === (value === null), 'TRANSFORM_MISMATCH');
    this.setTask(execution, { ...task, status: 'ready', input: value });
  }
  private taskInputFailed(id: string, name: string): void {
    this.running();
    const execution = this.getExecution(id);
    const task = this.task(execution, name);
    require(task.status === 'pending', 'NOT_PENDING');
    const spec = this.taskSpec(execution, name);
    require(spec.inputTransform !== undefined && spec.inputTransform !== 'discard', 'DISCARD_CANNOT_FAIL');
    this.setTask(execution, { ...task, status: 'failed' });
    this.fail({ run: execution.run, placement: execution.placement, task: name, cause: 'transform' }, spec.policy);
  }
  private beginTask(id: string, name: string): void {
    this.running();
    const execution = this.getExecution(id);
    require(!execution.complete, 'EXECUTION_COMPLETE');
    const concurrency = this.concurrencyOf(execution);
    const task = this.task(execution, name);
    require(task.status === 'ready', 'NOT_READY');
    require(BigInt(this.slotsHeld(execution)) < concurrency.limit, 'NO_SLOT');
    const spec = this.taskSpec(execution, name);
    const callID = keyTask(execution.id, name);
    const body = spec.body;
    if (body.type === 'function') {
      const declaration = requireValue(this.def.functions.find(f => f.id === body.function), 'UNKNOWN_FUNCTION');
      require(this.call(callID) === undefined, 'DUPLICATE_CALL');
      this.setTask(execution, { ...task, status: 'active' });
      this.state.calls = [...this.state.calls, { id: callID, owner: id, task: name, target: { kind: 'function', id: body.function },
        input: task.input, stream: 'stream' in declaration.output, timeout: spec.timeout ?? {}, policy: spec.policy, status: 'running', yields: 0 }];
      return;
    }
    const child = keyChild(callID);
    require(this.run(child) === undefined, 'DUPLICATE_RUN');
    this.setTask(execution, { ...task, status: 'active' });
    this.state.runs = [...this.state.runs, { path: child, workflow: body.workflow, input: task.input, owner: id, task: name, complete: false }];
  }
  private taskOutput(id: string, name: string, index: number, value: string): void {
    this.running();
    const execution = this.getExecution(id);
    const concurrency = this.concurrencyOf(execution);
    const spec = this.taskSpec(execution, name);
    require(spec.outputTransform !== undefined, 'NOT_IN_OUTPUT');
    const taskResult = requireValue(this.taskResult(id, name, index), 'UNKNOWN_RESULT');
    require(taskResult.output.kind === 'pending', 'ALREADY_TRANSFORMED');
    if (concurrency.output === 'list') {
      this.setTaskOutput(taskResult, { kind: 'value', value });
      return;
    }
    const result: Result = { id: keyTaskOutput(id, name, index), run: execution.run, placement: execution.placement, producer: id, arm: null, value };
    require(this.result(result.id) === undefined, 'DUPLICATE_RESULT');
    this.setTaskOutput(taskResult, { kind: 'value', value });
    this.addResult(result);
  }
  private taskOutputFailed(id: string, name: string, index: number): void {
    this.running();
    const execution = this.getExecution(id);
    const spec = this.taskSpec(execution, name);
    require(spec.outputTransform !== undefined, 'NOT_IN_OUTPUT');
    const result = requireValue(this.taskResult(id, name, index), 'UNKNOWN_RESULT');
    require(result.output.kind === 'pending', 'ALREADY_TRANSFORMED');
    this.setTaskOutput(result, { kind: 'failed' });
    this.fail({ run: execution.run, placement: execution.placement, task: name, cause: 'transform' }, spec.policy);
  }
  private settle(path: Path, name: string): void {
    this.running();
    const run = requireValue(this.run(path), 'UNKNOWN_RUN');
    require(!run.complete, 'RUN_COMPLETE');
    const workflow = requireValue(this.workflowByID(run.workflow), 'UNKNOWN_WORKFLOW');
    const placement = requireValue(workflow.placements.find(p => p.name === name), 'UNKNOWN_PLACEMENT');
    require(this.settledOf(path, name) === undefined, 'ALREADY_SETTLED');
    const shape = requireValue(this.shape(workflow, name), 'INVALID_SHAPE');
    const kind = requireValue(this.kinds(workflow).get(name), 'INVALID_KIND');
    const { settled, result } = requireValue(this.settleOutcome(path, placement, shape, kind), 'NOT_READY');
    if (result !== undefined) require(this.result(result.id) === undefined, 'DUPLICATE_RESULT');
    this.state.settled = [...this.state.settled, settled];
    if (result !== undefined) this.addResult(result);
  }
  private closeExecution(id: string): void {
    this.running();
    const execution = this.getExecution(id);
    require(!execution.complete, 'EXECUTION_COMPLETE');
    const concurrency = this.concurrencyOf(execution);
    require(execution.tasks.every(t => this.taskEnded(execution, t)), 'TASKS_RUNNING');
    const included = concurrency.tasks.filter(t => t.outputTransform !== undefined).map(t => t.name);
    const outputs = this.state.taskResults.filter(r => r.execution === id && included.includes(r.task));
    require(outputs.every(r => r.output.kind !== 'pending'), 'OUTPUT_PENDING');
    const invocation = requireValue(this.invocation(id), 'UNKNOWN_INVOCATION');
    if (execution.tasks.every(t => !included.includes(t.name) || t.status === 'skipped')) {
      this.completeExecution(id);
      this.setInvocation(invocation, 'skipped');
      return;
    }
    if (concurrency.output === 'stream') {
      this.completeExecution(id);
      this.setInvocation(invocation, 'succeeded');
      return;
    }
    const values = outputs.flatMap(r => r.output.kind === 'value' ? [r.output.value] : []);
    const result: Result = { id: keyList(id), run: execution.run, placement: execution.placement, producer: id, arm: null, value: listValue(values) };
    require(this.result(result.id) === undefined, 'DUPLICATE_RESULT');
    this.completeExecution(id);
    this.setInvocation(invocation, 'succeeded');
    this.addResult(result);
  }
  private closeRun(path: Path): void {
    this.running();
    const run = requireValue(this.run(path), 'UNKNOWN_RUN');
    require(!run.complete && path.length !== 0, 'NOT_CLOSABLE');
    const workflow = requireValue(this.workflowByID(run.workflow), 'UNKNOWN_WORKFLOW');
    require(workflow.placements.every(p => this.settledOf(path, p.name) !== undefined), 'NOT_SETTLED');
    const output = this.designatedOutput(run);
    const settled = requireValue(this.settledOf(path, output), 'NOT_SETTLED');
    const value = this.resultsOf(path, output)[0]?.value;
    require(run.owner !== null, 'ROOT_RUN');
    if (run.task === null) {
      const invocation = requireValue(this.invocation(run.owner), 'UNKNOWN_INVOCATION');
      if (settled.outcome === 'normal') {
        const result: Result = { id: keyReturned(invocation.id), run: invocation.run, placement: invocation.placement, producer: invocation.id,
          arm: null, value: requireValue(value, 'MISSING_RESULT') };
        require(this.result(result.id) === undefined, 'DUPLICATE_RESULT');
        this.completeRun(path);
        this.setInvocation(invocation, 'succeeded');
        this.addResult(result);
      } else {
        this.completeRun(path);
        this.setInvocation(invocation, settled.outcome);
      }
      return;
    }
    const execution = this.getExecution(run.owner);
    const task = this.task(execution, run.task);
    if (settled.outcome === 'normal') {
      const result: TaskResult = { execution: execution.id, task: task.name, index: 0, value: requireValue(value, 'MISSING_RESULT'), output: { kind: 'pending' } };
      require(this.taskResult(execution.id, task.name, 0) === undefined, 'DUPLICATE_RESULT');
      this.completeRun(path);
      this.setTask(execution, { ...task, status: 'succeeded' });
      this.addTaskResult(result);
    } else {
      this.completeRun(path);
      this.setTask(execution, { ...task, status: settled.outcome });
    }
  }
  private cancel(): void {
    require(this.state.started, 'NOT_STARTED');
    if (this.state.status === 'running') this.stop();
    else require(this.state.status === 'stopping', 'TERMINAL');
    this.state.cancelled = true;
  }
  private conclude(): void {
    require(this.state.started, 'NOT_STARTED');
    if (this.state.status === 'running') {
      const root = requireValue(this.run([]), 'NO_ROOT');
      const workflow = requireValue(this.workflowByID(root.workflow), 'UNKNOWN_WORKFLOW');
      require(workflow.placements.every(p => this.settledOf([], p.name) !== undefined), 'NOT_SETTLED');
      const allSkipped = workflow.placements.filter(p => !workflow.connections.some(c => c.source === p.name))
        .every(p => this.settledOf([], p.name)?.outcome === 'skipped');
      this.completeRun([]);
      this.state.status = this.state.failures.length > 0 ? 'failed' : allSkipped ? 'skipped' : 'succeeded';
      return;
    }
    if (this.state.status === 'stopping') {
      require(this.state.calls.every(c => callEnded(c.status)), 'CALLS_RUNNING');
      this.endUnfinished();
      this.state.status = this.state.failures.length > 0 ? 'failed' : 'cancelled';
      return;
    }
    throw new Rejection('TERMINAL');
  }
}

export function controlCandidates(definition: Definition, state: State): Op[] {
  if (!state.started) return [];
  if (state.status === 'stopping') return [{ type: 'conclude' }];
  if (state.status !== 'running') return [];
  const view = new View(definition, state);
  const invoked = new Set(state.invocations.map(i => JSON.stringify([i.run, i.placement, i.trigger])));
  const delivered = new Set(state.deliveries.map(d => JSON.stringify([d.run, d.connection, d.source])));
  const settled = new Set(state.settled.map(s => JSON.stringify([s.run, s.placement])));
  const ops: Op[] = state.calls.filter(c => c.stream && c.status === 'running').map(c => ({ type: 'fetch', call: c.id }));
  const closing: Op[] = [];
  for (const run of state.runs) {
    if (run.complete) continue;
    const workflow = view.workflowByID(run.workflow);
    if (workflow === undefined) continue;
    if (run.path.length !== 0) closing.push({ type: 'closeRun', run: run.path });
    for (const placement of workflow.placements) {
      if (settled.has(JSON.stringify([run.path, placement.name]))) continue;
      closing.push({ type: 'settle', run: run.path, placement: placement.name });
      if (placement.node.type === 'waitStream' || placement.node.type === 'merge') continue;
      const shape = view.shape(workflow, placement.name);
      if (shape === undefined) continue;
      if (shape.kind === 'none' || shape.kind === 'entry') {
        if (!invoked.has(JSON.stringify([run.path, placement.name, null]))) {
          ops.push({ type: 'invoke', run: run.path, placement: placement.name });
        }
      } else if (shape.kind === 'single') {
        const resolution = view.resolveSingle(run.path, shape.index, shape.connection);
        if (resolution.kind === 'value' && !invoked.has(JSON.stringify([run.path, placement.name, resolution.source]))) {
          ops.push({ type: 'invoke', run: run.path, placement: placement.name, trigger: resolution.source });
        }
      } else if (shape.kind === 'stream') {
        for (const delivery of view.deliveriesOn(run.path, shape.index)) {
          if (delivery.outcome.kind !== 'failed' && !invoked.has(JSON.stringify([run.path, placement.name, delivery.source]))) {
            ops.push({ type: 'invoke', run: run.path, placement: placement.name, trigger: delivery.source });
          }
        }
      }
    }
  }
  for (const result of state.results) {
    const workflow = view.workflow(result.run);
    if (workflow === undefined) continue;
    workflow.connections.forEach((connection, index) => {
      if (connection.source !== result.placement || (connection.arm !== undefined && result.arm !== connection.arm)
        || delivered.has(JSON.stringify([result.run, index, result.id]))) return;
      const op: Op = { type: 'deliver', run: result.run, connection: index, source: result.id };
      if (connection.transform !== 'discard') op.value = exploreValue('transform', String(index), result.id);
      ops.push(op);
    });
  }
  const executionClosures: Op[] = [];
  for (const execution of state.executions) {
    if (execution.complete) continue;
    for (const task of execution.tasks) {
      let spec;
      try { spec = view.taskSpec(execution, task.name); } catch (error) { if (error instanceof Rejection) continue; throw error; }
      if (task.status === 'pending' && spec.inputTransform !== undefined) {
        const op: Op = { type: 'taskInput', execution: execution.id, task: task.name };
        if (spec.inputTransform !== 'discard') op.value = exploreValue('input', execution.id, task.name);
        ops.push(op);
      } else if (task.status === 'ready') ops.push({ type: 'beginTask', execution: execution.id, task: task.name });
    }
    for (const result of state.taskResults) {
      if (result.execution === execution.id && result.output.kind === 'pending') {
        ops.push({ type: 'taskOutput', execution: execution.id, task: result.task, index: result.index,
          value: exploreValue('output', execution.id, result.task, String(result.index)) });
      }
    }
    executionClosures.push({ type: 'closeExecution', execution: execution.id });
  }
  return [...ops, ...executionClosures, ...closing, { type: 'conclude' }];
}
