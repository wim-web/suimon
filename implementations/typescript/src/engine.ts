import { setImmediate } from 'node:timers/promises';
import type { Concurrency, Definition, Op, Path, Payload, State, TaskSpec, Workflow } from './model-types.js';
import type { Binding, EngineOptions, Execution, Journal, Limits, Report, RecoverableJournal, ResumeOptions, StartOptions } from './runtime-types.js';
import { checkDefinitionRepresentation, checkDefinitionResources, encodeDefinition, parseDefinition, validateDefinition } from './definition.js';
import { controlCandidates, initialState, Rejection, step } from './machine.js';
import { decodeIdentity, exploreValue, identity } from './identity.js';
import { checkTrace, encodeHeader, encodeRecord, introduced } from './trace.js';
import { Bindings, Callback, decodeValue, encodeValue, scheduleTimer, synchronousTransformResult } from './callbacks.js';
import type { CallbackEvent } from './callbacks.js';
import { Budget, byteLength, checkLine, ended, engineLimits, QuotaError, terminal } from './limits.js';

export class TimeoutError extends Error {
  constructor(call: string, milliseconds: bigint, element: boolean) {
    super(`suimon: timed out: ${call} ${element ? 'waited for an element' : 'ran'} longer than ${milliseconds} ms`);
    this.name = 'TimeoutError';
  }
}
export class LostError extends Error {
  constructor() { super('suimon: the executor of the call was lost'); this.name = 'LostError'; }
}
export class StuckError extends Error {
  constructor(status: string) { super(`suimon: the execution cannot progress in status ${status}`); this.name = 'StuckError'; }
}

export class Engine {
  private readonly definition: Definition;
  private readonly bindings: Bindings;
  private readonly header: string;
  private readonly limits: Limits;
  private active = 0;

  constructor(definition: Definition, bindings: readonly Binding[], options: EngineOptions = {}) {
    checkDefinitionResources(definition);
    checkDefinitionRepresentation(definition);
    const canonical = encodeDefinition(definition);
    this.definition = parseDefinition(canonical);
    if (encodeDefinition(this.definition) !== canonical) throw new Error('suimon: the definition cannot be recorded faithfully');
    if (options.validate !== false) validateDefinition(this.definition);
    this.header = encodeHeader(this.definition, options.validate !== false) + '\n';
    checkLine(this.header.slice(0, -1));
    this.bindings = new Bindings(this.definition, bindings);
    this.limits = engineLimits(options.limits);
  }

  private acquire(): void {
    if (this.active >= this.limits.maxWorkflows) throw new QuotaError('workflows', this.limits.maxWorkflows);
    this.active++;
  }

  async start(input?: unknown, options: StartOptions = {}): Promise<Execution> {
    this.acquire();
    try {
      const driver = new Driver(this.definition, this.bindings, new Budget(this.limits, byteLength(this.header)), options.journal, initialState(), [], 0);
      const main = this.definition.workflows.find(workflow => workflow.id === this.definition.main);
      let op: Op = { type: 'start' };
      let payload: Payload | undefined;
      if (main?.input) {
        if (input === undefined) throw new Error('suimon: the main workflow requires an input');
        const value = exploreValue('input');
        payload = { value, payload: encodeValue(input) };
        op = { type: 'start', input: value };
      } else if (input !== undefined && input !== null) {
        throw new Error('suimon: the main workflow takes no input');
      }
      if (!await driver.apply(op, undefined, payload, this.header)) throw new Error('suimon: the start is rejected');
      return driver.launch(options.signal, () => { this.active--; });
    } catch (error) { this.active--; throw error; }
  }

  async run(input?: unknown, options: StartOptions = {}): Promise<Report> {
    return (await this.start(input, options)).wait();
  }

  async resume(journal: RecoverableJournal, options: ResumeOptions = {}): Promise<Execution> {
    this.acquire();
    try {
      const bytes = await journal.contents(this.limits.maxJournalBytes);
      if (bytes.byteLength > this.limits.maxJournalBytes) throw new QuotaError('journal bytes', this.limits.maxJournalBytes);
      const checked = checkTrace(bytes, this.definition);
      if (!checked.committed) throw new Error('suimon: the journal records no start');
      const budget = new Budget(this.limits);
      budget.restore(checked.state, checked.values, checked.committed, checked.length);
      if (checked.length < bytes.byteLength) await journal.truncate(checked.length);
      const driver = new Driver(this.definition, this.bindings, budget, journal, checked.state, checked.values, checked.committed);
      for (const call of checked.state.calls) {
        if (ended(call)) continue;
        const lost: Op = { type: 'lost', call: call.id };
        if (!await driver.apply(lost, new LostError())) {
          if (!await driver.apply(lost, new LostError())) throw new Error(`suimon: reporting call ${call.id} lost was rejected`);
        }
      }
      return driver.launch(options.signal, () => { this.active--; });
    } catch (error) { this.active--; throw error; }
  }
}

type Event = CallbackEvent
  | { kind: 'timer'; call: string; element: boolean; index: number; callback: Callback }
  | { kind: 'cancel' } | { kind: 'deadline' };

class Driver {
  private state: State;
  private readonly payloads = new Map<string, string>();
  private readonly errors: unknown[];
  private readonly callbacks = new Map<string, Callback>();
  private readonly events: Event[] = [];
  private wake: (() => void) | undefined;
  private seq: number;
  private closed = false;
  private cancelRequested = false;
  private quota: QuotaError | undefined;

  constructor(private readonly definition: Definition, private readonly bindings: Bindings,
    private readonly budget: Budget, private readonly journal: Journal | undefined,
    state: State, payloads: readonly Payload[], committed: number) {
    this.state = state;
    this.errors = state.failures.map(() => undefined);
    this.seq = 2 * committed + 1;
    for (const item of payloads) this.payloads.set(item.value, item.payload);
  }

  private send(event: Event): void {
    if (this.closed) return;
    this.events.push(event);
    this.wake?.();
  }

  launch(signal: AbortSignal | undefined, release: () => void): Execution {
    const cancel = (): void => {
      if (this.cancelRequested || this.closed) return;
      this.cancelRequested = true;
      this.send({ kind: 'cancel' });
    };
    signal?.addEventListener('abort', cancel, { once: true });
    if (signal?.aborted) cancel();
    const stopDeadline = scheduleTimer(BigInt(Math.max(0, Math.ceil(this.budget.deadline - performance.now()))), () => this.send({ kind: 'deadline' }));
    const wait = this.loop().catch(async (error: unknown) => {
      for (const callback of this.callbacks.values()) callback.cancel();
      await Promise.all([...this.callbacks.values()].map(callback => callback.done));
      throw error;
    }).finally(() => {
      this.closed = true;
      stopDeadline();
      signal?.removeEventListener('abort', cancel);
      release();
    });
    void wait.catch(() => {});
    return { cancel, wait: () => wait };
  }

  private async loop(): Promise<Report> {
    let turns = 0;
    while (!terminal(this.state)) {
      if (++turns % 64 === 0) await setImmediate();
      const event = this.events.shift();
      if (event) { await this.handle(event); continue; }
      let progressed = false;
      for (const op of controlCandidates(this.definition, this.state)) {
        let candidate: State;
        try { candidate = step(this.definition, this.state, op); }
        catch (error) { if (error instanceof Rejection) continue; throw error; }
        const transformed = this.transform(op);
        if (await this.apply(transformed.op, transformed.error, transformed.payload, '', transformed.op === op ? candidate : undefined)) {
          progressed = true;
          break;
        }
        if (this.state.status !== 'running') { progressed = true; break; }
      }
      if (progressed) continue;
      if (!this.callbacks.size) throw new StuckError(this.state.status);
      if (this.events.length) continue;
      await new Promise<void>(resolve => { this.wake = resolve; });
      this.wake = undefined;
    }
    const report = this.report();
    if (this.quota) { this.quota.report = report; throw this.quota; }
    return report;
  }

  private workflow(path: Path): Workflow | undefined {
    const run = this.state.runs.find(item => identity(...item.path) === identity(...path));
    return this.definition.workflows.find(item => item.id === run?.workflow);
  }

  private task(execution: string, task: string): { spec: TaskSpec; input: string | null; concurrency: Concurrency } | undefined {
    const owner = this.state.executions.find(item => item.id === execution);
    if (!owner) return undefined;
    const node = this.workflow(owner.run)?.placements.find(item => item.name === owner.placement)?.node;
    if (node?.type !== 'concurrency') return undefined;
    const spec = node.tasks.find(item => item.name === task);
    return spec ? { spec, input: owner.input, concurrency: node } : undefined;
  }

  private transform(op: Op): { op: Op; payload?: Payload; error?: unknown } {
    let transform: string | undefined;
    let input: string | null | undefined;
    let value: string | undefined;
    let failed: Op;
    switch (op.type) {
      case 'deliver': {
        if (op.value === undefined) return { op };
        transform = this.workflow(op.run)?.connections[op.connection]?.transform;
        input = this.state.results.find(item => item.id === op.source)?.value;
        value = op.value;
        failed = { type: 'transformFailed', run: op.run, connection: op.connection, source: op.source };
        break;
      }
      case 'taskInput': {
        if (op.value === undefined) return { op };
        const task = this.task(op.execution, op.task);
        transform = task?.spec.inputTransform;
        input = task?.input;
        value = op.value;
        failed = { type: 'taskInputFailed', execution: op.execution, task: op.task };
        break;
      }
      case 'taskOutput': {
        transform = this.task(op.execution, op.task)?.spec.outputTransform;
        input = this.state.taskResults.find(item => item.execution === op.execution && item.task === op.task && item.index === op.index)?.value;
        value = op.value;
        failed = { type: 'taskOutputFailed', execution: op.execution, task: op.task, index: op.index };
        break;
      }
      default: return { op };
    }
    try {
      const binding = transform === undefined ? undefined : this.bindings.transforms.get(transform);
      if (!binding || input == null) throw new Error(`suimon: transform ${String(transform)} has no binding or input`);
      const result = synchronousTransformResult(binding.run(decodeValue(this.payloadOf(input))));
      return { op, payload: { value, payload: encodeValue(result) } };
    } catch (error) { return { op: failed, error }; }
  }

  private payloadOf(id: string, pending?: Payload): string {
    const known = this.payloads.get(id);
    if (known !== undefined) return known;
    const remaining = this.budget.limits.maxPayloadBytes - this.budget.payloadBytes;
    if (pending?.value === id) {
      if (byteLength(pending.payload) > remaining) throw new QuotaError('payload bytes', this.budget.limits.maxPayloadBytes);
      return pending.payload;
    }
    const parts = decodeIdentity(id);
    if (!parts || parts[0] !== 'list' || identity(...parts) !== id) throw new Error(`suimon: no payload for value ${JSON.stringify(id)}`);
    let size = 2;
    const values: string[] = [];
    for (const element of parts.slice(1)) {
      const payload = this.payloadOf(element, pending);
      size += byteLength(payload) + (values.length ? 1 : 0);
      if (size > remaining) throw new QuotaError('payload bytes', this.budget.limits.maxPayloadBytes);
      values.push(payload);
    }
    if (size > remaining) throw new QuotaError('payload bytes', this.budget.limits.maxPayloadBytes);
    return `[${values.join(',')}]`;
  }

  async apply(op: Op, cause?: unknown, pending?: Payload, prefix = '', candidate?: State): Promise<boolean> {
    const before = this.state;
    let after: State;
    let values: Payload[];
    let encoded: string;
    let payloadSize: number;
    try {
      after = candidate ?? step(this.definition, before, op);
      values = introduced(before, after).filter(value => !this.payloads.has(value)).map(value => ({ value, payload: this.payloadOf(value, pending) }));
      if (!Number.isSafeInteger(this.seq + 1)) throw new QuotaError('record sequence', Number.MAX_SAFE_INTEGER);
      const operation = encodeRecord({ seq: this.seq, op, values });
      const commit = encodeRecord({ seq: this.seq + 1, commit: true });
      checkLine(operation);
      checkLine(commit);
      encoded = `${operation}\n${commit}\n`;
      payloadSize = this.budget.admit(before, after, op, values, encoded);
    } catch (error) {
      if (error instanceof Rejection) return false;
      if (error instanceof QuotaError && before.started) { await this.stopQuota(error); return false; }
      throw error;
    }
    if (this.journal) {
      await this.journal.append(new TextEncoder().encode(prefix + encoded));
      await this.journal.sync();
    }
    this.state = after;
    this.seq += 2;
    this.budget.commit(payloadSize, byteLength(encoded));
    for (const value of values) this.payloads.set(value.value, value.payload);
    while (this.errors.length < after.failures.length) this.errors.push(cause);
    this.publish(before, op);
    return true;
  }

  private async stopQuota(error: QuotaError): Promise<void> {
    this.quota ??= error;
    await this.cancel();
  }

  private async cancel(): Promise<void> {
    if (!this.state.cancelled && !terminal(this.state)) await this.apply({ type: 'cancel' });
  }

  private publish(before: State, op: Op): void {
    for (const call of this.state.calls.slice(before.calls.length)) {
      if (call.status === 'cancelling') { this.send({ kind: 'exited', call: call.id }); continue; }
      if (ended(call)) continue;
      const input = call.input === null ? undefined : this.payloadOf(call.input);
      const callback = new Callback(call, this.bindings, input, event => this.send(event), size => this.budget.reserve(size), this.budget.limits.maxPayloadBytes);
      this.callbacks.set(call.id, callback);
      if (call.timeout.callMs !== undefined) {
        callback.stopCallTimer = scheduleTimer(call.timeout.callMs, () => this.send({ kind: 'timer', call: call.id, element: false, index: 0, callback }));
      }
    }
    if (op.type === 'fetch') {
      const call = this.state.calls.find(item => item.id === op.call);
      const callback = this.callbacks.get(op.call);
      if (call?.status === 'fetching' && callback) {
        callback.fetch();
        if (call.timeout.elementMs !== undefined) {
          callback.stopElementTimer = scheduleTimer(call.timeout.elementMs, () => this.send({ kind: 'timer', call: call.id, element: true, index: call.yields, callback }));
        }
      }
    }
    for (const call of this.state.calls) {
      if (call.status === 'cancelling') this.callbacks.get(call.id)?.cancel();
    }
  }

  private async handle(event: Event): Promise<void> {
    if (event.kind === 'cancel') { await this.cancel(); return; }
    if (event.kind === 'deadline') {
      if (this.state.status === 'running') await this.stopQuota(new QuotaError('duration milliseconds', this.budget.limits.maxDurationMs));
      return;
    }
    if ('payload' in event) this.budget.queuedBytes -= byteLength(event.payload);
    const call = this.state.calls.find(item => item.id === event.call);
    if (!call) throw new Error(`suimon: unknown call ${event.call}`);
    const callback = this.callbacks.get(call.id);
    if (event.kind === 'timer') {
      if (callback !== event.callback) return;
      if (event.element ? call.status !== 'fetching' || call.yields !== event.index : call.status !== 'running' && call.status !== 'fetching') return;
      const ms = event.element ? call.timeout.elementMs : call.timeout.callMs;
      if (ms !== undefined) await this.apply({ type: 'timedOut', call: call.id, element: event.element }, new TimeoutError(call.id, ms, event.element));
      return;
    }
    if (event.kind === 'yielded') {
      if (call.status !== 'fetching' || call.yields !== event.index) return;
      callback?.stopElementTimer?.();
      if (callback) callback.stopElementTimer = undefined;
      const value = exploreValue('yield', call.id, String(call.yields));
      await this.apply({ type: 'yielded', call: call.id, value }, undefined, { value, payload: event.payload });
      return;
    }
    callback?.stopTimers();
    this.callbacks.delete(call.id);
    if (call.status === 'cancelling') { await this.apply({ type: 'terminated', call: call.id }); return; }
    if (ended(call)) return;
    if (event.kind === 'failed' && event.error instanceof QuotaError) {
      await this.stopQuota(event.error);
      await this.apply({ type: 'terminated', call: call.id });
      return;
    }
    let op: Op;
    let pending: Payload | undefined;
    let cause: unknown;
    switch (event.kind) {
      case 'returned': {
        const value = exploreValue('return', call.id);
        pending = { value, payload: event.payload };
        op = { type: 'returned', call: call.id, value };
        break;
      }
      case 'judged': op = { type: 'judged', call: call.id, arm: event.arm }; break;
      case 'ended': op = { type: 'ended', call: call.id }; break;
      case 'failed': op = { type: 'failed', call: call.id }; cause = event.error; break;
      case 'exited': op = { type: 'failed', call: call.id }; cause = new Error('suimon: the user code ended without a result'); break;
    }
    if (await this.apply(op, cause, pending)) return;
    if (this.quota) { await this.apply({ type: 'terminated', call: call.id }); return; }
    if (!await this.apply({ type: 'failed', call: call.id }, new Error('suimon: unexpected report of the user code'))) {
      throw new Error(`suimon: call ${call.id} cannot end`);
    }
  }

  private report(): Report {
    const state = this.state;
    if (state.status === 'running' || state.status === 'stopping') throw new StuckError(state.status);
    const outputs = new Map<string, unknown>();
    const endpoints = new Map<string, import('./model-types.js').Outcome>();
    const main = this.definition.workflows.find(item => item.id === this.definition.main);
    for (const placement of main?.placements ?? []) {
      if (main?.connections.some(connection => connection.source === placement.name)) continue;
      const settled = state.settled.find(item => item.run.length === 0 && item.placement === placement.name);
      if (settled) endpoints.set(placement.name, settled.outcome);
      const result = state.results.find(item => item.run.length === 0 && item.placement === placement.name);
      if (result) outputs.set(placement.name, decodeValue(this.payloadOf(result.value)));
    }
    return { status: state.status, outputs, endpoints, failures: state.failures.map((failure, index) => ({ ...failure, error: this.errors[index] })), state };
  }
}
