import type { Call, Op, Payload, State } from './model-types.js';
import type { Limits, Report } from './runtime-types.js';
import { checkInput } from './json.js';
import { encodeRecord } from './trace.js';

export class QuotaError extends Error {
  readonly resource: string;
  readonly limit: number;
  report: Report | undefined;

  constructor(resource: string, limit: number) {
    super(`suimon: resource quota exceeded: ${resource} (limit ${limit})`);
    this.name = 'QuotaError';
    this.resource = resource;
    this.limit = limit;
  }
}

export function defaultLimits(): Limits {
  return {
    maxWorkflows: 16, maxActiveCalls: 256, maxExecutions: 4096, maxTasks: 16384,
    maxElements: 10_000, maxPayloadBytes: 64 << 20, maxRecords: 250_000,
    maxJournalBytes: 128 << 20, maxDurationMs: 300_000,
  };
}

export function engineLimits(overrides: Partial<Limits> = {}): Limits {
  const limits = defaultLimits();
  for (const key of Object.keys(limits)) {
    if (!(key in overrides)) continue;
    const value = Reflect.get(overrides, key);
    if (typeof value !== 'number' || !Number.isSafeInteger(value) || value < 0) {
      throw new Error(`suimon: resource limit ${key} must be a nonnegative safe integer`);
    }
    if (value !== 0) Reflect.set(limits, key, value);
  }
  return limits;
}

export function ended(call: Call): boolean {
  return call.status !== 'running' && call.status !== 'fetching' && call.status !== 'cancelling';
}

export function terminal(state: State): boolean {
  return state.status !== 'running' && state.status !== 'stopping';
}

export function byteLength(value: string): number { return Buffer.byteLength(value, 'utf8'); }

export function checkLine(line: string): void {
  try { checkInput(line); }
  catch (cause) { throw new QuotaError(`journal line (${String(cause)})`, 1 << 20); }
}

const largestSequenceDigits = 19;
const transactionNewlines = 2;
const sequencePadding = 2 * (largestSequenceDigits - String(Number.MAX_SAFE_INTEGER).length);

function shutdownBytes(op: Op): number {
  return byteLength(encodeRecord({ seq: Number.MAX_SAFE_INTEGER, op, values: [] })) +
    byteLength(encodeRecord({ seq: Number.MAX_SAFE_INTEGER, commit: true })) + transactionNewlines + sequencePadding;
}

function shutdown(state: State): { calls: number; bytes: number } {
  let calls = 0;
  let bytes = shutdownBytes({ type: 'cancel' }) + shutdownBytes({ type: 'conclude' });
  for (const call of state.calls) {
    if (ended(call)) continue;
    checkLine(encodeRecord({ seq: Number.MAX_SAFE_INTEGER, op: { type: 'terminated', call: call.id }, values: [] }));
    calls++;
    bytes += shutdownBytes({ type: 'terminated', call: call.id });
  }
  return { calls, bytes };
}

export class Budget {
  readonly limits: Limits;
  readonly deadline: number;
  payloadBytes = 0;
  queuedBytes = 0;
  stagedBytes = 0;
  journalBytes: number;
  records = 0;

  constructor(limits: Limits, headerBytes = 0) {
    this.limits = limits;
    this.deadline = performance.now() + limits.maxDurationMs;
    this.journalBytes = headerBytes;
  }

  reserve(size: number): boolean {
    if (size > this.limits.maxPayloadBytes - this.payloadBytes - this.queuedBytes - this.stagedBytes) return false;
    this.queuedBytes += size;
    return true;
  }

  private check(resource: string, used: number, limit: number): void {
    if (used > limit) throw new QuotaError(resource, limit);
  }

  restore(state: State, values: readonly Payload[], committed: number, bytes: number): void {
    this.payloadBytes = values.reduce((total, value) => total + byteLength(value.payload), 0);
    this.records = 2 * committed;
    this.journalBytes = bytes;
    const reserve = shutdown(state);
    this.checkState(state, reserve.calls);
    this.check('payload bytes', this.payloadBytes, this.limits.maxPayloadBytes);
    const remainingRecords = terminal(state) ? 0 : 4 + 2 * reserve.calls - (state.cancelled ? 2 : 0);
    const remainingBytes = terminal(state) ? 0 : reserve.bytes - (state.cancelled ? shutdownBytes({ type: 'cancel' }) : 0);
    this.check('records', this.records + remainingRecords, this.limits.maxRecords);
    this.check('journal bytes', bytes + remainingBytes, this.limits.maxJournalBytes);
  }

  private checkState(state: State, calls: number): void {
    this.check('active calls', calls, this.limits.maxActiveCalls);
    this.check('executions', state.executions.length, this.limits.maxExecutions);
    this.check('tasks', state.executions.reduce((n, execution) => n + execution.tasks.length, 0), this.limits.maxTasks);
    this.check('stream elements', state.calls.reduce((n, call) => n + call.yields, 0), this.limits.maxElements);
  }

  admit(before: State, after: State, op: Op, values: readonly Payload[], encoded: string): number {
    const size = values.reduce((n, value) => n + byteLength(value.payload), 0);
    const reserve = shutdown(after);
    if (before.status === 'running' && op.type !== 'cancel' && op.type !== 'conclude') {
      this.checkState(after, reserve.calls);
      this.check('payload bytes', this.payloadBytes + size, this.limits.maxPayloadBytes);
      this.check('records', this.records + 2 + 4 + 2 * reserve.calls, this.limits.maxRecords);
      this.check('journal bytes', this.journalBytes + byteLength(encoded) + reserve.bytes, this.limits.maxJournalBytes);
      if (performance.now() >= this.deadline) throw new QuotaError('duration milliseconds', this.limits.maxDurationMs);
    }
    this.check('payload bytes', this.payloadBytes + this.queuedBytes + size, this.limits.maxPayloadBytes);
    this.stagedBytes += size;
    return size;
  }

  commit(payloadBytes: number, encodedBytes: number): void {
    this.stagedBytes -= payloadBytes;
    this.payloadBytes += payloadBytes;
    this.journalBytes += encodedBytes;
    this.records += 2;
  }
}
