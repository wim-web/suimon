import type { Failure, Outcome, State, Status } from './model-types.js';

export type Awaitable<T> = T | PromiseLike<T>;
export interface CallContext { readonly signal: AbortSignal }
export type Sequence<T> = Iterable<T> | AsyncIterable<T>;
export type Binding =
  | { kind: 'single'; id: string; input: boolean; run(input: unknown, context: CallContext): Awaitable<unknown> }
  | { kind: 'stream'; id: string; input: boolean; run(input: unknown, context: CallContext): Awaitable<Sequence<unknown>> }
  | { kind: 'judge'; id: string; run(input: unknown, context: CallContext): Awaitable<string> }
  | { kind: 'transform'; id: string; run(input: unknown): unknown };

/** A journal has one exclusive writer. Effects become observable only after sync resolves. */
export interface Journal {
  append(lines: Uint8Array): Promise<void>;
  sync(): Promise<void>;
}
export interface RecoverableJournal extends Journal {
  /** Reject oversized storage before allocating the returned bytes. */
  contents(maxBytes: number): Promise<Uint8Array>;
  /** Keep exactly the first byteLength bytes and make the change durable. */
  truncate(byteLength: number): Promise<void>;
}
export interface StartOptions { journal?: Journal; signal?: AbortSignal }
export interface ResumeOptions { signal?: AbortSignal }
export interface Limits {
  maxWorkflows: number; maxActiveCalls: number; maxExecutions: number; maxTasks: number;
  maxElements: number; maxPayloadBytes: number; maxRecords: number; maxJournalBytes: number;
  maxDurationMs: number;
}
export interface EngineOptions { validate?: boolean; limits?: Partial<Limits> }
export interface FailureReport extends Failure { error: unknown }
export interface Report {
  status: Exclude<Status, 'running' | 'stopping'>;
  outputs: ReadonlyMap<string, unknown>;
  endpoints: ReadonlyMap<string, Outcome>;
  failures: readonly FailureReport[];
  state: State;
}
export interface Execution { cancel(): void; wait(): Promise<Report> }
