import type { Call, Definition } from './model-types.js';
import type { Binding, Sequence } from './runtime-types.js';
import { byteLength, QuotaError } from './limits.js';

type FunctionBinding = Extract<Binding, { kind: 'single' | 'stream' }>;
type JudgeBinding = Extract<Binding, { kind: 'judge' }>;
type TransformBinding = Extract<Binding, { kind: 'transform' }>;

export class Bindings {
  readonly functions = new Map<string, FunctionBinding>();
  readonly judges = new Map<string, JudgeBinding>();
  readonly transforms = new Map<string, TransformBinding>();

  constructor(definition: Definition, bindings: readonly Binding[]) {
    for (const original of bindings) {
      const binding = { ...original };
      if (!binding.id) throw new Error('suimon: a binding needs an identifier');
      if (typeof binding.run !== 'function') throw new Error(`suimon: ${binding.id} has no callback`);
      if (binding.kind === 'transform' && binding.id === 'discard') throw new Error('suimon: discard is provided by the library and cannot be bound');
      const namespace = binding.kind === 'judge' ? this.judges : binding.kind === 'transform' ? this.transforms : this.functions;
      if (namespace.has(binding.id)) throw new Error(`suimon: ${binding.id} is bound twice`);
      switch (binding.kind) {
        case 'single': case 'stream': this.functions.set(binding.id, binding); break;
        case 'judge': this.judges.set(binding.id, binding); break;
        case 'transform': this.transforms.set(binding.id, binding); break;
      }
    }
    const checkFunction = (id: string): void => {
      const declaration = definition.functions.find(item => item.id === id);
      if (!declaration) return;
      const binding = this.functions.get(id);
      if (!binding) throw new Error(`suimon: function ${id} is not bound`);
      const kind = 'single' in declaration.output ? 'single' : 'stream';
      if (binding.kind !== kind) throw new Error(`suimon: function ${id} is declared as ${kind} but bound as ${binding.kind}`);
      if (binding.input !== (declaration.input !== undefined)) throw new Error(`suimon: function ${id} input does not match its binding`);
    };
    const checkTransform = (id: string | undefined): void => {
      if (id !== undefined && id !== 'discard' && !this.transforms.has(id)) throw new Error(`suimon: transform ${id} is not bound`);
    };
    for (const workflow of definition.workflows) {
      for (const placement of workflow.placements) {
        const node = placement.node;
        if (node.type === 'function') checkFunction(node.function);
        if (node.type === 'branch' && !this.judges.has(node.judge)) throw new Error(`suimon: judge ${node.judge} is not bound`);
        if (node.type === 'concurrency') {
          for (const task of node.tasks) {
            if (task.body.type === 'function') checkFunction(task.body.function);
            checkTransform(task.inputTransform);
            checkTransform(task.outputTransform);
          }
        }
      }
      for (const connection of workflow.connections) checkTransform(connection.transform);
    }
  }
}

export function encodeValue(value: unknown): string {
  const encoded = JSON.stringify(value, (_key, item: unknown) => {
    if (typeof item === 'number' && !Number.isFinite(item)) throw new TypeError('suimon: a value contains a nonfinite number');
    if (typeof item === 'undefined' || typeof item === 'function' || typeof item === 'symbol') throw new TypeError('suimon: a value is not JSON serializable');
    return item;
  });
  if (encoded === undefined) throw new TypeError('suimon: a value is not JSON serializable');
  return encoded;
}

export function decodeValue(payload: string): unknown { return JSON.parse(payload); }

export function synchronousTransformResult(value: unknown): unknown {
  if (value !== null && (typeof value === 'object' || typeof value === 'function') &&
      'then' in value && typeof value.then === 'function') {
    if (value instanceof Promise) void value.catch(() => {});
    throw new TypeError('suimon: transforms must return synchronously');
  }
  return value;
}


export type CallbackEvent =
  | { kind: 'returned'; call: string; payload: string }
  | { kind: 'yielded'; call: string; payload: string; index: number }
  | { kind: 'judged'; call: string; arm: string }
  | { kind: 'failed'; call: string; error: unknown }
  | { kind: 'ended' | 'exited'; call: string };

export function scheduleTimer(milliseconds: bigint, fire: () => void): () => void {
  let handle: ReturnType<typeof setTimeout>;
  let cancelled = false;
  let remaining = milliseconds;
  let started = performance.now();
  const arm = (): void => {
    const chunk = Number(remaining > 2_147_483_647n ? 2_147_483_647n : remaining);
    handle = setTimeout(() => {
      if (cancelled) return;
      const now = performance.now();
      const elapsed = BigInt(Math.max(0, Math.floor(now - started)));
      remaining -= elapsed;
      started += Number(elapsed);
      if (remaining <= 0n) fire(); else arm();
    }, chunk);
  };
  arm();
  return () => { cancelled = true; clearTimeout(handle); };
}

export function iteratorOf<T>(sequence: Sequence<T>): Iterator<T> | AsyncIterator<T> {
  if (typeof sequence !== 'string' && Symbol.asyncIterator in sequence) {
    const method = sequence[Symbol.asyncIterator];
    if (method != null) return method.call(sequence);
  }
  if (typeof sequence === 'string' || Symbol.iterator in sequence) return sequence[Symbol.iterator]();
  throw new TypeError('suimon: a stream must return an iterable');
}

export class Callback {
  readonly controller = new AbortController();
  readonly done: Promise<void>;
  private fetchPending = false;
  private wake: (() => void) | undefined;
  private readonly call: Call;
  private readonly send: (event: CallbackEvent) => void;
  private readonly reserve: (bytes: number) => boolean;
  private readonly maxPayloadBytes: number;
  stopCallTimer: (() => void) | undefined;
  stopElementTimer: (() => void) | undefined;

  constructor(call: Call, bindings: Bindings, input: string | undefined, send: (event: CallbackEvent) => void,
    reserve: (bytes: number) => boolean, maxPayloadBytes: number) {
    this.call = call;
    this.send = send;
    this.reserve = reserve;
    this.maxPayloadBytes = maxPayloadBytes;
    this.done = Promise.resolve().then(() => this.run(bindings, input));
  }

  fetch(): void { this.fetchPending = true; this.wake?.(); }
  cancel(): void { this.stopTimers(); this.controller.abort(); this.wake?.(); }
  stopTimers(): void { this.stopCallTimer?.(); this.stopElementTimer?.(); this.stopCallTimer = undefined; this.stopElementTimer = undefined; }

  private payload(value: unknown): string {
    const payload = encodeValue(value);
    if (!this.reserve(byteLength(payload))) throw new QuotaError('payload bytes', this.maxPayloadBytes);
    return payload;
  }

  private async fetchRequested(): Promise<boolean> {
    while (!this.fetchPending && !this.controller.signal.aborted) {
      await new Promise<void>(resolve => { this.wake = resolve; });
      this.wake = undefined;
    }
    this.fetchPending = false;
    return !this.controller.signal.aborted;
  }

  private async generate(sequence: Sequence<unknown>): Promise<CallbackEvent> {
    const iterator = iteratorOf(sequence);
    let finished = false;
    try {
      for (let index = 0; await this.fetchRequested(); index++) {
        const item = await iterator.next();
        if (this.controller.signal.aborted) break;
        if (item.done) { finished = true; return { kind: 'ended', call: this.call.id }; }
        this.send({ kind: 'yielded', call: this.call.id, payload: this.payload(item.value), index });
      }
      return { kind: 'exited', call: this.call.id };
    } finally {
      if (!finished && iterator.return) {
        let result = await iterator.return();
        while (!result.done) result = await iterator.next();
      }
    }
  }

  private async run(bindings: Bindings, input: string | undefined): Promise<void> {
    const call = this.call;
    let event: CallbackEvent;
    try {
      const value = input === undefined ? undefined : decodeValue(input);
      const context = { signal: this.controller.signal };
      if (call.target.kind === 'judge') {
        const binding = bindings.judges.get(call.target.id);
        if (!binding) throw new Error(`suimon: judge ${call.target.id} is not bound`);
        event = { kind: 'judged', call: call.id, arm: await binding.run(value, context) };
      } else {
        const binding = bindings.functions.get(call.target.id);
        if (!binding || (binding.kind === 'stream') !== call.stream) throw new Error(`suimon: function ${call.target.id} is not bound with its declared shape`);
        if (binding.kind === 'stream') event = await this.generate(await binding.run(value, context));
        else {
          const result = await binding.run(value, context);
          event = this.controller.signal.aborted ? { kind: 'exited', call: call.id } : { kind: 'returned', call: call.id, payload: this.payload(result) };
        }
      }
    } catch (error) { event = { kind: 'failed', call: call.id, error }; }
    this.send(event);
  }
}
