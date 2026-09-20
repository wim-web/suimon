import type { InstanceInfo, JsonObject, JsonValue, TraceEvent, TraceIndex, TraceTransaction } from '../types';

export function object(value: JsonValue | undefined): JsonObject {
  return value !== null && typeof value === 'object' && !Array.isArray(value) ? value : {};
}

export function operation(event: TraceEvent): { kind: string; args: JsonObject } | null {
  if (event.op === null) return null;
  if (typeof event.op === 'string') return { kind: event.op, args: {} };
  const entry = Object.entries(event.op)[0];
  return entry ? { kind: entry[0], args: object(entry[1]) } : null;
}

export function traceIndex(events: TraceEvent[]): TraceIndex {
  const instances = new Map<string, InstanceInfo>();
  const transactions: TraceTransaction[] = [];
  const committedEvents: TraceEvent[] = [];
  const committedSequences = new Set<number>();
  const attempts: TraceIndex['attempts'] = new Map();
  const successfulCompletions = new Set<number>();
  let executionInputs: Set<string> | undefined;
  let current: TraceTransaction | undefined;
  let status = 'ready';
  for (const [index, event] of events.entries()) {
    if (!current || current.id !== event.txn) {
      current = { id: event.txn, events: [], start: index, committed: false };
      transactions.push(current);
    }
    current.events.push(event);
    if (event.type === 'transaction.committed') {
      current.committed = true;
      const succeeded = new Set<string>();
      for (const fact of current.events) {
        committedEvents.push(fact); committedSequences.add(fact.sequence);
        if (fact.op === null && fact.type === 'instance.created') {
          const { id, node, path } = fact.data;
          if (typeof id === 'string' && typeof node === 'string') instances.set(id, { id, node, path: Array.isArray(path) ? path.filter((p): p is string => typeof p === 'string') : [] });
        }
        const op = operation(fact);
        if (op?.kind === 'start' && Array.isArray(op.args.inputs)) executionInputs = new Set(op.args.inputs.map(input => {
          const ref = object(object(input).entry); return JSON.stringify([ref.node, ref.port]);
        }));
        const attempt = fact.op === null ? fact.type === 'attempt.started' ? object(fact.data.attempt) : fact.type === 'attempt.finished' ? fact.data : null : null;
        if (attempt && typeof attempt.id === 'string' && typeof attempt.instance === 'string' && typeof attempt.status === 'string') {
          attempts.set(attempt.id, { instance: attempt.instance, status: attempt.status });
          if (fact.type === 'attempt.finished' && attempt.status === 'succeeded') succeeded.add(JSON.stringify([attempt.id, attempt.instance]));
        }
        if (fact.type === 'execution.started' && fact.op) status = 'running';
        if (fact.op === null && fact.type === 'execution.state_changed' && typeof fact.data.status === 'string') status = fact.data.status;
      }
      for (const command of current.events) {
        const op = operation(command), auth = object(op?.args.auth);
        if (op?.kind === 'complete' && succeeded.has(JSON.stringify([auth.attempt, auth.instance]))) successfulCompletions.add(command.sequence);
      }
      current = undefined;
    }
  }
  return { events, committedEvents, committedSequences, instances, transactions, executionInputs, attempts, successfulCompletions, status };
}

export function asTraceIndex(events: TraceEvent[] | TraceIndex): TraceIndex {
  return Array.isArray(events) ? traceIndex(events) : events;
}

export function eventNode(event: TraceEvent, instances: Map<string, InstanceInfo>): string | null {
  const op = operation(event);
  if (typeof op?.args.node === 'string') return op.args.node;
  const data = event.data;
  if (event.type === 'instance.created' && event.op === null && typeof data.node === 'string') return data.node;
  const instance = object(op?.args.auth).instance ?? op?.args.inst ?? data.by_instance ?? data.instance ?? object(data.attempt).instance;
  return typeof instance === 'string' ? instances.get(instance)?.node ?? null : null;
}

export function eventValues(event: TraceEvent, values: Record<string, JsonValue> = {}) {
  const ids = new Set<string>();
  const visit = (value: JsonValue): void => {
    if (!value || typeof value !== 'object') return;
    for (const [key, entry] of Object.entries(value)) {
      if (key === 'item' && typeof entry === 'string') ids.add(entry);
      if (key === 'item' && typeof object(entry).id === 'string') ids.add(object(entry).id as string);
      if (key === 'items' && Array.isArray(entry)) {
        for (const id of entry) if (typeof id === 'string') ids.add(id);
      }
      visit(entry);
    }
  };
  visit(event.op);
  visit(event.data);
  return [...ids].map(id => ({ id, available: Object.hasOwn(values, id), value: values[id] }));
}

export function eventCategory(event: TraceEvent): 'command' | 'fact' | 'commit' {
  return event.op !== null ? 'command' : event.type === 'transaction.committed' ? 'commit' : 'fact';
}

export function downloadJSON(name: string, data: unknown, jsonl = false) {
  const contents = jsonl && Array.isArray(data) ? data.map(event => JSON.stringify(event)).join('\n') + '\n' : JSON.stringify(data, null, 2) + '\n';
  const url = URL.createObjectURL(new Blob([contents], { type: jsonl ? 'application/x-ndjson' : 'application/json' }));
  const link = document.createElement('a');
  link.href = url;
  link.download = name;
  link.click();
  setTimeout(() => URL.revokeObjectURL(url), 1000);
}
