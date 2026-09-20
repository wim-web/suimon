import type { Graph, JsonObject, TraceEvent, WorkflowSnapshot } from '../types';

function record(value: unknown): value is Record<string, unknown> {
  return value !== null && typeof value === 'object' && !Array.isArray(value);
}
function assert(condition: unknown, message: string): asserts condition {
  if (!condition) throw new TypeError(message);
}
function modelNumbers(value: unknown): void {
  if (typeof value === 'number') assert(Number.isSafeInteger(value) && value >= 0, 'Model numbers must be safe non-negative integers');
  if (value && typeof value === 'object') Object.values(value).forEach(modelNumbers);
}
function ports(value: unknown): boolean {
  return Array.isArray(value) && value.every(port => record(port) && typeof port.name === 'string' && ['plain', 'stream'].includes(String(port.kind)));
}
function ref(value: unknown): boolean {
  return record(value) && typeof value.node === 'string' && typeof value.port === 'string';
}
export function parseGraph(value: unknown): Graph {
  assert(record(value) && Array.isArray(value.nodes) && Array.isArray(value.edges), 'Expected a workflow graph');
  assert(Array.isArray(value.entries) && value.entries.every(ref) && Array.isArray(value.exits) && value.exits.every(ref), 'Invalid graph entry/exit ports');
  const kinds = ['leaf', 'branch', 'loop', 'subworkflow', 'forEach', 'waitAll', 'coalesce', 'collect', 'filter', 'merge'];
  for (const node of value.nodes) {
    assert(record(node) && typeof node.id === 'string' && record(node.kind) && kinds.includes(String(node.kind.type)) && ports(node.inputs) && ports(node.outputs), 'Invalid graph node');
    if (['loop', 'subworkflow', 'forEach'].includes(String(node.kind.type))) parseGraph(node.kind.body);
    if (node.kind.type === 'leaf') {
      assert(typeof node.kind.concurrency === 'number' && record(node.kind.retry), 'Invalid leaf policy');
      const retry = node.kind.retry;
      assert(['maxAttempts', 'leaseSeconds', 'retrySeconds'].every(key => typeof retry[key] === 'number'), 'Invalid retry policy');
    }
    if (node.kind.type === 'loop') assert(typeof node.kind.maxIterations === 'number', 'Invalid loop limit');
    if (node.kind.type === 'branch') assert(Array.isArray(node.kind.arms) && node.kind.arms.every(arm => typeof arm === 'string'), 'Invalid branch arms');
  }
  assert(value.edges.every(edge => record(edge) && ref(edge.src) && ref(edge.dst)), 'Invalid graph edge');
  modelNumbers(value);
  return value as unknown as Graph;
}
export function parseTraceEvents(value: unknown): TraceEvent[] {
  assert(Array.isArray(value), 'Expected an events array');
  for (const event of value) {
    assert(record(event) && event.schema_version === 2 && typeof event.type === 'string' && typeof event.txn === 'string' && typeof event.sequence === 'number' && typeof event.recorded_at === 'number' && record(event.data), 'Expected schema v2 events');
    assert(event.op === null || event.op === 'idle' || event.op === 'cancel' || (record(event.op) && Object.keys(event.op).length === 1 && Object.values(event.op).every(record)), 'Invalid event operation');
    modelNumbers(event);
  }
  return value as TraceEvent[];
}
export function parseSnapshot(value: unknown): WorkflowSnapshot {
  assert(record(value) && Array.isArray(value.events), 'Expected graph, events, and optional values');
  const graph = parseGraph(value.graph);
  const events = parseTraceEvents(value.events);
  assert(value.values === undefined || record(value.values), 'Expected an item ID to value map');
  return { graph, events, values: value.values as JsonObject | undefined };
}
