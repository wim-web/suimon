import { checkDefinitionResources, encodeDefinition, parseDefinition, validateDefinition } from './definition.js';
import { JsonNumber, jsonEntries, parseJson, renderLean, renderWire } from './json.js';
import type { JsonObject, JsonValue } from './json.js';
import { initialState, stateValues, step } from './machine.js';
import type { CheckedTrace, Definition, Delivered, Op, Payload, State, TaskOutput, TraceRecord } from './model-types.js';

function object(value: JsonValue, at: string): JsonObject {
  if (value === null || typeof value !== 'object' || Array.isArray(value) || value instanceof JsonNumber) {
    throw new Error(`${at}: expected an object`);
  }
  return value;
}

function fields(value: JsonObject, allowed: readonly string[], at: string): void {
  for (const [key] of jsonEntries(value)) {
    if (!allowed.includes(key)) throw new Error(`${at}: unknown field ${key}`);
  }
}

class Fields {
  constructor(private readonly value: JsonObject, private readonly at: string) {}

  get(key: string): JsonValue {
    const value = this.value[key];
    if (value === undefined) throw new Error(`${this.at}: missing field ${key}`);
    return value;
  }

  text(key: string): string {
    const value = this.get(key);
    if (typeof value !== 'string') throw new Error(`${this.at}.${key}: expected a string`);
    return value;
  }

  optionalText(key: 'input' | 'trigger' | 'value'): { input?: string; trigger?: string; value?: string } {
    return this.value[key] === undefined ? {} : { [key]: this.text(key) };
  }

  boolean(key: string): boolean {
    const value = this.get(key);
    if (typeof value !== 'boolean') throw new Error(`${this.at}.${key}: expected a boolean`);
    return value;
  }

  natural(key: string): bigint {
    const value = this.get(key);
    if (typeof value !== 'bigint' || value < 0n) throw new Error(`${this.at}.${key}: expected a natural number`);
    return value;
  }

  saturatedIndex(key: string): number {
    const value = this.natural(key);
    return Number(value > BigInt(Number.MAX_SAFE_INTEGER) ? Number.MAX_SAFE_INTEGER : value);
  }

  path(key: string): string[] {
    const value = this.get(key);
    if (!Array.isArray(value)) throw new Error(`${this.at}.${key}: expected an array of strings`);
    const result: string[] = [];
    for (const item of value) {
      if (typeof item !== 'string') throw new Error(`${this.at}.${key}: expected an array of strings`);
      result.push(item);
    }
    return result;
  }
}

function readOp(value: JsonValue): Op {
  const source = object(value, 'op');
  const reader = new Fields(source, 'op');
  const type = reader.text('type');
  const keys = (...allowed: string[]): void => fields(source, ['type', ...allowed], `op ${type}`);
  switch (type) {
    case 'start':
      keys('input');
      return { type, ...reader.optionalText('input') };
    case 'invoke':
      keys('run', 'placement', 'trigger');
      return { type, run: reader.path('run'), placement: reader.text('placement'), ...reader.optionalText('trigger') };
    case 'fetch': case 'ended': case 'failed': case 'lost': case 'terminated':
      keys('call');
      return { type, call: reader.text('call') };
    case 'returned': case 'yielded':
      keys('call', 'value');
      return { type, call: reader.text('call'), value: reader.text('value') };
    case 'judged':
      keys('call', 'arm');
      return { type, call: reader.text('call'), arm: reader.text('arm') };
    case 'timedOut':
      keys('call', 'element');
      return { type, call: reader.text('call'), element: reader.boolean('element') };
    case 'deliver':
      keys('run', 'connection', 'source', 'value');
      return { type, run: reader.path('run'), connection: reader.saturatedIndex('connection'), source: reader.text('source'), ...reader.optionalText('value') };
    case 'transformFailed':
      keys('run', 'connection', 'source');
      return { type, run: reader.path('run'), connection: reader.saturatedIndex('connection'), source: reader.text('source') };
    case 'taskInput':
      keys('execution', 'task', 'value');
      return { type, execution: reader.text('execution'), task: reader.text('task'), ...reader.optionalText('value') };
    case 'taskInputFailed': case 'beginTask':
      keys('execution', 'task');
      return { type, execution: reader.text('execution'), task: reader.text('task') };
    case 'taskOutput':
      keys('execution', 'task', 'index', 'value');
      return { type, execution: reader.text('execution'), task: reader.text('task'), index: reader.saturatedIndex('index'), value: reader.text('value') };
    case 'taskOutputFailed':
      keys('execution', 'task', 'index');
      return { type, execution: reader.text('execution'), task: reader.text('task'), index: reader.saturatedIndex('index') };
    case 'settle':
      keys('run', 'placement');
      return { type, run: reader.path('run'), placement: reader.text('placement') };
    case 'closeExecution':
      keys('execution');
      return { type, execution: reader.text('execution') };
    case 'closeRun':
      keys('run');
      return { type, run: reader.path('run') };
    case 'cancel': case 'conclude':
      keys();
      return { type };
    default:
      throw new Error(`unknown op type ${type}`);
  }
}

function opValue(op: Op): JsonObject {
  switch (op.type) {
    case 'start': return { type: op.type, ...(op.input === undefined ? {} : { input: op.input }) };
    case 'invoke': return { type: op.type, run: op.run, placement: op.placement, ...(op.trigger === undefined ? {} : { trigger: op.trigger }) };
    case 'fetch': case 'ended': case 'failed': case 'lost': case 'terminated':
      return { type: op.type, call: op.call };
    case 'returned': case 'yielded': return { type: op.type, call: op.call, value: op.value };
    case 'judged': return { type: op.type, call: op.call, arm: op.arm };
    case 'timedOut': return { type: op.type, call: op.call, element: op.element };
    case 'deliver': return { type: op.type, run: op.run, connection: op.connection, source: op.source, ...(op.value === undefined ? {} : { value: op.value }) };
    case 'transformFailed': return { type: op.type, run: op.run, connection: op.connection, source: op.source };
    case 'taskInput': return { type: op.type, execution: op.execution, task: op.task, ...(op.value === undefined ? {} : { value: op.value }) };
    case 'taskInputFailed': case 'beginTask': return { type: op.type, execution: op.execution, task: op.task };
    case 'taskOutput': return { type: op.type, execution: op.execution, task: op.task, index: op.index, value: op.value };
    case 'taskOutputFailed': return { type: op.type, execution: op.execution, task: op.task, index: op.index };
    case 'settle': return { type: op.type, run: op.run, placement: op.placement };
    case 'closeExecution': return { type: op.type, execution: op.execution };
    case 'closeRun': return { type: op.type, run: op.run };
    case 'cancel': case 'conclude': return { type: op.type };
    default: {
      const exhaustive: never = op;
      return exhaustive;
    }
  }
}

export function encodeOp(op: Op): string {
  return renderWire(opValue(op));
}

export function encodeHeader(definition: Definition, validated: boolean): string {
  return `{"definition":${encodeDefinition(definition)},"validated":${validated}}`;
}

export function encodeRecord(record: TraceRecord): string {
  const seq = renderWire(record.seq);
  if ('commit' in record) return `{"seq":${seq},"commit":true}`;
  const prefix = `{"seq":${seq},"op":${encodeOp(record.op)}`;
  if (record.values.length === 0) return `${prefix}}`;
  const seen = new Set<string>();
  const values = record.values.map(({ value, payload }) => {
    if (/[\uD800-\uDFFF]/u.test(value) || /[\uD800-\uDFFF]/u.test(payload)) {
      throw new Error(`payload of ${JSON.stringify(value)} is not valid UTF-8`);
    }
    if (seen.has(value)) throw new Error(`duplicate payloads for [${value}]`);
    seen.add(value);
    return `${renderWire(value)}:${renderWire(payload)}`;
  });
  return `${prefix},"values":{${values.join(',')}}}`;
}

type ParsedRecord = { seq: bigint; commit: true } | { seq: bigint; op: Op; values: Payload[] };

function readRecord(line: string): ParsedRecord {
  const source = object(parseJson(line, 'trace'), 'record');
  const reader = new Fields(source, 'record');
  const seq = reader.natural('seq');
  if (source.commit === true && source.op === undefined) {
    fields(source, ['seq', 'commit'], 'record');
    return { seq, commit: true };
  }
  if (source.commit === undefined && source.op !== undefined) {
    fields(source, ['seq', 'op', 'values'], 'record');
    const values: Payload[] = [];
    if (source.values !== undefined) {
      for (const [value, payload] of jsonEntries(object(source.values, 'record.values'))) {
        if (typeof payload !== 'string') throw new Error(`record.values.${value}: expected a string`);
        values.push({ value, payload });
      }
    }
    return { seq, op: readOp(source.op), values };
  }
  throw new Error('record: either an op or a commit');
}

function readHeader(line: string, expected?: Definition): { definition: Definition; validated: boolean } {
  const source = object(parseJson(line, 'trace'), 'header');
  fields(source, ['definition', 'validated'], 'header');
  const reader = new Fields(source, 'header');
  const value = reader.get('definition');
  const validated = reader.boolean('validated');
  const definition = parseDefinition(renderWire(value));
  if (expected !== undefined && encodeDefinition(definition) !== encodeDefinition(expected)) {
    throw new Error('suimon: the journal records another definition');
  }
  if (validated) validateDefinition(definition);
  checkDefinitionResources(definition);
  return { definition, validated };
}

export function introduced(before: State, after: State): string[] {
  const seen = new Set(stateValues(before));
  const values: string[] = [];
  for (const value of stateValues(after)) {
    if (!seen.has(value)) {
      values.push(value);
      seen.add(value);
    }
  }
  return values;
}

export function checkTrace(data: Uint8Array | string, expectedDefinition?: Definition): CheckedTrace {
  const checked: CheckedTrace = { definition: null, validated: false, state: initialState(), values: [], committed: 0, length: 0 };
  const decoder = new TextDecoder('utf-8', { fatal: true, ignoreBOM: true });
  let start = 0;
  let byteOffset = 0;
  let lineNumber = 0;
  let next = 1n;
  let pending: Extract<ParsedRecord, { op: Op }> | undefined;
  while (start < data.length) {
    const end = typeof data === 'string' ? data.indexOf('\n', start) : data.indexOf(10, start);
    if (end < 0) break;
    lineNumber++;
    try {
      let line: string;
      if (typeof data === 'string') {
        line = data.slice(start, end);
        byteOffset += Buffer.byteLength(line, 'utf8') + 1;
      } else {
        try {
          line = decoder.decode(data.subarray(start, end));
        } catch {
          throw new Error('invalid UTF-8');
        }
        byteOffset = end + 1;
      }
      if (checked.definition === null) {
        const header = readHeader(line, expectedDefinition);
        checked.definition = header.definition;
        checked.validated = header.validated;
        checked.length = byteOffset;
      } else {
        const record = readRecord(line);
        if (record.seq !== next) throw new Error(`expected sequence ${next}, got ${record.seq}`);
        if ('op' in record) {
          if (pending !== undefined) throw new Error('an op before the previous commit');
          pending = record;
        } else {
          if (pending === undefined) throw new Error('a commit without an op');
          let after: State;
          try {
            after = step(checked.definition, checked.state, pending.op);
          } catch (error) {
            throw new Error(`rejected ${encodeOp(pending.op)}: ${error instanceof Error ? error.message : String(error)}`, { cause: error });
          }
          const added = introduced(checked.state, after);
          const allowed = new Set(added);
          const extra = pending.values.filter(({ value }) => !allowed.has(value)).map(({ value }) => value);
          if (extra.length > 0) throw new Error(`payloads for [${extra.join(', ')}], which the transition does not introduce`);
          const supplied = new Set(pending.values.map(({ value }) => value));
          const missing = added.filter(value => !supplied.has(value));
          if (missing.length > 0) throw new Error(`missing payloads for [${missing.join(', ')}]`);
          checked.state = after;
          checked.values.push(...pending.values);
          checked.committed++;
          checked.length = byteOffset;
          pending = undefined;
        }
        next++;
      }
    } catch (error) {
      throw new Error(`line ${lineNumber}: ${error instanceof Error ? error.message : String(error)}`, { cause: error });
    }
    start = end + 1;
  }
  return checked;
}

function valueConstructor(value: TaskOutput | Delivered): JsonValue {
  return value.kind === 'value' ? { value: { v: value.value } } : value.kind;
}

export function encodeState(state: State): string {
  return renderLean({
    status: state.status,
    started: state.started,
    cancelled: state.cancelled,
    runs: state.runs.map(run => ({ ...run })),
    invocations: state.invocations.map(invocation => ({ ...invocation })),
    calls: state.calls.map(call => ({
      ...call,
      target: { [call.target.kind]: { id: call.target.id } },
      timeout: { callMs: call.timeout.callMs ?? null, elementMs: call.timeout.elementMs ?? null },
    })),
    executions: state.executions.map(execution => ({ ...execution, tasks: execution.tasks.map(task => ({ ...task })) })),
    results: state.results.map(result => ({ ...result })),
    taskResults: state.taskResults.map(result => ({ ...result, output: valueConstructor(result.output) })),
    deliveries: state.deliveries.map(delivery => ({ ...delivery, outcome: valueConstructor(delivery.outcome) })),
    settled: state.settled.map(settlement => ({ ...settlement, arms: settlement.arms.map(({ arm, outcome }) => [arm, outcome]) })),
    failures: state.failures.map(failure => ({ ...failure })),
  });
}
