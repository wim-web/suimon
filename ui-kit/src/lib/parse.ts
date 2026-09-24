import type {
  Body, Call, CallTarget, Connection, Contract, Control, Definition, Delivered, Delivery, Execution, ExecutionRecord,
  Failure, FunctionDecl, Invocation, JudgeDecl, Op, OpType, Path, Placement, Policy, RecordLog, Result, Run,
  RuntimeState, Settled, Task, TaskOutput, TaskResult, TaskState, Timeout, TransformDecl, ValueType, Workflow,
} from '../types';
import { dictionary } from './dictionary';

type Obj = Record<string, unknown>;

function fail(at: string, message: string): never { throw new TypeError(`${at}: ${message}`); }
function isObject(value: unknown): value is Obj { return value !== null && typeof value === 'object' && !Array.isArray(value); }
function object(value: unknown, at: string, allowed?: readonly string[]): Obj {
  if (!isObject(value)) fail(at, 'expected an object');
  if (allowed) for (const key of Object.keys(value)) if (!allowed.includes(key)) fail(at, `unknown field ${key}`);
  return value;
}
function field(o: Obj, key: string, at: string): unknown {
  if (!Object.hasOwn(o, key)) fail(at, `missing field ${key}`);
  return o[key];
}
function string(value: unknown, at: string): string {
  if (typeof value !== 'string') fail(at, 'expected a string');
  return value;
}
/** Names in a definition are non-empty (definition.schema.json `name`). */
function name(value: unknown, at: string): string {
  if (string(value, at) === '') fail(at, 'empty string');
  return value as string;
}
function nat(value: unknown, at: string): number {
  if (typeof value !== 'number' || !Number.isSafeInteger(value) || value < 0) fail(at, 'expected a natural number');
  return value;
}
function positive(value: unknown, at: string): number {
  if (nat(value, at) < 1) fail(at, 'expected a positive integer');
  return value as number;
}
/** A limit or timeout of a definition: Lean and Go accept up to 2^64 - 1, which a JavaScript number
    cannot tell apart from 2^64, so both pass here. */
function bounded(value: unknown, at: string): number {
  if (typeof value !== 'number' || !Number.isInteger(value) || value < 1) fail(at, 'expected a positive integer');
  if (value > 2 ** 64) fail(at, 'must be at most 18446744073709551615');
  return value;
}
function bool(value: unknown, at: string): boolean {
  if (typeof value !== 'boolean') fail(at, 'expected a boolean');
  return value;
}
function array(value: unknown, at: string): unknown[] {
  if (!Array.isArray(value)) fail(at, 'expected an array');
  return value;
}
function optionalArray(o: Obj, key: string, at: string): unknown[] {
  return Object.hasOwn(o, key) ? array(o[key], `${at}.${key}`) : [];
}
function oneOf<T extends string>(value: unknown, at: string, values: readonly T[]): T {
  if (typeof value !== 'string' || !values.includes(value as T)) fail(at, `expected one of ${values.join(', ')}`);
  return value as T;
}
function unique(values: string[], at: string, what: string): void {
  const seen = new Set<string>();
  for (const value of values) { if (seen.has(value)) fail(at, `duplicate ${what} ${value}`); seen.add(value); }
}

/** A string with its escapes, a structural character, or a number or literal. */
const jsonToken = /"(?:[^"\\]|\\[\s\S])*"|[{}[\]:,]|[^{}[\]:,"\s]+/g;
/**
 * The tokens of JSON text that JSON.parse accepted, each exactly as written: `{`, `}`, `[`, `]`,
 * `:`, `,`, strings with their quotes and escapes, and numbers and literals. Whitespace between
 * tokens is left out.
 */
export function jsonTokens(text: string): string[] {
  return text.match(jsonToken) ?? [];
}

/**
 * The first key that repeats within one object of JSON text that JSON.parse accepted, compared after
 * its escapes are decoded. JSON.parse keeps the last field of such a key, where suimon rejects the
 * text, so the tokens of the text are read: each open object keeps the keys read so far.
 */
function repeatedKey(text: string): string | undefined {
  const open: (Set<string> | null)[] = []; // the keys of each open object, null for an array
  let atKey = false;
  for (const token of jsonTokens(text)) {
    if (token === '{') { open.push(new Set()); atKey = true; }
    else if (token === '[') { open.push(null); atKey = false; }
    else if (token === '}' || token === ']') { open.pop(); atKey = false; }
    else if (token === ',') atKey = open.at(-1) instanceof Set;
    else if (atKey) {
      const key = JSON.parse(token) as string, keys = open.at(-1)!;
      if (keys.has(key)) return key;
      keys.add(key);
      atKey = false;
    }
  }
  return undefined;
}
/** JSON text as suimon reads it: no object may repeat a key. */
function json(text: string, at: string, expected: string): unknown {
  let value: unknown;
  try { value = JSON.parse(text); } catch { return fail(at, expected); }
  const key = repeatedKey(text);
  if (key !== undefined) fail(at, `duplicate key ${JSON.stringify(key)}`);
  return value;
}

/* Definition */

function valueType(value: unknown, at: string): ValueType {
  if (typeof value === 'string') return name(value, at);
  if (isObject(value)) { object(value, at, ['list']); return { list: valueType(field(value, 'list', at), `${at}.list`) }; }
  return fail(at, 'a type is a name or {"list": type}');
}
function contract(value: unknown, at: string): Contract {
  const o = object(value, at, ['single', 'stream']);
  const single = Object.hasOwn(o, 'single'), stream = Object.hasOwn(o, 'stream');
  if (single === stream) fail(at, 'an output contract is either single or stream');
  return single ? { single: valueType(o.single, `${at}.single`) } : { stream: valueType(o.stream, `${at}.stream`) };
}
const policy = (value: unknown, at: string): Policy => oneOf(value, at, ['stop', 'continue'] as const);
function timeout(o: Obj, at: string): Timeout | undefined {
  if (!Object.hasOwn(o, 'timeout')) return undefined;
  const t = object(o.timeout, `${at}.timeout`, ['callMs', 'elementMs']), result: Timeout = {};
  if (Object.hasOwn(t, 'callMs')) result.callMs = bounded(t.callMs, `${at}.timeout.callMs`);
  if (Object.hasOwn(t, 'elementMs')) result.elementMs = bounded(t.elementMs, `${at}.timeout.elementMs`);
  return result;
}
function body(value: unknown, at: string): Body {
  const o = object(value, at);
  const type = oneOf(field(o, 'type', at), `${at}.type`, ['function', 'subworkflow'] as const);
  if (type === 'function') { object(o, at, ['type', 'function']); return { type, function: name(field(o, 'function', at), `${at}.function`) }; }
  object(o, at, ['type', 'workflow', 'output']);
  return { type, workflow: name(field(o, 'workflow', at), `${at}.workflow`), output: name(field(o, 'output', at), `${at}.output`) };
}
function task(value: unknown, at: string): Task {
  const o = object(value, at, ['name', 'body', 'inputTransform', 'outputTransform', 'policy', 'timeout']);
  const taskName = name(field(o, 'name', at), `${at}.name`);
  at = `${at.replace(/\[\d+\]$/, '')}[${taskName}]`;
  const result: Task = { name: taskName, body: body(field(o, 'body', at), `${at}.body`), policy: policy(field(o, 'policy', at), `${at}.policy`) };
  if (Object.hasOwn(o, 'inputTransform')) result.inputTransform = name(o.inputTransform, `${at}.inputTransform`);
  if (Object.hasOwn(o, 'outputTransform')) result.outputTransform = name(o.outputTransform, `${at}.outputTransform`);
  const t = timeout(o, at);
  if (t) result.timeout = t;
  return result;
}
const controlTypes = ['function', 'subworkflow', 'branch', 'waitStream', 'merge', 'concurrency'] as const;
function control(value: unknown, at: string): Control {
  const o = object(value, at);
  const type = oneOf(field(o, 'type', at), `${at}.type`, controlTypes);
  switch (type) {
    case 'function': case 'subworkflow': return body(o, at);
    case 'branch': {
      object(o, at, ['type', 'judge', 'arms']);
      const arms = array(field(o, 'arms', at), `${at}.arms`).map((arm, i) => name(arm, `${at}.arms[${i}]`));
      if (!arms.length) fail(`${at}.arms`, 'expected at least one arm');
      unique(arms, `${at}.arms`, 'arm');
      return { type, judge: name(field(o, 'judge', at), `${at}.judge`), arms };
    }
    case 'waitStream': case 'merge':
      object(o, at, ['type', 'element']);
      return { type, element: valueType(field(o, 'element', at), `${at}.element`) };
    case 'concurrency': {
      object(o, at, ['type', 'input', 'limit', 'tasks', 'output', 'element']);
      const tasks = array(field(o, 'tasks', at), `${at}.tasks`).map((item, i) => task(item, `${at}.tasks[${i}]`));
      if (!tasks.length) fail(`${at}.tasks`, 'expected at least one task');
      unique(tasks.map(t => t.name), `${at}.tasks`, 'task');
      const result: Control = {
        type, limit: bounded(field(o, 'limit', at), `${at}.limit`), tasks,
        output: oneOf(field(o, 'output', at), `${at}.output`, ['list', 'stream'] as const),
        element: valueType(field(o, 'element', at), `${at}.element`),
      };
      if (Object.hasOwn(o, 'input')) result.input = valueType(o.input, `${at}.input`);
      return result;
    }
  }
}
function placement(value: unknown, at: string): Placement {
  const o = object(value, at, ['name', 'node', 'policy', 'timeout']);
  const placementName = name(field(o, 'name', at), `${at}.name`);
  at = `${at.replace(/\[\d+\]$/, '')}[${placementName}]`;
  const result: Placement = { name: placementName, node: control(field(o, 'node', at), `${at}.node`), policy: policy(field(o, 'policy', at), `${at}.policy`) };
  const t = timeout(o, at);
  if (t) result.timeout = t;
  return result;
}
function connection(value: unknown, at: string): Connection {
  const o = object(value, at, ['source', 'arm', 'target', 'transform']);
  const result: Connection = { source: name(field(o, 'source', at), `${at}.source`), target: name(field(o, 'target', at), `${at}.target`), transform: name(field(o, 'transform', at), `${at}.transform`) };
  if (Object.hasOwn(o, 'arm')) result.arm = name(o.arm, `${at}.arm`);
  return result;
}
function workflow(value: unknown, at: string): Workflow {
  const o = object(value, at, ['id', 'input', 'placements', 'connections']);
  const id = name(field(o, 'id', at), `${at}.id`);
  at = `definition.workflows[${id}]`;
  const placements = array(field(o, 'placements', at), `${at}.placements`).map((item, i) => placement(item, `${at}.placements[${i}]`));
  if (!placements.length) fail(`${at}.placements`, 'expected at least one placement');
  const result: Workflow = { id, placements, connections: optionalArray(o, 'connections', at).map((item, i) => connection(item, `${at}.connections[${i}]`)) };
  if (Object.hasOwn(o, 'input')) {
    const entry = object(o.input, `${at}.input`, ['type', 'placement']);
    result.input = { type: valueType(field(entry, 'type', `${at}.input`), `${at}.input.type`), placement: name(field(entry, 'placement', `${at}.input`), `${at}.input.placement`) };
  }
  return result;
}

/** The references the kit follows to draw and navigate: placements, arms and called workflows. */
function checkReferences(definition: Definition): void {
  unique(definition.workflows.map(w => w.id), 'definition.workflows', 'workflow');
  const workflows = new Map(definition.workflows.map(w => [w.id, w]));
  if (!workflows.has(definition.main)) fail('definition.main', `unknown workflow ${definition.main}`);
  const checkBody = (b: Body, at: string) => {
    if (b.type !== 'subworkflow') return;
    const called = workflows.get(b.workflow);
    if (!called) fail(at, `unknown workflow ${b.workflow}`);
    if (!called.placements.some(p => p.name === b.output)) fail(at, `workflow ${b.workflow} has no placement ${b.output}`);
  };
  for (const w of definition.workflows) {
    const at = `definition.workflows[${w.id}]`;
    unique(w.placements.map(p => p.name), `${at}.placements`, 'placement');
    const placements = new Map(w.placements.map(p => [p.name, p]));
    if (w.input && !placements.has(w.input.placement)) fail(`${at}.input.placement`, `unknown placement ${w.input.placement}`);
    w.connections.forEach((c, i) => {
      const cat = `${at}.connections[${i}]`;
      const source = placements.get(c.source);
      if (!source) fail(`${cat}.source`, `unknown placement ${c.source}`);
      if (!placements.has(c.target)) fail(`${cat}.target`, `unknown placement ${c.target}`);
      if (source.node.type === 'branch') {
        if (c.arm === undefined) fail(cat, 'a connection from a branch needs an arm');
        if (!source.node.arms.includes(c.arm)) fail(`${cat}.arm`, `unknown arm ${c.arm}`);
      } else if (c.arm !== undefined) fail(`${cat}.arm`, 'only a connection from a branch has an arm');
    });
    for (const p of w.placements) {
      const pat = `${at}.placements[${p.name}].node`;
      if (p.node.type === 'subworkflow') checkBody(p.node, pat);
      if (p.node.type === 'concurrency') for (const t of p.node.tasks) checkBody(t.body, `${pat}.tasks[${t.name}].body`);
    }
  }
}

/**
 * Checks the structure of a definition (definition.schema.json) and the references the kit follows.
 * Types and Single/Stream kinds are left to `suimon validate`.
 *
 * The definition is a parsed value, or the text of a definition file, in which no object may repeat
 * a key, as `suimon validate` reads it; a parsed value has already lost such keys.
 */
export function parseDefinition(value: unknown): Definition {
  const at = 'definition';
  const o = object(typeof value === 'string' ? json(value, at, 'expected a JSON definition') : value, at,
    ['main', 'functions', 'judges', 'transforms', 'workflows']);
  const definition: Definition = {
    main: name(field(o, 'main', at), `${at}.main`),
    functions: optionalArray(o, 'functions', at).map((item, i): FunctionDecl => {
      const fat = `${at}.functions[${i}]`, f = object(item, fat, ['id', 'input', 'output']);
      const decl: FunctionDecl = { id: name(field(f, 'id', fat), `${fat}.id`), output: contract(field(f, 'output', fat), `${fat}.output`) };
      if (Object.hasOwn(f, 'input')) decl.input = valueType(f.input, `${fat}.input`);
      return decl;
    }),
    judges: optionalArray(o, 'judges', at).map((item, i): JudgeDecl => {
      const jat = `${at}.judges[${i}]`, j = object(item, jat, ['id', 'input']);
      return { id: name(field(j, 'id', jat), `${jat}.id`), input: valueType(field(j, 'input', jat), `${jat}.input`) };
    }),
    transforms: optionalArray(o, 'transforms', at).map((item, i): TransformDecl => {
      const tat = `${at}.transforms[${i}]`, t = object(item, tat, ['id', 'input', 'output']);
      return { id: name(field(t, 'id', tat), `${tat}.id`), input: valueType(field(t, 'input', tat), `${tat}.input`), output: valueType(field(t, 'output', tat), `${tat}.output`) };
    }),
    workflows: array(field(o, 'workflows', at), `${at}.workflows`).map((item, i) => workflow(item, `${at}.workflows[${i}]`)),
  };
  checkReferences(definition);
  return definition;
}

/* Runtime state (derived JSON of Suimon/State.lean). Unknown fields are ignored. */

function path(value: unknown, at: string): Path { return array(value, at).map((segment, i) => string(segment, `${at}[${i}]`)); }
function optional<T>(o: Obj, key: string, at: string, parse: (value: unknown, at: string) => T): T | null {
  return o[key] === undefined || o[key] === null ? null : parse(o[key], `${at}.${key}`);
}
function req<T>(o: Obj, key: string, at: string, parse: (value: unknown, at: string) => T): T { return parse(field(o, key, at), `${at}.${key}`); }
function list<T>(o: Obj, key: string, at: string, parse: (value: unknown, at: string) => T): T[] {
  return array(field(o, key, at), `${at}.${key}`).map((item, i) => parse(item, `${at}.${key}[${i}]`));
}
const outcomes = ['normal', 'skipped', 'failed', 'upstreamFailed'] as const;
const outcome = (value: unknown, at: string) => oneOf(value, at, outcomes);

function run(value: unknown, at: string): Run {
  const o = object(value, at);
  return { path: req(o, 'path', at, path), workflow: req(o, 'workflow', at, string), input: optional(o, 'input', at, string), owner: optional(o, 'owner', at, string), task: optional(o, 'task', at, string), complete: req(o, 'complete', at, bool) };
}
function invocation(value: unknown, at: string): Invocation {
  const o = object(value, at);
  return {
    id: req(o, 'id', at, string), run: req(o, 'run', at, path), placement: req(o, 'placement', at, string),
    trigger: optional(o, 'trigger', at, string), input: optional(o, 'input', at, string),
    status: req(o, 'status', at, (v, a) => oneOf(v, a, ['active', 'succeeded', 'skipped', 'failed', 'upstreamFailed', 'cancelled'] as const)),
    arm: optional(o, 'arm', at, string),
  };
}
function callTarget(value: unknown, at: string): CallTarget {
  const o = object(value, at, ['function', 'judge']);
  const keys = Object.keys(o);
  if (keys.length !== 1) fail(at, 'expected {"function": {"id": ...}} or {"judge": {"id": ...}}');
  const key = keys[0] as 'function' | 'judge', inner = object(o[key], `${at}.${key}`);
  const id = req(inner, 'id', `${at}.${key}`, string);
  return key === 'function' ? { function: { id } } : { judge: { id } };
}
function call(value: unknown, at: string): Call {
  const o = object(value, at), t = object(field(o, 'timeout', at), `${at}.timeout`);
  return {
    id: req(o, 'id', at, string), owner: req(o, 'owner', at, string), task: optional(o, 'task', at, string),
    target: req(o, 'target', at, callTarget), input: optional(o, 'input', at, string), stream: req(o, 'stream', at, bool),
    status: req(o, 'status', at, (v, a) => oneOf(v, a, ['running', 'fetching', 'cancelling', 'returned', 'failed', 'lost', 'cancelled'] as const)),
    yields: req(o, 'yields', at, nat),
    timeout: { callMs: optional(t, 'callMs', `${at}.timeout`, nat), elementMs: optional(t, 'elementMs', `${at}.timeout`, nat) },
    policy: req(o, 'policy', at, policy),
  };
}
function taskState(value: unknown, at: string): TaskState {
  const o = object(value, at);
  return { name: req(o, 'name', at, string), input: optional(o, 'input', at, string), status: req(o, 'status', at, (v, a) => oneOf(v, a, ['pending', 'ready', 'active', 'succeeded', 'skipped', 'failed', 'upstreamFailed', 'notStarted', 'cancelled'] as const)) };
}
function execution(value: unknown, at: string): Execution {
  const o = object(value, at);
  return { id: req(o, 'id', at, string), run: req(o, 'run', at, path), placement: req(o, 'placement', at, string), input: optional(o, 'input', at, string), tasks: list(o, 'tasks', at, taskState), complete: req(o, 'complete', at, bool) };
}
/** `{"value": {"v": id}}`, the derived JSON of a constructor with one value. */
function valueCase(value: unknown, at: string): { value: { v: string } } | undefined {
  if (!isObject(value) || !Object.hasOwn(value, 'value')) return undefined;
  return { value: { v: req(object(value.value, `${at}.value`), 'v', `${at}.value`, string) } };
}
function taskOutput(value: unknown, at: string): TaskOutput {
  if (value === 'pending' || value === 'failed') return value;
  return valueCase(value, at) ?? fail(at, 'expected "pending", {"value": {"v": ...}} or "failed"');
}
function taskResult(value: unknown, at: string): TaskResult {
  const o = object(value, at);
  return { execution: req(o, 'execution', at, string), task: req(o, 'task', at, string), index: req(o, 'index', at, nat), value: req(o, 'value', at, string), output: req(o, 'output', at, taskOutput) };
}
function result(value: unknown, at: string): Result {
  const o = object(value, at);
  return { id: req(o, 'id', at, string), run: req(o, 'run', at, path), placement: req(o, 'placement', at, string), producer: req(o, 'producer', at, string), arm: optional(o, 'arm', at, string), value: req(o, 'value', at, string) };
}
function delivered(value: unknown, at: string): Delivered {
  if (value === 'trigger' || value === 'failed') return value;
  return valueCase(value, at) ?? fail(at, 'expected {"value": {"v": ...}}, "trigger" or "failed"');
}
function delivery(value: unknown, at: string): Delivery {
  const o = object(value, at);
  return { run: req(o, 'run', at, path), connection: req(o, 'connection', at, nat), source: req(o, 'source', at, string), outcome: req(o, 'outcome', at, delivered) };
}
function settled(value: unknown, at: string): Settled {
  const o = object(value, at);
  return {
    run: req(o, 'run', at, path), placement: req(o, 'placement', at, string), outcome: req(o, 'outcome', at, outcome),
    arms: list(o, 'arms', at, (pair, pat) => {
      const items = array(pair, pat);
      if (items.length !== 2) fail(pat, 'expected [arm, outcome]');
      return [string(items[0], `${pat}[0]`), outcome(items[1], `${pat}[1]`)] as [string, Settled['outcome']];
    }),
  };
}
function failure(value: unknown, at: string): Failure {
  const o = object(value, at);
  return { run: req(o, 'run', at, path), placement: req(o, 'placement', at, string), task: optional(o, 'task', at, string), cause: req(o, 'cause', at, (v, a) => oneOf(v, a, ['error', 'timeout', 'lost', 'transform'] as const)) };
}

/** Checks a runtime state in the derived JSON form of Suimon/State.lean and normalizes Option fields to null. */
export function parseState(value: unknown): RuntimeState {
  const at = 'state', o = object(value, at);
  return {
    status: req(o, 'status', at, (v, a) => oneOf(v, a, ['running', 'stopping', 'succeeded', 'failed', 'cancelled', 'skipped'] as const)),
    started: req(o, 'started', at, bool), cancelled: req(o, 'cancelled', at, bool),
    runs: list(o, 'runs', at, run), invocations: list(o, 'invocations', at, invocation), calls: list(o, 'calls', at, call),
    executions: list(o, 'executions', at, execution), results: list(o, 'results', at, result), taskResults: list(o, 'taskResults', at, taskResult),
    deliveries: list(o, 'deliveries', at, delivery), settled: list(o, 'settled', at, settled), failures: list(o, 'failures', at, failure),
  };
}

/* Execution records (trace.schema.json) */

type FieldKind = 'text' | 'path' | 'index' | 'boolean';
const call1 = { call: ['text', true] } as const;
const taskKeys = { execution: ['text', true], task: ['text', true] } as const;
const opFields: Record<OpType, Record<string, readonly [FieldKind, boolean]>> = {
  start: { input: ['text', false] },
  invoke: { run: ['path', true], placement: ['text', true], trigger: ['text', false] },
  fetch: call1, ended: call1, failed: call1, lost: call1, terminated: call1,
  returned: { ...call1, value: ['text', true] }, yielded: { ...call1, value: ['text', true] },
  judged: { ...call1, arm: ['text', true] }, timedOut: { ...call1, element: ['boolean', true] },
  deliver: { run: ['path', true], connection: ['index', true], source: ['text', true], value: ['text', false] },
  transformFailed: { run: ['path', true], connection: ['index', true], source: ['text', true] },
  taskInput: { ...taskKeys, value: ['text', false] }, taskInputFailed: taskKeys, beginTask: taskKeys,
  taskOutput: { ...taskKeys, index: ['index', true], value: ['text', true] }, taskOutputFailed: { ...taskKeys, index: ['index', true] },
  settle: { run: ['path', true], placement: ['text', true] },
  closeExecution: { execution: ['text', true] }, closeRun: { run: ['path', true] },
  cancel: {}, conclude: {},
};
function op(value: unknown, at: string): Op {
  const o = object(value, at);
  const type = oneOf(field(o, 'type', at), `${at}.type`, Object.keys(opFields) as OpType[]);
  const fields = opFields[type];
  object(o, `${at} ${type}`, ['type', ...Object.keys(fields)]);
  const result: Record<string, unknown> = { type };
  for (const [key, [kind, required]] of Object.entries(fields)) {
    if (!Object.hasOwn(o, key)) { if (required) fail(`${at} ${type}`, `missing field ${key}`); continue; }
    const fat = `${at}.${key}`;
    result[key] = kind === 'text' ? string(o[key], fat) : kind === 'path' ? path(o[key], fat) : kind === 'index' ? nat(o[key], fat) : bool(o[key], fat);
  }
  return result as Op;
}
/** Payloads by value identity, without a prototype: an identity such as `__proto__` stays a key. */
function payloads(value: unknown, at: string): Record<string, string> {
  const o = object(value, at), result = dictionary<string>();
  for (const [id, payload] of Object.entries(o)) result[id] = string(payload, `${at}.${id}`);
  return result;
}
/** The header, the first line of a record: the definition of the execution, checked by parseDefinition. */
function header(value: unknown, at: string): Definition {
  if (!isObject(value) || !Object.hasOwn(value, 'definition')) fail(at, 'expected the header with the definition');
  const o = object(value, at, ['definition']);
  try { return parseDefinition(o.definition); } catch (error) { return fail(at, error instanceof Error ? error.message : String(error)); }
}
function record(value: unknown, at: string): ExecutionRecord {
  const o = object(value, at);
  if (Object.hasOwn(o, 'definition')) fail(at, 'the header must be the first line');
  const seq = positive(field(o, 'seq', at), `${at}.seq`);
  if (Object.hasOwn(o, 'commit')) {
    object(o, at, ['seq', 'commit']);
    if (o.commit !== true) fail(`${at}.commit`, 'expected true');
    return { seq, commit: true };
  }
  object(o, at, ['seq', 'op', 'values']);
  const parsed: ExecutionRecord = { seq, op: op(field(o, 'op', at), `${at}.op`) };
  if (Object.hasOwn(o, 'values')) parsed.values = payloads(o.values, `${at}.values`);
  return parsed;
}

export interface RecordOptions {
  /**
   * For an array input: the text after the last newline, which the host split off. It is never
   * parsed or committed, only returned as the log's tail. Ignored for text, whose tail is found here.
   */
  tail?: string;
}

/**
 * Checks execution record lines, as `suimon check` reads them, and keeps the torn tail apart.
 *
 * Text is split at newlines: the first complete line (followed by a newline) must be the header,
 * whose definition is checked with parseDefinition, each later complete line one record, and the
 * text after the last newline is the tail. A crash can leave a partial line there, even of the
 * header; the tail is never committed, even when it parses, so it is returned as text and not read.
 * No object of a line may repeat a key, at any depth, the definition of the header included.
 *
 * An array holds complete lines, as strings or parsed objects, for hosts that split lines
 * themselves: the header, then records. A parsed object has already lost the repeated keys of its
 * line. A host that kept a final line without its newline passes it as `options.tail` instead of as
 * an item, since an item is a complete line.
 *
 * Records must follow each other from seq 1, each op followed by its commit; an op without its
 * commit may only come last, and is uncommitted.
 */
export function parseRecordLog(value: unknown, options: RecordOptions = {}): RecordLog {
  let items: { value: unknown; at: string }[], tail: string;
  const line = (text: string, at: string) => json(text, at, 'expected a JSON record');
  if (typeof value === 'string') {
    const lines = value.split('\n');
    tail = lines.pop() ?? '';
    items = lines.map((text, i) => ({ value: line(text, `line ${i + 1}`), at: `line ${i + 1}` }));
  } else {
    if (options.tail !== undefined) string(options.tail, 'options.tail');
    tail = options.tail ?? '';
    items = array(value, 'records').map((item, i) => ({ value: typeof item === 'string' ? line(item, `records[${i}]`) : item, at: `records[${i}]` }));
  }
  const records: ExecutionRecord[] = [];
  let definition: Definition | null = null, pending = false;
  for (const [i, item] of items.entries()) {
    if (i === 0) { definition = header(item.value, item.at); continue; }
    const r = record(item.value, item.at);
    const expected = records.length + 1;
    if (r.seq !== expected) fail(item.at, `expected sequence ${expected}, got ${r.seq}`);
    if ('commit' in r) { if (!pending) fail(item.at, 'a commit without an op'); pending = false; }
    else { if (pending) fail(item.at, 'an op before the previous commit'); pending = true; }
    records.push(r);
  }
  return { definition, records, tail };
}

/** The records of `parseRecordLog`, without the header and the tail. */
export function parseRecords(value: unknown, options?: RecordOptions): ExecutionRecord[] {
  return parseRecordLog(value, options).records;
}
