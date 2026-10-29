import type { Body, Concurrency, Connection, Contract, Control, Definition, FunctionDecl, JudgeDecl, Kind, Placement, Policy, TaskSpec, Timeout, TransformDecl, ValueType, Workflow } from './model-types.js';
import { JsonNumber, MAX_INPUT_BYTES, parseJson, renderWire } from './json.js';
import type { JsonObject, JsonValue } from './json.js';

const MAX_UINT64 = (1n << 64n) - 1n;
export class ValidationError extends Error { override name = 'ValidationError'; }
function invalid(message: string): never { throw new ValidationError(message); }
function decodeError(message: string): never { throw new Error(message); }
const scalarCompare = (a: string, b: string): number => Buffer.compare(Buffer.from(a), Buffer.from(b));

function object(value: JsonValue, allowed: readonly string[], at: string): JsonObject {
  if (value === null || typeof value !== 'object' || Array.isArray(value) || value instanceof JsonNumber) decodeError(`${at}: expected an object`);
  for (const key of Object.keys(value).sort(scalarCompare)) if (!allowed.includes(key)) decodeError(`${at}: unknown field ${key}`);
  return value;
}
function required(value: JsonValue, key: string, at: string): JsonValue {
  if (value === null || typeof value !== 'object' || Array.isArray(value) || value instanceof JsonNumber || !Object.hasOwn(value, key)) decodeError(`${at}: missing field ${key}`);
  const field = value[key];
  if (field === undefined) decodeError(`${at}: missing field ${key}`);
  return field;
}
function text(value: JsonValue, at: string): string {
  if (typeof value !== 'string') decodeError(`${at}: expected a string`);
  if (value === '') decodeError(`${at}: empty string`);
  return value;
}
const textField = (value: JsonValue, key: string, at: string): string => text(required(value, key, at), `${at}.${key}`);
function optionalText(value: JsonObject, key: string, at: string): string | undefined {
  const v = value[key];
  return v === undefined ? undefined : text(v, `${at}.${key}`);
}
function natural(value: JsonObject, key: string, at: string): bigint | undefined {
  const v = value[key];
  if (v === undefined) return undefined;
  if (typeof v === 'bigint' && v >= 0n) {
    if (v > MAX_UINT64) decodeError(`${at}.${key}: must be at most ${MAX_UINT64}`);
    return v;
  }
  decodeError(`${at}.${key}: expected a natural number`);
}
function list(value: JsonObject, key: string, at: string): JsonValue[] {
  const v = value[key];
  if (v === undefined) return [];
  if (!Array.isArray(v)) decodeError(`${at}.${key}: expected an array`);
  return v;
}
function decodeType(value: JsonValue, at: string): ValueType {
  let depth = 0;
  while (typeof value !== 'string') {
    if (value === null || typeof value !== 'object' || Array.isArray(value) || value instanceof JsonNumber) decodeError(`${at}: a type is a name or {"list": type}`);
    if (depth === 64) decodeError('input exceeds maximum nesting depth of 64');
    value = required(object(value, ['list'], at), 'list', at);
    depth++;
  }
  if (value === '') decodeError(`${at}: empty type name`);
  let type: ValueType = value;
  while (depth-- > 0) type = { list: type };
  return type;
}
function decodeContract(value: JsonValue, at: string): Contract {
  const o = object(value, ['single', 'stream'], at);
  if (o.single !== undefined && o.stream === undefined) return { single: decodeType(o.single, `${at}.single`) };
  if (o.stream !== undefined && o.single === undefined) return { stream: decodeType(o.stream, `${at}.stream`) };
  decodeError(`${at}: an output contract is either single or stream`);
}
function decodePolicy(value: JsonValue, at: string): Policy {
  if (value === 'stop' || value === 'continue') return value;
  decodeError(`${at}: policy is stop or continue`);
}
function decodeTimeout(o: JsonObject, at: string): Timeout | undefined {
  if (o.timeout === undefined) return undefined;
  const value = object(o.timeout, ['callMs', 'elementMs'], `${at}.timeout`);
  const callMs = natural(value, 'callMs', `${at}.timeout`), elementMs = natural(value, 'elementMs', `${at}.timeout`);
  return { ...(callMs === undefined ? {} : { callMs }), ...(elementMs === undefined ? {} : { elementMs }) };
}
function decodeBody(value: JsonValue, at: string): Body {
  const type = textField(value, 'type', at);
  if (type === 'function') {
    const o = object(value, ['type', 'function'], at);
    return { type, function: textField(o, 'function', at) };
  }
  if (type === 'subworkflow') {
    const o = object(value, ['type', 'workflow', 'output'], at);
    return { type, workflow: textField(o, 'workflow', at), output: textField(o, 'output', at) };
  }
  decodeError(`${at}: unknown body type ${type}`);
}
function decodeTask(value: JsonValue, at: string): TaskSpec {
  const o = object(value, ['name', 'body', 'inputTransform', 'outputTransform', 'policy', 'timeout'], at);
  const name = textField(o, 'name', at);
  at += `.${name}`;
  const body = decodeBody(required(o, 'body', at), `${at}.body`);
  const inputTransform = optionalText(o, 'inputTransform', at), outputTransform = optionalText(o, 'outputTransform', at);
  const policy = decodePolicy(required(o, 'policy', at), `${at}.policy`), timeout = decodeTimeout(o, at);
  return { name, body, ...(inputTransform === undefined ? {} : { inputTransform }), ...(outputTransform === undefined ? {} : { outputTransform }), policy, ...(timeout === undefined ? {} : { timeout }) };
}
function decodeControl(value: JsonValue, at: string): Control {
  const type = textField(value, 'type', at);
  switch (type) {
    case 'function': case 'subworkflow': return decodeBody(value, at);
    case 'branch': {
      const o = object(value, ['type', 'judge', 'arms'], at);
      const arms = list(o, 'arms', at).map(v => text(v, `${at}.arms`));
      return { type, judge: textField(o, 'judge', at), arms };
    }
    case 'waitStream': case 'merge': {
      const o = object(value, ['type', 'element'], at);
      return { type, element: decodeType(required(o, 'element', at), `${at}.element`) };
    }
    case 'concurrency': {
      const o = object(value, ['type', 'input', 'limit', 'tasks', 'output', 'element'], at);
      const limit = natural(o, 'limit', at);
      const input = o.input === undefined ? undefined : decodeType(o.input, `${at}.input`);
      if (limit === undefined) decodeError(`${at}: missing field limit`);
      const tasks = list(o, 'tasks', at).map(v => decodeTask(v, `${at}.tasks`));
      const output = required(o, 'output', at);
      if (output !== 'list' && output !== 'stream') decodeError(`${at}.output: output is list or stream`);
      const element = decodeType(required(o, 'element', at), `${at}.element`);
      return { type, ...(input === undefined ? {} : { input }), limit, tasks, output, element };
    }
    default: decodeError(`${at}: unknown node type ${type}`);
  }
}
function decodePlacement(value: JsonValue, at: string): Placement {
  const o = object(value, ['name', 'node', 'policy', 'timeout'], at);
  const name = textField(o, 'name', at);
  at += `.${name}`;
  const node = decodeControl(required(o, 'node', at), `${at}.node`);
  const policy = decodePolicy(required(o, 'policy', at), `${at}.policy`), timeout = decodeTimeout(o, at);
  return { name, node, policy, ...(timeout === undefined ? {} : { timeout }) };
}
function decodeConnection(value: JsonValue, at: string): Connection {
  const o = object(value, ['source', 'arm', 'target', 'transform'], at);
  const source = textField(o, 'source', at), arm = optionalText(o, 'arm', at), target = textField(o, 'target', at), transform = textField(o, 'transform', at);
  return { source, ...(arm === undefined ? {} : { arm }), target, transform };
}
function decodeWorkflow(value: JsonValue, at: string): Workflow {
  const o = object(value, ['id', 'input', 'placements', 'connections'], at);
  const id = textField(o, 'id', at);
  at += `.${id}`;
  let input: Workflow['input'];
  if (o.input !== undefined) {
    const entry = object(o.input, ['type', 'placement'], `${at}.input`);
    input = { type: decodeType(required(entry, 'type', `${at}.input`), `${at}.input.type`), placement: textField(entry, 'placement', `${at}.input`) };
  }
  const placements = list(o, 'placements', at).map(v => decodePlacement(v, `${at}.placements`));
  const connections = list(o, 'connections', at).map(v => decodeConnection(v, `${at}.connections`));
  return { id, ...(input === undefined ? {} : { input }), placements, connections };
}
function decodeFunction(value: JsonValue, at: string): FunctionDecl {
  const o = object(value, ['id', 'input', 'output'], at);
  const id = textField(o, 'id', at);
  at += `.${id}`;
  const input = o.input === undefined ? undefined : decodeType(o.input, `${at}.input`);
  const output = decodeContract(required(o, 'output', at), `${at}.output`);
  return { id, ...(input === undefined ? {} : { input }), output };
}
function decodeJudge(value: JsonValue, at: string): JudgeDecl {
  const o = object(value, ['id', 'input'], at);
  const id = textField(o, 'id', at), input = required(o, 'input', at);
  return { id, input: decodeType(input, `${at}.${id}.input`) };
}
function decodeTransform(value: JsonValue, at: string): TransformDecl {
  const o = object(value, ['id', 'input', 'output'], at);
  const id = textField(o, 'id', at), input = decodeType(required(o, 'input', at), `${at}.${id}.input`), output = decodeType(required(o, 'output', at), `${at}.${id}.output`);
  return { id, input, output };
}

export function parseDefinition(data: string | Uint8Array): Definition {
  if ((typeof data === 'string' ? Buffer.byteLength(data, 'utf8') : data.byteLength) > MAX_INPUT_BYTES) decodeError(`input exceeds maximum size of ${MAX_INPUT_BYTES} bytes`);
  let source: string;
  if (typeof data === 'string') {
    if (/[\uD800-\uDFFF]/u.test(data)) decodeError('definition: invalid UTF-8');
    source = data;
  } else {
    try { source = new TextDecoder('utf-8', { fatal: true, ignoreBOM: true }).decode(data); }
    catch { decodeError('definition: invalid UTF-8'); }
  }
  const o = object(parseJson(source, 'definition'), ['main', 'functions', 'judges', 'transforms', 'workflows'], 'definition');
  const main = textField(o, 'main', 'definition');
  const functions = list(o, 'functions', 'definition').map(v => decodeFunction(v, 'functions'));
  const judges = list(o, 'judges', 'definition').map(v => decodeJudge(v, 'judges'));
  const transforms = list(o, 'transforms', 'definition').map(v => decodeTransform(v, 'transforms'));
  const workflows = list(o, 'workflows', 'definition').map(v => decodeWorkflow(v, 'workflows'));
  return { main, functions, judges, transforms, workflows };
}

function timeoutWire(timeout?: Timeout): JsonObject {
  if (timeout?.callMs === undefined && timeout?.elementMs === undefined) return {};
  return { timeout: { ...(timeout.callMs === undefined ? {} : { callMs: timeout.callMs }), ...(timeout.elementMs === undefined ? {} : { elementMs: timeout.elementMs }) } };
}
function typeWire(type: ValueType): JsonValue { return typeof type === 'string' ? type : { list: typeWire(type.list) }; }
function bodyWire(body: Body): JsonObject {
  return body.type === 'function' ? { type: body.type, function: body.function } : { type: body.type, workflow: body.workflow, output: body.output };
}
function taskWire(task: TaskSpec): JsonValue {
  return { name: task.name, body: bodyWire(task.body), ...(task.inputTransform === undefined ? {} : { inputTransform: task.inputTransform }), ...(task.outputTransform === undefined ? {} : { outputTransform: task.outputTransform }), policy: task.policy, ...timeoutWire(task.timeout) };
}
function controlWire(node: Control): JsonValue {
  switch (node.type) {
    case 'function': case 'subworkflow': return bodyWire(node);
    case 'branch': return { type: node.type, judge: node.judge, arms: [...node.arms] };
    case 'merge': case 'waitStream': return { type: node.type, element: typeWire(node.element) };
    case 'concurrency': return { type: node.type, ...(node.input === undefined ? {} : { input: typeWire(node.input) }), limit: node.limit, tasks: node.tasks.map(taskWire), output: node.output, element: typeWire(node.element) };
  }
}
export function encodeDefinition(def: Definition): string {
  return renderWire({
    main: def.main,
    functions: def.functions.map(f => ({ id: f.id, ...(f.input === undefined ? {} : { input: typeWire(f.input) }), output: 'single' in f.output ? { single: typeWire(f.output.single) } : { stream: typeWire(f.output.stream) } })),
    judges: def.judges.map(j => ({ id: j.id, input: typeWire(j.input) })),
    transforms: def.transforms.map(t => ({ id: t.id, input: typeWire(t.input), output: typeWire(t.output) })),
    workflows: def.workflows.map(w => ({ id: w.id, ...(w.input === undefined ? {} : { input: { type: typeWire(w.input.type), placement: w.input.placement } }), placements: w.placements.map(p => ({ name: p.name, node: controlWire(p.node), policy: p.policy, ...timeoutWire(p.timeout) })), connections: w.connections.map(c => ({ source: c.source, ...(c.arm === undefined ? {} : { arm: c.arm }), target: c.target, transform: c.transform })) })),
  });
}

function checkLimit(name: string, count: number, limit: number): void {
  if (count > limit) invalid(`definition: ${name} limit exceeded (max ${limit})`);
}
export function checkDefinitionResources(def: Definition): void {
  const wc = def.workflows.length, declarations = def.functions.length + def.judges.length + def.transforms.length;
  checkLimit('workflow', wc, 128);
  checkLimit('declaration', declarations, 1024);
  const name = (s: string): void => checkLimit('name byte', Buffer.byteLength(s, 'utf8'), 256);
  const type = (t: ValueType): void => {
    let depth = 0;
    while (typeof t !== 'string') { checkLimit('type depth', ++depth, 32); t = t.list; }
    name(t);
  };
  const optionalType = (t?: ValueType): void => { if (t !== undefined) type(t); };
  const body = (b: Body): void => { if (b.type === 'function') name(b.function); else { name(b.workflow); name(b.output); } };
  name(def.main);
  for (const f of def.functions) { name(f.id); optionalType(f.input); type(contractType(f.output)); }
  for (const j of def.judges) { name(j.id); type(j.input); }
  for (const t of def.transforms) { name(t.id); type(t.input); type(t.output); }
  let placements = 0, connections = 0, tasks = 0, arms = 0;
  for (const w of def.workflows) {
    placements += w.placements.length;
    connections += w.connections.length;
    checkLimit('placement', placements, 1024);
    checkLimit('connection', connections, 4096);
    name(w.id);
    if (w.input !== undefined) { type(w.input.type); name(w.input.placement); }
    for (const p of w.placements) {
      name(p.name);
      const node = p.node;
      switch (node.type) {
        case 'function': case 'subworkflow': body(node); break;
        case 'branch':
          name(node.judge);
          arms += node.arms.length;
          checkLimit('arm', arms, 1024);
          node.arms.forEach(name);
          break;
        case 'waitStream': case 'merge': type(node.element); break;
        case 'concurrency':
          optionalType(node.input);
          type(node.element);
          tasks += node.tasks.length;
          checkLimit('task', tasks, 1024);
          for (const t of node.tasks) {
            name(t.name); body(t.body);
            if (t.inputTransform !== undefined) name(t.inputTransform === 'discard' ? '' : t.inputTransform);
            if (t.outputTransform !== undefined) name(t.outputTransform);
          }
          break;
      }
    }
    for (const c of w.connections) { name(c.source); name(c.target); name(c.transform === 'discard' ? '' : c.transform); if (c.arm !== undefined) name(c.arm); }
  }
  const d = declarations + wc, n = d + placements + connections + tasks + arms + 1;
  let work = n * n + wc * wc * wc * (placements + tasks + 1);
  for (const w of def.workflows) {
    const v = w.placements.length, e = w.connections.length;
    work += (2 * v + 2 * e + 1) * (v + 1) * (v * (v + e + d + 1) + e);
    work += v * v * (v * e + v);
    work += (e + tasks + v + 1) * (wc + 1) * (wc + placements + d + 1);
  }
  work += arms * connections;
  checkLimit('validation work', work, 1_000_000_000);
}

const functionDecl = (d: Definition, id: string): FunctionDecl | undefined => d.functions.find(f => f.id === id);
const judgeDecl = (d: Definition, id: string): JudgeDecl | undefined => d.judges.find(j => j.id === id);
const transformDecl = (d: Definition, id: string): TransformDecl | undefined => d.transforms.find(t => t.id === id);
const workflowDecl = (d: Definition, id: string): Workflow | undefined => d.workflows.find(w => w.id === id);
const placementDecl = (w: Workflow, name: string): Placement | undefined => w.placements.find(p => p.name === name);
const incoming = (w: Workflow, name: string): Connection[] => w.connections.filter(c => c.target === name);
const outgoing = (w: Workflow, name: string): Connection[] => w.connections.filter(c => c.source === name);
const isEntry = (w: Workflow, name: string): boolean => w.input?.placement === name;
const isEndpoint = (w: Workflow, name: string): boolean => outgoing(w, name).length === 0;
const contractType = (c: Contract): ValueType => 'single' in c ? c.single : c.stream;
const contractKind = (c: Contract): Kind => 'single' in c ? 'single' : 'stream';
const typeEqual = (a: ValueType, b: ValueType): boolean => {
  while (typeof a !== 'string' && typeof b !== 'string') { a = a.list; b = b.list; }
  return a === b;
};
function typeName(t: ValueType): string { while (typeof t !== 'string') t = t.list; return t; }
function typeText(t: ValueType): string {
  let depth = 0;
  while (typeof t !== 'string') { depth++; t = t.list; }
  return `${'List<'.repeat(depth)}${t}${'>'.repeat(depth)}`;
}

export function bodyInput(def: Definition, body: Body): ValueType | undefined {
  return body.type === 'function' ? functionDecl(def, body.function)?.input : workflowDecl(def, body.workflow)?.input?.type;
}
function bodyKnown(def: Definition, body: Body): boolean {
  return body.type === 'function' ? functionDecl(def, body.function) !== undefined : workflowDecl(def, body.workflow) !== undefined;
}
function localResult(def: Definition, node: Exclude<Control, Body>): ValueType | undefined {
  switch (node.type) {
    case 'branch': return judgeDecl(def, node.judge)?.input;
    case 'waitStream': case 'merge': return { list: node.element };
    case 'concurrency': return node.output === 'list' ? { list: node.element } : node.element;
  }
}
function bodyElement(def: Definition, body: Body): ValueType | undefined {
  for (let fuel = def.workflows.length + 1; fuel > 0; fuel--) {
    if (body.type === 'function') { const f = functionDecl(def, body.function); return f === undefined ? undefined : contractType(f.output); }
    const w = workflowDecl(def, body.workflow);
    const p = w === undefined ? undefined : placementDecl(w, body.output);
    if (p === undefined) return undefined;
    if (p.node.type !== 'function' && p.node.type !== 'subworkflow') return localResult(def, p.node);
    body = p.node;
  }
  return undefined;
}
export function bodyContract(def: Definition, body: Body): Contract | undefined {
  if (body.type === 'function') return functionDecl(def, body.function)?.output;
  const element = bodyElement(def, body);
  return element === undefined ? undefined : { single: element };
}
function resultType(def: Definition, node: Control): ValueType | undefined {
  return node.type === 'function' || node.type === 'subworkflow' ? bodyElement(def, node) : localResult(def, node);
}
export function outputType(def: Definition, workflow: Workflow | string, placement: Placement | string): ValueType | undefined {
  const w = typeof workflow === 'string' ? workflowDecl(def, workflow) : workflow;
  const p = typeof placement === 'string' ? w === undefined ? undefined : placementDecl(w, placement) : placement;
  return p === undefined ? undefined : resultType(def, p.node);
}
function inputType(def: Definition, node: Control): { known: boolean; type: ValueType | undefined } {
  switch (node.type) {
    case 'function': case 'subworkflow': return { known: bodyKnown(def, node), type: bodyInput(def, node) };
    case 'branch': { const j = judgeDecl(def, node.judge); return { known: j !== undefined, type: j?.input }; }
    case 'waitStream': case 'merge': return { known: true, type: node.element };
    case 'concurrency': return { known: true, type: node.input };
  }
}
function combineInput(w: Workflow, name: string, sources: Kind[]): { known: boolean; kind: Kind | undefined } {
  if (isEntry(w, name)) return { known: sources.length === 0, kind: 'single' };
  const first = sources[0];
  return { known: sources.every(k => k === first), kind: first };
}
function inputKind(w: Workflow, name: string, kinds: Map<string, Kind>): { known: boolean; kind: Kind | undefined } {
  const sources: Kind[] = [];
  for (const c of incoming(w, name)) { const kind = kinds.get(c.source); if (kind === undefined) return { known: false, kind: undefined }; sources.push(kind); }
  return combineInput(w, name, sources);
}
function outputKind(def: Definition, node: Control, input?: Kind): Kind | undefined {
  switch (node.type) {
    case 'function': {
      if (input === 'stream') return 'stream';
      const f = functionDecl(def, node.function);
      return f === undefined ? undefined : contractKind(f.output);
    }
    case 'subworkflow': return input === 'stream' ? 'stream' : workflowDecl(def, node.workflow) === undefined ? undefined : 'single';
    case 'branch': return input;
    case 'waitStream': return input === 'stream' ? 'single' : undefined;
    case 'merge': return input === 'single' ? 'single' : undefined;
    case 'concurrency': return input === 'stream' || node.output === 'stream' ? 'stream' : 'single';
  }
}
function workflowKinds(def: Definition, w: Workflow): Map<string, Kind> {
  const kinds = new Map<string, Kind>(), rows = new Map<string, Placement>(), pending = new Map<string, number>(), outputs = new Map<string, string[]>();
  for (const p of w.placements) if (!rows.has(p.name)) rows.set(p.name, p);
  for (const c of w.connections) {
    if (!rows.has(c.target)) continue;
    pending.set(c.target, (pending.get(c.target) ?? 0) + 1);
    const targets = outputs.get(c.source) ?? [];
    targets.push(c.target);
    outputs.set(c.source, targets);
  }
  const queue = [...rows.keys()].filter(name => !pending.has(name));
  for (let i = 0; i < queue.length; i++) {
    const name = queue[i];
    if (name === undefined) continue;
    const row = rows.get(name);
    if (row === undefined) continue;
    const input = inputKind(w, name, kinds);
    if (!input.known) continue;
    const kind = outputKind(def, row.node, input.kind);
    if (kind === undefined) continue;
    kinds.set(name, kind);
    for (const target of outputs.get(name) ?? []) {
      const remaining = (pending.get(target) ?? 0) - 1;
      pending.set(target, remaining);
      if (remaining === 0) queue.push(target);
    }
  }
  return kinds;
}
export function deriveKinds(def: Definition): Map<string, Map<string, Kind>> {
  const result = new Map<string, Map<string, Kind>>();
  for (const w of def.workflows) if (!result.has(w.id)) result.set(w.id, workflowKinds(def, w));
  return result;
}

function representable(def: Definition): void {
  const name = (s: string): void => { if (/[\uD800-\uDFFF]/u.test(s)) invalid(`the name ${JSON.stringify(s)} is not valid UTF-8`); };
  const type = (t?: ValueType): void => { if (t !== undefined) name(typeName(t)); };
  const body = (b: Body): void => { if (b.type === 'function') name(b.function); else { name(b.workflow); name(b.output); } };
  name(def.main);
  for (const f of def.functions) { name(f.id); type(f.input); type(contractType(f.output)); }
  for (const j of def.judges) { name(j.id); type(j.input); }
  for (const t of def.transforms) { name(t.id); type(t.input); type(t.output); }
  for (const w of def.workflows) {
    name(w.id);
    if (w.input !== undefined) { type(w.input.type); name(w.input.placement); }
    for (const p of w.placements) {
      name(p.name);
      const n = p.node;
      switch (n.type) {
        case 'function': case 'subworkflow': body(n); break;
        case 'branch': name(n.judge); n.arms.forEach(name); break;
        case 'merge': case 'waitStream': type(n.element); break;
        case 'concurrency':
          type(n.input); type(n.element);
          for (const t of n.tasks) { name(t.name); body(t.body); if (t.inputTransform !== undefined) name(t.inputTransform); if (t.outputTransform !== undefined) name(t.outputTransform); }
          break;
      }
    }
    for (const c of w.connections) { name(c.source); name(c.target); if (c.arm !== undefined) name(c.arm); name(c.transform); }
  }
}
function unique(names: string[]): boolean { return new Set(names).size === names.length; }
function acyclic(vertices: string[], edges: [string, string][]): boolean {
  const indegrees = new Map(vertices.map(v => [v, 0])), outputs = new Map<string, string[]>();
  for (const [source, target] of edges) {
    if (!indegrees.has(source) || !indegrees.has(target)) continue;
    indegrees.set(target, (indegrees.get(target) ?? 0) + 1);
    const targets = outputs.get(source) ?? [];
    targets.push(target); outputs.set(source, targets);
  }
  const queue = [...indegrees.keys()].filter(v => indegrees.get(v) === 0);
  for (let i = 0; i < queue.length; i++) {
    const source = queue[i];
    if (source === undefined) continue;
    for (const target of outputs.get(source) ?? []) {
      const count = (indegrees.get(target) ?? 0) - 1;
      indegrees.set(target, count);
      if (count === 0) queue.push(target);
    }
  }
  return queue.length === indegrees.size;
}
function workflowRefs(node: Control): string[] {
  if (node.type === 'subworkflow') return [node.workflow];
  if (node.type === 'concurrency') return node.tasks.flatMap(t => t.body.type === 'subworkflow' ? [t.body.workflow] : []);
  return [];
}
function validateBody(def: Definition, at: string, b: Body): ValueType | undefined {
  if (b.type === 'function') {
    const f = functionDecl(def, b.function);
    if (f === undefined) invalid(`${at}: unknown function ${b.function}`);
    return f.input;
  }
  const w = workflowDecl(def, b.workflow);
  if (w === undefined) invalid(`${at}: unknown workflow ${b.workflow}`);
  if (placementDecl(w, b.output) === undefined) invalid(`${at}: workflow ${b.workflow} has no placement ${b.output}`);
  if (!isEndpoint(w, b.output)) invalid(`${at}: ${b.output} is not an endpoint of workflow ${b.workflow}`);
  return w.input?.type;
}
function validateTypes(at: string, ...types: (ValueType | undefined)[]): void {
  for (const t of types) if (t !== undefined && typeName(t) === '') invalid(`${at}: empty type name`);
}
function validateTimeout(at: string, timeout: Timeout | undefined, contract: Contract | undefined, judge: boolean): void {
  if (timeout?.callMs === undefined && timeout?.elementMs === undefined) return;
  if (contract === undefined && !judge) invalid(`${at}: a timeout is only for a function call or a branch judge`);
  if ((timeout.callMs !== undefined && timeout.callMs <= 0n) || (timeout.elementMs !== undefined && timeout.elementMs <= 0n)) invalid(`${at}: a timeout must be positive`);
  if ((timeout.callMs !== undefined && timeout.callMs > MAX_UINT64) || (timeout.elementMs !== undefined && timeout.elementMs > MAX_UINT64)) invalid(`${at}: a timeout must be at most ${MAX_UINT64}`);
  if (timeout.elementMs !== undefined && (contract === undefined || contractKind(contract) !== 'stream')) invalid(`${at}: an element timeout is only for a Stream function`);
}
function validateTask(def: Definition, parent: string, node: Concurrency, task: TaskSpec): void {
  const at = `${parent} task ${task.name}`;
  if (task.name === '') invalid(`${at}: empty task name`);
  const input = validateBody(def, at, task.body);
  if (input === undefined) {
    if (task.inputTransform === 'discard') {
      if (node.input === undefined) invalid(`${at}: the concurrency has no input to discard`);
    } else if (task.inputTransform !== undefined || node.input !== undefined) invalid(`${at}: the body takes no input, so the input transform must be discard`);
  } else {
    const id = task.inputTransform;
    if (id === undefined) invalid(`${at}: an input transform is required`);
    if (id === 'discard') invalid(`${at}: discard passes no value, but the body takes ${typeText(input)}`);
    const t = transformDecl(def, id);
    if (t === undefined) invalid(`${at}: unknown transform ${id}`);
    if (node.input === undefined) invalid(`${at}: the concurrency has no input for the task`);
    if (!typeEqual(t.input, node.input)) invalid(`${at}: transform ${id} takes ${typeText(t.input)}, but the concurrency input is ${typeText(node.input)}`);
    if (!typeEqual(t.output, input)) invalid(`${at}: transform ${id} returns ${typeText(t.output)}, but the body takes ${typeText(input)}`);
  }
  if (task.outputTransform !== undefined) {
    const id = task.outputTransform, t = transformDecl(def, id);
    if (t === undefined) invalid(`${at}: unknown transform ${id}`);
    const element = bodyElement(def, task.body);
    if (element === undefined) invalid(`${at}: the result type cannot be derived`);
    if (!typeEqual(t.input, element)) invalid(`${at}: transform ${id} takes ${typeText(t.input)}, but the body produces ${typeText(element)}`);
    if (!typeEqual(t.output, node.element)) invalid(`${at}: transform ${id} returns ${typeText(t.output)}, but the output element is ${typeText(node.element)}`);
  }
  validateTimeout(at, task.timeout, task.body.type === 'function' ? functionDecl(def, task.body.function)?.output : undefined, false);
}
function validateConnection(def: Definition, w: Workflow, c: Connection): void {
  const at = `${w.id}: connection ${c.source} -> ${c.target}`, source = placementDecl(w, c.source), target = placementDecl(w, c.target);
  if (source === undefined) invalid(`${at}: unknown source`);
  if (target === undefined) invalid(`${at}: unknown target`);
  if (source.node.type === 'branch') {
    if (c.arm === undefined) invalid(`${at}: a connection from a branch needs an arm`);
    if (!source.node.arms.includes(c.arm)) invalid(`${at}: unknown arm ${c.arm}`);
  } else if (c.arm !== undefined) invalid(`${at}: only a connection from a branch has an arm`);
  const produced = resultType(def, source.node);
  if (produced === undefined) invalid(`${at}: the result type of ${c.source} cannot be derived`);
  const expected = inputType(def, target.node);
  if (!expected.known) invalid(`${at}: ${c.target} has an unknown reference`);
  if (c.transform === 'discard') {
    if (expected.type !== undefined) invalid(`${at}: discard passes no value, but ${c.target} takes ${typeText(expected.type)}`);
    return;
  }
  if (expected.type === undefined) invalid(`${at}: ${c.target} takes no input, so the transform must be discard`);
  const t = transformDecl(def, c.transform);
  if (t === undefined) invalid(`${at}: unknown transform ${c.transform}`);
  if (!typeEqual(t.input, produced)) invalid(`${at}: transform ${c.transform} takes ${typeText(t.input)}, but ${c.source} produces ${typeText(produced)}`);
  if (!typeEqual(t.output, expected.type)) invalid(`${at}: transform ${c.transform} returns ${typeText(t.output)}, but ${c.target} takes ${typeText(expected.type)}`);
}
function validateEntry(def: Definition, w: Workflow, entry: NonNullable<Workflow['input']>): void {
  const at = `${w.id}: entry ${entry.placement}`;
  validateTypes(at, entry.type);
  const p = placementDecl(w, entry.placement);
  if (p === undefined) invalid(`${at}: unknown placement`);
  if (p.node.type === 'merge') invalid(`${at}: Merge cannot be the entry`);
  const expected = inputType(def, p.node);
  if (!expected.known) invalid(`${at}: unknown reference`);
  if (expected.type === undefined || !typeEqual(expected.type, entry.type)) invalid(`${at}: the input type ${typeText(entry.type)} does not match the placement`);
  if (incoming(w, entry.placement).length !== 0) invalid(`${at}: the entry cannot have an input connection`);
}
function validatePlacement(def: Definition, w: Workflow, kinds: Map<string, Kind>, p: Placement): void {
  const at = `${w.id}.${p.name}`, edges = incoming(w, p.name), node = p.node;
  let expected: ValueType | undefined;
  switch (node.type) {
    case 'function': case 'subworkflow': expected = validateBody(def, at, node); break;
    case 'branch': {
      const j = judgeDecl(def, node.judge);
      if (j === undefined) invalid(`${at}: unknown judge ${node.judge}`);
      if (node.arms.length === 0 || !unique(node.arms) || node.arms.includes('')) invalid(`${at}: arms must be distinct non-empty names`);
      if (!outgoing(w, p.name).some(c => c.arm !== undefined && node.arms.includes(c.arm))) invalid(`${at}: at least one arm needs a connection`);
      expected = j.input;
      break;
    }
    case 'waitStream': validateTypes(at, node.element); expected = node.element; break;
    case 'merge':
      validateTypes(at, node.element);
      if (edges.length === 0) invalid(`${at}: Merge needs input connections`);
      expected = node.element;
      break;
    case 'concurrency':
      validateTypes(at, node.input, node.element);
      if (node.limit <= 0n) invalid(`${at}: limit must be positive`);
      if (node.limit > MAX_UINT64) invalid(`${at}: limit must be at most ${MAX_UINT64}`);
      if (node.tasks.length === 0) invalid(`${at}: concurrency needs tasks`);
      if (!unique(node.tasks.map(t => t.name))) invalid(`${at}: duplicate task name`);
      if (!node.tasks.some(t => t.outputTransform !== undefined)) invalid(`${at}: at least one task must be in the output`);
      for (const task of node.tasks) validateTask(def, at, node, task);
      expected = node.input;
      break;
  }
  if (node.type !== 'merge') {
    const count = edges.length + Number(isEntry(w, p.name));
    if (expected !== undefined && count !== 1) invalid(`${at}: needs exactly one input`);
    if (expected === undefined && count > 1) invalid(`${at}: accepts at most one connection`);
  }
  if (node.type === 'waitStream') {
    const input = inputKind(w, p.name, kinds);
    if (!input.known || input.kind !== 'stream') invalid(`${at}: waitStream needs a Stream input`);
  } else if (node.type === 'merge') {
    for (const c of edges) if (kinds.get(c.source) !== 'single') invalid(`${at}: Merge accepts only Single inputs (${c.source})`);
  }
  if (!kinds.has(p.name)) invalid(`${at}: Single/Stream cannot be derived`);
  validateTimeout(at, p.timeout, node.type === 'function' ? functionDecl(def, node.function)?.output : undefined, node.type === 'branch');
}
function validateWorkflow(def: Definition, w: Workflow, kinds: Map<string, Kind>): void {
  const at = `workflow ${w.id}`;
  if (w.id === '') invalid('empty workflow id');
  if (w.placements.length === 0) invalid(`${at}: no placements`);
  for (const p of w.placements) if (p.name === '') invalid(`${at}: empty placement name`);
  if (!unique(w.placements.map(p => p.name))) invalid(`${at}: duplicate placement name`);
  for (const c of w.connections) validateConnection(def, w, c);
  if (!acyclic(w.placements.map(p => p.name), w.connections.map(c => [c.source, c.target]))) invalid(`${at}: connections contain a cycle`);
  if (w.input !== undefined) validateEntry(def, w, w.input);
  for (const p of w.placements) validatePlacement(def, w, kinds, p);
  for (const p of w.placements) if (isEndpoint(w, p.name) && kinds.get(p.name) !== 'single') invalid(`${at}: endpoint ${p.name} must be Single`);
}
export function validateDefinition(def: Definition): void {
  checkDefinitionResources(def);
  representable(def);
  if (!unique(def.functions.map(f => f.id))) invalid('duplicate function id');
  if (!unique(def.judges.map(j => j.id))) invalid('duplicate judge id');
  if (!unique(def.transforms.map(t => t.id))) invalid('duplicate transform id');
  if (def.transforms.some(t => t.id === 'discard')) invalid('discard is provided by the library and cannot be declared');
  if (!unique(def.workflows.map(w => w.id))) invalid('duplicate workflow id');
  if (workflowDecl(def, def.main) === undefined) invalid(`unknown main workflow ${def.main}`);
  const callEdges: [string, string][] = [];
  for (const w of def.workflows) for (const p of w.placements) for (const ref of workflowRefs(p.node)) callEdges.push([w.id, ref]);
  if (!acyclic(def.workflows.map(w => w.id), callEdges)) invalid('workflows call each other in a cycle');
  for (const f of def.functions) { if (f.id === '') invalid('empty function id'); validateTypes(`function ${f.id}`, f.input, contractType(f.output)); }
  for (const j of def.judges) { if (j.id === '') invalid('empty judge id'); validateTypes(`judge ${j.id}`, j.input); }
  for (const t of def.transforms) { if (t.id === '') invalid('empty transform id'); validateTypes(`transform ${t.id}`, t.input, t.output); }
  const kinds = deriveKinds(def);
  for (const w of def.workflows) validateWorkflow(def, w, kinds.get(w.id) ?? new Map());
}
