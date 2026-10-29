import assert from 'node:assert/strict';
import { readFileSync, readdirSync, mkdtempSync, writeFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { spawnSync } from 'node:child_process';
import test from 'node:test';
import { parseDefinition } from '../dist/definition.js';
import { encodeState } from '../dist/trace.js';
import { initialState, step, stateValues, controlCandidates, Rejection } from '../dist/machine.js';
import { identity, decodeIdentity, compareStrings, listValue, keyInvocation, keyTask } from '../dist/identity.js';

const fixtureDir = new URL('../../../ui-kit/tests/fixtures/', import.meta.url);
const freeze = value => {
  if (value !== null && typeof value === 'object') {
    for (const child of Object.values(value)) freeze(child);
    Object.freeze(value);
  }
  return value;
};

function replay(text, seen = new Set()) {
  const [header, ...records] = text.slice(0, text.lastIndexOf('\n')).split('\n').map(line => JSON.parse(line));
  const definition = freeze(parseDefinition(JSON.stringify(header.definition)));
  let state = initialState();
  let pending;
  for (const record of records) {
    if (record.commit) { state = pending; pending = undefined; continue; }
    const before = structuredClone(state);
    freeze(state);
    pending = step(definition, state, record.op);
    seen.add(record.op.type);
    assert.deepEqual(state, before);
  }
  return state;
}

for (const file of readdirSync(fixtureDir).filter(file => file.endsWith('.records.jsonl'))) {
  test(`pure machine replays ${file}`, () => {
    const actual = replay(readFileSync(new URL(file, fixtureDir), 'utf8'));
    const expected = JSON.parse(readFileSync(new URL(file.replace('.records.jsonl', '.state.json'), fixtureDir), 'utf8'));
    assert.deepEqual(JSON.parse(encodeState(actual)), expected);
  });
}

test('identities count Unicode scalars, decode permissive lengths, and lists keep multiplicity', () => {
  const parts = ['', '🙂', 'é', 'a:b', '\u{10ffff}', ''];
  assert.equal(identity(...parts), '0:1:🙂1:é3:a:b1:\u{10ffff}0:');
  assert.deepEqual(decodeIdentity(identity(...parts)), parts);
  assert.deepEqual(decodeIdentity(':'), ['']);
  assert.deepEqual(decodeIdentity('0001:a'), ['a']);
  assert.equal(decodeIdentity('2:a'), undefined);
  assert.equal(decodeIdentity('999999999999999999999:a'), undefined);
  assert.equal(decodeIdentity('1:a0'), undefined);
  assert.deepEqual(['🙂', '\uffff', 'a'].sort(compareStrings), ['a', '\uffff', '🙂']);
  assert.equal(listValue(['z', 'a', 'z']), identity('list', 'a', 'z', 'z'));
});

function singleDefinition(stream = false) {
  return { main: 'main', functions: [{ id: 'f', output: stream ? { stream: 'T' } : { single: 'T' } }], judges: [], transforms: [],
    workflows: [{ id: 'main', placements: [{ name: 'p', node: { type: 'function', function: 'f' }, policy: 'continue', timeout: { callMs: 1n, elementMs: 2n } }], connections: [] }] };
}
function invoked(definition) {
  return step(definition, step(definition, initialState(), { type: 'start' }), { type: 'invoke', run: [], placement: 'p' });
}
function rejects(definition, state, op, code) {
  const snapshot = structuredClone(state);
  freeze(state);
  assert.throws(() => step(definition, state, op), error => error instanceof Rejection && error.code === code);
  assert.deepEqual(state, snapshot);
}

test('operation preconditions reject without changing prior snapshots', () => {
  const definition = singleDefinition();
  const empty = initialState();
  rejects(definition, empty, { type: 'invoke', run: [], placement: 'p' }, 'NOT_RUNNING');
  rejects(definition, empty, { type: 'cancel' }, 'NOT_STARTED');
  rejects(definition, empty, { type: 'start', input: 'unexpected' }, 'INPUT_MISMATCH');
  const state = invoked(definition);
  const call = state.calls[0].id;
  rejects(definition, state, { type: 'invoke', run: [], placement: 'p' }, 'DUPLICATE_INVOCATION');
  rejects(definition, state, { type: 'fetch', call }, 'NOT_FETCHABLE');
  rejects(definition, state, { type: 'terminated', call }, 'NOT_CANCELLING');
  rejects(definition, state, { type: 'judged', call, arm: 'x' }, 'NOT_JUDGING');
  rejects(definition, state, { type: 'conclude' }, 'NOT_SETTLED');
  rejects(definition, state, { type: 'closeRun', run: [] }, 'NOT_CLOSABLE');
  const returned = step(definition, state, { type: 'returned', call, value: 'v' });
  assert.equal(state.calls[0].status, 'running');
  rejects(definition, returned, { type: 'returned', call, value: 'late' }, 'NOT_RETURNABLE');
  rejects(definition, returned, { type: 'timedOut', call, element: false }, 'NO_TIMEOUT');
  const settled = step(definition, returned, { type: 'settle', run: [], placement: 'p' });
  rejects(definition, settled, { type: 'settle', run: [], placement: 'p' }, 'ALREADY_SETTLED');
  const done = step(definition, settled, { type: 'conclude' });
  assert.equal(done.status, 'succeeded');
  rejects(definition, done, { type: 'cancel' }, 'TERMINAL');
});

test('timeouts retain task slots until termination; cancellation preserves failures', () => {
  const definition = singleDefinition();
  definition.workflows[0].placements[0].node = { type: 'concurrency', limit: 1n, tasks: ['a', 'b'].map(name => ({
    name, body: { type: 'function', function: 'f' }, outputTransform: 't', policy: 'continue', timeout: { callMs: 1n },
  })), output: 'list', element: 'T' };
  let state = invoked(definition);
  const execution = keyInvocation([], 'p', null);
  state = step(definition, state, { type: 'beginTask', execution, task: 'a' });
  const call = keyTask(execution, 'a');
  state = step(definition, state, { type: 'timedOut', call, element: false });
  rejects(definition, state, { type: 'beginTask', execution, task: 'b' }, 'NO_SLOT');
  rejects(definition, state, { type: 'closeExecution', execution }, 'TASKS_RUNNING');
  state = step(definition, state, { type: 'terminated', call });
  state = step(definition, state, { type: 'beginTask', execution, task: 'b' });
  state = step(definition, state, { type: 'cancel' });
  rejects(definition, state, { type: 'conclude' }, 'CALLS_RUNNING');
  state = step(definition, state, { type: 'lost', call: keyTask(execution, 'b') });
  state = step(definition, state, { type: 'conclude' });
  assert.equal(state.status, 'failed');
  assert.equal(state.cancelled, true);
  assert.deepEqual(state.failures.map(f => f.cause), ['timeout']);
  assert.deepEqual(state.executions[0].tasks.map(t => t.status), ['failed', 'cancelled']);
});

test('empty streams settle normally and scheduler supplies only control operations', () => {
  const definition = singleDefinition(true);
  let state = invoked(definition);
  assert.equal(controlCandidates(definition, state)[0].type, 'fetch');
  const call = state.calls[0].id;
  state = step(definition, state, { type: 'fetch', call });
  state = step(definition, state, { type: 'ended', call });
  state = step(definition, state, { type: 'settle', run: [], placement: 'p' });
  state = step(definition, state, { type: 'conclude' });
  assert.equal(state.status, 'succeeded');
  assert.deepEqual(state.results, []);
  assert.deepEqual(stateValues(state), []);
  const controls = new Set(['invoke', 'fetch', 'deliver', 'taskInput', 'beginTask', 'taskOutput', 'settle', 'closeExecution', 'closeRun', 'conclude']);
  for (const file of readdirSync(fixtureDir).filter(file => file.endsWith('.records.jsonl'))) {
    const [header, ...records] = readFileSync(new URL(file, fixtureDir), 'utf8').trim().split('\n').map(JSON.parse);
    const def = parseDefinition(JSON.stringify(header.definition));
    let current = initialState();
    for (const record of records) if (record.op !== undefined) {
      current = step(def, current, record.op);
      const candidates = controlCandidates(def, current);
      assert.ok(candidates.every(op => controls.has(op.type)));
      assert.deepEqual(candidates, controlCandidates(def, current));
    }
  }
});

const oracle = process.env.SUIMON_GO_ORACLE;
test('Go random walks cover every operation and agree on final states', { skip: !oracle }, () => {
  const directory = mkdtempSync(join(tmpdir(), 'suimon-machine-'));
  const names = ['Test/definitions/branch.json', 'Test/definitions/merge.json', 'Test/definitions/users.json',
    'Test/definitions/chains/alternating.json', 'Test/definitions/chains/nested.json',
    'implementations/go/src/testdata/calls.json', 'implementations/go/src/testdata/fanout.json', 'implementations/go/src/testdata/limit.json'];
  const seen = new Set();
  try {
    for (const name of names) for (let seed = 1; seed <= 32; seed++) {
      const definition = new URL(`../../../${name}`, import.meta.url).pathname;
      const generated = spawnSync(oracle, ['gen', definition, '--seed', String(seed)], { encoding: 'utf8', maxBuffer: 32 * 1024 * 1024 });
      assert.equal(generated.status, 0, generated.stderr);
      const actual = replay(generated.stdout, seen);
      const trace = join(directory, 'trace.jsonl');
      writeFileSync(trace, generated.stdout);
      const checked = spawnSync(oracle, ['check', trace, '--state'], { encoding: 'utf8', maxBuffer: 32 * 1024 * 1024 });
      assert.equal(checked.status, 0, checked.stderr);
      assert.deepEqual(JSON.parse(encodeState(actual)), JSON.parse(checked.stdout), `${name} seed ${seed}`);
    }
    assert.deepEqual([...seen].sort(), ['start', 'invoke', 'fetch', 'returned', 'judged', 'yielded', 'ended', 'failed', 'timedOut',
      'lost', 'terminated', 'deliver', 'transformFailed', 'taskInput', 'taskInputFailed', 'beginTask', 'taskOutput', 'taskOutputFailed',
      'settle', 'closeExecution', 'closeRun', 'cancel', 'conclude'].sort());
  } finally { rmSync(directory, { recursive: true, force: true }); }
});
