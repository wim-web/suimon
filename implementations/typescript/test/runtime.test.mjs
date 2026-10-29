import assert from 'node:assert/strict';
import test from 'node:test';
import { setImmediate as tick } from 'node:timers/promises';
import { Engine, LostError, TimeoutError } from '../dist/engine.js';
import { QuotaError } from '../dist/limits.js';
import { MemoryJournal } from '../dist/journal.js';
import { checkTrace, encodeHeader, encodeRecord, encodeState } from '../dist/trace.js';

function deferred() {
  let resolve;
  const promise = new Promise(r => { resolve = r; });
  return { promise, resolve };
}
async function eventually(predicate) {
  for (let i = 0; i < 1000; i++) { if (predicate()) return; await tick(); }
  assert.fail('expected event did not occur');
}
function single(options = {}) {
  return {
    main: 'main', functions: [{ id: 'f', output: { single: 'N' } }], judges: [], transforms: [],
    workflows: [{ id: 'main', placements: [{ name: 'f', node: { type: 'function', function: 'f' }, policy: 'continue', ...options }], connections: [] }],
  };
}
function streamFlow() {
  return {
    main: 'main',
    functions: [{ id: 'source', output: { stream: 'N' } }, { id: 'sink', input: 'N', output: { single: 'N' } }],
    judges: [], transforms: [{ id: 'id', input: 'N', output: 'N' }],
    workflows: [{ id: 'main', placements: [
      { name: 'source', node: { type: 'function', function: 'source' }, policy: 'continue' },
      { name: 'sink', node: { type: 'function', function: 'sink' }, policy: 'continue' },
      { name: 'all', node: { type: 'waitStream', element: 'N' }, policy: 'continue' },
    ], connections: [
      { source: 'source', target: 'sink', transform: 'id' },
      { source: 'sink', target: 'all', transform: 'id' },
    ] }],
  };
}
function concurrency(limit = 1n) {
  return {
    main: 'main', functions: [{ id: 'a', output: { single: 'N' } }, { id: 'b', output: { single: 'N' } }], judges: [], transforms: [{ id: 'id', input: 'N', output: 'N' }],
    workflows: [{ id: 'main', placements: [{ name: 'tasks', policy: 'continue', node: {
      type: 'concurrency', limit, output: 'list', element: 'N', tasks: [
        { name: 'a', body: { type: 'function', function: 'a' }, policy: 'continue', outputTransform: 'id', timeout: { callMs: 10n } },
        { name: 'b', body: { type: 'function', function: 'b' }, policy: 'continue', outputTransform: 'id' },
      ],
    } }], connections: [] }],
  };
}
const identity = { kind: 'transform', id: 'id', run: input => input };
const binding = run => ({ kind: 'single', id: 'f', input: false, run });
async function replay(journal, definition, report) {
  const trace = checkTrace(await journal.contents(1 << 24), definition);
  assert.equal(encodeState(trace.state), encodeState(report.state));
  return trace;
}
class BarrierJournal extends MemoryJournal {
  block;
  reached = deferred();
  release = deferred();
  lastType;
  async append(bytes) {
    const records = new TextDecoder().decode(bytes).trim().split('\n').map(line => JSON.parse(line));
    this.lastType = records.findLast(record => record.op)?.op.type;
    await super.append(bytes);
  }
  async sync() {
    if (this.lastType === this.block) {
      this.reached.resolve();
      await this.release.promise;
      this.block = undefined;
    }
    await super.sync();
  }
}

test('single values round trip through JSON and completed recovery changes no bytes', async () => {
  const definition = single();
  const original = { n: 4 };
  let calls = 0;
  const engine = new Engine(definition, [binding(() => { calls++; return original; })]);
  const journal = new MemoryJournal();
  const report = await engine.run(undefined, { journal });
  original.n = 9;
  assert.deepEqual(report.outputs.get('f'), { n: 4 });
  assert.equal(report.status, 'succeeded');
  await replay(journal, definition, report);
  const before = await journal.contents(1 << 20);
  const restored = await (await engine.resume(journal)).wait();
  assert.equal(restored.status, 'succeeded');
  assert.equal(calls, 1);
  assert.deepEqual(await journal.contents(1 << 20), before);
});

test('bindings and definition are snapshotted; undeclared unused functions need no binding', async () => {
  const definition = single();
  definition.functions.push({ id: 'unused', output: { single: 'N' } });
  const implementation = binding(() => 3);
  const engine = new Engine(definition, [implementation]);
  definition.workflows[0].placements[0].node.function = 'unused';
  implementation.run = () => 99;
  assert.equal((await engine.run()).outputs.get('f'), 3);
  assert.throws(() => new Engine(single(), [binding(() => 1), binding(() => 2)]), /bound twice/);
  assert.throws(() => new Engine(single(), [{ kind: 'stream', id: 'f', input: false, run: () => [] }]), /declared as/);
});

for (const validate of [true, false]) {
  test(`engine rejects unpaired surrogates before recording a definition (validate=${validate})`, () => {
    const definition = single({ name: 'p\ud800' });
    assert.throws(() => new Engine(definition, [binding(() => 7)], { validate }), {
      name: 'ValidationError', message: 'the name "p\\ud800" is not valid UTF-8',
    });
  });

  test(`engine preserves astral placement names in outputs and journals (validate=${validate})`, async () => {
    const definition = single({ name: 'p😀' });
    const journal = new MemoryJournal();
    const report = await new Engine(definition, [binding(() => 7)], { validate }).run(undefined, { journal });
    assert.equal(report.status, 'succeeded');
    assert.deepEqual([...report.outputs], [['p😀', 7]]);
    const trace = await replay(journal, definition, report);
    assert.deepEqual(trace.definition, definition);
    assert.equal(trace.validated, validate);
  });
}

test('start, callback invocation, and final report wait for journal sync', { timeout: 5000 }, async () => {
  for (const block of ['start', 'invoke', 'conclude']) {
    const journal = new BarrierJournal(); journal.block = block;
    let called = false;
    let finished = false;
    const engine = new Engine(single(), [binding(() => { called = true; return 7; })]);
    const waiting = engine.run(undefined, { journal }).then(report => { finished = true; return report; });
    await journal.reached.promise;
    assert.equal(finished, false);
    if (block !== 'conclude') assert.equal(called, false);
    journal.release.resolve();
    assert.equal((await waiting).outputs.get('f'), 7);
  }
});

test('cancellation is durable before abort and waits for actual function exit', { timeout: 5000 }, async () => {
  const entered = deferred(), aborted = deferred(), exit = deferred();
  const journal = new BarrierJournal();
  const engine = new Engine(single(), [binding(async (_input, { signal }) => {
    entered.resolve();
    signal.addEventListener('abort', () => aborted.resolve(), { once: true });
    await aborted.promise;
    await exit.promise;
    return 8;
  })]);
  const execution = await engine.start(undefined, { journal });
  await entered.promise;
  journal.block = 'cancel';
  execution.cancel(); execution.cancel();
  await journal.reached.promise;
  let wasAborted = false; void aborted.promise.then(() => { wasAborted = true; });
  await tick(); assert.equal(wasAborted, false);
  journal.release.resolve();
  await aborted.promise;
  let finished = false; void execution.wait().then(() => { finished = true; });
  await tick(); assert.equal(finished, false);
  exit.resolve();
  const report = await execution.wait();
  assert.equal(report.status, 'cancelled');
  assert.equal(report.outputs.size, 0);
  const trace = await replay(journal, single(), report);
  assert.equal(trace.state.calls[0].status, 'cancelled');
});

test('external AbortSignal is forwarded through durable cancellation', { timeout: 5000 }, async () => {
  const entered = deferred(), aborted = deferred();
  const source = new AbortController();
  const journal = new BarrierJournal(); journal.block = 'cancel';
  let callbackSignal;
  const execution = await new Engine(single(), [binding(async (_input, { signal }) => {
    callbackSignal = signal;
    entered.resolve();
    await new Promise(resolve => signal.addEventListener('abort', resolve, { once: true }));
    aborted.resolve();
    return null;
  })]).start(undefined, { journal, signal: source.signal });
  await entered.promise;
  source.abort();
  await journal.reached.promise;
  assert.equal(callbackSignal.aborted, false);
  journal.release.resolve();
  await aborted.promise;
  assert.equal((await execution.wait()).status, 'cancelled');
});

test('timeout retains a concurrency slot until user code has exited', { timeout: 5000 }, async () => {
  const definition = concurrency();
  const abort = deferred(), exit = deferred();
  let second = false;
  const journal = new MemoryJournal();
  const engine = new Engine(definition, [
    { kind: 'single', id: 'a', input: false, run: async (_input, { signal }) => {
      await new Promise(resolve => signal.addEventListener('abort', resolve, { once: true }));
      abort.resolve(); await exit.promise; return 1;
    } },
    { kind: 'single', id: 'b', input: false, run: () => { second = true; return 2; } }, identity,
  ]);
  const execution = await engine.start(undefined, { journal });
  await abort.promise; await tick();
  assert.equal(second, false);
  exit.resolve();
  const report = await execution.wait();
  assert.equal(second, true);
  assert.equal(report.failures[0].cause, 'timeout');
  assert.ok(report.failures[0].error instanceof TimeoutError);
  assert.deepEqual(report.outputs.get('tasks'), [2]);
  await replay(journal, definition, report);
});

test('stream pulls are sequential and advance while downstream calls are blocked', { timeout: 5000 }, async () => {
  const definition = streamFlow();
  const unblock = deferred();
  let producing = false, produced = 0, consumed = 0, sourceDone = false;
  const engine = new Engine(definition, [
    { kind: 'stream', id: 'source', input: false, run: () => ({
      [Symbol.asyncIterator]() { return this; },
      async next() {
        assert.equal(producing, false); producing = true;
        await tick(); producing = false;
        if (produced === 3) { sourceDone = true; return { done: true }; }
        return { done: false, value: ++produced };
      },
    }) },
    { kind: 'single', id: 'sink', input: true, run: async input => { consumed++; await unblock.promise; return input * 2; } }, identity,
  ]);
  const journal = new MemoryJournal();
  const execution = await engine.start(undefined, { journal });
  await eventually(() => sourceDone && consumed === 3);
  unblock.resolve();
  const report = await execution.wait();
  assert.deepEqual(report.outputs.get('all'), [2, 4, 6]);
  await replay(journal, definition, report);
});

test('stream cancellation waits for pending next and finally without concurrent pulls', { timeout: 5000 }, async () => {
  const definition = streamFlow();
  const nextEntered = deferred(), abort = deferred(), nextExit = deferred(), cleanupEntered = deferred(), cleanupExit = deferred();
  let downstream = 0;
  const engine = new Engine(definition, [
    { kind: 'stream', id: 'source', input: false, run: async function* (_input, { signal }) {
      try {
        signal.addEventListener('abort', () => abort.resolve(), { once: true });
        nextEntered.resolve(); await nextExit.promise; yield 99;
      } finally { cleanupEntered.resolve(); await cleanupExit.promise; }
    } },
    { kind: 'single', id: 'sink', input: true, run: input => { downstream++; return input; } }, identity,
  ]);
  const execution = await engine.start(); await nextEntered.promise;
  execution.cancel(); await abort.promise;
  let finished = false; void execution.wait().then(() => { finished = true; });
  await tick(); assert.equal(finished, false);
  nextExit.resolve(); await cleanupEntered.promise;
  await tick(); assert.equal(finished, false);
  cleanupExit.resolve();
  assert.equal((await execution.wait()).status, 'cancelled');
  assert.equal(downstream, 0);
});

test('full uint64 timeouts do not overflow into immediate Node timers', { timeout: 5000 }, async () => {
  const definition = single({ timeout: { callMs: 18_446_744_073_709_551_615n } });
  const report = await new Engine(definition, [binding(async () => { await new Promise(resolve => setTimeout(resolve, 15)); return 12; })]).run();
  assert.equal(report.status, 'succeeded');
  assert.equal(report.failures.length, 0);
});

test('user failures resolve a report with the original error; non-JSON output fails the call', async () => {
  const failure = new Error('callback failed');
  const report = await new Engine(single(), [binding(() => { throw failure; })]).run();
  assert.equal(report.status, 'failed');
  assert.equal(report.failures[0].error, failure);
  const cyclic = {}; cyclic.self = cyclic;
  const invalid = await new Engine(single(), [binding(() => cyclic)]).run();
  assert.equal(invalid.status, 'failed');
  assert.ok(invalid.failures[0].error instanceof TypeError);
});

test('recovery records lost calls before new work, keeps the header, and never retries callbacks', { timeout: 5000 }, async () => {
  const definition = single();
  const entered = deferred();
  let calls = 0;
  const bindings = [binding(async (_input, { signal }) => {
    calls++; entered.resolve();
    await new Promise(resolve => signal.addEventListener('abort', resolve, { once: true }));
    return 0;
  })];
  const journal = new MemoryJournal();
  const original = await new Engine(definition, bindings, { validate: false }).start(undefined, { journal });
  await entered.promise;
  const crash = await journal.contents(1 << 20);
  original.cancel(); await original.wait();
  const recoveredJournal = new MemoryJournal(Buffer.concat([crash, Buffer.from('{"seq":999')]));
  const recovered = await (await new Engine(definition, bindings).resume(recoveredJournal)).wait();
  assert.equal(calls, 1);
  assert.equal(recovered.failures[0].cause, 'lost');
  assert.ok(recovered.failures[0].error instanceof LostError);
  const bytes = await recoveredJournal.contents(1 << 20);
  assert.deepEqual(bytes.subarray(0, crash.indexOf(10) + 1), crash.subarray(0, crash.indexOf(10) + 1));
  await replay(recoveredJournal, definition, recovered);
  const again = await (await new Engine(definition, bindings).resume(recoveredJournal)).wait();
  assert.equal(again.failures[0].error, undefined);
});

test('restored limits are checked before truncating a crash tail', { timeout: 5000 }, async () => {
  const definition = single();
  const entered = deferred();
  const journal = new MemoryJournal();
  const execution = await new Engine(definition, [binding(async (_input, { signal }) => {
    entered.resolve(); await new Promise(resolve => signal.addEventListener('abort', resolve, { once: true })); return null;
  })]).start(undefined, { journal });
  await entered.promise;
  const crash = Buffer.concat([await journal.contents(1 << 20), Buffer.from('{')]);
  execution.cancel(); await execution.wait();
  const recovery = new MemoryJournal(crash);
  await assert.rejects(new Engine(definition, [binding(() => 1)], { limits: { maxRecords: 4 } }).resume(recovery), QuotaError);
  assert.deepEqual(await recovery.contents(1 << 20), new Uint8Array(crash));
});

test('host quotas retain a terminal replayable report within the configured budgets', { timeout: 5000 }, async () => {
  for (const limits of [{ maxRecords: 8 }, { maxPayloadBytes: 2 }]) {
    const definition = single();
    const journal = new MemoryJournal();
    const engine = new Engine(definition, [binding(() => 'larger than budget')], { limits });
    const execution = await engine.start(undefined, { journal });
    let error;
    try { await execution.wait(); } catch (caught) { error = caught; }
    assert.ok(error instanceof QuotaError);
    assert.equal(error.report.status, 'cancelled');
    const trace = await replay(journal, definition, error.report);
    if (limits.maxRecords) assert.ok(trace.committed * 2 <= limits.maxRecords);
    if (limits.maxPayloadBytes) assert.ok(trace.values.reduce((n, v) => n + Buffer.byteLength(v.payload), 0) <= limits.maxPayloadBytes);
  }
});

test('element, active-call, and duration quotas cooperatively stop producers', { timeout: 5000 }, async () => {
  for (const limits of [{ maxElements: 2 }, { maxActiveCalls: 1 }, { maxDurationMs: 10 }]) {
    const definition = streamFlow();
    let sourceExited = false, active = 0;
    const engine = new Engine(definition, [
      { kind: 'stream', id: 'source', input: false, run: async function* (_input, { signal }) {
        try { for (let i = 0; !signal.aborted; i++) { await tick(); yield i; } }
        finally { sourceExited = true; }
      } },
      { kind: 'single', id: 'sink', input: true, run: async (input, { signal }) => {
        active++;
        await new Promise(resolve => signal.addEventListener('abort', resolve, { once: true }));
        active--; return input;
      } }, identity,
    ], { limits });
    const journal = new MemoryJournal();
    let error; try { await engine.run(undefined, { journal }); } catch (caught) { error = caught; }
    assert.ok(error instanceof QuotaError);
    assert.equal(error.report.status, 'cancelled');
    assert.equal(sourceExited, true); assert.equal(active, 0);
    await replay(journal, definition, error.report);
  }
});

test('workflow quota includes cancellation cleanup and is released after wait', { timeout: 5000 }, async () => {
  const entered = deferred(), aborted = deferred(), exit = deferred();
  const engine = new Engine(single(), [binding(async (_input, { signal }) => {
    entered.resolve();
    await new Promise(resolve => signal.addEventListener('abort', resolve, { once: true }));
    aborted.resolve(); await exit.promise; return 1;
  })], { limits: { maxWorkflows: 1 } });
  const execution = await engine.start(); await entered.promise;
  execution.cancel(); await aborted.promise;
  await assert.rejects(engine.start(), QuotaError);
  exit.resolve(); await execution.wait();
  const next = await engine.start(); next.cancel(); await next.wait();
});

test('storage errors reject without a report after live callback cleanup', { timeout: 5000 }, async () => {
  const entered = deferred(), aborted = deferred(), exit = deferred();
  const error = new Error('storage unavailable');
  const journal = new BarrierJournal();
  const originalSync = journal.sync.bind(journal);
  journal.sync = async () => { if (journal.lastType === 'cancel') throw error; await originalSync(); };
  const execution = await new Engine(single(), [binding(async (_input, { signal }) => {
    entered.resolve();
    await new Promise(resolve => signal.addEventListener('abort', resolve, { once: true }));
    aborted.resolve(); await exit.promise; return 9;
  })]).start(undefined, { journal });
  await entered.promise; execution.cancel(); await aborted.promise;
  let rejected = false; void execution.wait().catch(() => { rejected = true; });
  await tick(); assert.equal(rejected, false);
  exit.resolve();
  await assert.rejects(execution.wait(), caught => caught === error && !('report' in caught));
});

test('element timeout ignores late values and waits for iterator cleanup', { timeout: 5000 }, async () => {
  const definition = streamFlow();
  definition.workflows[0].placements[0].timeout = { elementMs: 10n };
  const aborted = deferred(), nextExit = deferred(), cleanup = deferred();
  let sinkCalls = 0;
  const execution = await new Engine(definition, [
    { kind: 'stream', id: 'source', input: false, run: async function* (_input, { signal }) {
      try {
        signal.addEventListener('abort', () => aborted.resolve(), { once: true });
        await nextExit.promise;
        yield 42;
      } finally { await cleanup.promise; }
    } },
    { kind: 'single', id: 'sink', input: true, run: input => { sinkCalls++; return input; } }, identity,
  ]).start();
  await aborted.promise;
  let finished = false; void execution.wait().then(() => { finished = true; });
  nextExit.resolve(); await tick();
  assert.equal(finished, false);
  cleanup.resolve();
  const report = await execution.wait();
  assert.equal(sinkCalls, 0);
  assert.equal(report.failures[0].cause, 'timeout');
  assert.equal(report.state.calls[0].yields, 0);
});

test('only the currently pending fetch can time out', { timeout: 5000 }, async () => {
  const definition = streamFlow();
  definition.workflows[0].placements[0].timeout = { elementMs: 100n };
  const report = await new Engine(definition, [
    { kind: 'stream', id: 'source', input: false, run: async function* () {
      for (let index = 0; index < 5; index++) { await new Promise(resolve => setTimeout(resolve, 30)); yield index; }
    } },
    { kind: 'single', id: 'sink', input: true, run: input => input }, identity,
  ]).run();
  assert.equal(report.status, 'succeeded');
  assert.equal(report.failures.length, 0);
  assert.equal(report.outputs.get('all').length, 5);
});

test('transform errors and asynchronous transform misuse become workflow failures', async () => {
  for (const transform of [() => { throw new Error('transform failed'); }, () => Promise.reject(new Error('must not be awaited'))]) {
    const definition = streamFlow();
    let transformed = 0;
    const report = await new Engine(definition, [
      { kind: 'stream', id: 'source', input: false, run: () => [1] },
      { kind: 'single', id: 'sink', input: true, run: input => input },
      { kind: 'transform', id: 'id', run: input => { transformed++; return transform(input); } },
    ]).run();
    assert.equal(report.status, 'failed');
    assert.equal(report.failures[0].cause, 'transform');
    assert.equal(transformed, 1);
    await tick();
  }
});

test('string iterables are accepted as streams and synchronous generators close on quota', async () => {
  const definition = streamFlow();
  const journal = new MemoryJournal();
  const report = await new Engine(definition, [
    { kind: 'stream', id: 'source', input: false, run: () => 'abc' },
    { kind: 'single', id: 'sink', input: true, run: input => input }, identity,
  ]).run(undefined, { journal });
  assert.deepEqual(report.outputs.get('all'), ['a', 'b', 'c']);
  await replay(journal, definition, report);
  let exited = false;
  const engine = new Engine(definition, [
    { kind: 'stream', id: 'source', input: false, run: function* () { try { while (true) yield 1; } finally { exited = true; } } },
    { kind: 'single', id: 'sink', input: true, run: input => input }, identity,
  ], { limits: { maxElements: 2 } });
  await assert.rejects(engine.run(), QuotaError);
  assert.equal(exited, true);
});

test('task and execution limits reject growth while preserving shutdown capacity', async () => {
  for (const limits of [{ maxTasks: 1 }, { maxExecutions: 1 }]) {
    const definition = concurrency();
    if (limits.maxExecutions) {
      definition.workflows[0].placements.push({ ...structuredClone(definition.workflows[0].placements[0]), name: 'more' });
    }
    const journal = new MemoryJournal();
    let error;
    try {
      await new Engine(definition, [
        { kind: 'single', id: 'a', input: false, run: () => 1 },
        { kind: 'single', id: 'b', input: false, run: () => 2 }, identity,
      ], { limits }).run(undefined, { journal });
    } catch (caught) { error = caught; }
    assert.ok(error instanceof QuotaError);
    assert.equal(error.report.status, 'cancelled');
    await replay(journal, definition, error.report);
  }
});

test('oversized record lines trigger quota shutdown without corrupting the journal', async () => {
  const definition = single();
  const journal = new MemoryJournal();
  let error;
  try { await new Engine(definition, [binding(() => 'x'.repeat(1 << 20))]).run(undefined, { journal }); }
  catch (caught) { error = caught; }
  assert.ok(error instanceof QuotaError);
  assert.equal(error.report.status, 'cancelled');
  await replay(journal, definition, error.report);
});

test('required workflow input distinguishes undefined from JSON null', async () => {
  const definition = single();
  definition.functions[0].input = 'N';
  definition.workflows[0].input = { type: 'N', placement: 'f' };
  const engine = new Engine(definition, [{ kind: 'single', id: 'f', input: true, run: input => input }]);
  await assert.rejects(engine.start(), /requires an input/);
  assert.equal((await engine.run(null)).outputs.get('f'), null);
});

test('recovery loses calls in creation order and stops before starting untouched placements', async () => {
  const definition = single({ policy: 'stop' });
  definition.functions.push({ id: 'g', output: { single: 'N' } }, { id: 'h', output: { single: 'N' } });
  definition.workflows[0].placements.push(
    { name: 'g', node: { type: 'function', function: 'g' }, policy: 'continue' },
    { name: 'h', node: { type: 'function', function: 'h' }, policy: 'continue' },
  );
  const ops = [{ type: 'start' }, { type: 'invoke', run: [], placement: 'f' }, { type: 'invoke', run: [], placement: 'g' }];
  const lines = [encodeHeader(definition, true)];
  ops.forEach((op, index) => lines.push(encodeRecord({ seq: index * 2 + 1, op, values: [] }), encodeRecord({ seq: index * 2 + 2, commit: true })));
  const journal = new MemoryJournal(lines.join('\n') + '\n');
  let calls = 0;
  const engine = new Engine(definition, ['f', 'g', 'h'].map(id => ({ kind: 'single', id, input: false, run: () => { calls++; return 1; } })));
  const report = await (await engine.resume(journal)).wait();
  assert.equal(calls, 0);
  assert.equal(report.status, 'failed');
  assert.deepEqual(report.state.calls.map(call => call.status), ['lost', 'cancelled']);
  assert.deepEqual(report.failures.map(failure => failure.placement), ['f']);
  await replay(journal, definition, report);
});

test('streams fall back to sync iteration when the async method is null or undefined', async () => {
  for (const absent of [undefined, null]) {
    const sequence = { [Symbol.asyncIterator]: absent, *[Symbol.iterator]() { yield 1; yield 2; } };
    const engine = new Engine(streamFlow(), [
      { kind: 'stream', id: 'source', input: false, run: () => sequence },
      { kind: 'single', id: 'sink', input: true, run: input => input }, identity,
    ]);
    const report = await engine.run();
    assert.equal(report.status, 'succeeded');
    assert.deepEqual([...report.outputs.get('all')].sort(), [1, 2]);
  }
});
