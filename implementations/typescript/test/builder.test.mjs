import assert from 'node:assert/strict';
import test from 'node:test';
import { spawnSync } from 'node:child_process';
import { setTimeout as delay } from 'node:timers/promises';
import { DefinitionBuilder, defineType, discard } from '../dist/builder.js';
import { MemoryJournal } from '../dist/journal.js';
import { checkTrace, encodeState } from '../dist/trace.js';

const text = defineType('Text', value => {
  if (typeof value !== 'string') throw new TypeError('Expected text');
  return value;
});
const settings = { policy: 'continue' };

test('typed streams, per-input concurrency, child workflows and excluded tasks compose', async () => {
  const d = new DefinitionBuilder();
  const source = d.streamNoInput('source', text, async function* () { yield 'a'; yield 'b'; });
  const upper = d.func('upper', text, text, value => value.toUpperCase());
  const same = d.passthrough('same', text);
  const child = d.workflow('child', text);
  const childEnd = child.call('answer', upper, settings);
  child.entry(childEnd);
  let finished = 0;
  const audit = d.funcNoInput('audit', text, async () => { await delay(5); finished++; return 'ignored'; });
  const main = d.workflow('main');
  const users = main.call('source', source, settings);
  const fan = main.concurrency('fan', {
    input: text, element: text, output: 'stream', limit: 1n, ...settings,
    tasks: [d.task('child', child.body(childEnd), same, same, settings),
      d.sideTask('audit', audit, discard(text), settings)],
  });
  const done = main.waitStream('done', text, settings);
  main.connect(users, fan, same);
  main.connect(fan, done, same);
  const engine = d.build(main);
  const journal = new MemoryJournal();
  const report = await engine.run(undefined, { journal });
  assert.equal(report.status, 'succeeded');
  assert.deepEqual([...report.output(done)].sort(), ['A', 'B']);
  assert.equal(finished, 2);
  const bytes = await journal.contents(1 << 24);
  assert.equal(encodeState(checkTrace(bytes).state), encodeState(report.state));
  const resumed = await (await engine.resume(journal)).wait();
  assert.deepEqual(resumed.output(done), report.output(done));
  assert.equal(finished, 2, 'completed side effects must not run again');
  assert.deepEqual(await journal.contents(1 << 24), bytes);
});

test('branch nonselection propagates through subworkflows and Merge without fabricated outputs', async () => {
  const d = new DefinitionBuilder();
  const same = d.passthrough('same', text);
  const route = d.judge('route', text, ['take', 'skip'], () => 'skip');
  const selected = d.func('selected', text, text, () => { throw new Error('must not run'); });
  const main = d.workflow('main', text);
  const branch = main.branch('branch', route, settings);
  main.entry(branch);
  const a = main.call('a', selected, settings);
  const b = main.call('b', selected, settings);
  const done = main.merge('done', text, settings);
  main.connect(branch.arm('take'), a, same);
  main.connect(branch.arm('take'), b, same);
  main.connect(a, done, same);
  main.connect(b, done, same);
  const report = await d.build(main).run('request');
  assert.equal(report.status, 'skipped');
  assert.equal(report.endpoints.get('done'), 'skipped');
  assert.throws(() => report.output(done), /No output/);
});

test('typed no-input concurrency List and discard preserve separate value contracts', async () => {
  const d = new DefinitionBuilder();
  const one = d.funcNoInput('one', text, () => 'one');
  const two = d.streamNoInput('two', text, function* () { yield 'two'; yield 'two'; });
  const same = d.passthrough('same', text);
  const main = d.workflow('main');
  const done = main.concurrencyNoInput('done', { ...settings, element: text, output: 'list', limit: 2n,
    tasks: [d.taskNoInput('one', one, same, settings), d.taskNoInput('two', two, same, settings)] });
  const report = await d.build(main).run();
  assert.deepEqual([...report.output(done)].sort(), ['one', 'two', 'two']);
});

test('parsers reject recovered or incoming values that do not satisfy the declared type', async () => {
  const d = new DefinitionBuilder();
  const echo = d.func('echo', text, text, value => value);
  const main = d.workflow('main', text);
  const end = main.call('end', echo, settings);
  main.entry(end);
  const engine = d.build(main);
  await assert.rejects(engine.run(42), /Expected text/);
  const report = await engine.run('valid');
  assert.equal(report.output(end), 'valid');
});

test('builder rejects cross-workflow connections and references from another definition', () => {
  const d = new DefinitionBuilder();
  const fn = d.func('echo', text, text, value => value);
  const one = d.workflow('one', text);
  const two = d.workflow('two', text);
  const a = one.call('a', fn, settings);
  const b = two.call('b', fn, settings);
  assert.throws(() => one.connect(a, b, d.passthrough('same', text)), /within its workflow/);
  const other = new DefinitionBuilder();
  assert.throws(() => other.build(one), /same definition builder/);
});

test('invalid async typed transforms fail the workflow without an unhandled rejection', () => {
  const script = `
    import { DefinitionBuilder, defineType } from ${JSON.stringify(new URL('../dist/builder.js', import.meta.url).href)};
    const t = defineType('Text', value => { if (typeof value !== 'string') throw new TypeError('Expected text'); return value; });
    const d = new DefinitionBuilder();
    const source = d.funcNoInput('source', t, () => 'ok');
    const target = d.func('target', t, t, value => value);
    const bad = d.transform('bad', t, t, async () => { throw new Error('bad async transform'); });
    const w = d.workflow('main');
    const a = w.call('a', source, { policy: 'continue' });
    const b = w.call('b', target, { policy: 'continue' });
    w.connect(a, b, bad);
    const report = await d.build(w).run();
    if (report.status !== 'failed') throw new Error('Expected workflow failure');
    await new Promise(resolve => setTimeout(resolve, 10));
  `;
  const result = spawnSync(process.execPath, ['--input-type=module', '-e', script], { encoding: 'utf8' });
  assert.equal(result.status, 0, result.stderr);
});

test('typed stream cancellation drains yielding finally blocks before releasing the execution', async () => {
  const d = new DefinitionBuilder();
  let started;
  const ready = new Promise(resolve => { started = resolve; });
  let finished = false;
  const source = d.streamNoInput('source', text, async function* ({ signal }) {
    started();
    try {
      await new Promise(resolve => signal.addEventListener('abort', resolve, { once: true }));
      yield 'late';
    } finally {
      yield 'cleanup';
      finished = true;
    }
  });
  const main = d.workflow('main');
  const a = main.call('a', source, settings);
  const done = main.waitStream('done', text, settings);
  main.connect(a, done, d.passthrough('same', text));
  const execution = await d.build(main).start();
  await ready;
  execution.cancel();
  const report = await execution.wait();
  assert.equal(report.status, 'cancelled');
  assert.equal(finished, true, 'underlying generator cleanup must complete before wait resolves');
  assert.throws(() => report.output(done), /No output/);
});
