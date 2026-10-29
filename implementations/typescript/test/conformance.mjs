import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdtempSync, readFileSync, readdirSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import test, { after } from 'node:test';
import { parseDefinition, validateDefinition, encodeDefinition } from '../dist/definition.js';
import { Engine } from '../dist/engine.js';
import { MemoryJournal } from '../dist/journal.js';
import { checkTrace, encodeState } from '../dist/trace.js';

const root = fileURLToPath(new URL('../../../', import.meta.url));
const temp = mkdtempSync(join(tmpdir(), 'suimon-ts-conformance-'));
after(() => rmSync(temp, { recursive: true, force: true }));
const go = process.env.SUIMON_GO_CLI ?? join(temp, 'suimon-go');
if (!process.env.SUIMON_GO_CLI) execFileSync('go', ['build', '-o', go, './cmd/suimon'], { cwd: join(root, 'implementations/go') });
const oracles = [go, ...(process.env.SUIMON_LEAN_CLI ? [process.env.SUIMON_LEAN_CLI] : [])];
const invoke = (oracle, ...args) => execFileSync(oracle, args, { encoding: 'utf8', maxBuffer: 32 * 1024 * 1024 }).trimEnd();
const definitions = ['Test/definitions', 'implementations/go/src/testdata', 'implementations/go/example/definitions'].flatMap(directory =>
  readdirSync(join(root, directory), { recursive: true }).filter(name => name.endsWith('.json')).map(name => join(root, directory, name)));

for (const file of definitions) test(`definition and generated traces agree: ${file.slice(root.length)}`, () => {
  const def = parseDefinition(readFileSync(file));
  validateDefinition(def);
  const canonical = join(temp, 'definition.json');
  writeFileSync(canonical, encodeDefinition(def));
  for (const oracle of oracles) invoke(oracle, 'validate', canonical);
  for (const seed of [0, 1, 7, 42, 314]) {
    const trace = invoke(go, 'gen', file, '--seed', String(seed)) + '\n';
    const traceFile = join(temp, 'generated.jsonl');
    writeFileSync(traceFile, trace);
    const actual = encodeState(checkTrace(trace).state);
    for (const oracle of oracles) assert.equal(actual, invoke(oracle, 'check', traceFile, '--state'), `seed ${seed}`);
  }
});

const fixtureDir = join(root, 'ui-kit/tests/fixtures');
for (const file of readdirSync(fixtureDir).filter(name => name.endsWith('.records.jsonl'))) test(`existing trace fixture: ${file}`, () => {
  const bytes = readFileSync(join(fixtureDir, file));
  const actual = encodeState(checkTrace(bytes).state);
  assert.equal(actual, readFileSync(join(fixtureDir, file.replace('.records.jsonl', '.state.json')), 'utf8').trimEnd());
  for (const oracle of oracles) assert.equal(actual, invoke(oracle, 'check', join(fixtureDir, file), '--state'));
});

function bind(def) {
  return [
    ...def.functions.map(fn => 'stream' in fn.output
      ? { id: fn.id, kind: 'stream', input: fn.input !== undefined, async *run(input) { const value = input ?? `${fn.id}:🦀`; yield value; yield value; } }
      : { id: fn.id, kind: 'single', input: fn.input !== undefined, run: input => input ?? `${fn.id}:🦀` }),
    ...def.judges.map(judge => ({ id: judge.id, kind: 'judge', run() {
      const placement = def.workflows.flatMap(flow => flow.placements).find(p => p.node.type === 'branch' && p.node.judge === judge.id);
      return placement.node.arms[0];
    } })),
    ...def.transforms.map(transform => ({ id: transform.id, kind: 'transform', run: input => input })),
  ];
}
for (const file of definitions) test(`real TS execution and recovery checked by oracles: ${file.slice(root.length)}`, async () => {
  const def = parseDefinition(readFileSync(file));
  const engine = new Engine(def, bind(def));
  const main = def.workflows.find(flow => flow.id === def.main);
  const journal = new MemoryJournal();
  const report = await engine.run(main.input ? 'request' : undefined, { journal });
  assert.equal(report.status, 'succeeded');
  const bytes = await journal.contents(32 * 1024 * 1024);
  const traceFile = join(temp, 'runtime.jsonl');
  writeFileSync(traceFile, bytes);
  for (const oracle of oracles) assert.equal(encodeState(report.state), invoke(oracle, 'check', traceFile, '--state'));
  const lines = Buffer.from(bytes).toString('utf8').split('\n');
  const invocation = lines.findIndex(line => line.includes('"type":"invoke"'));
  if (invocation < 0) return;
  const cut = lines.slice(0, invocation + 2).join('\n') + '\n';
  const recoveredJournal = new MemoryJournal(cut);
  const recovered = await (await engine.resume(recoveredJournal)).wait();
  const recoveredBytes = await recoveredJournal.contents(32 * 1024 * 1024);
  writeFileSync(traceFile, recoveredBytes);
  for (const oracle of oracles) assert.equal(encodeState(recovered.state), invoke(oracle, 'check', traceFile, '--state'));
  assert.deepEqual(Buffer.from(recoveredBytes.subarray(0, Buffer.byteLength(cut))), Buffer.from(cut));
});
