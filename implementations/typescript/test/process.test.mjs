import assert from 'node:assert/strict';
import { spawn } from 'node:child_process';
import { once } from 'node:events';
import { appendFileSync, closeSync, fsyncSync, ftruncateSync, mkdtempSync, openSync, readFileSync, rmSync, statSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import test from 'node:test';
import { Engine } from '../dist/engine.js';
import { checkTrace, encodeState } from '../dist/trace.js';

const definition = {
  main: 'main', functions: [{ id: 'source', output: { single: 'Text' } }, { id: 'waiting', input: 'Text', output: { single: 'Text' } }],
  judges: [], transforms: [{ id: 'same', input: 'Text', output: 'Text' }],
  workflows: [{ id: 'main', placements: [
    { name: 'source', node: { type: 'function', function: 'source' }, policy: 'continue' },
    { name: 'waiting', node: { type: 'function', function: 'waiting' }, policy: 'continue' },
  ], connections: [{ source: 'source', target: 'waiting', transform: 'same' }] }],
};

class DiskJournal {
  constructor(path) { this.path = path; }
  async append(bytes) { appendFileSync(this.path, bytes); }
  async sync() {
    const fd = openSync(this.path, 'r+');
    try { fsyncSync(fd); } finally { closeSync(fd); }
  }
  async contents(maxBytes) {
    if (statSync(this.path).size > maxBytes) throw new Error('Journal exceeds byte budget');
    return readFileSync(this.path);
  }
  async truncate(size) {
    const fd = openSync(this.path, 'r+');
    try { ftruncateSync(fd, size); fsyncSync(fd); } finally { closeSync(fd); }
  }
}

test('a killed Node process resumes durable results without repeating completed or running calls', { timeout: 10_000 }, async t => {
  const temp = mkdtempSync(join(tmpdir(), 'suimon-process-'));
  const path = join(temp, 'execution.jsonl');
  const effects = join(temp, 'effects');
  writeFileSync(path, '', { mode: 0o600 });
  const script = `
    import { appendFileSync, openSync, closeSync, fsyncSync } from 'node:fs';
    import { Engine } from ${JSON.stringify(new URL('../dist/engine.js', import.meta.url).href)};
    const path = ${JSON.stringify(path)};
    const journal = {
      async append(bytes) { appendFileSync(path, bytes); },
      async sync() { const fd = openSync(path, 'r+'); try { fsyncSync(fd); } finally { closeSync(fd); } },
    };
    await new Engine(${JSON.stringify(definition)}, [
      { kind: 'single', id: 'source', input: false, run() { appendFileSync(${JSON.stringify(effects)}, 'completed\\n'); return 'saved'; } },
      { kind: 'single', id: 'waiting', input: true, run() { process.stdout.write('running\\n'); return new Promise(() => {}); } },
      { kind: 'transform', id: 'same', run: value => value },
    ]).run(undefined, { journal });
  `;
  const child = spawn(process.execPath, ['--input-type=module', '-e', script], { stdio: ['ignore', 'pipe', 'pipe'] });
  let stderr = '';
  child.stderr.on('data', chunk => { stderr += chunk; });
  t.after(() => { child.kill('SIGKILL'); rmSync(temp, { recursive: true, force: true }); });
  await new Promise((resolve, reject) => {
    let stdout = '';
    child.stdout.on('data', chunk => { stdout += chunk; if (stdout.includes('running\n')) resolve(); });
    child.once('error', reject);
    child.once('exit', () => reject(new Error(`Child exited before readiness: ${stderr}`)));
  });
  const exited = once(child, 'exit');
  child.kill('SIGKILL');
  const [, signal] = await exited;
  assert.equal(signal, 'SIGKILL');
  const prefix = readFileSync(path);
  appendFileSync(path, '{"seq":');
  let calls = 0;
  const bindings = [
    { kind: 'single', id: 'source', input: false, run() { calls++; return 'repeated'; } },
    { kind: 'single', id: 'waiting', input: true, run() { calls++; return 'repeated'; } },
    { kind: 'transform', id: 'same', run: value => value },
  ];
  const journal = new DiskJournal(path);
  const report = await (await new Engine(definition, bindings).resume(journal)).wait();
  assert.equal(calls, 0);
  assert.equal(readFileSync(effects, 'utf8'), 'completed\n');
  assert.equal(report.status, 'failed');
  assert.deepEqual(report.failures.map(failure => failure.cause), ['lost']);
  const final = readFileSync(path);
  assert.deepEqual(final.subarray(0, prefix.byteLength), prefix);
  assert.equal(encodeState(checkTrace(final).state), encodeState(report.state));
});
