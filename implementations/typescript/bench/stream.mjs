import assert from 'node:assert/strict';
import { Engine } from '../dist/index.js';

const count = Number(process.argv[2] ?? 1000);
assert.ok(Number.isSafeInteger(count) && count >= 0, 'element count must be a nonnegative safe integer');
const definition = {
  main: 'main',
  functions: [{ id: 'source', output: { stream: 'N' } }, { id: 'sink', input: 'N', output: { single: 'N' } }],
  judges: [],
  transforms: [{ id: 'id', input: 'N', output: 'N' }],
  workflows: [{ id: 'main', placements: [
    { name: 'source', node: { type: 'function', function: 'source' }, policy: 'continue' },
    { name: 'sink', node: { type: 'function', function: 'sink' }, policy: 'continue' },
    { name: 'all', node: { type: 'waitStream', element: 'N' }, policy: 'continue' },
  ], connections: [
    { source: 'source', target: 'sink', transform: 'id' },
    { source: 'sink', target: 'all', transform: 'id' },
  ] }],
};
let sinkCalls = 0;
let transformCalls = 0;
const engine = new Engine(definition, [
  { kind: 'stream', id: 'source', input: false, *run() { for (let i = 0; i < count; i++) yield i; } },
  { kind: 'single', id: 'sink', input: true, run(value) { sinkCalls++; return value; } },
  { kind: 'transform', id: 'id', run(value) { transformCalls++; return value; } },
]);
const started = performance.now();
const cpu = process.cpuUsage();
const report = await engine.run();
const elapsedMs = performance.now() - started;
const cpuUs = process.cpuUsage(cpu);
const output = report.outputs.get('all');
assert.equal(report.status, 'succeeded');
assert.equal(sinkCalls, count);
assert.equal(transformCalls, count * 2);
assert.equal(output.length, count);
assert.deepEqual([...output].sort((a, b) => a - b), Array.from({ length: count }, (_, i) => i));
console.log(JSON.stringify({ node: process.version, count, status: report.status, outputs: output.length,
  sinkCalls, transformCalls, elapsedMs, cpuUs }));
