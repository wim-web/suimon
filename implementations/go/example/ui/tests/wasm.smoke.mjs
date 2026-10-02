import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';
import { setTimeout as delay } from 'node:timers/promises';

await import('../public/wasm/wasm_exec.js');
const go = new globalThis.Go();
const ready = new Promise(resolve => { globalThis.suimonReady = resolve; });
const { instance } = await WebAssembly.instantiate(await readFile(new URL('../public/wasm/playground.wasm', import.meta.url)), go.importObject);
const exited = go.run(instance).then(() => { throw new Error('Go exited unexpectedly'); });
await Promise.race([ready, exited]);

async function call(method, path, body, status = 200) {
  const response = await globalThis.suimonRequest(method, path, body === undefined ? '' : JSON.stringify(body));
  assert.equal(response.status, status, response.body);
  return response.body ? JSON.parse(response.body) : undefined;
}

async function start(scenario, input, unitMs = 10) {
  return (await call('POST', '/api/runs', { scenario, input, unitMs }, 201)).id;
}

async function finish(id) {
  let offset = 0;
  const records = [];
  const deadline = Date.now() + 15_000;
  while (Date.now() < deadline) {
    const progress = await call('GET', `/api/runs/${id}?after=${offset}`);
    assert.equal(progress.error, undefined);
    assert.equal(progress.offset, offset);
    records.push(...progress.records);
    offset += progress.records.length;
    if (progress.done) {
      const full = await call('GET', `/api/runs/${id}`);
      assert.deepEqual(records, full.records);
      assert.ok(JSON.parse(records[0]).definition);
      return progress;
    }
    await delay(20);
  }
  assert.fail(`run ${id} did not finish`);
}

test('the compiled Go runtime executes every playground scenario', { timeout: 30_000 }, async () => {
  const scenarios = await call('GET', '/api/scenarios');
  assert.deepEqual(scenarios.map(s => s.id), ['stream', 'batch', 'branch', 'merge', 'limit', 'timeout', 'stop']);
  const expected = {
    stream: ['succeeded', 'collect', 5], batch: ['succeeded', 'collect', 5],
    branch: ['succeeded', 'decide', 1], merge: ['succeeded', 'summary', 3],
    limit: ['succeeded', 'lookups', 4], timeout: ['failed', 'collect', 2], stop: ['failed'],
  };
  const results = {};
  for (const scenario of scenarios) {
    const id = await start(scenario.id);
    const progress = await finish(id);
    const report = await call('GET', `/api/runs/${id}/report`);
    const [status, endpoint, count] = expected[scenario.id];
    assert.equal(progress.state.status, status, scenario.id);
    assert.equal(report.status, status, scenario.id);
    if (endpoint) assert.equal(JSON.parse(report.outputs[endpoint]).length, count, scenario.id);
    if (scenario.id === 'timeout') assert.equal(report.failures[0].cause, 'timeout');
    if (scenario.id === 'stop') assert.ok(progress.spans.some(s => s.function === 'ship' && s.outcome === 'cancelled'));
    results[scenario.id] = progress;
  }
  const stream = results.stream.spans;
  assert.ok(stream.find(s => s.function === 'process').startMs < stream.find(s => s.function === 'produce').endMs);
  const batch = results.batch.spans;
  assert.ok(batch.filter(s => s.function === 'process').every(s => s.startMs >= batch.find(s => s.function === 'produceAll').endMs));
});

test('browser input changes the branch, and active runs can be cancelled', async () => {
  const id = await start('branch', { id: 'browser-order', amount: 5000 });
  await finish(id);
  const report = await call('GET', `/api/runs/${id}/report`);
  assert.deepEqual(JSON.parse(report.outputs.decide), [{ order: 'browser-order', by: 'review' }]);

  const running = await start('stream', undefined, 1000);
  assert.equal((await globalThis.suimonRequest('GET', `/api/runs/${running}/report`, '')).status, 409);
  await call('POST', `/api/runs/${running}/cancel`, undefined, 204);
  assert.equal((await finish(running)).state.status, 'cancelled');
  assert.equal((await call('GET', `/api/runs/${running}/report`)).status, 'cancelled');
});

test('the Wasm bridge preserves request validation and missing-run errors', async () => {
  for (const [method, path, body, status] of [
    ['POST', '/api/runs', '{', 400],
    ['POST', '/api/runs', '{"scenario":"stream","unitMs":0}', 400],
    ['POST', '/api/runs', '{"scenario":"unknown","unitMs":10}', 404],
    ['GET', '/api/runs/missing', '', 404],
  ]) {
    const response = await globalThis.suimonRequest(method, path, body);
    assert.equal(response.status, status, response.body);
    assert.ok(response.body.trim());
  }
});
