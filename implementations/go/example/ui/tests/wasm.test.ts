import { afterEach, beforeEach, expect, it, vi } from 'vitest';

class FakeWorker {
  static current: FakeWorker;
  onmessage?: (event: MessageEvent) => void;
  onerror?: (event: { message: string }) => void;
  onmessageerror?: () => void;
  postMessage = vi.fn();
  terminate = vi.fn();
  constructor(readonly url: URL) { FakeWorker.current = this; }
  reply(data: unknown) { this.onmessage?.({ data } as MessageEvent); }
}

beforeEach(() => {
  vi.resetModules();
  vi.stubGlobal('Worker', FakeWorker);
  vi.stubGlobal('document', { baseURI: 'https://example.test/suimon/' });
  vi.stubEnv('BASE_URL', './');
});
afterEach(() => { vi.unstubAllGlobals(); vi.unstubAllEnvs(); });

it('loads the worker under the page path and matches out-of-order replies', async () => {
  const { wasmRequest } = await import('../src/wasm');
  const first = wasmRequest('/api/scenarios');
  const second = wasmRequest('/api/runs/r1/cancel', { method: 'POST' });
  const worker = FakeWorker.current;
  expect(worker.url.href).toBe('https://example.test/suimon/wasm-worker.js');
  expect(worker.postMessage.mock.calls.map(([message]) => message)).toEqual([
    { id: 1, path: '/api/scenarios', method: 'GET', body: '' },
    { id: 2, path: '/api/runs/r1/cancel', method: 'POST', body: '' },
  ]);
  worker.reply({ id: 2, status: 204, body: '' });
  worker.reply({ id: 1, status: 200, body: '[]' });
  expect((await second).status).toBe(204);
  expect(await (await first).json()).toEqual([]);
});

it('aborts a pending read without affecting another request or accepting its late reply', async () => {
  const { wasmRequest } = await import('../src/wasm');
  const controller = new AbortController();
  const first = wasmRequest('/api/scenarios', { signal: controller.signal });
  const rejected = expect(first).rejects.toMatchObject({ name: 'AbortError' });
  const second = wasmRequest('/api/scenarios');
  controller.abort();
  await rejected;
  FakeWorker.current.reply({ id: 1, status: 200, body: 'ignored' });
  FakeWorker.current.reply({ id: 2, status: 200, body: '[]' });
  expect(await (await second).json()).toEqual([]);
});

it('rejects pending and future calls when the Go runtime exits', async () => {
  const { wasmRequest } = await import('../src/wasm');
  const first = wasmRequest('/api/scenarios');
  const second = wasmRequest('/api/runs/r1');
  const rejected = Promise.all([expect(first).rejects.toThrow('runtime stopped'), expect(second).rejects.toThrow('runtime stopped')]);
  FakeWorker.current.reply({ fatal: 'runtime stopped' });
  await rejected;
  expect(FakeWorker.current.terminate).toHaveBeenCalledOnce();
  await expect(wasmRequest('/api/scenarios')).rejects.toThrow('runtime stopped');
});

it('surfaces module-load failures to the caller', async () => {
  const { wasmRequest } = await import('../src/wasm');
  const response = wasmRequest('/api/scenarios');
  const rejected = expect(response).rejects.toThrow('Could not load the Go runtime: 404');
  FakeWorker.current.reply({ id: 1, error: 'Could not load the Go runtime: 404' });
  await rejected;
});
