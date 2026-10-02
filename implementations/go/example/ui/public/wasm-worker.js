// Keep the Go scheduler and record replay off the UI thread. Asset paths are relative
// to this worker so the same build works under a GitHub Pages repository path.
let runtime;

async function loadRuntime() {
  importScripts('./wasm/wasm_exec.js');
  const go = new Go();
  const started = new Promise(resolve => { globalThis.suimonReady = resolve; });
  const response = await fetch(new URL('./wasm/playground.wasm', self.location.href));
  if (!response.ok) throw new Error(`Could not load the Go runtime: ${response.status}`);
  const { instance } = await WebAssembly.instantiate(await response.arrayBuffer(), go.importObject);
  const exited = go.run(instance).then(() => { throw new Error('The Go runtime stopped. Reload to restart it.'); });
  void exited.catch(error => self.postMessage({ fatal: String(error.message ?? error) }));
  await Promise.race([started, exited]);
}

self.onmessage = async ({ data: { id, method, path, body } }) => {
  try {
    runtime ??= loadRuntime();
    await runtime;
    const response = await globalThis.suimonRequest(method, path, body);
    self.postMessage({ id, ...response });
  } catch (error) {
    self.postMessage({ id, error: String(error.message ?? error) });
  }
};
