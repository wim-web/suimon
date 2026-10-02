interface Reply { id?: number; status: number; body: string; error?: string; fatal?: string }
interface Pending { resolve: (response: Response) => void; reject: (error: Error) => void }

let worker: Worker | undefined;
let failure: Error | undefined;
let next = 0;
const pending = new Map<number, Pending>();

function fail(error: Error) {
  failure = error;
  for (const request of pending.values()) request.reject(error);
  pending.clear();
  worker?.terminate();
}

function getWorker(): Worker {
  if (failure) throw failure;
  if (worker) return worker;
  worker = new Worker(new URL(`${import.meta.env.BASE_URL}wasm-worker.js`, document.baseURI));
  worker.onmessage = ({ data }: MessageEvent<Reply>) => {
    if (data.fatal) { fail(new Error(data.fatal)); return; }
    const request = data.id === undefined ? undefined : pending.get(data.id);
    if (!request) return;
    pending.delete(data.id!);
    if (data.error) request.reject(new Error(data.error));
    else request.resolve(new Response(data.status === 204 ? null : data.body, { status: data.status }));
  };
  worker.onerror = event => fail(new Error(event.message || 'The Go worker failed. Reload to retry.'));
  worker.onmessageerror = () => fail(new Error('Could not read a response from the Go worker.'));
  return worker;
}

export async function wasmRequest(path: string, init: RequestInit = {}): Promise<Response> {
  const { signal } = init;
  signal?.throwIfAborted();
  const target = getWorker();
  const id = ++next;
  let abort: (() => void) | undefined;
  try {
    return await new Promise<Response>((resolve, reject) => {
      abort = () => { pending.delete(id); reject(signal?.reason); };
      signal?.addEventListener('abort', abort, { once: true });
      pending.set(id, { resolve, reject });
      target.postMessage({ id, path, method: init.method ?? 'GET', body: init.body ?? '' });
    });
  } finally {
    pending.delete(id);
    if (abort) signal?.removeEventListener('abort', abort);
  }
}
