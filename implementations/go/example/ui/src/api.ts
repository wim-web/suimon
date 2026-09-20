import { parseGraph, parseTraceEvents } from '@suimon/ui-kit';
import type { Graph, JsonValue, PortRef, WorkflowSnapshot } from '@suimon/ui-kit';

export interface Sample { id: string; title: string; description: string; input: string; graph: Graph }
export interface RunOutput { port: PortRef; items: { id: string; value: JsonValue }[] }
export interface RunFrame { snapshot: WorkflowSnapshot; elapsedMS: number; done: boolean; error?: string; outputs: RunOutput[] }

function record(value: unknown): value is Record<string, unknown> { return value !== null && typeof value === 'object' && !Array.isArray(value); }
function jsonValue(value: unknown): value is JsonValue {
  if (value === null || typeof value === 'string' || typeof value === 'boolean') return true;
  if (typeof value === 'number') return Number.isFinite(value);
  return Array.isArray(value) ? value.every(jsonValue) : record(value) && Object.values(value).every(jsonValue);
}

export function parseOutputs(value: unknown): RunOutput[] {
  if (!Array.isArray(value)) throw new Error('Expected outputs array');
  return value.map((output: unknown) => {
    if (!record(output) || !record(output.port) || typeof output.port.node !== 'string' || typeof output.port.port !== 'string' || !Array.isArray(output.items)) throw new Error('Invalid output port');
    const items = output.items.map((item: unknown) => {
      if (!record(item) || typeof item.id !== 'string' || !Object.hasOwn(item, 'value') || !jsonValue(item.value)) throw new Error('Invalid output item');
      return { id: item.id, value: item.value };
    });
    return { port: { node: output.port.node, port: output.port.port }, items };
  });
}

export async function loadSamples(signal: AbortSignal): Promise<Sample[]> {
  const response = await fetch('/api/samples', { signal });
  if (!response.ok) throw new Error(await response.text());
  const raw: unknown = await response.json();
  if (!Array.isArray(raw)) throw new Error('Invalid samples response');
  return raw.map((value: unknown) => {
    if (!value || typeof value !== 'object') throw new Error('Invalid sample');
    const sample = value as Record<string, unknown>;
    if (typeof sample.id !== 'string' || typeof sample.title !== 'string' || typeof sample.description !== 'string' || typeof sample.input !== 'string') throw new Error('Invalid sample metadata');
    return { id: sample.id, title: sample.title, description: sample.description, input: sample.input, graph: parseGraph(sample.graph) };
  });
}

function parseFrame(line: string, previous?: RunFrame): RunFrame {
  const raw: unknown = JSON.parse(line);
  if (!record(raw)) throw new Error('Invalid run frame');
  const frame = raw;
  if (typeof frame.done !== 'boolean' || typeof frame.elapsed_ms !== 'number' || !Number.isFinite(frame.elapsed_ms) || frame.elapsed_ms < 0) throw new Error('Invalid run progress');
  if (frame.error !== undefined && typeof frame.error !== 'string') throw new Error('Invalid run error');
  if (previous && frame.elapsed_ms < previous.elapsedMS) throw new Error('Run progress moved backwards');
  if (previous && frame.graph !== undefined) throw new Error('Graph must only appear in the first run frame');
  const graph = previous?.snapshot.graph ?? parseGraph(frame.graph);
  const priorEvents = previous?.snapshot.events ?? [];
  const priorValues = previous?.snapshot.values ?? {};
  const offset = priorEvents.length;
  if (!Number.isSafeInteger(frame.event_offset) || frame.event_offset !== offset) throw new Error('Run event offset is missing, repeated or out of order');
  // Validate only the new records. Existing events and topology keep their
  // identities; the kit still receives an immutable, complete snapshot.
  const events = parseTraceEvents(frame.events);
  if (events.some((event, i) => event.sequence !== offset + i + 1)) throw new Error('Run event sequence is missing, repeated or out of order');
  const last = events.at(-1);
  if (last && (last.type !== 'transaction.committed' || last.op !== null)) throw new Error('Run frame contains an uncommitted event suffix');
  if (!record(frame.values) || !Object.values(frame.values).every(jsonValue)) throw new Error('Invalid run values');
  const valueIDs = Object.keys(frame.values);
  if (valueIDs.some(id => Object.hasOwn(priorValues, id))) throw new Error('Run item value was already received');
  if (!frame.done && (frame.outputs !== undefined || frame.error !== undefined)) throw new Error('Run outcome appeared before the final frame');
  const snapshot: WorkflowSnapshot = {
    graph,
    events: events.length ? [...priorEvents, ...events] : priorEvents,
    values: valueIDs.length ? { ...priorValues, ...frame.values as Record<string, JsonValue> } : priorValues,
  };
  return { snapshot, elapsedMS: frame.elapsed_ms, done: frame.done, error: frame.error, outputs: frame.done ? parseOutputs(frame.outputs) : [] };
}

// HTTP chunks may split a JSON record or a multibyte UTF-8 character.
export async function* readRunFrames(response: Response): AsyncGenerator<RunFrame> {
  if (!response.ok) throw new Error(await response.text());
  if (!response.body) throw new Error('Run response has no body');
  const reader = response.body.getReader();
  const decoder = new TextDecoder();
  let buffer = '', finished = false;
  let previous: RunFrame | undefined;
  try {
    while (true) {
      const { done, value } = await reader.read();
      buffer += done ? decoder.decode() : decoder.decode(value, { stream: true });
      if (done && buffer.trim()) buffer += '\n';
      let boundary: number;
      while ((boundary = buffer.indexOf('\n')) >= 0) {
        const line = buffer.slice(0, boundary).trim();
        buffer = buffer.slice(boundary + 1);
        if (!line) continue;
        if (finished) throw new Error('Received data after the final run frame');
        const frame = parseFrame(line, previous);
        previous = frame;
        finished = frame.done;
        yield frame;
      }
      if (done) break;
    }
    if (!finished) throw new Error('実行結果を受信する前に接続が終了しました');
  } finally { await reader.cancel(); reader.releaseLock(); }
}
