import type { Definition, RuntimeState } from '../types';
import { findPlacement, findWorkflow, incoming } from './definition';
import { findExecution, findRun, samePath, taskOutputValue } from './status';

/**
 * Payload strings by value identity, plus the members of lists the engine builds itself (waitStream,
 * Merge, concurrency List). Records store the payloads of those lists too; the members are what the
 * state tells when no payload is at hand.
 */
export interface ValueIndex { payloads: ReadonlyMap<string, string>; lists: ReadonlyMap<string, readonly string[]> }
export type ResolvedValue =
  | { kind: 'payload'; id: string; payload: string }
  | { kind: 'list'; id: string; items: ResolvedValue[] }
  | { kind: 'missing'; id: string };

/** Members of the engine-built list values of the state. */
function lists(definition: Definition, state: RuntimeState): Map<string, string[]> {
  const found = new Map<string, string[]>();
  for (const result of state.results) {
    const run = findRun(state, result.run), workflow = run && findWorkflow(definition, run.workflow);
    const placement = findPlacement(workflow, result.placement);
    if (!workflow || !placement) continue;
    const node = placement.node;
    const delivered = (index: number) => state.deliveries.filter(d => samePath(d.run, result.run) && d.connection === index)
      .flatMap(d => typeof d.outcome === 'object' ? [d.outcome.value.v] : []);
    if (node.type === 'waitStream') found.set(result.value, incoming(workflow, placement.name).flatMap(c => delivered(c.index)));
    else if (node.type === 'merge') found.set(result.value, incoming(workflow, placement.name).flatMap(c => delivered(c.index).slice(0, 1)));
    else if (node.type === 'concurrency' && node.output === 'list') {
      // A List result names the execution that produced it; its members are the transformed outputs.
      const execution = findExecution(state, result.producer);
      if (!execution) continue;
      const included = new Set(node.tasks.filter(t => t.outputTransform).map(t => t.name));
      found.set(result.value, state.taskResults.filter(t => t.execution === execution.id && included.has(t.task)).flatMap(t => taskOutputValue(t.output) ?? []));
    }
  }
  return found;
}

export function valueIndex(definition: Definition, state?: RuntimeState, payloads: Record<string, string> = {}): ValueIndex {
  return { payloads: new Map(Object.entries(payloads)), lists: state ? lists(definition, state) : new Map() };
}

export function resolveValue(index: ValueIndex | undefined, id: string, depth = 0): ResolvedValue {
  if (index?.payloads.has(id)) return { kind: 'payload', id, payload: index.payloads.get(id)! };
  const items = index?.lists.get(id);
  if (items && depth < 16) return { kind: 'list', id, items: items.map(item => resolveValue(index, item, depth + 1)) };
  return { kind: 'missing', id };
}

/** A payload string as text: a JSON object or array is indented, anything else is shown as it is. */
export function formatPayload(payload: string): string {
  const text = payload.trim();
  if (!text.startsWith('{') && !text.startsWith('[')) return payload;
  try { return JSON.stringify(JSON.parse(text), null, 2); } catch { return payload; }
}

export function previewValue(value: ResolvedValue, max = 60): string {
  const text = value.kind === 'payload' ? value.payload.trim().replace(/\s+/g, ' ')
    : value.kind === 'list' ? `[${value.items.map(item => previewValue(item, max)).join(', ')}]` : '…';
  return text.length > max ? `${text.slice(0, max - 1)}…` : text;
}
