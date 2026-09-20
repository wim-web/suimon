import type { TraceEvent, TraceIndex } from '../types';
import { instanceDefinitionPath } from './routing';
import { asTraceIndex } from './trace';

export interface NodeActivity { running: number; succeeded: number; failed: number }

// Summarize committed attempts, including descendants of a container node.
// No runtime State codec or transport is required by the kit.
export function nodeActivity(events: TraceEvent[] | TraceIndex, scope: string[] = []): Record<string, NodeActivity> {
  const { instances, attempts } = asTraceIndex(events);
  const activity = new Map<string, NodeActivity>();
  for (const attempt of attempts.values()) {
    const instance = instances.get(attempt.instance);
    if (!instance) continue;
    const parent = instanceDefinitionPath(instance, instances);
    if (!parent) continue;
    const definition = [...parent, instance.node];
    if (!scope.every((part, i) => part === definition[i]) || definition.length <= scope.length) continue;
    const node = definition[scope.length]!;
    const stats = activity.get(node) ?? { running: 0, succeeded: 0, failed: 0 };
    if (attempt.status === 'running') stats.running++;
    if (attempt.status === 'succeeded') stats.succeeded++;
    if (attempt.status === 'failed') stats.failed++;
    activity.set(node, stats);
  }
  return Object.fromEntries(activity);
}
