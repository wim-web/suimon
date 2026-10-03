import { renderToStaticMarkup } from 'react-dom/server';
import { describe, expect, it } from 'vitest';
import type { RuntimeState } from '../src/types';
import { FailureList } from '../src/components/FailureList';
import { RecordPanel } from '../src/components/RecordPanel';
import { RunSelector } from '../src/components/RunSelector';
import { WorkflowWorkbench } from '../src/components/WorkflowWorkbench';
import { parseState } from '../src/lib/parse';
import { createRuntimeIndex } from '../src/lib/runtime-index';
import { RUNTIME_LIMITS } from '../src/lib/runtime-limits';
import { pathKey, runTree } from '../src/lib/status';
import { definition, state } from './helpers';

function graph(parents: (number | null)[]): RuntimeState {
  // Paths are opaque identities, so a single-segment path can have a deep ownership chain.
  const paths = parents.map((_, i) => i ? [`run/${i}`] : []);
  return {
    status: 'running', started: parents.length > 0, cancelled: false,
    runs: parents.map((parent, i) => ({ path: paths[i]!, workflow: 'users', input: null, owner: parent === null ? null : `i${parent}`, task: null, complete: false })),
    invocations: paths.map((run, i) => ({ id: `i${i}`, run, placement: 'fetchAllUsers', trigger: null, input: null, status: 'active', arm: null })),
    calls: [], executions: [], results: [], taskResults: [], deliveries: [], settled: [], failures: [],
  };
}
const chain = (depth: number) => graph(Array.from({ length: depth + 1 }, (_, i) => i ? i - 1 : null));

describe('runtime ownership validation', () => {
  it('accepts an empty state and preserves depth-first order and sibling ordinals', () => {
    expect(runTree(parseState(graph([])))).toEqual([]);
    const s = graph([null, 0, 1, 0, 3, 0]);
    expect(runTree(parseState(s)).map(n => [n.run.path, n.depth, n.ordinal])).toEqual([
      [[], 0, 1], [['run/1'], 1, 1], [['run/2'], 2, 1], [['run/3'], 1, 2], [['run/4'], 2, 1], [['run/5'], 1, 3],
    ]);
  });

  it.each<[string, () => RuntimeState, string]>([
    ['self ownership', () => graph([null, 1]), 'ownership cycle'],
    ['disconnected cycle', () => graph([null, 2, 1]), 'ownership cycle'],
    ['cycle without a root', () => { const s = graph([null, 2, 1]); s.runs.shift(); s.invocations.shift(); return s; }, 'ownership cycle'],
    ['duplicate root path', () => { const s = chain(1); s.runs.push({ ...s.runs[1]!, path: [] }); return s; }, 'duplicate run path'],
    ['duplicate child path', () => { const s = chain(1); s.runs.push({ ...s.runs[1]! }); return s; }, 'duplicate run path'],
    ['owned root', () => graph([0]), 'root run cannot have an owner or task'],
    ['root task', () => { const s = chain(0); s.runs[0]!.task = 'task'; return s; }, 'root run cannot have an owner or task'],
    ['orphan', () => graph([null, null]), 'child run needs an owner'],
    ['unknown owner', () => graph([null, 99]), 'unknown invocation'],
    ['unknown caller run', () => { const s = chain(1); s.invocations[0]!.run = ['missing']; return s; }, 'unknown run'],
    ['unknown execution', () => { const s = chain(1); s.runs[1]!.task = 'task'; return s; }, 'unknown execution'],
    ['task ownership cycle', () => {
      const s = graph([null, 2, 1]), i = s.invocations[2]!;
      s.executions.push({ id: i.id, run: i.run, placement: i.placement, input: null, tasks: [{ name: 'task', input: null, status: 'active' }], complete: false });
      s.runs[1]!.task = 'task';
      return s;
    }, 'ownership cycle'],
    ['unknown task', () => { const s = state('users-a'); s.runs[1]!.task = 'missing'; return s; }, 'unknown task'],
    ['duplicate task', () => { const s = state('users-a'); s.executions[0]!.tasks.push(s.executions[0]!.tasks[0]!); return s; }, 'duplicate task name'],
    ['execution placement', () => { const s = state('users-a'); s.executions[0]!.placement = 'other'; return s; }, 'execution must match its invocation'],
    ['execution run', () => { const s = state('users-a'); s.executions[0]!.run = s.runs[1]!.path; return s; }, 'execution must match its invocation'],
    ['execution invocation', () => { const s = state('users-a'); s.invocations = s.invocations.filter(i => i.id !== s.executions[0]!.id); return s; }, 'execution must match its invocation'],
    ['deep chain', () => chain(RUNTIME_LIMITS.runDepth + 1), 'ownership depth exceeds'],
  ])('rejects %s both at parsing and direct traversal', (_, makeState, message) => {
    const s = makeState();
    for (const read of [parseState, runTree]) {
      expect(() => read(s)).toThrow(TypeError);
      expect(() => read(s)).toThrow(message);
    }
  });

  it.each(['invocations', 'executions', 'calls', 'results'] as const)('rejects duplicate IDs within %s', field => {
    const s = state('users-a');
    const items: { id: string }[] = s[field];
    items.push(items[0]!);
    expect(() => parseState(s)).toThrow(`state.${field}`);
    expect(() => runTree(s)).toThrow('duplicate id');
  });

  it('allows IDs shared by executions, calls and their invocations', () => {
    const s = state('users-a');
    expect(s.executions.every(e => s.invocations.some(i => i.id === e.id))).toBe(true);
    expect(s.calls.some(c => s.invocations.some(i => i.id === c.id))).toBe(true);
    expect(parseState(s)).toEqual(s);
  });

  it('rejects duplicates even when a supplied index has hidden them', () => {
    const s = chain(1);
    s.runs.push({ ...s.runs[1]! });
    const index = createRuntimeIndex(s);
    expect(index.runs.size).toBe(2);
    expect(() => runTree(s, index)).toThrow('duplicate run path');
    const invocations = chain(1);
    invocations.invocations.push({ ...invocations.invocations[0]! });
    expect(() => runTree(invocations, createRuntimeIndex(invocations))).toThrow('duplicate id');
  });

  it('accepts the maximum depth regardless of input order', () => {
    const s = chain(RUNTIME_LIMITS.runDepth);
    s.runs.reverse();
    const nodes = runTree(parseState(s));
    expect(nodes.map(n => n.depth)).toEqual(Array.from({ length: RUNTIME_LIMITS.runDepth + 1 }, (_, i) => i));
  });

  it('rejects a very deep chain without exhausting the JavaScript stack', () => {
    const s = chain(RUNTIME_LIMITS.runs - 1);
    for (const read of [parseState, runTree]) {
      expect(() => read(s)).toThrow(TypeError);
      expect(() => read(s)).toThrow('ownership depth exceeds');
    }
  });

  it('bounds path length separately from ownership depth', () => {
    const s = chain(1);
    s.runs[1]!.path = Array.from({ length: RUNTIME_LIMITS.pathSegments }, (_, i) => `segment ${i}`);
    s.invocations[1]!.run = s.runs[1]!.path;
    expect(runTree(parseState(s))[1]!.depth).toBe(1);
    s.runs[1]!.path.push('over limit');
    expect(() => parseState(s)).toThrow('path segments');
    expect(() => runTree(s)).toThrow('path segments');
  });

  it('accepts the run budget and rejects excess runs before reading their contents', () => {
    const s = graph(Array.from({ length: RUNTIME_LIMITS.runs }, (_, i) => i ? 0 : null));
    expect(runTree(parseState(s))).toHaveLength(RUNTIME_LIMITS.runs);
    // Invalid elements ensure the length check precedes structural parsing and graph construction.
    const oversized = { ...s, runs: Array(RUNTIME_LIMITS.runs + 1).fill(null) };
    expect(() => parseState(oversized)).toThrow(`at most ${RUNTIME_LIMITS.runs} runs`);
    expect(() => runTree(oversized)).toThrow(`at most ${RUNTIME_LIMITS.runs} runs`);
  });

  it('terminates on deterministic arbitrary ownership graphs with bounded, unique output', () => {
    let seed = 0x5eed;
    const random = (max: number) => { seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0; return seed % max; };
    let accepted = 0, rejected = 0;
    for (let sample = 0; sample < 200; sample++) {
      const count = 2 + random(39);
      const parents = Array.from({ length: count }, (_, i) => i ? random(sample % 2 ? i : count) : null);
      // Independent oracle: follow numeric parents, including components not reachable from root.
      const cyclic = parents.some((_, start) => {
        const seen = new Set<number>();
        for (let i: number | null = start; i !== null; i = parents[i]!) {
          if (seen.has(i)) return true;
          seen.add(i);
        }
        return false;
      });
      const s = graph(parents);
      if (cyclic) {
        expect(() => parseState(s)).toThrow('ownership cycle');
        expect(() => runTree(s)).toThrow('ownership cycle');
        rejected++;
      } else {
        const nodes = runTree(parseState(s));
        expect(nodes).toHaveLength(count);
        expect(new Set(nodes.map(n => pathKey(n.run.path))).size).toBe(count);
        expect(nodes.every(n => n.depth <= RUNTIME_LIMITS.runDepth)).toBe(true);
        const positions = new Map(nodes.map((n, i) => [pathKey(n.run.path), i]));
        for (const [i, node] of nodes.entries()) if (node.owner) expect(positions.get(pathKey(node.owner.run))!).toBeLessThan(i);
        accepted++;
      }
    }
    expect(accepted).toBeGreaterThan(0);
    expect(rejected).toBeGreaterThan(0);
  });
});

describe('components receiving unparsed runtime states', () => {
  const p = definition('users');
  it.each(['cycle', 'duplicate', 'depth', 'count'] as const)('renders a bounded error for invalid %s', invalid => {
    const s = invalid === 'depth' ? chain(RUNTIME_LIMITS.runDepth + 1) : graph([null, 2, 1]);
    if (invalid === 'duplicate') s.runs.push({ ...s.runs[0]! });
    if (invalid === 'count') s.runs = Array(RUNTIME_LIMITS.runs + 1).fill(s.runs[0]);
    for (const component of [
      <WorkflowWorkbench definition={p} state={s} run={s.runs[1]!.path} />,
      <RunSelector state={s} onSelectRun={() => undefined} />,
      <RecordPanel definition={p} state={s} transitions={[]} />,
      <FailureList state={s} />,
    ]) {
      const html = renderToStaticMarkup(component);
      expect(html).toContain('role="alert"');
      expect(html).toContain('Invalid runtime state');
      expect(html.length).toBeLessThan(500);
    }
  });

  it('renders every breadcrumb and run at the maximum valid depth', () => {
    const s = chain(RUNTIME_LIMITS.runDepth);
    const html = renderToStaticMarkup(<WorkflowWorkbench definition={p} state={s} run={s.runs.at(-1)!.path} />);
    expect(html).not.toContain('role="alert"');
    const breadcrumbs = html.match(/<nav class="sui-breadcrumbs"[\s\S]*?<\/nav>/)![0];
    expect(breadcrumbs.match(/<button\b/g)).toHaveLength(RUNTIME_LIMITS.runDepth + 1);
    expect(breadcrumbs).toContain('aria-current="page"');
    const selector = renderToStaticMarkup(<RunSelector state={s} onSelectRun={() => undefined} />);
    expect(selector.match(/<button /g)).toHaveLength(RUNTIME_LIMITS.runDepth + 1);
  });
});
