import { readFileSync } from 'node:fs';
import { renderToStaticMarkup } from 'react-dom/server';
import { expect, it } from 'vitest';
import { createWorkflowView } from '../src/lib/view';
import { traceIndex } from '../src/lib/trace';
import { parseGraph } from '../src/lib/parse';
import { relationLabel } from '../src/lib/routing';
import { TracePanel } from '../src/components/TracePanel';
import type { Graph, TraceEvent } from '../src/types';

const fixture = (name: string) => readFileSync(new URL(`../../Test/${name}`, import.meta.url), 'utf8');
const events = (name: string): TraceEvent[] => fixture(`traces/${name}.jsonl`).trim().split('\n').map(line => JSON.parse(line) as TraceEvent);

it('includes incoming Collect events before its instance exists, retaining the sender', () => {
  const graph = parseGraph(JSON.parse(fixture('graphs/streaming.json')));
  const trace: TraceEvent[] = [
    { schema_version: 2, sequence: 1, txn: 'arrival', recorded_at: 0, type: 'token.placed', op: null, data: { by_instance: 'each-instance', edge: '["edge","1"]', token: { item: { id: 'result' } } } },
    { schema_version: 2, sequence: 2, txn: 'arrival', recorded_at: 0, type: 'transaction.committed', op: null, data: {} },
  ];
  const index = traceIndex(trace), view = createWorkflowView(graph, index, { result: 'ARRIVED' });
  expect(view.index).toBe(index);
  expect(index.instances.size).toBe(0);
  expect(view.io.collect?.inputs[0]?.items[0]?.value).toBe('ARRIVED');
  expect(view.eventsByNode.get('collect')).toEqual([trace[0]]);
  expect(view.eventsByNode.get('each')).toEqual([trace[0]]);
  expect(relationLabel(view.relations.get(1))).toBe('each.out → collect.in');
  const html = renderToStaticMarkup(<TracePanel events={trace} index={index} view={view} nodeFilter="collect" onSelectEvent={() => undefined} />);
  expect(html).toContain('token.placed');
  expect(html).toContain('each.out');
  expect(html).toContain('collect.in');
  expect(html).not.toContain('一致するイベントがありません');
  expect(createWorkflowView(graph, trace.slice(0, 1)).eventsByNode.has('collect')).toBe(false);
});

it('keeps actor attribution while matching the destination of a real fixture', () => {
  const graph = parseGraph(JSON.parse(fixture('graphs/coalesce.json')));
  const trace = events('coalesce').slice(0, 23);
  const view = createWorkflowView(graph, trace);
  const placed = trace.find(event => event.type === 'token.placed' && event.data.edge === '["edge","3"]')!;
  expect(view.relations.get(placed.sequence)?.actor?.node).toBe('right');
  expect(view.relations.get(placed.sequence)?.destination?.node).toBe('join');
  expect(view.eventsByNode.get('join')).toContain(placed);
  expect(view.eventsByNode.get('right')).toContain(placed);
});

it('uses the definition scope rather than mixing equal node names in nested graphs', () => {
  const root = parseGraph(JSON.parse(fixture('graphs/loop.json'))), trace = events('loop-retry');
  const kind = root.nodes[0]!.kind;
  if (!('body' in kind)) throw new Error('missing loop body');
  const graph: Graph = kind.body, index = traceIndex(trace);
  const body = createWorkflowView(graph, index, {}, ['loop']);
  expect(body.eventsByNode.get('work')?.length).toBeGreaterThan(0);
  expect(createWorkflowView(graph, index, {}, ['other']).eventsByNode.size).toBe(0);
  expect(createWorkflowView(root, index).eventsByNode.has('work')).toBe(false);
});
