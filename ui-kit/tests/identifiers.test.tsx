import { renderToStaticMarkup } from 'react-dom/server';
import { expect, it } from 'vitest';
import type { OpRecord } from '../src/types';
import { NodeIcon } from '../src/components/NodeIcon';
import { PlacementInspector } from '../src/components/PlacementInspector';
import { RecordInspector } from '../src/components/RecordInspector';
import { statusLabel, statusTone } from '../src/components/StatusBadge';
import { deriveKinds } from '../src/lib/definition';
import { dictionary, lookup } from '../src/lib/dictionary';
import { layoutWorkflow } from '../src/lib/layout';
import { parseDefinition, parseRecordLog, parseState } from '../src/lib/parse';
import { recordTransitions, recordValues } from '../src/lib/records';
import { runOverlay } from '../src/lib/status';
import { resolveValue, valueIndex } from '../src/lib/values';

// Names that are also members of Object.prototype. In an object literal the first two find a
// function, the last finds the prototype, and assigning `__proto__` replaces the prototype.
const names = ['toString', 'constructor', '__proto__'];
const definitionText = JSON.stringify({
  main: 'w',
  functions: [{ id: 'items', input: 'Query', output: { stream: 'Item' } }, { id: 'save', input: { list: 'Item' }, output: { single: 'Receipt' } }],
  workflows: [{
    id: 'w', input: { type: 'Query', placement: 'toString' },
    placements: [
      { name: 'toString', node: { type: 'function', function: 'items' }, policy: 'stop' },
      { name: 'constructor', node: { type: 'waitStream', element: 'Item' }, policy: 'stop' },
      { name: '__proto__', node: { type: 'function', function: 'save' }, policy: 'stop' },
    ],
    connections: [{ source: 'toString', target: 'constructor', transform: 'item' }, { source: 'constructor', target: '__proto__', transform: 'items' }],
  }],
});
const definition = parseDefinition(definitionText);
/** The same workflow with ordinary placement names. */
const renamed = parseDefinition(definitionText.replaceAll('"toString"', '"a"').replaceAll('"constructor"', '"b"').replaceAll('"__proto__"', '"c"'));
const state = parseState({
  status: 'running', started: true, cancelled: false,
  runs: [{ path: [], workflow: 'w', input: 'query', owner: null, task: null, complete: false }],
  invocations: [
    { id: 'i1', run: [], placement: 'toString', trigger: null, input: 'query', status: 'succeeded', arm: null },
    { id: 'i2', run: [], placement: 'constructor', trigger: null, input: null, status: 'active', arm: null },
  ],
  calls: [{ id: 'c1', owner: 'i1', task: null, target: { function: { id: 'items' } }, input: 'query', stream: true, status: 'returned', yields: 1, timeout: { callMs: null, elementMs: null }, policy: 'stop' }],
  executions: [], taskResults: [],
  results: [{ id: 'r1', run: [], placement: 'toString', producer: 'c1', arm: null, value: 'item' }],
  deliveries: [{ run: [], connection: 0, source: 'r1', outcome: { value: { v: 'item' } } }],
  settled: [{ run: [], placement: 'toString', outcome: 'normal', arms: [] }],
  failures: [],
});

it('lays out placements named like Object.prototype members as any others, and reads given positions by own key', () => {
  const layout = layoutWorkflow(definition, 'w'), expected = layoutWorkflow(renamed, 'w');
  expect(layout.nodes.map(n => n.name)).toEqual(names);
  expect(layout.nodes.every(n => Number.isFinite(n.position.x) && Number.isFinite(n.position.y))).toBe(true);
  expect(layout.nodes.map(n => n.position)).toEqual(expected.nodes.map(n => n.position));
  expect(layout.input!.position).toEqual(expected.input!.position);
  const given = layoutWorkflow(definition, 'w', { constructor: { x: 5, y: 6 }, ['__proto__']: { x: 7, y: 8 } });
  expect(given.nodes.map(n => n.position)).toEqual([expected.nodes[0]!.position, { x: 5, y: 6 }, { x: 7, y: 8 }]);
});

it('derives the kinds of those placements, in a dictionary without a prototype', () => {
  const kinds = deriveKinds(definition, definition.workflows[0]!);
  expect(Object.entries(kinds)).toEqual([['toString', 'stream'], ['constructor', 'single'], ['__proto__', 'single']]);
  expect(kinds['valueOf']).toBeUndefined();
  const layout = layoutWorkflow(definition, 'w');
  expect(layout.nodes.map(n => n.kind)).toEqual(['stream', 'single', 'single']);
  expect(layout.edges.map(e => e.kind)).toEqual(['stream', 'single']);
});

it('overlays the status of each of those placements in a run', () => {
  const overlay = runOverlay(definition, state, [])!;
  expect(Object.keys(overlay.placements)).toEqual(names);
  expect(names.map(name => [overlay.placements[name]?.placement, overlay.placements[name]?.phase]))
    .toEqual([['toString', 'settled'], ['constructor', 'active'], ['__proto__', 'idle']]);
  expect(overlay.placements['valueOf']).toBeUndefined();
});

it('inspects those placements with their kind and status', () => {
  const html = names.map(name => renderToStaticMarkup(<PlacementInspector definition={definition} workflow="w" placement={name} state={state} run={[]} />));
  expect(html.map(h => /<dt>Output kind<\/dt><dd>([^<]*)</.exec(h)?.[1])).toEqual(['Stream', 'Single', 'Single']);
  expect(html.map(h => /Invocations<span> (\d+)<\/span>/.exec(h)?.[1])).toEqual(['1', '1', '0']);
  expect(html[0]).toContain('title="Settled outcome">normal<');
  expect(html[1]).toContain('sui-tone-accent">active<');
  expect(html[2]).toContain('sui-tone-muted">idle<');
  expect(html[2]).toContain('Not invoked in this run');
});

it('keeps a payload whose value identity is __proto__, from the record to the inspector', () => {
  const start = '{"seq":1,"op":{"type":"start","input":"__proto__"},"values":{"__proto__":"{\\"q\\":1}"}}';
  const log = parseRecordLog([`{"definition":${definitionText}}`, start, '{"seq":2,"commit":true}', ''].join('\n'));
  expect(Object.entries((log.records[0] as OpRecord).values!)).toEqual([['__proto__', '{"q":1}']]);
  const transitions = recordTransitions(log.records), payloads = recordValues(transitions);
  expect(Object.entries(payloads)).toEqual([['__proto__', '{"q":1}']]);
  expect(payloads['toString']).toBeUndefined();
  expect(resolveValue(valueIndex(definition, undefined, payloads), '__proto__')).toEqual({ kind: 'payload', id: '__proto__', payload: '{"q":1}' });
  const html = renderToStaticMarkup(<RecordInspector transition={transitions[0]!} />);
  expect(html).toContain('&quot;q&quot;: 1');
  expect(html).not.toContain('payload not provided');
});

it('reads a caller object by own key only, as for presentations and overlays, and builds dictionaries without a prototype', () => {
  const given = JSON.parse('{"__proto__":1,"constructor":2}') as Record<string, number>;
  expect(names.map(name => lookup(given, name))).toEqual([undefined, 2, 1]);
  expect(lookup(undefined, 'toString')).toBeUndefined();
  const built = dictionary<number>();
  names.forEach((name, i) => { built[name] = i; });
  expect(Object.entries(built)).toEqual([['toString', 0], ['constructor', 1], ['__proto__', 2]]);
  expect(built['valueOf']).toBeUndefined();
});

it('gives a status or control type named like an Object.prototype member the default tone, label and icon', () => {
  for (const name of names) {
    expect(statusTone(name)).toBe('muted');
    expect(statusLabel(name)).toBe(name);
    expect(renderToStaticMarkup(<NodeIcon kind={name} />)).toContain('--node-accent:var(--sui-accent-strong)');
  }
});
