import { renderToStaticMarkup } from 'react-dom/server';
import { expect, it } from 'vitest';
import { EventInspector } from '../src/components/EventInspector';
import { NodeSidebar } from '../src/components/NodeSidebar';
import { NodeIOPanel } from '../src/components/NodeIOPanel';
import { WorkflowToolbar } from '../src/components/WorkflowToolbar';
import type { TraceEvent } from '../src/types';

it('renders untrusted values as text in the standalone inspector', () => {
  const event: TraceEvent = { schema_version: 2, sequence: 1, recorded_at: 0, txn: 'tx', type: 'token.placed', op: null, data: { token: { item: { id: 'payload' } } } };
  const html = renderToStaticMarkup(<EventInspector event={event} values={{ payload: '<script>alert(1)</script>' }} />);
  expect(html).toContain('&lt;script&gt;');
  expect(html).not.toContain('<script>');
  expect(html).toContain('Event JSON');
});

it('gives the toolbar logo an accessible image role', () => {
  expect(renderToStaticMarkup(<WorkflowToolbar title="Example" />)).toContain('role="img" aria-label="suimon"');
});

it('shows input and output values together with their connections in a standalone panel', () => {
  const html = renderToStaticMarkup(<NodeIOPanel data={{
    inputs: [{ port: { name: 'in', kind: 'plain' }, connections: ['trim.out'], items: [{ id: 'input', instance: 'uppercase', sequence: 19, available: true, value: '<hello>' }] }],
    outputs: [{ port: { name: 'out', kind: 'plain' }, connections: ['Workflow output'], items: [{ id: 'output', instance: 'uppercase', sequence: 24, available: true, value: '<HELLO>' }] }],
  }} />);
  expect(html).toContain('入力 in');
  expect(html).toContain('出力 out');
  expect(html).toContain('trim.out');
  expect(html).toContain('&lt;hello&gt;');
  expect(html).toContain('&lt;HELLO&gt;');
  expect(html).not.toContain('<hello>');
});

it('supports composing the sidebar without a workbench or runtime connection', () => {
  const html = renderToStaticMarkup(<NodeSidebar graph={{ nodes: [], edges: [], entries: [], exits: [] }} onSelectNode={() => undefined}><label>Custom input</label></NodeSidebar>);
  expect(html).toContain('Custom input');
  expect(html).toContain('一致するノードがありません');
});

it('distinguishes arrived, pending and consumed stream inputs before EOS', () => {
  const html = renderToStaticMarkup(<NodeIOPanel data={{ inputs: [{
    port: { name: 'in', kind: 'stream' }, connections: ['each.out'], channels: [{ id: 'channel', closed: false }],
    items: [{ id: 'one', channel: 'channel', tokenIndex: 0, sequence: 12, consumed: false, available: true, value: 'ONE' }],
  }], outputs: [{ port: { name: 'out', kind: 'plain' }, connections: [], items: [] }] }} />);
  expect(html).toContain('到着 1件 · 消費 0件 · 待機 1件');
  expect(html).toContain('EOS 未到着');
  expect(html).toContain('待機中');
  expect(html).toContain('ONE');
});
