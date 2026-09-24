import { renderToStaticMarkup } from 'react-dom/server';
import { expect, it } from 'vitest';
import { PlacementInspector } from '../src/components/PlacementInspector';
import { RecordInspector } from '../src/components/RecordInspector';
import { RecordPanel } from '../src/components/RecordPanel';
import { RunSelector } from '../src/components/RunSelector';
import { WorkflowToolbar } from '../src/components/WorkflowToolbar';
import { WorkflowWorkbench } from '../src/components/WorkflowWorkbench';
import { parseRecordLog, parseRecords } from '../src/lib/parse';
import { recordTransitions, recordValues } from '../src/lib/records';
import { runTree } from '../src/lib/status';
import { valueIndex } from '../src/lib/values';
import { definition, recordText, records, state } from './helpers';

it('inspects a placement with its definition, connections, invocations and results', () => {
  const p = definition('users'), s = state('users-a');
  const values = valueIndex(p, s, { ...recordValues(recordTransitions(records('users-a'))), '5:value5:input': '<tenant>' });
  const html = renderToStaticMarkup(<PlacementInspector definition={p} workflow="users" placement="perUser" state={s} run={[]} values={values} onSelectRun={() => undefined} onOpenWorkflow={() => undefined} />);
  expect(html).toContain('Concurrency');
  expect(html).toContain('profileFlow → format');
  expect(html).toContain('fetchAllUsers');
  expect(html).toContain('summaries');
  expect(html).toContain('Invocations<span> 2</span>');
  expect(html).toContain('run profileFlow');
  expect(html).toContain('#2');
  expect(html).toContain('result');
  expect(html).not.toContain('payload not provided');
  const entry = renderToStaticMarkup(<PlacementInspector definition={p} workflow="users" placement="fetchAllUsers" state={s} run={[]} values={values} />);
  expect(entry).toContain('&lt;tenant&gt;');
  expect(entry).not.toContain('<tenant>');
  expect(entry).toContain('Stream&lt;User&gt;');
  const endpoint = renderToStaticMarkup(<PlacementInspector definition={p} workflow="users" placement="all" />);
  expect(endpoint).toContain('endpoint');
  expect(endpoint).not.toContain('Invocations');
});

it('shows task outputs as transformed, failed or pending, and each List under its execution', () => {
  const p = definition('users');
  const b = state('users-b');
  const failed = renderToStaticMarkup(<PlacementInspector definition={p} workflow="users" placement="perUser" state={b} run={[]} values={valueIndex(p, b, recordValues(recordTransitions(records('users-b'))))} />);
  expect(failed).toContain('output transform failed');
  expect(failed).not.toContain('output transform pending');
  expect(failed).toContain('outputs');
  expect(failed).toContain('transformed<b>2</b>');
  expect(failed.match(/sui-invocation-results/g)).toHaveLength(2);
  const c = state('users-c');
  const running = renderToStaticMarkup(<PlacementInspector definition={p} workflow="users" placement="perUser" state={c} run={[]} />);
  expect(running).toContain('output transform pending');
  expect(running).toContain('No results');
});

it('lists runs as a tree and records with their commit state and relation', () => {
  const p = definition('users'), s = state('users-a');
  const runs = renderToStaticMarkup(<RunSelector state={s} run={runTree(s)[2]!.run.path} onSelectRun={() => undefined} />);
  expect(runs).toContain('perUser.profile #2 → profileFlow');
  expect(runs.match(/aria-pressed="true"/g)).toHaveLength(1);
  const lines = recordText('users-a').split('\n');
  const transitions = recordTransitions(parseRecords(lines.slice(0, 14).join('\n') + '\n'));
  const panel = renderToStaticMarkup(<RecordPanel transitions={transitions} definition={p} state={s} />);
  expect(panel).toContain('1 uncommitted');
  expect(panel).toContain('fetchAllUsers');
  expect(panel.match(/sui-record-row/g)).toHaveLength(7);
  const filtered = renderToStaticMarkup(<RecordPanel transitions={transitions} definition={p} state={s} filter={{ run: [], placement: 'perUser' }} />);
  expect(filtered.match(/sui-record-row/g)?.length).toBe(1);
  expect(renderToStaticMarkup(<RecordPanel transitions={[]} definition={p} />)).toContain('No execution records');
  const log = parseRecordLog(recordText('users-c'));
  const torn = renderToStaticMarkup(<RecordPanel transitions={recordTransitions(log.records)} tail={log.tail} definition={p} state={state('users-c')} />);
  expect(torn).toContain('1 uncommitted');
  expect(torn).toContain('partial last line');
  expect(torn).toContain('never committed');
});

it('shows a record with its fields and payloads as text', () => {
  const html = renderToStaticMarkup(<RecordInspector transition={{ seq: 7, committed: false, op: { type: 'returned', call: 'c', value: 'v' }, values: { v: '<b>done</b>' } }} relation={{ run: [], placement: 'ship' }} />);
  expect(html).toContain('uncommitted');
  expect(html).toContain('&lt;b&gt;done&lt;/b&gt;');
  expect(html).not.toContain('<b>done</b>');
  expect(html).toContain('ship');
});

it('renders the toolbar status and failure count', () => {
  const html = renderToStaticMarkup(<WorkflowToolbar title="users" status="failed" failures={2} />);
  expect(html).toContain('role="img" aria-label="suimon"');
  expect(html).toContain('2 failures');
  expect(html).toContain('sui-tone-danger');
});

it('composes the workbench from a definition alone or with a state and records', () => {
  const p = definition('users');
  expect(renderToStaticMarkup(<WorkflowWorkbench definition={p} />)).toContain('No runtime state');
  const html = renderToStaticMarkup(<WorkflowWorkbench definition={p} state={state('users-a')} records={records('users-a')} title="Users" />);
  expect(html).toContain('Users');
  expect(html).toContain('perUser.profile #1 → profileFlow');
  expect(html).toContain('Records <b>50</b>');
});
