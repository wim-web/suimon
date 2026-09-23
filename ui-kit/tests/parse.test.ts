import { describe, expect, it } from 'vitest';
import { parseProgram, parseRecordLog, parseRecords, parseState } from '../src/lib/parse';
import { clone, program, programJson, recordText, stateJson } from './helpers';

type Json = Record<string, any>;

describe('parseProgram', () => {
  it('accepts the example programs and normalizes optional lists', () => {
    for (const name of ['users', 'branch', 'merge']) expect(program(name).workflows.length).toBeGreaterThan(0);
    const users = program('users');
    expect(users.judges).toEqual([]);
    expect(users.workflows[1]!.connections).toHaveLength(1);
    const perUser = users.workflows[0]!.placements[1]!.node;
    expect(perUser.type === 'concurrency' && perUser.tasks[1]!.timeout).toEqual({ callMs: 5000 });
  });

  it.each<[string, (p: Json) => void, string]>([
    ['unknown field', p => { p.extra = 1; }, 'program: unknown field extra'],
    ['main', p => { p.main = 'nowhere'; }, 'program.main: unknown workflow nowhere'],
    ['node type', p => { p.workflows[0].placements[0].node.type = 'loop'; }, 'program.workflows[shipping].placements[list].node.type: expected one of'],
    ['policy', p => { delete p.workflows[0].placements[1].policy; }, 'placements[paid]: missing field policy'],
    ['arm', p => { delete p.workflows[0].connections[1].arm; }, 'connections[1]: a connection from a branch needs an arm'],
    ['unknown arm', p => { p.workflows[0].connections[1].arm = 'later'; }, 'connections[1].arm: unknown arm later'],
    ['target', p => { p.workflows[0].connections[0].target = 'gone'; }, 'connections[0].target: unknown placement gone'],
    ['timeout', p => { p.workflows[0].placements[0].timeout.callMs = 0; }, 'timeout.callMs: expected a positive integer'],
    ['type', p => { p.functions[0].output = { stream: '' }; }, 'program.functions[0].output.stream: empty string'],
  ])('rejects a broken program: %s', (_, edit, message) => {
    const json = clone(programJson('branch')) as Json;
    edit(json);
    expect(() => parseProgram(json)).toThrow(TypeError);
    expect(() => parseProgram(json)).toThrow(message);
  });

  it('checks the workflows that placements and tasks call', () => {
    const json = clone(programJson('users')) as Json;
    json.workflows[0].placements[1].node.tasks[0].body.output = 'missing';
    expect(() => parseProgram(json)).toThrow('tasks[profile].body: workflow profileFlow has no placement missing');
    json.workflows[0].placements[1].node.tasks[0].body.workflow = 'other';
    expect(() => parseProgram(json)).toThrow('unknown workflow other');
  });
});

describe('parseState', () => {
  it('accepts the derived JSON of the Lean state', () => {
    for (const name of ['users-a', 'branch-a', 'merge-a']) expect(parseState(stateJson(name)).status).toBe('succeeded');
    expect(parseState(stateJson('users-b')).status).toBe('failed');
    expect(parseState(stateJson('users-c')).status).toBe('running');
    const s = parseState(stateJson('users-a'));
    expect(s.runs.filter(r => r.task === 'profile')).toHaveLength(2);
    expect(s.calls.find(c => 'function' in c.target && c.target.function.id === 'fetchOrders')?.timeout).toEqual({ callMs: 5000, elementMs: null });
    const branch = parseState(stateJson('branch-a'));
    expect(branch.settled.find(x => x.placement === 'paid')?.arms).toEqual([['paid', 'normal'], ['unpaid', 'normal']]);
    expect(branch.calls.some(c => 'judge' in c.target)).toBe(true);
    expect(parseState(stateJson('merge-a')).deliveries.some(d => d.outcome === 'trigger')).toBe(true);
  });

  it('reads task outputs as pending, a value or failed, and the producer of each result', () => {
    const outputs = (name: string) => parseState(stateJson(name)).taskResults.map(r => typeof r.output === 'object' ? 'value' : r.output);
    expect(outputs('users-a')).toEqual(['value', 'value', 'value', 'value']);
    expect(outputs('users-b').sort()).toEqual(['failed', 'value', 'value']);
    expect(outputs('users-c')).toContain('pending');
    const b = parseState(stateJson('users-b'));
    const failed = b.taskResults.find(r => r.output === 'failed')!;
    expect(b.executions.map(e => e.id)).toContain(failed.execution);
    expect(b.results.filter(r => r.placement === 'perUser').map(r => r.producer).sort()).toEqual(b.executions.map(e => e.id).sort());
    const value = b.taskResults.find(r => typeof r.output === 'object')!.output;
    expect(typeof value === 'object' && typeof value.value.v).toBe('string');
  });

  it('reads an absent Option field as null', () => {
    const json = clone(stateJson('merge-a')) as Json;
    delete json.invocations[0].trigger;
    expect(parseState(json).invocations[0]!.trigger).toBeNull();
  });

  it.each<[string, (s: Json) => void, string]>([
    ['status', s => { s.status = 'done'; }, 'state.status: expected one of running'],
    ['outcome', s => { s.settled[0].outcome = 'ok'; }, 'state.settled[0].outcome'],
    ['target', s => { s.calls[0].target = { worker: { id: 'x' } }; }, 'state.calls[0].target: unknown field worker'],
    ['delivery', s => { s.deliveries[0].outcome = { value: 'x' }; }, 'state.deliveries[0].outcome'],
    ['path', s => { s.runs[0].path = 'root'; }, 'state.runs[0].path: expected an array'],
    ['producer', s => { delete s.results[0].producer; }, 'state.results[0]: missing field producer'],
  ])('rejects a broken state: %s', (_, edit, message) => {
    const json = clone(stateJson('merge-a')) as Json;
    edit(json);
    expect(() => parseState(json)).toThrow(TypeError);
    expect(() => parseState(json)).toThrow(message);
  });

  it.each<[string, (s: Json) => void, string]>([
    ['null output', s => { s.taskResults[0].output = null; }, 'state.taskResults[0].output: expected "pending"'],
    ['bare output', s => { s.taskResults[0].output = 'x'; }, 'state.taskResults[0].output: expected "pending"'],
    ['missing output', s => { delete s.taskResults[0].output; }, 'state.taskResults[0]: missing field output'],
    ['output value', s => { s.taskResults[0].output = { value: 'x' }; }, 'state.taskResults[0].output.value: expected an object'],
  ])('rejects a broken task output: %s', (_, edit, message) => {
    const json = clone(stateJson('users-a')) as Json;
    edit(json);
    expect(() => parseState(json)).toThrow(message);
  });
});

describe('parseRecords', () => {
  const text = recordText('users-a');
  const lines = text.slice(0, -1).split('\n');

  it('reads JSON lines, arrays of lines and arrays of records', () => {
    expect(text.endsWith('\n')).toBe(true);
    const parsed = parseRecords(text);
    expect(parsed).toHaveLength(lines.length);
    expect(parsed[0]).toEqual({ seq: 1, op: { type: 'start', input: '5:value5:input' }, values: { '5:value5:input': '5:value5:input' } });
    expect(parsed[1]).toEqual({ seq: 2, commit: true });
    expect(parseRecordLog(text)).toEqual({ records: parsed, tail: '' });
    expect(parseRecords(lines)).toEqual(parsed);
    expect(parseRecords(lines.map(line => JSON.parse(line)))).toEqual(parsed);
  });

  it('keeps the payloads of engine-built lists in the op record that built them', () => {
    const settle = parseRecords(recordText('branch-a')).find(r => 'op' in r && r.op.type === 'settle' && r.op.placement === 'receipts');
    expect(settle && 'values' in settle && Object.keys(settle.values!)).toEqual([expect.stringMatching(/^4:list/)]);
  });

  it('keeps an op without its commit at the end', () => {
    expect(parseRecords(lines.slice(0, 3).join('\n') + '\n').at(-1)).toMatchObject({ seq: 3, op: { type: 'invoke' } });
  });

  it('never commits the text after the last newline, even when it parses', () => {
    const c = recordText('users-c');
    expect(c.endsWith('\n')).toBe(false);
    const log = parseRecordLog(c);
    expect(log.records).toHaveLength(81);
    expect(log.records.at(-1)).toMatchObject({ seq: 81, op: { type: 'taskOutput' } });
    expect(log.tail).toBe('{"seq":82,"commit":true}');
    expect(parseRecords(lines.slice(0, 4).join('\n') + '\n' + lines[4]!.slice(0, 20))).toHaveLength(4);
    expect(parseRecordLog(lines.slice(0, 2).join('\n'))).toEqual({ records: parseRecords(lines[0]! + '\n'), tail: lines[1] });
    expect(parseRecordLog('')).toEqual({ records: [], tail: '' });
    // An array holds complete lines; a host passes the tail it split off as an option.
    expect(parseRecordLog(lines.slice(0, 81), { tail: lines[81] })).toEqual(log);
    expect(() => parseRecords([lines[0]!.slice(0, 20)])).toThrow('records[0]: expected a JSON record');
    expect(() => parseRecordLog([], { tail: 1 as unknown as string })).toThrow('options.tail: expected a string');
  });

  it.each<[string, string[], string]>([
    ['gap', [lines[0]!, '{"seq":3,"commit":true}'], 'line 2: expected sequence 2, got 3'],
    ['commit first', ['{"seq":1,"commit":true}'], 'line 1: a commit without an op'],
    ['two ops', [lines[0]!, lines[2]!.replace('"seq":3', '"seq":2')], 'line 2: an op before the previous commit'],
    ['unknown op', ['{"seq":1,"op":{"type":"retry"}}'], 'line 1.op.type: expected one of'],
    ['missing field', ['{"seq":1,"op":{"type":"invoke","run":[]}}'], 'missing field placement'],
    ['extra field', ['{"seq":1,"op":{"type":"cancel","reason":"x"}}'], 'unknown field reason'],
    ['commit value', ['{"seq":1,"op":{"type":"cancel"}}', '{"seq":2,"commit":false}'], 'line 2.commit: expected true'],
    ['bad line', ['{"seq":1', '{"seq":2,"commit":true}'], 'line 1: expected a JSON record'],
    ['blank line', [lines[0]!, '', lines[1]!], 'line 2: expected a JSON record'],
    ['payload', ['{"seq":1,"op":{"type":"start","input":"v"},"values":{"v":{"a":1}}}'], 'line 1.values.v: expected a string'],
  ])('rejects broken records: %s', (_, input, message) => {
    expect(() => parseRecords(input.join('\n') + '\n')).toThrow(TypeError);
    expect(() => parseRecords(input.join('\n') + '\n')).toThrow(message);
  });
});
