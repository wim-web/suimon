import { describe, expect, it } from 'vitest';
import { parseDefinition, parseRecordLog, parseRecords, parseState } from '../src/lib/parse';
import { clone, definition, definitionJson, definitionText, recordText, stateJson } from './helpers';

type Json = Record<string, any>;

describe('parseDefinition', () => {
  it('accepts the example definitions and normalizes optional lists', () => {
    for (const name of ['users', 'branch', 'merge']) expect(definition(name).workflows.length).toBeGreaterThan(0);
    const users = definition('users');
    expect(users.judges).toEqual([]);
    expect(users.workflows[1]!.connections).toHaveLength(1);
    const perUser = users.workflows[0]!.placements[1]!.node;
    expect(perUser.type === 'concurrency' && perUser.tasks[1]!.timeout).toEqual({ callMs: 5000 });
  });

  it.each<[string, (p: Json) => void, string]>([
    ['unknown field', p => { p.extra = 1; }, 'definition: unknown field extra'],
    ['main', p => { p.main = 'nowhere'; }, 'definition.main: unknown workflow nowhere'],
    ['node type', p => { p.workflows[0].placements[0].node.type = 'loop'; }, 'definition.workflows[shipping].placements[list].node.type: expected one of'],
    ['policy', p => { delete p.workflows[0].placements[1].policy; }, 'placements[paid]: missing field policy'],
    ['arm', p => { delete p.workflows[0].connections[1].arm; }, 'connections[1]: a connection from a branch needs an arm'],
    ['unknown arm', p => { p.workflows[0].connections[1].arm = 'later'; }, 'connections[1].arm: unknown arm later'],
    ['target', p => { p.workflows[0].connections[0].target = 'gone'; }, 'connections[0].target: unknown placement gone'],
    ['timeout', p => { p.workflows[0].placements[0].timeout.callMs = 0; }, 'timeout.callMs: expected a positive integer'],
    ['large timeout', p => { p.workflows[0].placements[0].timeout.callMs = 2 ** 65; }, 'timeout.callMs: must be at most 18446744073709551615'],
    ['type', p => { p.functions[0].output = { stream: '' }; }, 'definition.functions[0].output.stream: empty string'],
  ])('rejects a broken definition: %s', (_, edit, message) => {
    const json = clone(definitionJson('branch')) as Json;
    edit(json);
    expect(() => parseDefinition(json)).toThrow(TypeError);
    expect(() => parseDefinition(json)).toThrow(message);
  });

  it('accepts a timeout up to 2^64 - 1, as Lean and Go do', () => {
    const json = clone(definitionJson('branch')) as Json;
    json.workflows[0].placements[0].timeout.callMs = 2 ** 60;
    expect(parseDefinition(json).workflows[0]!.placements[0]!.timeout?.callMs).toBe(2 ** 60);
  });

  it('reads the text of a definition file, in which no object may repeat a key', () => {
    for (const name of ['users', 'branch', 'merge']) expect(parseDefinition(definitionText(name))).toEqual(definition(name));
    // A key may repeat in other objects, and a string may look like a repeated key.
    const text = '{"main":"w","transforms":[{"id":"t,{\\"id\\":1,\\"id\\":[]}","input":"A","output":"A"}],' +
      '"workflows":[{"id":"w","placements":[{"name":"a","node":{"type":"merge","element":"T"},"policy":"stop"},' +
      '{"name":"b","node":{"type":"merge","element":"T"},"policy":"stop"}]}]}';
    expect(parseDefinition(text).transforms[0]!.id).toBe('t,{"id":1,"id":[]}');
  });

  it.each<[string, string, string]>([
    ['at the top', '{"main":"x","main":"w","workflows":[]}', 'definition: duplicate key "main"'],
    ['nested', '{"main":"w","workflows":[{"id":"w","placements":[{"name":"a","node":{"type":"merge","element":"T","type":"merge"},"policy":"stop"}]}]}',
      'definition: duplicate key "type"'],
    ['after escapes', '{"main":"x","workflows":[],"\\u006d\\u0061in":"w"}', 'definition: duplicate key "main"'],
    ['quoted', '{"main":"w","workflows":[],"\\n\\"":1,"\\n\\"":2}', 'definition: duplicate key "\\n\\""'],
    ['not JSON', '{"main":"w",}', 'definition: expected a JSON definition'],
  ])('rejects definition text: %s', (_, text, message) => {
    expect(() => parseDefinition(text)).toThrow(TypeError);
    expect(() => parseDefinition(text)).toThrow(message);
  });

  it('checks the workflows that placements and tasks call', () => {
    const json = clone(definitionJson('users')) as Json;
    json.workflows[0].placements[1].node.tasks[0].body.output = 'missing';
    expect(() => parseDefinition(json)).toThrow('tasks[profile].body: workflow profileFlow has no placement missing');
    json.workflows[0].placements[1].node.tasks[0].body.workflow = 'other';
    expect(() => parseDefinition(json)).toThrow('unknown workflow other');
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
  // The header, then the records.
  const [header, ...lines] = text.slice(0, -1).split('\n') as [string, ...string[]];
  const withHeader = (records: string[]) => [header, ...records].join('\n') + '\n';

  it('reads JSON lines, arrays of lines and arrays of records', () => {
    expect(text.endsWith('\n')).toBe(true);
    const parsed = parseRecords(text);
    expect(parsed).toHaveLength(lines.length);
    expect(parsed[0]).toEqual({ seq: 1, op: { type: 'start', input: '5:value5:input' }, values: { '5:value5:input': '5:value5:input' } });
    expect(parsed[1]).toEqual({ seq: 2, commit: true });
    expect(parseRecordLog(text)).toEqual({ definition: definition('users'), records: parsed, tail: '' });
    expect(parseRecords([header, ...lines])).toEqual(parsed);
    expect(parseRecords([header, ...lines].map(line => JSON.parse(line)))).toEqual(parsed);
  });

  it('reads the definition from the header, the first line only', () => {
    expect(parseRecordLog(header + '\n')).toEqual({ definition: definition('users'), records: [], tail: '' });
    // A crash inside the header leaves no complete line, and no definition yet.
    expect(parseRecordLog(header.slice(0, 40))).toEqual({ definition: null, records: [], tail: header.slice(0, 40) });
    expect(() => parseRecords(lines.slice(0, 2).join('\n') + '\n')).toThrow('line 1: expected the header with the definition');
    expect(() => parseRecords(lines.slice(0, 2))).toThrow('records[0]: expected the header with the definition');
    expect(() => parseRecords('{"definition":{"main":"w","workflows":[]}}\n')).toThrow('line 1: definition.main: unknown workflow w');
    expect(() => parseRecords('{"definition":{"main":"w"},"seq":1}\n')).toThrow('line 1: unknown field seq');
    expect(() => parseRecords(withHeader([header]))).toThrow('line 2: the header must be the first line');
    expect(() => parseRecords(withHeader([lines[0]!, lines[1]!, header]))).toThrow('line 4: the header must be the first line');
  });

  it('rejects a line in which an object repeats a key, the definition of the header included', () => {
    expect(() => parseRecords(header.replace('"main":', '"main":"x","main":') + '\n')).toThrow('line 1: duplicate key "main"');
    expect(() => parseRecords(header.replace('"policy":', '"policy":"stop","policy":') + '\n')).toThrow('line 1: duplicate key "policy"');
    expect(() => parseRecords([header, '{"seq":1,"seq":1,"op":{"type":"start"}}'])).toThrow('records[1]: duplicate key "seq"');
    // A payload may look like a repeated key; the same key in another object is not repeated.
    const payload = '{"seq":1,"op":{"type":"start","input":"v"},"values":{"v":"{\\"a\\":1,\\"a\\":2}"}}';
    expect(parseRecords(withHeader([payload]))[0]).toMatchObject({ values: { v: '{"a":1,"a":2}' } });
    // The torn tail is not read.
    expect(parseRecordLog(withHeader(lines.slice(0, 2)) + '{"seq":3,"seq":3').tail).toBe('{"seq":3,"seq":3');
  });

  it('keeps the payloads of engine-built lists in the op record that built them', () => {
    const settle = parseRecords(recordText('branch-a')).find(r => 'op' in r && r.op.type === 'settle' && r.op.placement === 'receipts');
    expect(settle && 'values' in settle && Object.keys(settle.values!)).toEqual([expect.stringMatching(/^4:list/)]);
  });

  it('keeps an op without its commit at the end', () => {
    expect(parseRecords(withHeader(lines.slice(0, 3))).at(-1)).toMatchObject({ seq: 3, op: { type: 'invoke' } });
  });

  it('never commits the text after the last newline, even when it parses', () => {
    const c = recordText('users-c');
    expect(c.endsWith('\n')).toBe(false);
    const log = parseRecordLog(c);
    expect(log.records).toHaveLength(81);
    expect(log.records.at(-1)).toMatchObject({ seq: 81, op: { type: 'taskOutput' } });
    expect(log.tail).toBe('{"seq":82,"commit":true}');
    expect(parseRecords(withHeader(lines.slice(0, 4)) + lines[4]!.slice(0, 20))).toHaveLength(4);
    expect(parseRecordLog([header, lines[0]!].join('\n'))).toEqual({ definition: definition('users'), records: [], tail: lines[0] });
    expect(parseRecordLog('')).toEqual({ definition: null, records: [], tail: '' });
    // An array holds complete lines; a host passes the tail it split off as an option.
    expect(parseRecordLog([header, ...lines.slice(0, 81)], { tail: lines[81] })).toEqual(log);
    expect(() => parseRecords([header.slice(0, 20)])).toThrow('records[0]: expected a JSON record');
    expect(() => parseRecordLog([], { tail: 1 as unknown as string })).toThrow('options.tail: expected a string');
  });

  it.each<[string, string[], string]>([
    ['gap', [lines[0]!, '{"seq":3,"commit":true}'], 'line 3: expected sequence 2, got 3'],
    ['commit first', ['{"seq":1,"commit":true}'], 'line 2: a commit without an op'],
    ['two ops', [lines[0]!, lines[2]!.replace('"seq":3', '"seq":2')], 'line 3: an op before the previous commit'],
    ['unknown op', ['{"seq":1,"op":{"type":"retry"}}'], 'line 2.op.type: expected one of'],
    ['missing field', ['{"seq":1,"op":{"type":"invoke","run":[]}}'], 'missing field placement'],
    ['extra field', ['{"seq":1,"op":{"type":"cancel","reason":"x"}}'], 'unknown field reason'],
    ['commit value', ['{"seq":1,"op":{"type":"cancel"}}', '{"seq":2,"commit":false}'], 'line 3.commit: expected true'],
    ['bad line', ['{"seq":1', '{"seq":2,"commit":true}'], 'line 2: expected a JSON record'],
    ['blank line', [lines[0]!, '', lines[1]!], 'line 3: expected a JSON record'],
    ['payload', ['{"seq":1,"op":{"type":"start","input":"v"},"values":{"v":{"a":1}}}'], 'line 2.values.v: expected a string'],
    ['repeated key', ['{"seq":1,"seq":1,"op":{"type":"start"}}'], 'line 2: duplicate key "seq"'],
    ['repeated op key', ['{"seq":1,"op":{"type":"start","type":"cancel"}}'], 'line 2: duplicate key "type"'],
    ['repeated payload key', ['{"seq":1,"op":{"type":"start","input":"v"},"values":{"v":"a","v":"b"}}'], 'line 2: duplicate key "v"'],
    ['repeated escaped key', ['{"seq":1,"\\u0073eq":1,"op":{"type":"start"}}'], 'line 2: duplicate key "seq"'],
  ])('rejects broken records: %s', (_, input, message) => {
    expect(() => parseRecords(withHeader(input))).toThrow(TypeError);
    expect(() => parseRecords(withHeader(input))).toThrow(message);
  });
});
