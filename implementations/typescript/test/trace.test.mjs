import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdtempSync, readFileSync, readdirSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import test from 'node:test';
import { parseDefinition } from '../dist/definition.js';
import { MemoryJournal } from '../dist/journal.js';
import { initialState, step } from '../dist/machine.js';
import { checkTrace, encodeHeader, encodeOp, encodeRecord, encodeState, introduced } from '../dist/trace.js';

const fixtureRoot = new URL('../../../ui-kit/tests/fixtures/', import.meta.url);
const fixtureNames = readdirSync(fixtureRoot).filter(name => name.endsWith('.records.jsonl'));
const echoDefinition = parseDefinition(JSON.stringify({
  main: 'echo', functions: [{ id: 'echo', input: 'Text', output: { single: 'Text' } }],
  workflows: [{ id: 'echo', input: { type: 'Text', placement: 'echo' }, placements: [{ name: 'echo', node: { type: 'function', function: 'echo' }, policy: 'stop' }] }],
}));
const header = encodeHeader(echoDefinition, true) + '\n';
const start = '{"seq":1,"op":{"type":"start","input":"input"},"values":{"input":"opaque payload"}}\n{"seq":2,"commit":true}\n';

function recordOps(definition, operations) {
  let state = initialState();
  const lines = [encodeHeader(definition, true)];
  let seq = 1;
  for (const op of operations) {
    const after = step(definition, state, op);
    const values = introduced(state, after).map(value => ({ value, payload: `opaque ${value}\n🍣` }));
    lines.push(encodeRecord({ seq: seq++, op, values }), encodeRecord({ seq: seq++, commit: true }));
    state = after;
  }
  return { text: lines.join('\n') + '\n', state };
}

for (const name of fixtureNames) {
  test(`replays ${name} to its exact Lean state`, () => {
    const bytes = readFileSync(new URL(name, fixtureRoot));
    const checked = checkTrace(bytes);
    const state = readFileSync(new URL(name.replace('.records.jsonl', '.state.json'), fixtureRoot), 'utf8').trimEnd();
    assert.equal(encodeState(checked.state), state);
    assert.equal(checked.length < bytes.length, name === 'users-c.records.jsonl');
    assert.equal(checked.committed, (bytes.subarray(0, checked.length).toString('utf8').trimEnd().split('\n').length - 1) / 2);
    const [headerLine, ...lines] = bytes.subarray(0, checked.length).toString('utf8').trimEnd().split('\n');
    assert.equal(encodeHeader(checked.definition, checked.validated), headerLine);
    for (const line of lines) {
      const parsed = JSON.parse(line);
      const record = 'op' in parsed ? { seq: parsed.seq, op: parsed.op, values: Object.entries(parsed.values ?? {}).map(([value, payload]) => ({ value, payload })) } : parsed;
      assert.equal(encodeRecord(record), line);
    }
  });
}

test('recovers only committed UTF-8 bytes at every crash cut', () => {
  let state = step(echoDefinition, initialState(), { type: 'start', input: '入力🍣' });
  state = step(echoDefinition, state, { type: 'invoke', run: [], placement: 'echo' });
  const call = state.calls[0].id;
  const trace = recordOps(echoDefinition, [
    { type: 'start', input: '入力🍣' },
    { type: 'invoke', run: [], placement: 'echo' },
    { type: 'returned', call, value: '応答🍣' },
    { type: 'settle', run: [], placement: 'echo' },
    { type: 'conclude' },
  ]);
  const bytes = Buffer.from(trace.text);
  const boundaries = [{ length: 0, committed: 0, definition: false, state: initialState() }];
  let offset = 0;
  for (const [index, line] of trace.text.trimEnd().split('\n').entries()) {
    offset += Buffer.byteLength(line) + 1;
    if (index === 0 || index % 2 === 0) {
      const checked = checkTrace(bytes.subarray(0, offset));
      boundaries.push({ length: offset, committed: checked.committed, definition: true, state: checked.state });
    }
  }
  let boundaryIndex = 0;
  for (let cut = 0; cut <= bytes.length; cut++) {
    while (boundaries[boundaryIndex + 1]?.length <= cut) boundaryIndex++;
    const expected = boundaries[boundaryIndex];
    const checked = checkTrace(bytes.subarray(0, cut));
    assert.equal(checked.length, expected.length, `cut ${cut}`);
    assert.equal(checked.committed, expected.committed, `cut ${cut}`);
    assert.equal(checked.definition !== null, expected.definition, `cut ${cut}`);
    assert.deepEqual(checked.state, expected.state, `cut ${cut}`);
  }
  assert.deepEqual(checkTrace(trace.text).state, trace.state);
  assert.equal(checkTrace(trace.text).length, bytes.length);
});

test('rejects corrupt complete lines while ignoring an incomplete last line', () => {
  const broken = '{"seq":3,"op":';
  assert.equal(checkTrace(header + start + broken).committed, 1);
  assert.throws(() => checkTrace(header + start + broken + '\n'), /line 4:/);
  const invalidUtf8 = Buffer.concat([Buffer.from(header + start + '{"seq":3,"op":{"type":"start","input":"'), Buffer.from([0xff])]);
  assert.equal(checkTrace(invalidUtf8).committed, 1);
  assert.throws(() => checkTrace(Buffer.concat([invalidUtf8, Buffer.from('"}}\n')])), /line 4: invalid UTF-8/);
  const withBom = Buffer.concat([Buffer.from([0xef, 0xbb, 0xbf]), Buffer.from(header)]);
  assert.throws(() => checkTrace(withBom), /line 1:/);
});

test('validates pending record syntax without applying its operation or payload checks', () => {
  const uncommitted = '{"seq":1,"op":{"type":"returned","call":"missing","value":"new"},"values":{"stray":"anything"}}\n';
  assert.equal(checkTrace(header + uncommitted).length, Buffer.byteLength(header));
  assert.throws(() => checkTrace(header + uncommitted + '{"seq":2,"commit":true}\n'), /line 3: rejected .*NOT_RUNNING/);
  assert.throws(() => checkTrace(header + '{"seq":1,"op":{"type":"returned","call":"missing"}}\n'), /op: missing field value/);
  assert.doesNotThrow(() => checkTrace(header + '{"seq":1,"op":{"type":"taskOutputFailed","execution":"e","task":"t","index":999999999999999999999999999999999}}\n'));
});

test('rejects sequence, record, operation, and payload corruption', () => {
  const cases = [
    ['{"seq":1,"commit":true}\n', /a commit without an op/],
    ['{"seq":0,"op":{"type":"start"}}\n', /expected sequence 1, got 0/],
    ['{"seq":999999999999999999999,"commit":true}\n', /expected sequence 1, got 999999999999999999999/],
    ['{"seq":-1,"commit":true}\n', /line 2:/],
    ['{"seq":1.0,"commit":true}\n', /line 2:/],
    ['{"seq":1e0,"commit":true}\n', /line 2:/],
    ['{"seq":1,"seq":1,"op":{"type":"start"}}\n', /duplicate key/],
    ['{"seq":1,"op":{"type":"start","type":"cancel"}}\n', /duplicate key/],
    ['{"seq":1,"op":{"type":"start","input":"input"},"values":{"input":"x","input":"y"}}\n', /duplicate key/],
    ['{"seq":1,"op":{"type":"start","input":null}}\n', /op.input: expected a string/],
    ['{"seq":1,"op":{"type":"closeRun","run":[1]}}\n', /op.run: expected an array of strings/],
    ['{"seq":1,"op":{"type":"start","unknown":1}}\n', /op start: unknown field unknown/],
    ['{"seq":1,"op":{"type":"jump"}}\n', /unknown op type jump/],
    ['{"seq":1,"op":{"type":"start"},"values":[]}\n', /record.values: expected an object/],
    ['{"seq":1,"op":{"type":"start"},"values":{"v":1}}\n', /record.values.v: expected a string/],
    ['{"seq":1,"commit":false}\n', /record: either an op or a commit/],
    ['{"seq":1,"commit":true,"op":{"type":"cancel"}}\n', /record: either an op or a commit/],
    ['{"seq":1,"commit":true,"values":{}}\n', /record: unknown field values/],
    ['{"seq":1,"op":{"type":"start","input":"input"}}\n{"seq":2,"commit":true}\n', /missing payloads for \[input\]/],
    ['{"seq":1,"op":{"type":"start","input":"input"},"values":{"other":"x"}}\n{"seq":2,"commit":true}\n', /payloads for \[other\], which the transition does not introduce/],
    ['{"seq":1,"op":{"type":"start","input":"input"}}\n{"seq":2,"op":{"type":"cancel"}}\n', /an op before the previous commit/],
    [start + '{"seq":3,"op":{"type":"invoke","run":[],"placement":"echo"},"values":{"input":"again"}}\n{"seq":4,"commit":true}\n', /payloads for \[input\], which the transition does not introduce/],
    ['{"seq":1,"op":{"type":"start","input":"\\ud800"}}\n', /surrogate/],
    ['{"seq":1,"op":{"type":"start","input":"\\udfff"}}\n', /surrogate/],
  ];
  for (const [suffix, message] of cases) assert.throws(() => checkTrace(header + suffix), message, suffix);
  assert.equal(checkTrace(header + start).values[0].payload, 'opaque payload');
  assert.throws(() => checkTrace(header + '{"seq":1,"op":{"type":"start","input":"' + String.fromCharCode(0xd800) + '"}}\n'), /invalid UTF-8/);
});

test('preserves original header mode and compares canonical definitions', () => {
  const invalid = parseDefinition('{"main":"missing","workflows":[]}');
  assert.equal(checkTrace(encodeHeader(invalid, false) + '\n', invalid).validated, false);
  assert.throws(() => checkTrace(encodeHeader(invalid, true) + '\n'), /unknown main workflow missing/);
  assert.throws(() => checkTrace(header, invalid), /another definition/);
  const raw = JSON.parse(header);
  const reformatted = JSON.stringify({ validated: raw.validated, definition: raw.definition }, null, 0) + '\n';
  assert.equal(checkTrace(reformatted, echoDefinition).validated, true);
  assert.throws(() => checkTrace('{"definition":{},"validated":null}\n'), /header.validated: expected a boolean/);
  assert.throws(() => checkTrace('{"definition":{},"validated":false,"seq":0}\n'), /header: unknown field seq/);
  assert.throws(() => checkTrace(header + header), /line 2: record: missing field seq/);
});

test('writes every operation with canonical field order and optional omissions', () => {
  const operations = [
    { type: 'start' }, { input: '', type: 'start' },
    { placement: 'p', run: ['🍣'], type: 'invoke' }, { trigger: '', placement: 'p', run: [], type: 'invoke' },
    ...['fetch', 'ended', 'failed', 'lost', 'terminated'].map(type => ({ call: 'c', type })),
    ...['returned', 'yielded'].map(type => ({ value: 'v', call: 'c', type })),
    { arm: 'a', call: 'c', type: 'judged' }, { element: false, call: 'c', type: 'timedOut' },
    { source: 's', connection: 0, run: [], type: 'deliver' },
    { value: '', source: 's', connection: 0, run: [], type: 'deliver' },
    { source: 's', connection: 0, run: [], type: 'transformFailed' },
    { task: 't', execution: 'e', type: 'taskInput' }, { value: '', task: 't', execution: 'e', type: 'taskInput' },
    ...['taskInputFailed', 'beginTask'].map(type => ({ task: 't', execution: 'e', type })),
    { value: 'v', index: 0, task: 't', execution: 'e', type: 'taskOutput' },
    { index: 0, task: 't', execution: 'e', type: 'taskOutputFailed' },
    { placement: 'p', run: [], type: 'settle' }, { execution: 'e', type: 'closeExecution' },
    { run: [], type: 'closeRun' }, { type: 'cancel' }, { type: 'conclude' },
  ];
  for (const op of operations) {
    const encoded = encodeOp(op);
    assert.match(encoded, /^\{"type":/);
    assert.deepEqual(JSON.parse(encoded), op);
    assert.doesNotThrow(() => checkTrace(header + encodeRecord({ seq: 1, op, values: [] }) + '\n'));
  }
  assert.equal(encodeOp({ trigger: '', placement: 'p', run: [], type: 'invoke' }), '{"type":"invoke","run":[],"placement":"p","trigger":""}');
  assert.equal(encodeRecord({ seq: 6, commit: true }), '{"seq":6,"commit":true}');
  assert.equal(encodeRecord({ seq: 5, op: { type: 'deliver', run: ['a'], connection: 3, source: 's"\\\n\u0001\u007f<é>', value: 'v' }, values: [{ value: 'v', payload: 'p\t' }] }), '{"seq":5,"op":{"type":"deliver","run":["a"],"connection":3,"source":"s\\"\\\\\\u000a\\u0001\u007f<é>","value":"v"},"values":{"v":"p\\u0009"}}');
});

test('keeps numeric and prototype-like payload IDs in record order', () => {
  const values = [{ value: '2', payload: 'second' }, { value: '1', payload: 'first' }, { value: '__proto__', payload: 'prototype' }];
  const record = encodeRecord({ seq: 1, op: { type: 'start', input: 'input' }, values });
  assert.match(record, /"values":\{"2":"second","1":"first","__proto__":"prototype"\}/);
  assert.throws(() => checkTrace(header + record + '\n{"seq":2,"commit":true}\n'), /payloads for \[2, 1, __proto__\]/);
  const prototype = encodeRecord({ seq: 1, op: { type: 'start', input: '__proto__' }, values: [{ value: '__proto__', payload: 'opaque' }] });
  assert.deepEqual(checkTrace(header + prototype + '\n{"seq":2,"commit":true}\n').values, [{ value: '__proto__', payload: 'opaque' }]);
  assert.throws(() => encodeRecord({ seq: 1, op: { type: 'start' }, values: [{ value: 'same', payload: 'x' }, { value: 'same', payload: 'y' }] }), /duplicate payloads/);
  for (const invalid of [{ value: String.fromCharCode(0xd800), payload: 'x' }, { value: 'x', payload: String.fromCharCode(0xdfff) }]) {
    assert.throws(() => encodeRecord({ seq: 1, op: { type: 'start' }, values: [invalid] }), /not valid UTF-8/);
  }
});

test('bounds complete line input size and nesting', () => {
  assert.throws(() => checkTrace(header + '{"seq":1,"op":{"type":"start","input":"' + 'x'.repeat(1 << 20) + '"}}\n'), /maximum size/);
  assert.throws(() => checkTrace(header + '['.repeat(65) + ']'.repeat(65) + '\n'), /maximum nesting depth/);
  assert.doesNotThrow(() => checkTrace('['.repeat(65)));
});

test('MemoryJournal owns byte copies and bounds reads before returning storage', async () => {
  const initial = Buffer.from('abc');
  const journal = new MemoryJournal(initial);
  initial.fill(0);
  const appended = Buffer.from('def');
  await journal.append(appended);
  appended.fill(0);
  await journal.sync();
  await assert.rejects(journal.contents(5), /journal bytes exceeds limit 5/);
  const first = await journal.contents(6);
  assert.equal(Buffer.from(first).toString(), 'abcdef');
  first.fill(0);
  assert.equal(Buffer.from(await journal.contents(6)).toString(), 'abcdef');
  await journal.truncate(4);
  await journal.append(Buffer.from('XY'));
  assert.equal(Buffer.from(await journal.contents(6)).toString(), 'abcdXY');
  await journal.truncate(0);
  assert.equal((await journal.contents(0)).length, 0);
  await assert.rejects(journal.truncate(1), RangeError);
  await assert.rejects(journal.truncate(-1), RangeError);
  await assert.rejects(journal.truncate(0.5), RangeError);
  await assert.rejects(journal.contents(-1), RangeError);
  await assert.rejects(journal.contents(Infinity), RangeError);
  const utf8 = new MemoryJournal('🍣');
  assert.equal((await utf8.contents(4)).length, 4);
  await utf8.truncate(2);
  assert.deepEqual(await utf8.contents(2), new Uint8Array([0xf0, 0x9f]));
});

for (const [name, binary] of [['Go', process.env.SUIMON_GO_CLI], ['Lean', process.env.SUIMON_LEAN_CLI]]) {
  test(`${name} accepts TypeScript writers and generated traces replay identically`, { skip: !binary }, () => {
    const temp = mkdtempSync(join(tmpdir(), 'suimon-trace-'));
    try {
      const path = join(temp, 'trace.jsonl');
      for (const fixture of fixtureNames) {
        const text = readFileSync(new URL(fixture, fixtureRoot), 'utf8');
        const checked = checkTrace(text);
        writeFileSync(path, text);
        const state = execFileSync(binary, ['check', path, '--state'], { encoding: 'utf8' }).trimEnd();
        assert.equal(encodeState(checked.state), state, fixture);
      }
      for (const suffix of [
        start,
        start + '{"seq":3,"op":',
        start + '{"seq":3,"op":\n',
        '{"seq":1,"op":{"type":"start","input":"input"}}\n{"seq":2,"commit":true}\n',
        '{"seq":1,"op":{"type":"start","input":"input"},"values":{"other":"stray"}}\n{"seq":2,"commit":true}\n',
        '{"seq":1,"op":{"type":"start","input":"input"},"values":{"input":"first","input":"again"}}\n',
      ]) {
        const text = header + suffix;
        writeFileSync(path, text);
        const oracle = spawnSync(binary, ['check', path, '--state'], { encoding: 'utf8' });
        if (oracle.status === 0) assert.equal(encodeState(checkTrace(text).state), oracle.stdout.trimEnd());
        else assert.throws(() => checkTrace(text), undefined, `${name} rejects ${suffix}`);
      }
      const definitionPath = join(temp, 'definition.json');
      for (const source of ['users', 'merge', 'branch', 'chains/nested', 'chains/alternating']) {
        const definitionText = readFileSync(new URL(`../../../Test/definitions/${source}.json`, import.meta.url), 'utf8');
        writeFileSync(definitionPath, definitionText);
        for (const seed of [1, 7, 31]) {
          const trace = execFileSync(binary, ['gen', definitionPath, '--seed', String(seed), '--steps', '250'], { encoding: 'utf8' });
          const checked = checkTrace(trace);
          writeFileSync(path, trace);
          const state = execFileSync(binary, ['check', path, '--state'], { encoding: 'utf8' }).trimEnd();
          assert.equal(encodeState(checked.state), state, `${source} seed ${seed}`);
          const [head, ...lines] = trace.trimEnd().split('\n');
          assert.equal(encodeHeader(checked.definition, checked.validated), head);
          const rewritten = [head, ...lines.map(line => {
            const parsed = JSON.parse(line);
            return encodeRecord('op' in parsed ? { ...parsed, values: Object.entries(parsed.values ?? {}).map(([value, payload]) => ({ value, payload })) } : parsed);
          })].join('\n') + '\n';
          assert.equal(rewritten, trace, `${source} canonical writers`);
          writeFileSync(path, rewritten);
          assert.equal(execFileSync(binary, ['check', path, '--state'], { encoding: 'utf8' }).trimEnd(), state);
        }
      }
    } finally {
      rmSync(temp, { recursive: true, force: true });
    }
  });
}
