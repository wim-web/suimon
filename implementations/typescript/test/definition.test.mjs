import assert from 'node:assert/strict';
import { readFileSync, readdirSync, mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';
import test from 'node:test';
import { parseDefinition, encodeDefinition, validateDefinition, checkDefinitionResources, deriveKinds, bodyInput, bodyContract, outputType, ValidationError } from '../dist/definition.js';
import { checkInput, parseJson, renderWire, renderLean, jsonEntries, JsonNumber } from '../dist/json.js';

const root = fileURLToPath(new URL('../../../', import.meta.url));
const read = path => readFileSync(join(root, path), 'utf8');
const fixture = name => JSON.parse(read(`Test/definitions/${name}.json`));
const workflow = (d, id) => d.workflows.find(w => w.id === id);
const placement = (w, name) => w.placements.find(p => p.name === name);
const connection = (w, source, target) => w.connections.find(c => c.source === source && c.target === target);
const task = (p, name) => p.node.tasks.find(t => t.name === name);
const minimal = () => ({ main: 'w', functions: [{ id: 'f', output: { single: 'T' } }], judges: [], transforms: [], workflows: [{ id: 'w', placements: [{ name: 'p', node: { type: 'function', function: 'f' }, policy: 'stop' }], connections: [] }] });
const concurrent = () => ({ ...minimal(), transforms: [{ id: 't', input: 'T', output: 'T' }], workflows: [{ id: 'w', placements: [{ name: 'c', policy: 'stop', node: { type: 'concurrency', limit: 1n, tasks: [{ name: 'a', body: { type: 'function', function: 'f' }, outputTransform: 't', policy: 'stop' }], output: 'list', element: 'T' } }], connections: [] }] });
const errorOf = source => {
  try { validateDefinition(parseDefinition(source)); return null; }
  catch (error) { return error.message; }
};
const sources = [
  'Test/definitions/merge.json', 'Test/definitions/branch.json', 'Test/definitions/users.json',
  'Test/definitions/chains/nested.json', 'Test/definitions/chains/alternating.json',
  'implementations/go/src/testdata/calls.json', 'implementations/go/src/testdata/fanout.json', 'implementations/go/src/testdata/limit.json',
];
const mutations = [
  ['duplicate placement', 'merge', d => { const w = workflow(d, 'dashboard'); w.placements.push(w.placements[0]); }, 'workflow dashboard: duplicate placement name'],
  ['unknown main', 'merge', d => { d.main = 'nope'; }, 'unknown main workflow nope'],
  ['unknown transform', 'merge', d => { connection(workflow(d, 'dashboard'), 'sales', 'archive').transform = 'nope'; }, 'dashboard: connection sales -> archive: unknown transform nope'],
  ['unknown output endpoint', 'users', d => { task(placement(workflow(d, 'users'), 'perUser'), 'profile').body.output = 'fetch'; }, 'users.perUser task profile: fetch is not an endpoint of workflow profileFlow'],
  ['transform input', 'merge', d => { connection(workflow(d, 'dashboard'), 'sales', 'archive').transform = 'stockWidget'; }, 'dashboard: connection sales -> archive: transform stockWidget takes Stock, but sales produces Sales'],
  ['transform output', 'merge', d => { connection(workflow(d, 'dashboard'), 'sales', 'archive').transform = 'salesWidget'; }, 'dashboard: connection sales -> archive: transform salesWidget returns Widget, but archive takes Sales'],
  ['entry type', 'users', d => { workflow(d, 'users').input = { type: { list: 'Org' }, placement: 'fetchAllUsers' }; }, 'users: entry fetchAllUsers: the input type List<Org> does not match the placement'],
  ['task input transform', 'users', d => { delete task(placement(workflow(d, 'users'), 'perUser'), 'orders').inputTransform; }, 'users.perUser task orders: an input transform is required'],
  ['task output transform', 'users', d => { task(placement(workflow(d, 'users'), 'perUser'), 'orders').outputTransform = 'profileSummary'; }, 'users.perUser task orders: transform profileSummary takes Profile, but the body produces Orders'],
  ['two inputs', 'merge', d => { const w = workflow(d, 'dashboard'); w.connections.push(connection(w, 'sales', 'archive')); }, 'dashboard.archive: needs exactly one input'],
  ['missing input', 'merge', d => { const w = workflow(d, 'dashboard'); w.connections = w.connections.filter(c => c.target !== 'archive'); }, 'dashboard.archive: needs exactly one input'],
  ['input to no input', 'merge', d => { workflow(d, 'dashboard').connections.push({ source: 'sales', target: 'stock', transform: 'sales' }); }, 'dashboard: connection sales -> stock: stock takes no input, so the transform must be discard'],
  ['Merge entry', 'merge', d => { workflow(d, 'dashboard').input = { type: 'Widget', placement: 'widgets' }; }, 'dashboard: entry widgets: Merge cannot be the entry'],
  ['discard with input', 'merge', d => { connection(workflow(d, 'dashboard'), 'sales', 'archive').transform = 'discard'; }, 'dashboard: connection sales -> archive: discard passes no value, but archive takes Sales'],
  ['two discard connections', 'merge', d => { workflow(d, 'dashboard').connections.push({ source: 'stock', target: 'notify', transform: 'discard' }); }, 'dashboard.notify: accepts at most one connection'],
  ['declared discard', 'merge', d => { d.transforms.push({ id: 'discard', input: 'A', output: 'A' }); }, 'discard is provided by the library and cannot be declared'],
  ['recursive call', 'users', d => { placement(workflow(d, 'profileFlow'), 'format').node = { type: 'subworkflow', workflow: 'profileFlow', output: 'format' }; }, 'workflows call each other in a cycle'],
  ['cycle', 'merge', d => { workflow(d, 'dashboard').connections.push({ source: 'archive', target: 'sales', transform: 'discard' }); }, 'workflow dashboard: connections contain a cycle'],
  ['waitStream on Single', 'merge', d => { placement(workflow(d, 'dashboard'), 'page').node = { type: 'waitStream', element: { list: 'Widget' } }; }, 'dashboard.page: waitStream needs a Stream input'],
  ['Merge of Stream', 'branch', d => { placement(workflow(d, 'shipping'), 'receipts').node = { type: 'merge', element: 'Receipt' }; }, 'shipping.receipts: Merge accepts only Single inputs (ship)'],
  ['Stream endpoint', 'branch', d => { const w = workflow(d, 'shipping'); w.connections = w.connections.filter(c => c.target !== 'receipts'); w.placements = w.placements.filter(p => p.name !== 'receipts'); }, 'workflow shipping: endpoint ship must be Single'],
  ['no connected arm', 'branch', d => { const w = workflow(d, 'shipping'); w.connections = w.connections.filter(c => c.target !== 'ship'); }, 'shipping.paid: at least one arm needs a connection'],
  ['unknown arm', 'branch', d => { connection(workflow(d, 'shipping'), 'paid', 'ship').arm = 'refunded'; }, 'shipping: connection paid -> ship: unknown arm refunded'],
  ['missing arm', 'branch', d => { delete connection(workflow(d, 'shipping'), 'paid', 'ship').arm; }, 'shipping: connection paid -> ship: a connection from a branch needs an arm'],
  ['arm outside branch', 'merge', d => { connection(workflow(d, 'dashboard'), 'sales', 'archive').arm = 'x'; }, 'dashboard: connection sales -> archive: only a connection from a branch has an arm'],
  ['zero limit', 'users', d => { placement(workflow(d, 'users'), 'perUser').node.limit = 0; }, 'users.perUser: limit must be positive'],
  ['no output task', 'users', d => { for (const t of placement(workflow(d, 'users'), 'perUser').node.tasks) delete t.outputTransform; }, 'users.perUser: at least one task must be in the output'],
  ['timeout aggregate', 'users', d => { placement(workflow(d, 'users'), 'all').timeout = { callMs: 10 }; }, 'users.all: a timeout is only for a function call or a branch judge'],
  ['element timeout Single', 'merge', d => { placement(workflow(d, 'dashboard'), 'sales').timeout = { elementMs: 10 }; }, 'dashboard.sales: an element timeout is only for a Stream function'],
  ['zero timeout', 'branch', d => { placement(workflow(d, 'shipping'), 'paid').timeout = { callMs: 0 }; }, 'shipping.paid: a timeout must be positive'],
  ['task timeout workflow', 'users', d => { task(placement(workflow(d, 'users'), 'perUser'), 'profile').timeout = { callMs: 5 }; }, 'users.perUser task profile: a timeout is only for a function call or a branch judge'],
  ['unknown judge', 'branch', d => { placement(workflow(d, 'shipping'), 'paid').node.judge = 'isFree'; }, 'shipping: connection list -> paid: paid has an unknown reference'],
  ['unknown judge placement', 'branch', d => { workflow(d, 'shipping').placements.push({ name: 'orphan', node: { type: 'branch', judge: 'nope', arms: ['a'] }, policy: 'stop' }); }, 'shipping.orphan: unknown judge nope'],
  ['duplicate arms', 'branch', d => { placement(workflow(d, 'shipping'), 'paid').node.arms = ['paid', 'paid']; }, 'shipping.paid: arms must be distinct non-empty names'],
  ['duplicate task', 'users', d => { const n = placement(workflow(d, 'users'), 'perUser').node; n.tasks.push(n.tasks[0]); }, 'users.perUser: duplicate task name'],
  ['unknown source', 'merge', d => { connection(workflow(d, 'dashboard'), 'sales', 'archive').source = 'x'; }, 'dashboard: connection x -> archive: unknown source'],
  ['empty workflow', 'merge', d => { workflow(d, 'dashboard').placements = []; }, 'workflow dashboard: no placements'],
  ['duplicate workflow', 'users', d => { d.workflows.push(workflow(d, 'profileFlow')); }, 'duplicate workflow id'],
  ['list type mismatch', 'users', d => { placement(workflow(d, 'users'), 'all').node = { type: 'waitStream', element: { list: { list: 'Summary' } } }; }, 'users: connection perUser -> all: transform summaries returns List<Summary>, but all takes List<List<Summary>>'],
];

const syntaxSources = [
  '', '{"main":"w",}', '{"main":"w","workflows":[]} x', String.raw`{"main":"\q"}`, String.raw`{"main":"é\u00zz"}`, '{"main":"a\u0001"}',
  String.raw`{"main":"\ud83d","workflows":[{"id":"\ude00","placements":[]}]}`, String.raw`{"main":"\ud83d\ude00","workflows":[]}`,
  '{"z":1,"main":"w","b":2}', '{"main":"w","functions":[{"id":"f","input":null,"output":{"single":"A"}}]}',
  '{"main":"w","workflows":[{"id":"","placements":[]}]}', '{"main":"w","limit":1e99999999999999999999}',
  '{"main":"x","main":"w","workflows":[]}', String.raw`{"main":"x","workflows":[],"\u006d\u0061in":"w"}`,
  String.raw`{"main":"w","workflows":[{"id":"w","placements":[],"\n'\u0001\u007f\"é":1,"\n'\u0001\u007f\"\u00e9":2}]}`,
  '{"main":"w","functions":[{"id":"f","output":{"single":{"list":{"list":{"lst":"A"}}}}}]}', '[1,2]',
  '{"main":"w","functions":[{"id":"","output":{"single":"A"}}]}', '{"main":"w","judges":[{"id":"","input":"A"}]}',
  '{"main":"w","transforms":[{"id":"","input":"A","output":"A"}]}', '{"main":"w","transforms":[{"id":"t","input":"A","output":{"list":""}}]}',
  '{"main":"w","workflows":[{"id":"w","input":{"type":"","placement":"a"},"placements":[]}]}',
];
const numberForms = ['2.0', '20e-1', '0.2e1', '0.0', '2.5', '-1', '1e-1', '1e-1000000000', '18446744073709551615', '18446744073709551616', '1e20', '1e1000000000', '0e1000000000', '-0', '1e1', '1.5e3', '1.8446744073709551616e19', '25e-1', '1e18446744073709551616', '1e18446744073709551617', '-0.000e999', '1e-', '1e+', '1.', '-', '01', '1.e0', '2E+2'];
const limitSource = value => encodeDefinition(concurrent()).replace('"limit":1', `"limit":${value}`);
const timeoutSource = value => encodeDefinition(minimal()).replace('"policy":"stop"', `"policy":"stop","timeout":{"callMs":${value}}`);

for (const path of sources) test(`definition fixture ${path}`, () => {
  const d = parseDefinition(read(path));
  validateDefinition(d);
  assert.deepEqual(parseDefinition(encodeDefinition(d)), d);
  const kinds = deriveKinds(d);
  for (const w of d.workflows) assert.equal(kinds.get(w.id).size, w.placements.length);
});
for (const [label, name, mutate, expected] of mutations) test(`validation first error ${label}`, () => {
  const d = fixture(name); mutate(d);
  assert.equal(errorOf(JSON.stringify(d)), expected);
});

test('canonical encoding agrees with current committed trace headers', () => {
  const directory = join(root, 'ui-kit/tests/fixtures');
  for (const file of readdirSync(directory).filter(f => f.endsWith('.records.jsonl'))) {
    const line = readFileSync(join(directory, file), 'utf8').split('\n')[0];
    const header = parseJson(line, 'trace');
    assert.equal(`{"definition":${encodeDefinition(parseDefinition(renderWire(header.definition)))},"validated":${header.validated}}`, line, file);
  }
});

test('exact uint64 definition numbers and integral notation', () => {
  for (const [form, expected] of [['2.0', 2n], ['20e-1', 2n], ['0.2e1', 2n], ['1.5e3', 1500n], ['18446744073709551615', (1n << 64n) - 1n]]) {
    const d = parseDefinition(limitSource(form));
    assert.equal(d.workflows[0].placements[0].node.limit, expected);
    validateDefinition(d);
    assert.equal(encodeDefinition(d).includes(`"limit":${expected}`), true);
  }
  for (const form of ['2.5', '-1', '1e-1', '1e-1000000000']) assert.match(errorOf(limitSource(form)), /expected a natural number$/);
  for (const form of ['18446744073709551616', '1e20', '1e1000000000']) assert.match(errorOf(limitSource(form)), /must be at most 18446744073709551615$/);
  for (const form of ['0.0', '0e1000000000', '-0']) assert.equal(errorOf(limitSource(form)), 'w.c: limit must be positive');
  assert.equal(parseDefinition(timeoutSource('1.5e3')).workflows[0].placements[0].timeout.callMs, 1500n);
});

test('strict shape errors and optional field omission', () => {
  assert.equal(errorOf('{"z":1,"main":"w","b":2}'), 'definition: unknown field b');
  assert.equal(errorOf('{"main":"w","functions":[{"id":"f","input":null,"output":{"single":"T"}}]}'), 'functions.f.input: a type is a name or {"list": type}');
  for (const key of ['functions', 'judges', 'transforms', 'workflows']) assert.equal(errorOf(`{"main":"w","${key}":null}`), `definition.${key}: expected an array`);
  const d = minimal(); d.workflows[0].placements[0].timeout = {};
  assert.equal(encodeDefinition(d).includes('timeout'), false);
  assert.deepEqual(parseDefinition('{"main":"w"}'), { main: 'w', functions: [], judges: [], transforms: [], workflows: [] });
});

test('definition and trace Unicode rules and offsets differ deliberately', () => {
  assert.equal(parseJson(String.raw`"\ud83d"`, 'definition'), '\ufffd');
  assert.equal(parseJson(String.raw`"\ude00"`, 'definition'), '\ufffd');
  assert.equal(parseJson(String.raw`"\ud83d\ude00"`, 'definition'), '😀');
  assert.equal(parseJson(String.raw`"\ud83d\u0041"`, 'definition'), '\ufffdA');
  assert.throws(() => parseJson(String.raw`"\ud83d"`, 'trace'), { message: 'unpaired high surrogate at offset 7' });
  assert.throws(() => parseJson(String.raw`"\ude00"`, 'trace'), { message: 'unpaired low surrogate at offset 7' });
  assert.throws(() => parseJson('{"é":1,"é":2}', 'definition'), { message: 'offset 12: duplicate key "é"' });
  assert.throws(() => parseJson('{"é":1,"é":2}', 'trace'), { message: 'duplicate key "é" at offset 10' });
  assert.throws(() => parseDefinition(new Uint8Array([0xff])), { message: 'definition: invalid UTF-8' });
  assert.throws(() => parseDefinition('\ud800'), { message: 'definition: invalid UTF-8' });
  assert.throws(() => parseJson('"\ud800"', 'trace'), /invalid UTF-8/);
  assert.throws(() => parseDefinition(new Uint8Array([0xef, 0xbb, 0xbf, 123, 125])), /offset 0: unexpected input/);
});

test('wire renderers preserve ordered opaque values and full numbers', () => {
  const value = parseJson(String.raw`{"2":"a","1":"b","__proto__":"safe","a":"\n\t\r\u0000\"\\é😀","n":18446744073709551616}`, 'trace');
  assert.deepEqual(jsonEntries(value).map(([key]) => key), ['2', '1', '__proto__', 'a', 'n']);
  assert.equal(Object.getPrototypeOf(value), null);
  assert.equal(renderWire(value), String.raw`{"2":"a","1":"b","__proto__":"safe","a":"\u000a\u0009\u000d\u0000\"\\é😀","n":18446744073709551616}`);
  assert.equal(renderLean({ '😀': '\n\r\t', '\ue000': 'x' }), '{"\ue000":"x","😀":"\\n\\r\\u0009"}');
  assert.equal(renderWire('\ud800'), '"\ufffd"');
  for (const source of ['-1', '1.0', '1e0', '01', '[1,]', '{} {}']) assert.throws(() => parseJson(source, 'trace'));
  for (const source of ['{"a":1,"a":2}', String.raw`{"a":1,"\u0061":2}`, '[{"a":{"b":[],"b":{}}}]']) assert.throws(() => parseJson(source, 'trace'), /duplicate key/);
  assert.equal(typeof parseJson('18446744073709551616', 'trace'), 'bigint');
  assert.ok(parseJson('0.5', 'definition') instanceof JsonNumber);
});

test('input limits count bytes and open containers while ignoring string punctuation', () => {
  checkInput(' '.repeat((1 << 20) - 2) + '{}');
  assert.throws(() => checkInput(' '.repeat(1 << 20) + 'é'), /maximum size of 1048576 bytes/);
  assert.doesNotThrow(() => parseJson('['.repeat(64) + '0' + ']'.repeat(64), 'trace'));
  assert.throws(() => parseJson('['.repeat(65) + '0' + ']'.repeat(65), 'trace'), /maximum nesting depth of 64/);
  assert.doesNotThrow(() => checkInput(JSON.stringify('['.repeat(1000) + '"\\[]')));
});

test('resource caps precede semantic validation and bound cyclic type objects', () => {
  const cases = [
    ['workflow', d => { d.workflows = Array.from({ length: 129 }, () => d.workflows[0]); }],
    ['declaration', d => { d.functions = Array.from({ length: 1025 }, () => d.functions[0]); }],
    ['placement', d => { d.workflows[0].placements = Array.from({ length: 1025 }, () => d.workflows[0].placements[0]); }],
    ['connection', d => { d.workflows[0].connections = Array.from({ length: 4097 }, () => ({ source: 'p', target: 'p', transform: 't' })); }],
    ['task', d => { const n = concurrent().workflows[0].placements[0].node; n.tasks = Array(1025).fill(n.tasks[0]); d.workflows[0].placements[0].node = n; }],
    ['arm', d => { d.workflows[0].placements[0].node = { type: 'branch', judge: 'j', arms: Array(1025).fill('a') }; }],
    ['name byte', d => { d.main = 'あ'.repeat(86); }],
    ['type depth', d => { let t = 'T'; for (let i = 0; i < 33; i++) t = { list: t }; d.functions[0].output = { single: t }; }],
    ['validation work', d => { const w = d.workflows[0]; w.placements = Array.from({ length: 151 }, (_, i) => ({ name: `p${i}`, node: { type: 'merge', element: 'T' }, policy: 'stop' })); w.connections = Array.from({ length: 300 }, (_, i) => ({ source: `p${Math.floor(i / 2)}`, target: `p${Math.floor(i / 2) + 1}`, transform: 't' })); }],
  ];
  for (const [label, mutate] of cases) {
    const d = minimal(); mutate(d);
    assert.throws(() => checkDefinitionResources(d), new RegExp(`definition: ${label} limit exceeded`), label);
    assert.throws(() => validateDefinition(d), new RegExp(`definition: ${label} limit exceeded`), label);
  }
  const d = minimal();
  const cycle = { list: 'T' }; cycle.list = cycle; d.functions[0].output = { single: cycle };
  assert.throws(() => checkDefinitionResources(d), /type depth limit exceeded/);
});

test('derivation is finite with unknown or cyclic references and does not mutate definitions', () => {
  const d = parseDefinition(read('Test/definitions/users.json')), before = encodeDefinition(d);
  const freeze = value => { if (typeof value === 'object' && value !== null) { Object.freeze(value); for (const v of Object.values(value)) freeze(v); } };
  freeze(d); validateDefinition(d);
  const kinds = deriveKinds(d);
  assert.equal(kinds.get('users').get('fetchAllUsers'), 'stream');
  assert.equal(kinds.get('users').get('perUser'), 'stream');
  assert.equal(kinds.get('users').get('all'), 'single');
  const b = task(placement(workflow(d, 'users'), 'perUser'), 'profile').body;
  assert.equal(bodyInput(d, b), 'UserId');
  assert.deepEqual(bodyContract(d, b), { single: 'Profile' });
  assert.deepEqual(outputType(d, 'users', 'all'), { list: { list: 'Summary' } });
  assert.equal(encodeDefinition(d), before);
  const cyc = minimal();
  cyc.workflows[0].placements[0].node = { type: 'subworkflow', workflow: 'w', output: 'p' };
  assert.equal(bodyContract(cyc, cyc.workflows[0].placements[0].node), undefined);
  assert.equal(deriveKinds(cyc).get('w').get('p'), 'single');
  cyc.workflows[0].connections.push({ source: 'p', target: 'p', transform: 'discard' });
  assert.equal(deriveKinds(cyc).get('w').size, 0);
  assert.throws(() => validateDefinition(cyc), ValidationError);
});

const oracle = process.env.SUIMON_GO_ORACLE;
test('Go differential acceptance, canonical headers, and first errors', { skip: !oracle }, () => {
  const dir = mkdtempSync(join(tmpdir(), 'suimon-definition-'));
  const all = sources.map(path => [path, read(path)]);
  for (const [label, name, mutate] of mutations) { const d = fixture(name); mutate(d); all.push([label, JSON.stringify(d)]); }
  for (const [i, text] of syntaxSources.entries()) all.push([`syntax ${i}`, text]);
  for (const form of numberForms) { all.push([`limit ${form}`, limitSource(form)]); all.push([`timeout ${form}`, timeoutSource(form)]); }
  try {
    for (const [i, [label, source]] of all.entries()) {
      const path = join(dir, `${i}.json`); writeFileSync(path, source);
      const result = spawnSync(oracle, ['validate', path], { encoding: 'utf8' });
      assert.ifError(result.error);
      const error = errorOf(source);
      assert.equal(error, result.status === 0 ? null : result.stderr.trimEnd(), label);
      if (error === null) {
        const generated = spawnSync(oracle, ['gen', path, '--steps', '0'], { encoding: 'utf8' });
        assert.equal(generated.status, 0, generated.stderr);
        assert.equal(generated.stdout.trimEnd(), `{"definition":${encodeDefinition(parseDefinition(source))},"validated":true}`, label);
      }
    }
  } finally { rmSync(dir, { recursive: true, force: true }); }
});
