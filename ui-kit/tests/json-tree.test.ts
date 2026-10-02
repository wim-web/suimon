import { expect, it } from 'vitest';
import { jsonDocument, jsonMembers } from '../src/lib/json-tree';

it('keeps duplicate fields, number lexemes and escaped strings intact', () => {
  const payload = String.raw` {"n":9007199254740993,"n":1e400,"s":"a\"b\\c\n","nested":[-0,1.50,{"__proto__":true}]} `;
  const document = jsonDocument(payload)!;
  const members = jsonMembers(document, document.root);
  expect(members.map(m => m.label)).toEqual(['"n"', '"n"', '"s"', '"nested"']);
  expect(members.slice(0, 3).map(m => payload.slice(m.value.start, m.value.end))).toEqual(['9007199254740993', '1e400', String.raw`"a\"b\\c\n"`]);
  const nested = jsonMembers(document, members[3]!.value);
  expect(nested.map(m => payload.slice(m.value.start, m.value.end))).toEqual(['-0', '1.50', '{"__proto__":true}']);
  expect(jsonMembers(document, nested[2]!.value)[0]!.label).toBe('"__proto__"');
});

it('rejects malformed JSON and reads empty containers and primitives', () => {
  for (const payload of ['plain text', '', '{"a":1,}', '[1 2]', '{a:1}', 'true false']) expect(jsonDocument(payload)).toBeNull();
  for (const payload of ['{}', '[]', ' true ', '"x"', '-1.2e3', 'null']) {
    const doc = jsonDocument(payload)!;
    expect(doc).not.toBeNull();
    expect(jsonMembers(doc, doc.root)).toEqual([]);
  }
});

it('indexes only the requested nesting level without recursively building a tree', () => {
  const payload = '['.repeat(10_000) + '0' + ']'.repeat(10_000);
  const doc = jsonDocument(payload)!;
  const children = jsonMembers(doc, doc.root);
  expect(children).toEqual([{ label: '[0]', value: { kind: 'array', start: 1, end: payload.length - 1 } }]);
});
