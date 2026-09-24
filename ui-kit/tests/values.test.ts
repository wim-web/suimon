import { describe, expect, it } from 'vitest';
import { formatPayload } from '../src/lib/values';

describe('formatPayload', () => {
  it('indents an ordinary payload as JSON.stringify does', () => {
    const payload = '{"id":7,"name":"Ada","tags":["a","b"],"address":{"city":"Kyoto","zip":null},"active":true,"score":-1.5}';
    expect(formatPayload(payload)).toBe(JSON.stringify(JSON.parse(payload), null, 2));
  });

  it('keeps every number as written, integers beyond 2^53 included', () => {
    expect(formatPayload('{"id":9007199254740993}')).toBe('{\n  "id": 9007199254740993\n}');
    expect(formatPayload('[123456789012345678901234567890,-9007199254740993,-0,1.50,1E+2,1e400]'))
      .toBe('[\n  123456789012345678901234567890,\n  -9007199254740993,\n  -0,\n  1.50,\n  1E+2,\n  1e400\n]');
  });

  it('keeps strings as written, with their escapes and the punctuation inside them', () => {
    const payload = String.raw`{"id":"a\"b\\c\/dé\n","text":"{ [1, 2] : x, }  ok"}`;
    expect(formatPayload(payload)).toBe(String.raw`{
  "id": "a\"b\\c\/dé\n",
  "text": "{ [1, 2] : x, }  ok"
}`);
  });

  it('keeps a repeated key', () => {
    expect(formatPayload('{"a":1,"a":2}')).toBe('{\n  "a": 1,\n  "a": 2\n}');
  });

  it('indents each level of nesting by two spaces, whatever the whitespace between tokens', () => {
    expect(formatPayload(' {"a" : [1, {"b":null}],\n\t"c":{"d":[true,false]}} \n')).toBe([
      '{',
      '  "a": [',
      '    1,',
      '    {',
      '      "b": null',
      '    }',
      '  ],',
      '  "c": {',
      '    "d": [',
      '      true,',
      '      false',
      '    ]',
      '  }',
      '}',
    ].join('\n'));
  });

  it('keeps empty objects and arrays compact', () => {
    expect(formatPayload('{}')).toBe('{}');
    expect(formatPayload('[ ]')).toBe('[]');
    expect(formatPayload('{"a":{ },"b":[],"c":[{}, []]}')).toBe('{\n  "a": {},\n  "b": [],\n  "c": [\n    {},\n    []\n  ]\n}');
  });

  it('returns text that is not a JSON object or array unchanged', () => {
    for (const payload of ['{"a":1,}', '{"a":', '[1 2]', '[01]', '{a:1}', "{'a':1}", '{"a":1} x', '{"a":"\t"}', 'plain text', '', ' "a string" ', '9007199254740993'])
      expect(formatPayload(payload)).toBe(payload);
  });
});
