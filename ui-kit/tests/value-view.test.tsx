import { renderToStaticMarkup } from 'react-dom/server';
import { expect, it, vi } from 'vitest';
import { ValueView, PayloadText } from '../src/components/ValueView';
import { RecordInspector } from '../src/components/RecordInspector';
import type * as values from '../src/lib/values';
import * as json from '../src/lib/json-tree';
import type { Transition } from '../src/types';

it('does no JSON parsing while closed, even for multi-megabyte JSON', () => {
  const format = vi.spyOn(json, 'jsonDocument');
  try {
    const payload = '{"items":[' + '"some value",'.repeat(500_000) + 'null]}';
    const html = renderToStaticMarkup(<ValueView value={{ kind: 'payload', id: 'v', payload }} label="result" />);
    expect(html).toContain('characters');
    expect(html).not.toContain('some value');
    expect(html).not.toContain('<pre>');
    expect(format).not.toHaveBeenCalled();
  } finally { format.mockRestore(); }
});

it('does not visit a closed list, including descendants or members without payloads', () => {
  const items = new Proxy(new Array<string>(100_000), { get(target, key, receiver) {
    if (typeof key === 'string' && /^\d+$/.test(key)) throw new Error('visited a closed list member');
    return Reflect.get(target, key, receiver);
  } });
  const index: values.ValueIndex = { payloads: new Map(), lists: new Map([['root', items]]) };
  const html = renderToStaticMarkup(<ValueView valueId="root" values={index} />);
  expect(html).toContain('List · 100000 items');
  expect(html).not.toContain('payload not provided');
});

it('does not serialize Record JSON before expansion', () => {
  const transition: Transition = { seq: 1, op: { type: 'start' }, committed: true, values: {} };
  Object.defineProperty(transition.op, 'toJSON', { value: () => { throw new Error('serialized closed record'); } });
  expect(renderToStaticMarkup(<RecordInspector transition={transition} />)).not.toContain('<pre>');
});

it('renders a large JSON container through index ranges, not text pages', () => {
  const payload = '[' + Array(100_000).fill('9007199254740993').join(',') + ']';
  const html = renderToStaticMarkup(<PayloadText payload={payload} />);
  expect(html).toContain('Array · 100000 items');
  expect(html).toContain('[0 … 9999]');
  expect(html).not.toContain('9007199254740993');
  expect(html).not.toContain('pages');
  expect(html.length).toBeLessThan(5_000);
  expect(renderToStaticMarkup(<PayloadText payload="<b>done</b>" />)).toContain('&lt;b&gt;done&lt;/b&gt;');
});
