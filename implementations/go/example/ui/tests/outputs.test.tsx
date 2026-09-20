import { renderToStaticMarkup } from 'react-dom/server';
import { expect, it } from 'vitest';
import { RunOutputs } from '../src/RunOutputs';

it('renders all output ports and items including falsy values', () => {
  const html = renderToStaticMarkup(<RunOutputs outputs={[
    { port: { node: 'one', port: 'out' }, items: [{ id: 'a', value: 0 }, { id: 'b', value: false }] },
    { port: { node: 'two', port: 'result' }, items: [{ id: 'c', value: null }, { id: 'd', value: '' }] },
  ]} />);
  expect(html).toContain('one.out');
  expect(html).toContain('two.result');
  expect(html.match(/<pre/g)).toHaveLength(4);
  for (const value of ['0', 'false', 'null', '&quot;&quot;']) expect(html).toContain(`>${value}</pre>`);
});

it('distinguishes no outputs from an omitted result', () => {
  expect(renderToStaticMarkup(<RunOutputs outputs={[]} />)).toContain('出力なし');
  const html = renderToStaticMarkup(<RunOutputs outputs={[{ port: { node: 'one', port: 'out' }, items: [] }]} />);
  expect(html).toContain('one.out');
  expect(html).toContain('出力なし');
});
