import { readFileSync } from 'node:fs';
import { renderToStaticMarkup } from 'react-dom/server';
import { expect, it } from 'vitest';
import { parseScenarios } from '../src/api';
import { Playground } from '../src/App';

const definition = (id: string) => JSON.parse(readFileSync(new URL(`../../definitions/${id}.json`, import.meta.url), 'utf8')) as unknown;
const input = { names: ['alpha', 'bravo'] };
const scenarios = parseScenarios([
  { id: 'stream', title: 'Stream', description: 'Fetching takes one unit per item.', definition: definition('stream'), input, compare: 'batch' },
  { id: 'batch', title: 'Batch', description: 'Batch processes in parallel, but only after fetching everything.', definition: definition('batch'), input, compare: 'stream' },
]);

/** The markup from the first occurrence of open up to the next occurrence of close. */
function part(html: string, open: string, close: string): string {
  const start = html.indexOf(open);
  expect(start, open).toBeGreaterThanOrEqual(0);
  return html.slice(start, html.indexOf(close, start));
}

const options = (html: string) => [...html.matchAll(/<option\b([^>]*)>(.*?)<\/option>/g)].map(([, attributes, text]) => ({
  value: attributes!.match(/\bvalue="([^"]*)"/)?.[1], selected: /\bselected(?:=|\s|$)/.test(attributes!),
  text: text!.trim(),
}));

it('initially shows the scenario choice in the header and its workflow and input in the left pane', () => {
  const html = renderToStaticMarkup(<Playground scenarios={scenarios} />);
  const header = part(html, '<header class="sui-toolbar"', '</header>');
  expect(header).toMatch(/<select[^>]*aria-label="Scenario"/);
  expect(options(header)).toEqual(scenarios.map((scenario, index) => ({
    value: scenario.id, selected: index === 0, text: scenario.title,
  })));
  const sidebar = part(html, '<aside class="sui-sidebar"', '</aside>');
  expect(sidebar).toContain('produce');
  expect(sidebar).not.toContain('aria-label="Scenario"');
  expect(sidebar).not.toContain('Batch');
  expect(sidebar).toContain(scenarios[0]!.description);
  expect(sidebar).toContain('id="scenario-input"');
  // Both sides of the comparison have a lane before either has run.
  expect(html.match(/not run yet/g)).toHaveLength(2);
});

it('initially offers the run units in the left pane and uses 600ms for both timeline lanes', () => {
  const html = renderToStaticMarkup(<Playground scenarios={scenarios} />);
  const sidebar = part(html, '<aside class="sui-sidebar"', '</aside>');
  const unit = part(sidebar, '<select id="run-unit"', '</select>');
  expect(options(unit)).toEqual([
    { value: '200', selected: false, text: expect.stringMatching(/\b200ms\b/) },
    { value: '600', selected: true, text: expect.stringMatching(/\b600ms\b/) },
    { value: '1000', selected: false, text: expect.stringMatching(/\b1000ms\b/) },
  ]);
  // Before a run, both lanes of the comparison are for the chosen unit.
  const timeline = part(html, '<section class="app-timeline"', '</section>');
  expect(timeline.match(/unit <b>600ms<\/b>/g)).toHaveLength(2);
});
