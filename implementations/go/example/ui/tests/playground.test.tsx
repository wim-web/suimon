import { readFileSync } from 'node:fs';
import { renderToStaticMarkup } from 'react-dom/server';
import { expect, it } from 'vitest';
import { parseScenarios } from '../src/api';
import { Playground } from '../src/App';

const definition = (id: string) => JSON.parse(readFileSync(new URL(`../../definitions/${id}.json`, import.meta.url), 'utf8')) as unknown;
const input = { names: ['alpha', 'bravo'] };
const scenarios = parseScenarios([
  { id: 'stream', title: 'Stream', description: 'produce yields each item after one unit.', definition: definition('stream'), input, compare: 'batch' },
  { id: 'batch', title: 'Batch', description: 'produceAll returns the whole list at once.', definition: definition('batch'), input, compare: 'stream' },
]);

/** The markup from the first occurrence of open up to the next occurrence of close. */
function part(html: string, open: string, close: string): string {
  const start = html.indexOf(open);
  expect(start, open).toBeGreaterThanOrEqual(0);
  return html.slice(start, html.indexOf(close, start));
}

it('chooses the scenario in the header, and keeps the left pane for the workflow and the run', () => {
  const html = renderToStaticMarkup(<Playground scenarios={scenarios} />);
  const header = part(html, '<header class="sui-toolbar"', '</header>');
  expect(header).toMatch(/<select[^>]*aria-label="Scenario"/);
  expect(header).toContain('<option value="stream" selected="">Stream</option><option value="batch">Batch</option>');
  const sidebar = part(html, '<aside class="sui-sidebar"', '</aside>');
  expect(sidebar).toContain('produce');
  expect(sidebar).not.toContain('aria-label="Scenario"');
  expect(sidebar).not.toContain('Batch');
  expect(sidebar).toContain('produce yields each item after one unit.');
  expect(sidebar).toContain('id="scenario-input"');
  // Both sides of the comparison have a lane before either has run.
  expect(html.match(/not run yet/g)).toHaveLength(2);
});

it('chooses the unit of the next run in the left pane, 600ms by default', () => {
  const html = renderToStaticMarkup(<Playground scenarios={scenarios} />);
  const unit = part(part(html, '<aside class="sui-sidebar"', '</aside>'), '<select id="run-unit"', '</select>');
  expect(unit).toContain('<option value="200">200ms · fast</option><option value="600" selected="">600ms · normal</option><option value="1000">1000ms · slow</option>');
  // Before a run, both lanes of the comparison are for the chosen unit.
  const timeline = part(html, '<section class="app-timeline"', '</section>');
  expect(timeline.match(/unit <b>600ms<\/b>/g)).toHaveLength(2);
});
