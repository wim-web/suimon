import { renderToStaticMarkup } from 'react-dom/server';
import { expect, it } from 'vitest';
import { Timeline } from '../src/Timeline';

it('marks the first downstream start in each lane, and shows a lane that has not run', () => {
  const html = renderToStaticMarkup(<Timeline highlight="process" lanes={[
    { key: 'stream', label: 'Stream', run: { label: 'Stream', elapsedMs: 400, done: true, spans: [
      { function: 'produce', detail: '2 items', startMs: 0, endMs: 100, marks: [50, 100], outcome: 'ok' },
      { function: 'process', detail: 'alpha', startMs: 51, endMs: 151, marks: [], outcome: 'ok' },
    ] } },
    { key: 'batch', label: 'Batch', run: null },
  ]} />);
  expect(html).toContain('first process at <b>51ms</b>');
  expect(html).toContain('user code done at <b>151ms</b>');
  expect(html).toContain('not run yet');
  expect(html.match(/class="app-mark"/g)).toHaveLength(2);
  // The marker runs through every row of the lane.
  expect(html.match(/class="app-marker"/g)).toHaveLength(2);
});
