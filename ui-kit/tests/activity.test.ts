import { readFileSync } from 'node:fs';
import { expect, it } from 'vitest';
import { nodeActivity } from '../src/lib/activity';
import type { TraceEvent } from '../src/types';

const trace = (name: string): TraceEvent[] => readFileSync(new URL(`../../Test/traces/${name}.jsonl`, import.meta.url), 'utf8').trim().split('\n').map(line => JSON.parse(line) as TraceEvent);

it('keeps running attempts until their finish transaction is committed', () => {
  const events = trace('minimal');
  expect(nodeActivity(events).work).toEqual({ running: 0, succeeded: 1, failed: 0 });
  const beforeCommit = events.findIndex(event => event.txn === 'txn-3' && event.type === 'transaction.committed');
  expect(nodeActivity(events.slice(0, beforeCommit)).work).toEqual({ running: 1, succeeded: 0, failed: 0 });
});

it('aggregates child attempts into the containing node and supports nested scopes', () => {
  const events = trace('loop-retry');
  expect(nodeActivity(events).loop).toEqual({ running: 0, succeeded: 3, failed: 0 });
  expect(nodeActivity(events, ['loop']).work).toEqual({ running: 0, succeeded: 3, failed: 0 });
  expect(nodeActivity(events, ['other'])).toEqual({});
});
