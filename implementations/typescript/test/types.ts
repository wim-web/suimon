import { DefinitionBuilder, defineType, discard } from '../src/builder.js';

const text = defineType('Text', value => {
  if (typeof value !== 'string') throw new TypeError('Expected text');
  return value;
});
const count = defineType('Count', value => {
  if (typeof value !== 'number') throw new TypeError('Expected count');
  return value;
});
const d = new DefinitionBuilder();
const read = d.func('read', text, text, value => value);
const measure = d.func('measure', count, count, value => value);
const notify = d.funcNoInput('notify', text, () => 'done');
const same = d.passthrough('same', text);
const length = d.transform('length', text, count, value => value.length);
const main = d.workflow('main', text);
const a = main.call('a', read, { policy: 'stop' });
const b = main.call('b', measure, { policy: 'stop' });
const c = main.call('c', notify, { policy: 'stop' });
main.entry(a);
main.connect(a, b, length);
main.connect(a, c, discard(text));
// @ts-expect-error The transform must return the target input type.
main.connect(a, b, same);
// @ts-expect-error A value-taking target cannot receive discard.
main.connect(a, b, discard(text));
// @ts-expect-error The workflow input must match its entry.
main.entry(b);
// @ts-expect-error Policy is required at each placement.
main.call('missing-policy', read, {});
// @ts-expect-error Merge does not have a timeout.
main.merge('aggregate', text, { policy: 'stop', timeout: { callMs: 1n } });
const child = d.workflow('child', text);
const childOut = child.call('output', read, { policy: 'stop' });
child.entry(childOut);
// @ts-expect-error A subworkflow call does not have a timeout.
main.call('child', child.body(childOut), { policy: 'stop', timeout: { callMs: 1n } });
// @ts-expect-error A subworkflow task does not have a timeout.
d.task('child-task', child.body(childOut), same, same, { policy: 'stop', timeout: { callMs: 1n } });
// @ts-expect-error Task input transforms must match the body input.
d.task('bad-input', read, length, same, { policy: 'continue' });
// @ts-expect-error A no-input task cannot call a body that requires input.
d.taskNoInput('required-input', read, same, { policy: 'continue' });
// @ts-expect-error Collected task results must match the concurrency element type.
main.concurrency('bad-output', { input: text, element: count, output: 'list', limit: 1n, policy: 'continue', tasks: [d.task('text-task', read, same, same, { policy: 'continue' })] });
const engine = d.build(main);
void engine.start('request');
// @ts-expect-error Required typed workflow input cannot be omitted.
void engine.start();
// @ts-expect-error Wrong workflow input.
void engine.run(42);
const result = await engine.run('request');
const value: number = result.output(b);
void value;
// @ts-expect-error Endpoint output keeps its declared value type.
const wrong: string = result.output(b);
void wrong;
