import { DefinitionBuilder, defineType, MemoryJournal } from '@suimon/engine';

const text = defineType('Text', value => {
  if (typeof value !== 'string') throw new TypeError('Expected text');
  return value;
});
const definition = new DefinitionBuilder();
const words = definition.stream('words', text, text, async function* (input, { signal }) {
  for (const word of input.split(' ')) {
    signal.throwIfAborted();
    yield word;
  }
});
const upper = definition.func('upper', text, text, input => input.toUpperCase());
const same = definition.passthrough('same', text);
const flow = definition.workflow('words', text);
const source = flow.call('source', words, { policy: 'stop' });
const mapped = flow.call('mapped', upper, { policy: 'continue', timeout: { callMs: 1000n } });
const collected = flow.waitStream('collected', text, { policy: 'continue' });
flow.entry(source);
flow.connect(source, mapped, same);
flow.connect(mapped, collected, same);

const engine = definition.build(flow);
const journal = new MemoryJournal();
const execution = await engine.start('hello suimon', { journal });
const report = await execution.wait();
console.log(report.status, report.output(collected));
const recovered = await (await engine.resume(journal)).wait();
console.log(recovered.status, recovered.output(collected));
