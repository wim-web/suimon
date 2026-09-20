import { Check } from 'lucide-react';
import type { RunOutput } from './api';

export function RunOutputs({ outputs }: { outputs: RunOutput[] }) {
  return <section className="app-output" aria-label="実行結果" aria-live="polite">
    <div><Check size={12} />OUTPUT</div>
    {outputs.length ? outputs.map((output, i) => <div className="app-output-port" key={i}>
      <h3>{output.port.node}.{output.port.port}</h3>
      {output.items.length ? output.items.map((item, j) => <pre key={j} title={item.id}>{JSON.stringify(item.value, null, 2)}</pre>) : <p>出力なし</p>}
    </div>) : <p>出力なし</p>}
  </section>;
}
