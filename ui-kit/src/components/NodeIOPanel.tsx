import { ArrowDown, ArrowUpRight } from 'lucide-react';
import type { NodeIOData, NodeIOPort } from '../lib/node-io';

export interface NodeIOPanelProps { data: NodeIOData }

function PortValues({ data, direction }: { data: NodeIOPort; direction: 'input' | 'output' }) {
  const Icon = direction === 'input' ? ArrowDown : ArrowUpRight;
  const consumed = data.items.filter(item => item.consumed === true).length;
  const waiting = data.items.filter(item => item.consumed === false).length;
  const channels = data.channels ?? [];
  const closed = channels.filter(channel => channel.closed).length;
  return <section className={`sui-io-port sui-io-${direction}`} aria-label={`${direction === 'input' ? '入力' : '出力'} ${data.port.name}`}>
    <div className="sui-io-port-title"><Icon size={13} /><strong>{data.port.name}</strong><span>{data.port.kind}</span></div>
    {data.connections.length > 0 && <div className="sui-io-connections">{direction === 'input' ? 'From' : 'To'} · {data.connections.join(', ')}</div>}
    {direction === 'input' && data.port.kind === 'stream' && <div className="sui-io-queue"><span>到着 {data.items.length}件 · 消費 {consumed}件 · 待機 {waiting}件</span><span>{channels.length > 1 ? `EOS ${closed}/${channels.length}` : closed ? 'EOS 受信済み' : 'EOS 未到着'}</span></div>}
    {data.items.length === 0 ? <p className="sui-io-empty">値はまだ記録されていません</p> : data.items.map(item => <div className="sui-io-item" key={JSON.stringify(item.channel !== undefined ? [item.channel, item.tokenIndex] : [item.instance, item.id])}>
      {direction === 'input' && item.consumed !== undefined && <span className={`sui-io-item-state ${item.consumed ? '' : 'is-pending'}`}>{item.consumed ? '消費済み' : '待機中'}</span>}
      <pre>{item.available ? JSON.stringify(item.value, null, 2) : '値は未提供'}</pre>
      <details><summary>Item details · event {item.sequence}</summary><dl><dt>Item</dt><dd>{item.id}</dd><dt>Instance</dt><dd>{item.instance ?? '—'}</dd>{item.consumedSequence !== undefined && <><dt>Consumed at</dt><dd>event {item.consumedSequence}</dd></>}</dl></details>
    </div>)}
  </section>;
}

export function NodeIOPanel({ data }: NodeIOPanelProps) {
  return <div className="sui-node-io-panel">
    <section><h3>INPUT <span>入力</span></h3>{data.inputs.map(port => <PortValues key={port.port.name} data={port} direction="input" />)}{!data.inputs.length && <p className="sui-io-empty">入力ポートなし</p>}</section>
    <section><h3>OUTPUT <span>出力</span></h3>{data.outputs.map(port => <PortValues key={port.port.name} data={port} direction="output" />)}{!data.outputs.length && <p className="sui-io-empty">出力ポートなし</p>}</section>
  </div>;
}
