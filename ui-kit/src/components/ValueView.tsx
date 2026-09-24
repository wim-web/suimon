import type { ResolvedValue } from '../lib/values';
import { formatPayload } from '../lib/values';

export interface ValueViewProps { value: ResolvedValue; label?: string }
/** A value by identity: its payload, the members of an engine-built list, or a note that no payload was provided. */
export function ValueView({ value, label }: ValueViewProps) {
  return <div className="sui-value">
    {label !== undefined && <span className="sui-value-label" title={value.id}>{label}</span>}
    {value.kind === 'payload' ? <pre>{formatPayload(value.payload)}</pre>
      : value.kind === 'list' ? <div className="sui-value-list"><small>List · {value.items.length}</small>{value.items.map((item, i) => <ValueView key={i} value={item} />)}</div>
        : <p className="sui-value-missing" title={value.id}>payload not provided</p>}
  </div>;
}
