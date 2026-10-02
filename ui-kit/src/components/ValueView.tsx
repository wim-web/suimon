import type { ResolvedValue, ValueIndex } from '../lib/values';
import { LazyDetails } from './LazyDetails';
import { JsonTree } from './JsonTree';
import { TreeChildren } from './TreeChildren';

export type ValueViewProps = { label?: string } & (
  | { value: ResolvedValue; valueId?: never; values?: never }
  /** Resolve members only in expanded tree ranges; a closed list never walks its descendants. */
  | { value?: never; valueId: string; values?: ValueIndex }
);

/** Kept as the payload entry point for record details and value disclosures. */
export function PayloadText({ payload }: { payload: string }) {
  return <JsonTree payload={payload} />;
}

function ValueNode(props: ValueViewProps & { depth: number }) {
  const { value, valueId, values, label, depth } = props;
  const id = value?.id ?? valueId!;
  const payload = value ? (value.kind === 'payload' ? value.payload : undefined) : values?.payloads.get(id);
  const items = value ? (value.kind === 'list' ? value.items : undefined) : depth < 16 ? values?.lists.get(id) : undefined;
  if (payload === undefined && !items) return <div className="sui-value">
    {label !== undefined && <span className="sui-value-label" title={id}>{label}</span>}
    <p className="sui-value-missing" title={id}>payload not provided</p>
  </div>;
  return <LazyDetails className="sui-value" summary={<><span className="sui-value-label" title={id}>{label ?? 'Value'}</span>
    <small>{payload !== undefined ? `${payload.length} characters` : `List · ${items!.length} items`}</small></>}>
    {() => payload !== undefined ? <PayloadText payload={payload} /> : <div className="sui-value-list">
      <TreeChildren count={items!.length} rangeLabel={(start, end) => `Items ${start + 1}–${end}`} renderItem={i => {
        const item = items![i]!;
        return typeof item === 'string'
          ? <ValueNode key={`${i}:${item}`} valueId={item} values={values} depth={depth + 1} label={`Item ${i + 1}`} />
          : <ValueNode key={`${i}:${item.id}`} value={item} depth={depth + 1} label={`Item ${i + 1}`} />;
      }} />
    </div>}
  </LazyDetails>;
}

/** Payloads and list members remain closed until requested. */
export function ValueView(props: ValueViewProps) {
  return <ValueNode key={props.value?.id ?? props.valueId} {...props} depth={0} />;
}
