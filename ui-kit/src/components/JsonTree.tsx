import { useMemo } from 'react';
import { jsonDocument, jsonMembers } from '../lib/json-tree';
import type { JsonDocument, JsonSpan } from '../lib/json-tree';
import { LazyDetails } from './LazyDetails';
import { TreeChildren } from './TreeChildren';

function Scalar({ text }: { text: string }) {
  if (text.length <= 240) return <code className="sui-json-scalar">{text}</code>;
  return <LazyDetails className="sui-tree-branch" summary={<><code>{text.slice(0, 120)}…</code><small>{text.length} characters</small></>}>
    {() => <textarea className="sui-value-text" aria-label="Full value text" readOnly value={text} spellCheck={false} />}
  </LazyDetails>;
}

function Container({ document, node }: { document: JsonDocument; node: JsonSpan }) {
  const members = useMemo(() => jsonMembers(document, node), [document, node]);
  return <>
    <small className="sui-tree-count">{node.kind === 'array' ? `Array · ${members.length} items` : `Object · ${members.length} properties`}</small>
    <TreeChildren count={members.length} renderItem={i => {
      const member = members[i]!;
      return <Member key={member.value.start} document={document} node={member.value} label={member.label} />;
    }} rangeLabel={node.kind === 'object' ? (start, end) => `Properties ${start + 1}–${end}` : undefined} />
  </>;
}

function Member({ document, node, label }: { document: JsonDocument; node: JsonSpan; label: string }) {
  const key = <span className="sui-json-key">{label}: </span>;
  if (node.kind === 'array' || node.kind === 'object') return <LazyDetails className="sui-tree-branch" summary={<>{key}<span>{node.kind === 'array' ? '[…]' : '{…}'}</span></>}>
    {() => <Container document={document} node={node} />}
  </LazyDetails>;
  return <div className="sui-json-member">{key}<Scalar text={document.text.slice(node.start, node.end)} /></div>;
}

/** Mounted only after the enclosing value is opened; JSON stays in the application. */
export function JsonTree({ payload }: { payload: string }) {
  const document = useMemo(() => jsonDocument(payload), [payload]);
  if (!document) return payload.length <= 240 ? <pre>{payload}</pre>
    : <textarea className="sui-value-text" aria-label="Value text" readOnly value={payload} spellCheck={false} />;
  return <div className="sui-json-tree">{document.root.kind === 'array' || document.root.kind === 'object'
    ? <Container document={document} node={document.root} />
    : <Scalar text={document.text.slice(document.root.start, document.root.end)} />}</div>;
}
