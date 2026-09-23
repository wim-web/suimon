import { ArrowDownToLine, Braces, Combine, GitBranch, Layers, ListEnd, Workflow } from 'lucide-react';
import type { CSSProperties } from 'react';

const icons: Record<string, typeof Braces> = {
  function: Braces, subworkflow: Workflow, branch: GitBranch, waitStream: ListEnd, merge: Combine, concurrency: Layers, input: ArrowDownToLine,
};
const accents: Record<string, string> = {
  function: 'var(--sui-kind-function)', subworkflow: 'var(--sui-kind-subworkflow)', branch: 'var(--sui-kind-branch)',
  waitStream: 'var(--sui-kind-collect)', merge: 'var(--sui-kind-collect)', concurrency: 'var(--sui-kind-concurrency)',
};

export interface NodeIconProps { kind: string; accent?: string; size?: number }
/** The icon of a control type (function, subworkflow, branch, waitStream, merge, concurrency) or `input`. */
export function NodeIcon({ kind, accent, size = 17 }: NodeIconProps) {
  const Icon = icons[kind] ?? Braces;
  return <span className="sui-node-icon" style={{ '--node-accent': accent ?? accents[kind] ?? 'var(--sui-accent-strong)' } as CSSProperties}><Icon size={size} strokeWidth={1.6} aria-hidden="true" /></span>;
}
