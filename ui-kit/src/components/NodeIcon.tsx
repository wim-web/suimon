import { ArrowDownToLine, ArrowUpFromLine, Braces, Combine, Filter, GitBranch, Layers, Repeat2, Type, Workflow } from 'lucide-react';
import type { CSSProperties } from 'react';

export interface NodeIconProps { kind: string; accent?: string; size?: number }
export function NodeIcon({ kind, accent = 'var(--sui-accent-strong)', size = 17 }: NodeIconProps) {
  const Icon = ({ leaf: Braces, branch: GitBranch, loop: Repeat2, forEach: Layers, filter: Filter, merge: Combine, entry: ArrowUpFromLine, exit: ArrowDownToLine, text: Type } as Record<string, typeof Braces>)[kind] ?? Workflow;
  return <span className="sui-node-icon" style={{ '--node-accent': accent } as CSSProperties}><Icon size={size} strokeWidth={1.6} /></span>;
}
