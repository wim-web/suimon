import type { ReactNode } from 'react';
import { TriangleAlert, Workflow as WorkflowIcon } from 'lucide-react';
import { statusLabel, statusTone } from './StatusBadge';

export interface WorkflowToolbarProps {
  title: string;
  subtitle?: string;
  /** The overall status of the state, or a host-defined word such as `ready`. */
  status?: string;
  failures?: number;
  onShowFailures?: () => void;
  actions?: ReactNode;
}
export function WorkflowToolbar({ title, subtitle, status = 'ready', failures = 0, onShowFailures, actions }: WorkflowToolbarProps) {
  return <header className="sui-toolbar">
    <div className="sui-brand" role="img" aria-label="suimon"><WorkflowIcon size={21} aria-hidden="true" /></div>
    <div className="sui-workflow-title"><span>{subtitle ?? 'Workflow'}</span><h1>{title}</h1></div>
    <div className="sui-toolbar-actions">
      {failures > 0 && <button className="sui-button sui-tone-danger" onClick={onShowFailures} disabled={!onShowFailures}><TriangleAlert size={13} />{failures} {failures === 1 ? 'failure' : 'failures'}</button>}
      <span className={`sui-status sui-tone-${statusTone(status)}`}><i />{statusLabel(status)}</span>
      {actions}
    </div>
  </header>;
}
