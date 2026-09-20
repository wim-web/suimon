import { useState } from 'react';
import type { ReactNode } from 'react';
import { ChevronDown, Download, Workflow } from 'lucide-react';

export interface WorkflowToolbarProps {
  title: string;
  subtitle?: string;
  status?: string;
  actions?: ReactNode;
  onExport?: (kind: 'graph' | 'trace' | 'snapshot') => void;
}
export function WorkflowToolbar({ title, subtitle, status = 'ready', actions, onExport }: WorkflowToolbarProps) {
  const [menu, setMenu] = useState(false);
  return <header className="sui-toolbar">
    <div className="sui-brand" role="img" aria-label="suimon"><Workflow size={21} aria-hidden="true" /></div>
    <div className="sui-workflow-title"><span>{subtitle ?? 'Workspace'}</span><h1>{title}</h1></div>
    <span className="sui-version">WORKFLOW</span>
    <div className="sui-toolbar-actions"><span className={`sui-status sui-status-${status}`}><i />{status}</span>{actions}
      {onExport && <div className="sui-export"><button className="sui-button" aria-expanded={menu} onClick={() => setMenu(!menu)}><Download size={14} />Export<ChevronDown size={12} /></button>
        {menu && <><button className="sui-menu-dismiss" aria-label="エクスポートメニューを閉じる" onClick={() => setMenu(false)} /><div className="sui-menu">{(['graph', 'trace', 'snapshot'] as const).map(kind => <button key={kind} onClick={() => { onExport(kind); setMenu(false); }}>{kind}.{kind === 'trace' ? 'jsonl' : 'json'}</button>)}</div></>}
      </div>}
    </div>
  </header>;
}
