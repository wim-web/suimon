import { useState } from 'react';
import type { ReactNode } from 'react';

/** Closed disclosures do not build their contents or retain previously rendered payloads. */
export function LazyDetails({ className, summary, children }: { className: string; summary: ReactNode; children: () => ReactNode }) {
  const [open, setOpen] = useState(false);
  return <details className={className} open={open} onToggle={event => setOpen(event.currentTarget.open)}>
    <summary>{summary}</summary>
    {open && children()}
  </details>;
}
