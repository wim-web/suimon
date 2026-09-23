const tones: Record<string, string> = {
  active: 'accent', running: 'accent', fetching: 'accent', stopping: 'warning', cancelling: 'warning',
  succeeded: 'success', normal: 'success', transformed: 'success', returned: 'success', complete: 'success', committed: 'success',
  skipped: 'muted', pending: 'muted', ready: 'muted', notStarted: 'muted', idle: 'muted', waiting: 'muted',
  failed: 'danger', lost: 'danger', cancelled: 'danger', uncommitted: 'warning', upstreamFailed: 'warning',
};
const labels: Record<string, string> = { upstreamFailed: 'upstream failed', notStarted: 'not started' };

/** The color family used for a status, outcome or phase name from the state. */
export function statusTone(status: string): string { return tones[status] ?? 'muted'; }
export function statusLabel(status: string): string { return labels[status] ?? status; }

export interface StatusBadgeProps { status: string; count?: number; title?: string }
export function StatusBadge({ status, count, title }: StatusBadgeProps) {
  return <span className={`sui-badge sui-tone-${statusTone(status)}`} title={title}>{statusLabel(status)}{count !== undefined && <b>{count}</b>}</span>;
}

/** Badges for counts by status, in the given order of statuses. */
export function StatusCounts({ counts, order }: { counts: Partial<Record<string, number>>; order: readonly string[] }) {
  const shown = order.filter(status => counts[status]);
  return shown.length ? <span className="sui-badges">{shown.map(status => <StatusBadge key={status} status={status} count={counts[status]} />)}</span> : null;
}
