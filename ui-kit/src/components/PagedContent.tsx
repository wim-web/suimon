import { useEffect, useState } from 'react';
import type { ReactNode } from 'react';
import { ChevronFirst, ChevronLast, ChevronLeft, ChevronRight } from 'lucide-react';

function PageNumber({ page, pages, label, onChange }: { page: number; pages: number; label: string; onChange: (page: number) => void }) {
  const [draft, setDraft] = useState(String(page + 1));
  useEffect(() => { setDraft(String(page + 1)); }, [page]);
  const commit = () => {
    const value = Number(draft);
    const next = draft.trim() && Number.isFinite(value) ? Math.max(1, Math.min(pages, Math.floor(value))) : page + 1;
    setDraft(String(next)); onChange(next - 1);
  };
  return <input type="number" min={1} max={pages} aria-label={`Page of ${label}`} value={draft}
    onChange={event => setDraft(event.target.value)} onBlur={commit}
    onKeyDown={event => { if (event.key === 'Enter') { event.preventDefault(); commit(); } }} />;
}

/** Only invoke the renderer for one page; appending items preserves the reader's page. */
export function PagedContent({ count, pageSize = 50, label, children }: {
  count: number; pageSize?: number; label: string; children: (start: number, end: number) => ReactNode;
}) {
  const size = Number.isFinite(pageSize) ? Math.max(1, Math.floor(pageSize)) : 50;
  const pages = Math.max(1, Math.ceil(count / size));
  const [requestedPage, setPage] = useState(0);
  const page = Math.min(requestedPage, pages - 1), start = page * size, end = Math.min(count, start + size);
  useEffect(() => { if (requestedPage !== page) setPage(page); }, [page, requestedPage]);
  return <div className="sui-paged-content">
    {pages > 1 && <nav className="sui-pagination" aria-label={`${label} pages`}>
      <span className="sui-page-range">{start + 1}–{end} of {count}</span>
      <div>
        <button className="sui-icon-button" aria-label={`First page of ${label}`} disabled={page === 0} onClick={() => setPage(0)}><ChevronFirst size={14} /></button>
        <button className="sui-icon-button" aria-label={`Previous page of ${label}`} disabled={page === 0} onClick={() => setPage(page - 1)}><ChevronLeft size={14} /></button>
        <PageNumber page={page} pages={pages} label={label} onChange={setPage} /><span> / {pages}</span>
        <button className="sui-icon-button" aria-label={`Next page of ${label}`} disabled={page === pages - 1} onClick={() => setPage(page + 1)}><ChevronRight size={14} /></button>
        <button className="sui-icon-button" aria-label={`Last page of ${label}`} disabled={page === pages - 1} onClick={() => setPage(pages - 1)}><ChevronLast size={14} /></button>
      </div>
    </nav>}
    {children(start, end)}
  </div>;
}
