/** Source spans preserve number spelling, duplicate object keys and string escapes. */
export interface JsonSpan { start: number; end: number; kind: 'object' | 'array' | 'string' | 'scalar' }
export interface JsonMember { label: string; value: JsonSpan }
export interface JsonDocument { text: string; root: JsonSpan }

const whitespace = (c: string | undefined) => c === ' ' || c === '\n' || c === '\r' || c === '\t';
function skipSpace(text: string, at: number): number { while (whitespace(text[at])) at++; return at; }
function stringEnd(text: string, at: number): number {
  for (let i = at + 1; i < text.length; i++) {
    if (text[i] === '\\') i++;
    else if (text[i] === '"') return i + 1;
  }
  return text.length;
}

/** The document has already passed JSON.parse; only boundaries are read here. */
function valueEnd(text: string, at: number): number {
  if (text[at] === '"') return stringEnd(text, at);
  if (text[at] === '{' || text[at] === '[') {
    let depth = 0;
    for (let i = at; i < text.length; i++) {
      const c = text[i];
      if (c === '"') i = stringEnd(text, i) - 1;
      else if (c === '{' || c === '[') depth++;
      else if ((c === '}' || c === ']') && --depth === 0) return i + 1;
    }
  }
  let end = at;
  while (end < text.length && !whitespace(text[end]) && !',]}'.includes(text[end]!)) end++;
  return end;
}
function span(text: string, start: number, end: number): JsonSpan {
  const c = text[start];
  return { start, end, kind: c === '{' ? 'object' : c === '[' ? 'array' : c === '"' ? 'string' : 'scalar' };
}

export function jsonDocument(payload: string): JsonDocument | null {
  try { JSON.parse(payload); } catch { return null; }
  const start = skipSpace(payload, 0);
  let end = payload.length;
  while (whitespace(payload[end - 1])) end--;
  return { text: payload, root: span(payload, start, end) };
}

/** Index just one expanded container; descendants remain source spans until opened. */
export function jsonMembers(document: JsonDocument, parent: JsonSpan): JsonMember[] {
  if (parent.kind !== 'object' && parent.kind !== 'array') return [];
  const { text } = document, members: JsonMember[] = [];
  let at = skipSpace(text, parent.start + 1);
  while (at < parent.end - 1) {
    let label = `[${members.length}]`;
    if (parent.kind === 'object') {
      const end = stringEnd(text, at);
      label = text.slice(at, end);
      at = skipSpace(text, skipSpace(text, end) + 1); // colon
    }
    const end = valueEnd(text, at);
    members.push({ label, value: span(text, at, end) });
    at = skipSpace(text, end);
    if (text[at] === ',') at = skipSpace(text, at + 1);
  }
  return members;
}
