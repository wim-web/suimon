import type { Path } from './model-types.js';

export function identity(...parts: string[]): string {
  return parts.map(part => `${Array.from(part).length}:${part}`).join('');
}

export function decodeIdentity(id: string): string[] | undefined {
  const points = Array.from(id);
  const parts: string[] = [];
  let cursor = 0;
  while (cursor < points.length) {
    let length = 0;
    while (cursor < points.length) {
      const point = points[cursor];
      if (point === undefined || point < '0' || point > '9') break;
      length = length * 10 + Number(point);
      if (length > points.length) return undefined;
      cursor++;
    }
    if (points[cursor] !== ':') return undefined;
    cursor++;
    if (length > points.length - cursor) return undefined;
    parts.push(points.slice(cursor, cursor + length).join(''));
    cursor += length;
  }
  return parts;
}

export function compareStrings(a: string, b: string): number {
  const left = a[Symbol.iterator]();
  const right = b[Symbol.iterator]();
  for (;;) {
    const x = left.next();
    const y = right.next();
    if (x.done || y.done) return x.done ? (y.done ? 0 : -1) : 1;
    const xc = x.value.codePointAt(0) ?? 0;
    const yc = y.value.codePointAt(0) ?? 0;
    if (xc !== yc) return xc < yc ? -1 : 1;
  }
}

export function listValue(values: readonly string[]): string {
  return identity('list', ...[...values].sort(compareStrings));
}

export function exploreValue(...parts: string[]): string {
  return identity('value', ...parts);
}

export function samePath(left: readonly string[], right: readonly string[]): boolean {
  return left.length === right.length && left.every((part, index) => part === right[index]);
}

export function keyWithin(path: Path, label: string): string {
  return identity(...path, label);
}

function keySplit(id: string): { path: Path; label: string } | undefined {
  const parts = decodeIdentity(id);
  if (parts === undefined || identity(...parts) !== id) return undefined;
  const label = parts.pop();
  return label === undefined ? undefined : { path: parts, label };
}

export function keyScope(id: string): Path {
  return keySplit(id)?.path ?? [];
}

export function keyRelative(path: Path, id: string): string[] {
  const split = keySplit(id);
  return split !== undefined && samePath(split.path, path) ? [split.label] : [id, ''];
}

export function keyChild(id: string): Path {
  const split = keySplit(id);
  return split === undefined ? [id] : [...split.path, split.label];
}

export function keyOwned(kind: string, owner: string, ...parts: string[]): string {
  const path = keyScope(owner);
  return keyWithin(path, identity(kind, ...keyRelative(path, owner), ...parts));
}

export function keyInvocation(path: Path, placement: string, trigger: string | null): string {
  return keyWithin(path, identity('invocation', placement, ...(trigger === null ? [] : keyRelative(path, trigger))));
}

export const keyTask = (execution: string, task: string): string => keyOwned('task', execution, task);
export const keyCallResult = (call: string, index: number): string => keyOwned('result', call, String(index));
export const keyAggregate = (path: Path, placement: string): string => keyWithin(path, identity('aggregate', placement));
export const keyTaskOutput = (execution: string, task: string, index: number): string => keyOwned('output', execution, task, String(index));
export const keyList = (execution: string): string => keyOwned('list', execution);
export const keyReturned = (invocation: string): string => keyOwned('return', invocation);
