import type { RecoverableJournal } from './runtime-types.js';

export class MemoryJournal implements RecoverableJournal {
  private chunks: Uint8Array[] = [];
  private byteLength = 0;

  constructor(initial: Uint8Array | string = new Uint8Array()) {
    const bytes = typeof initial === 'string' ? new TextEncoder().encode(initial) : Uint8Array.from(initial);
    if (bytes.length > 0) this.chunks.push(bytes);
    this.byteLength = bytes.length;
  }

  async append(lines: Uint8Array): Promise<void> {
    if (lines.length === 0) return;
    this.chunks.push(Uint8Array.from(lines));
    this.byteLength += lines.length;
  }

  async sync(): Promise<void> {}

  async contents(maxBytes: number = Number.MAX_SAFE_INTEGER): Promise<Uint8Array> {
    if (!Number.isSafeInteger(maxBytes) || maxBytes < 0) throw new RangeError('maxBytes must be a nonnegative safe integer');
    if (this.byteLength > maxBytes) throw new RangeError(`suimon: journal bytes exceeds limit ${maxBytes}`);
    const bytes = new Uint8Array(this.byteLength);
    let offset = 0;
    for (const chunk of this.chunks) {
      bytes.set(chunk, offset);
      offset += chunk.length;
    }
    return bytes;
  }

  async truncate(byteLength: number): Promise<void> {
    if (!Number.isSafeInteger(byteLength) || byteLength < 0 || byteLength > this.byteLength) {
      throw new RangeError('byteLength must be a nonnegative safe integer within the journal');
    }
    const kept: Uint8Array[] = [];
    let remaining = byteLength;
    for (const chunk of this.chunks) {
      if (remaining === 0) break;
      kept.push(remaining >= chunk.length ? chunk : chunk.slice(0, remaining));
      remaining -= Math.min(remaining, chunk.length);
    }
    this.chunks = kept;
    this.byteLength = byteLength;
  }
}
