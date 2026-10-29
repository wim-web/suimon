export class JsonNumber {
  constructor(readonly negative: boolean, readonly mantissa: bigint, readonly exponent: bigint) {}
}

export type JsonValue = null | boolean | string | number | bigint | JsonNumber | JsonValue[] | { [key: string]: JsonValue };
export type JsonObject = { [key: string]: JsonValue };
const fieldOrder = new WeakMap<JsonObject, string[]>();
export function jsonEntries(object: JsonObject): [string, JsonValue][] {
  return (fieldOrder.get(object) ?? Object.keys(object)).map(key => {
    const value = object[key];
    if (value === undefined) throw new Error(`wire field ${key} is undefined`);
    return [key, value];
  });
}
export const MAX_INPUT_BYTES = 1 << 20;
export const MAX_INPUT_DEPTH = 64;

export function checkInput(text: string): void {
  if (Buffer.byteLength(text, 'utf8') > MAX_INPUT_BYTES) throw new Error(`input exceeds maximum size of ${MAX_INPUT_BYTES} bytes`);
  let depth = 0, quoted = false, escaped = false;
  for (const c of text) {
    if (quoted) {
      if (escaped) escaped = false;
      else if (c === '\\') escaped = true;
      else if (c === '"') quoted = false;
    } else if (c === '"') quoted = true;
    else if (c === '[' || c === '{') {
      if (++depth > MAX_INPUT_DEPTH) throw new Error(`input exceeds maximum nesting depth of ${MAX_INPUT_DEPTH}`);
    } else if ((c === ']' || c === '}') && depth > 0) depth--;
  }
}

function scalarCompare(a: string, b: string): number {
  const x = Array.from(a), y = Array.from(b);
  for (let i = 0; i < Math.min(x.length, y.length); i++) {
    const p = x[i]?.codePointAt(0) ?? 0, q = y[i]?.codePointAt(0) ?? 0;
    if (p !== q) return p - q;
  }
  return x.length - y.length;
}

function quoteCore(c: string, inString: boolean): string {
  if (c === '\n') return '\\n';
  if (c === '\t') return '\\t';
  if (c === '\\') return '\\\\';
  if (c === '"') return '\\"';
  if (!inString && c === "'") return "\\'";
  const n = c.codePointAt(0) ?? 0;
  if (n < 32 || n === 127) return `\\x${n.toString(16).padStart(2, '0')}`;
  return c;
}
const quoteChar = (c: string): string => `'${quoteCore(c, false)}'`;
const quoteKey = (s: string): string => `"${Array.from(s, c => quoteCore(c, true)).join('')}"`;

function renderString(s: string, lean: boolean): string {
  let result = '"';
  for (const c of s) {
    const n = c.codePointAt(0) ?? 0;
    if (c === '"') result += '\\"';
    else if (c === '\\') result += '\\\\';
    else if (lean && c === '\n') result += '\\n';
    else if (lean && c === '\r') result += '\\r';
    else if (n < 32) result += `\\u${n.toString(16).padStart(4, '0')}`;
    else if (n >= 0xd800 && n <= 0xdfff) result += '\ufffd';
    else result += c;
  }
  return result + '"';
}

function render(value: JsonValue, lean: boolean): string {
  if (value === null) return 'null';
  if (typeof value === 'string') return renderString(value, lean);
  if (typeof value === 'boolean' || typeof value === 'bigint') return String(value);
  if (typeof value === 'number') {
    if (!Number.isSafeInteger(value) || value < 0) throw new Error('wire number must be a safe natural number');
    return String(value);
  }
  if (value instanceof JsonNumber) {
    const sign = value.negative && value.mantissa !== 0n ? '-' : '';
    return `${sign}${value.mantissa}${value.exponent === 0n ? '' : `e-${value.exponent}`}`;
  }
  if (Array.isArray(value)) return `[${value.map(v => render(v, lean)).join(',')}]`;
  const entries = jsonEntries(value);
  if (lean) entries.sort(([a], [b]) => scalarCompare(a, b));
  return `{${entries.map(([key, v]) => `${renderString(key, lean)}:${render(v, lean)}`).join(',')}}`;
}

export const renderWire = (value: JsonValue): string => render(value, false);
export const renderLean = (value: JsonValue): string => render(value, true);

const digit = (c: string | undefined): boolean => c !== undefined && c >= '0' && c <= '9';
const whitespace = (c: string | undefined): boolean => c === ' ' || c === '\t' || c === '\n' || c === '\r';
const escapes: Readonly<Record<string, string>> = { '"': '"', '\\': '\\', '/': '/', b: '\b', f: '\f', n: '\n', r: '\r', t: '\t' };

class Parser {
  private readonly chars: string[];
  private pos = 0;
  constructor(source: string, private readonly mode: 'definition' | 'trace') { this.chars = Array.from(source); }
  private peek(): string | undefined { return this.chars[this.pos]; }
  private ws(): void { while (whitespace(this.peek())) this.pos++; }
  private fail(message: string, at = this.pos): never {
    if (this.mode === 'trace') throw new Error(`${message} at offset ${at}`);
    const offset = Buffer.byteLength(this.chars.slice(0, at).join(''), 'utf8');
    throw new Error(`offset ${offset}: ${message}`);
  }
  private next(): string {
    const c = this.peek();
    if (c === undefined) this.fail('unexpected end of input');
    this.pos++;
    return c;
  }
  private lookahead(predicate: (c: string) => boolean, description: string): void {
    const c = this.peek();
    if (c === undefined) this.fail('unexpected end of input');
    if (!predicate(c)) this.fail(`expected ${description}`);
  }
  parse(): JsonValue {
    this.ws();
    const value = this.value();
    this.ws();
    const c = this.peek();
    if (c !== undefined) this.fail(this.mode === 'trace' ? `unexpected trailing character ${quoteChar(c)}` : 'expected end of input');
    return value;
  }
  private value(): JsonValue {
    this.ws();
    const c = this.peek();
    if (c === undefined) this.fail('unexpected end of input');
    if (c === '{') return this.object();
    if (c === '[') return this.array();
    if (c === '"') { this.pos++; return this.string(); }
    for (const [word, value] of [['true', true], ['false', false], ['null', null]] satisfies [string, JsonValue][]) {
      if (c === word[0]) {
        if (this.chars.slice(this.pos, this.pos + word.length).join('') !== word) {
          this.fail(this.mode === 'trace' ? 'invalid literal' : `expected: ${word}`, this.pos + (this.mode === 'trace' ? 1 : 0));
        }
        this.pos += word.length;
        return value;
      }
    }
    if (digit(c) || (this.mode === 'definition' && c === '-')) return this.number();
    this.fail(this.mode === 'trace' ? `unexpected character ${quoteChar(c)}` : 'unexpected input');
  }
  private object(): JsonObject {
    this.pos++;
    this.ws();
    const result: JsonObject = Object.create(null);
    const keys: string[] = [];
    fieldOrder.set(result, keys);
    if (this.peek() === undefined) this.fail(this.mode === 'trace' ? 'unterminated object' : 'unexpected end of input');
    if (this.peek() === '}') { this.pos++; return result; }
    for (;;) {
      this.ws();
      if (this.mode === 'trace') {
        if (this.peek() === undefined) this.fail('unterminated object');
        if (this.peek() !== '"') this.fail('expected a string key');
      } else this.lookahead(c => c === '"', '"');
      this.pos++;
      const key = this.string();
      if (Object.hasOwn(result, key)) this.fail(`duplicate key ${quoteKey(key)}`);
      this.ws();
      if (this.mode === 'trace') {
        if (this.peek() === undefined) this.fail('unterminated object');
        if (this.peek() !== ':') this.fail("expected ':'");
      } else this.lookahead(c => c === ':', ':');
      this.pos++;
      result[key] = this.value();
      keys.push(key);
      this.ws();
      if (this.mode === 'trace') {
        const c = this.peek();
        if (c === undefined) this.fail('unterminated object');
        if (c !== '}' && c !== ',') this.fail("expected ',' or '}'");
        this.pos++;
        if (c === '}') return result;
      } else {
        const c = this.next();
        if (c === '}') return result;
        if (c !== ',') this.fail('unexpected character in object');
      }
    }
  }
  private array(): JsonValue[] {
    this.pos++;
    this.ws();
    const result: JsonValue[] = [];
    if (this.peek() === undefined) this.fail(this.mode === 'trace' ? 'unterminated array' : 'unexpected end of input');
    if (this.peek() === ']') { this.pos++; return result; }
    for (;;) {
      result.push(this.value());
      this.ws();
      if (this.mode === 'trace') {
        const c = this.peek();
        if (c === undefined) this.fail('unterminated array');
        if (c !== ']' && c !== ',') this.fail("expected ',' or ']'");
        this.pos++;
        if (c === ']') return result;
      } else {
        const c = this.next();
        if (c === ']') return result;
        if (c !== ',') this.fail('unexpected character in array');
      }
    }
  }
  private hex(): number {
    const c = this.next();
    if (!/^[0-9a-fA-F]$/.test(c)) this.fail('invalid hex character');
    return Number.parseInt(c, 16);
  }
  private string(): string {
    let result = '';
    for (;;) {
      const c = this.peek();
      if (c === undefined) this.fail(this.mode === 'trace' ? 'unterminated string' : 'unexpected end of input');
      if (c === '"') { this.pos++; return result; }
      if (c === '\\') {
        const slash = this.pos++;
        const e = this.peek();
        if (e === undefined) this.fail(this.mode === 'trace' ? 'unterminated escape' : 'unexpected end of input');
        this.pos++;
        const simple = escapes[e];
        if (simple !== undefined) { result += simple; continue; }
        if (e !== 'u') this.fail(this.mode === 'trace' ? `invalid escape ${quoteChar(e)}` : 'illegal \\u escape');
        let n = 0;
        if (this.mode === 'trace') {
          if (slash + 6 > this.chars.length) this.fail('truncated \\u escape', slash + 2);
          const digits = this.chars.slice(slash + 2, slash + 6).join('');
          if (!/^[0-9a-fA-F]{4}$/.test(digits)) this.fail('invalid \\u escape', slash + 6);
          n = Number.parseInt(digits, 16);
          this.pos = slash + 6;
        } else for (let i = 0; i < 4; i++) n = n * 16 + this.hex();
        if (n < 0xd800 || n > 0xdfff) { result += String.fromCodePoint(n); continue; }
        if (n >= 0xdc00) {
          if (this.mode === 'trace') this.fail('unpaired low surrogate');
          result += '\ufffd';
          continue;
        }
        const low = this.chars.slice(this.pos, this.pos + 6).join('');
        if (this.mode === 'trace') {
          if (this.pos + 6 > this.chars.length) this.fail('unpaired high surrogate');
          if (!low.startsWith('\\u')) this.fail('unpaired high surrogate', this.pos + 6);
          if (!/^\\u[0-9a-fA-F]{4}$/.test(low)) this.fail('invalid \\u escape', this.pos + 6);
          const value = Number.parseInt(low.slice(2), 16);
          if (value < 0xdc00 || value > 0xdfff) this.fail('invalid low surrogate', this.pos + 6);
        }
        if (/^\\u[dD][c-fC-F][0-9a-fA-F]{2}$/.test(low)) {
          result += String.fromCodePoint(0x10000 + (n - 0xd800) * 0x400 + Number.parseInt(low.slice(2), 16) - 0xdc00);
          this.pos += 6;
        } else result += '\ufffd';
      } else {
        const n = c.codePointAt(0) ?? 0;
        if (n < 32) this.fail(this.mode === 'trace' ? 'control character in string' : 'unexpected character in string', this.pos + (this.mode === 'trace' ? 0 : 1));
        result += c;
        this.pos++;
      }
    }
  }
  private digits(): string {
    const start = this.pos;
    while (digit(this.peek())) this.pos++;
    return this.chars.slice(start, this.pos).join('');
  }
  private number(): bigint | JsonNumber {
    let negative = false;
    if (this.peek() === '-') { this.pos++; negative = true; }
    let whole: string;
    if (this.peek() === '0') {
      this.pos++;
      whole = '0';
      if (this.mode === 'trace' && digit(this.peek())) this.fail('leading zero in number');
    } else {
      this.lookahead(c => c >= '1' && c <= '9', '1-9');
      whole = this.digits();
    }
    if (this.mode === 'trace') return BigInt(whole);
    let fraction = '', exponent = 0n;
    if (this.peek() === '.') {
      this.pos++;
      this.lookahead(digit, 'digit');
      fraction = this.digits();
      exponent = BigInt(fraction.length);
    }
    let mantissa = BigInt(whole + fraction);
    if (this.peek() === 'e' || this.peek() === 'E') {
      this.pos++;
      const sign = this.peek();
      if (sign === undefined) this.fail('unexpected end of input');
      if (sign === '-' || sign === '+') this.pos++;
      this.lookahead(digit, '0-9');
      const shift = BigInt(this.digits());
      if (sign === '-') exponent += shift;
      else {
        if (shift > (1n << 64n)) this.fail('exp too large');
        if (shift <= exponent) exponent -= shift;
        else {
          const padding = shift - exponent;
          exponent = 0n;
          if (mantissa !== 0n) mantissa *= 10n ** (padding > 64n ? 64n : padding);
        }
      }
    }
    if (mantissa === 0n) return 0n;
    while (exponent > 0n && mantissa % 10n === 0n) { mantissa /= 10n; exponent--; }
    if (exponent === 0n) return negative ? -mantissa : mantissa;
    return new JsonNumber(negative, mantissa, exponent);
  }
}

export function parseJson(text: string, mode: 'definition' | 'trace'): JsonValue {
  checkInput(text);
  if (/[\uD800-\uDFFF]/u.test(text)) throw new Error('invalid UTF-8');
  return new Parser(text, mode).parse();
}
