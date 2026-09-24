import { readFileSync } from 'node:fs';
import { parseDefinition, parseRecords, parseState } from '../src/lib/parse';

export const definitionText = (name: string) => readFileSync(new URL(`../../Test/definitions/${name}.json`, import.meta.url), 'utf8');
export const definitionJson = (name: string): unknown => JSON.parse(definitionText(name));
export const definition = (name: string) => parseDefinition(definitionJson(name));
export const stateJson = (name: string): unknown => JSON.parse(readFileSync(new URL(`./fixtures/${name}.state.json`, import.meta.url), 'utf8'));
export const state = (name: string) => parseState(stateJson(name));
export const recordText = (name: string) => readFileSync(new URL(`./fixtures/${name}.records.jsonl`, import.meta.url), 'utf8');
export const records = (name: string) => parseRecords(recordText(name));
export const clone = <T>(value: T): T => structuredClone(value);
