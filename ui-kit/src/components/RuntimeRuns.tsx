import { useMemo } from 'react';
import type { RuntimeState } from '../types';
import { runTree } from '../lib/status';
import type { RunNode } from '../lib/status';

/** Components also accept typed states directly, without the parser's validation. */
export function useRunTree(state?: RuntimeState): { nodes: RunNode[]; invalid: boolean } {
  return useMemo(() => {
    try { return { nodes: state ? runTree(state) : [], invalid: false }; }
    catch (error) {
      if (!(error instanceof TypeError)) throw error;
      return { nodes: [], invalid: true };
    }
  }, [state]);
}

export function InvalidRuntimeState() {
  return <p role="alert" className="sui-empty-small sui-tone-danger">Invalid runtime state: check run ownership and UI limits.</p>;
}
