export type JsonValue = null | boolean | number | string | JsonValue[] | { [key: string]: JsonValue };
export type JsonObject = { [key: string]: JsonValue };

export interface Port { name: string; kind: 'plain' | 'stream' }
export interface PortRef { node: string; port: string }
export interface GraphEdge { src: PortRef; dst: PortRef }
export type NodeKind =
  | { type: 'leaf'; concurrency: number; retry: { maxAttempts: number; leaseSeconds: number; retrySeconds: number } }
  | { type: 'branch'; arms: string[] }
  | { type: 'loop'; body: Graph; maxIterations: number }
  | { type: 'subworkflow' | 'forEach'; body: Graph }
  | { type: 'waitAll' | 'coalesce' | 'collect' | 'filter' | 'merge' };

export interface GraphNode { id: string; kind: NodeKind; inputs: Port[]; outputs: Port[] }
export interface Graph { nodes: GraphNode[]; edges: GraphEdge[]; entries: PortRef[]; exits: PortRef[] }
export interface TraceEvent {
  schema_version: 2;
  sequence: number;
  txn: string;
  recorded_at: number;
  type: string;
  op: string | JsonObject | null;
  data: JsonObject;
}
export interface WorkflowSnapshot { graph: Graph; events: TraceEvent[]; values?: Record<string, JsonValue> }
export type PortSide = 'top' | 'bottom' | 'left' | 'right';
export interface NodePresentation { label?: string; description?: string; accent?: string; position?: { x: number; y: number }; inputSide?: PortSide; outputSide?: PortSide }
export type NodePresentations = Record<string, NodePresentation>;
export interface InstanceInfo { id: string; node: string; path: string[] }
export interface TraceTransaction { id: string; events: TraceEvent[]; start: number; committed: boolean }
export interface TraceIndex {
  events: TraceEvent[];
  committedEvents: TraceEvent[];
  committedSequences: Set<number>;
  instances: Map<string, InstanceInfo>;
  transactions: TraceTransaction[];
  executionInputs?: Set<string>;
  attempts: Map<string, { instance: string; status: string }>;
  successfulCompletions: Set<number>;
  status: string;
}
