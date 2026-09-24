import type { Body, Connection, Control, Definition, Placement, ValueType, Workflow } from '../types';

export type Kind = 'single' | 'stream';
export interface IndexedConnection extends Connection { index: number }

export function findWorkflow(definition: Definition, id: string): Workflow | undefined {
  return definition.workflows.find(w => w.id === id);
}
export function findPlacement(workflow: Workflow | undefined, name: string): Placement | undefined {
  return workflow?.placements.find(p => p.name === name);
}
export function renderValueType(type: ValueType): string {
  return typeof type === 'string' ? type : `List<${renderValueType(type.list)}>`;
}
export function isEntry(workflow: Workflow, name: string): boolean { return workflow.input?.placement === name; }
/** A placement without outgoing connections is an endpoint (§13.2). */
export function isEndpoint(workflow: Workflow, name: string): boolean { return !workflow.connections.some(c => c.source === name); }

/** Connections keep their index in the workflow; the runtime state refers to them by that index. */
export function incoming(workflow: Workflow, name: string): IndexedConnection[] {
  return workflow.connections.flatMap((c, index) => c.target === name ? [{ ...c, index }] : []);
}
export function outgoing(workflow: Workflow, name: string): IndexedConnection[] {
  return workflow.connections.flatMap((c, index) => c.source === name ? [{ ...c, index }] : []);
}

/** The workflows a placement calls: its own body, or the bodies of its concurrency tasks. */
export function calledWorkflows(control: Control): { workflow: string; output: string; task?: string }[] {
  if (control.type === 'subworkflow') return [{ workflow: control.workflow, output: control.output }];
  if (control.type === 'concurrency') return control.tasks.flatMap(t => t.body.type === 'subworkflow' ? [{ workflow: t.body.workflow, output: t.body.output, task: t.name }] : []);
  return [];
}

export function bodyLabel(body: Body): string {
  return body.type === 'function' ? body.function : `${body.workflow} → ${body.output}`;
}

function bodyKind(definition: Definition, body: Body): Kind | null {
  if (body.type === 'subworkflow') return findWorkflow(definition, body.workflow) ? 'single' : null;
  const decl = definition.functions.find(f => f.id === body.function);
  return decl ? ('single' in decl.output ? 'single' : 'stream') : null;
}

/** Output kind of one control from its input kind (§5.2, §8.4); undefined input means no input. */
function outputKind(definition: Definition, control: Control, input: Kind | undefined): Kind | null {
  switch (control.type) {
    case 'function': case 'subworkflow': return input === 'stream' ? 'stream' : bodyKind(definition, control);
    case 'branch': return input ?? null;
    case 'waitStream': return input === 'stream' ? 'single' : null;
    case 'merge': return input === 'single' ? 'single' : null;
    case 'concurrency': return input === 'stream' ? 'stream' : control.output === 'list' ? 'single' : 'stream';
  }
}

/**
 * Single/Stream of each placement's output, derived as in Suimon/Derive.lean. A placement whose
 * kind cannot be derived (an invalid or unchecked definition) gets null.
 */
export function deriveKinds(definition: Definition, workflow: Workflow): Record<string, Kind | null> {
  const kinds: Record<string, Kind | null> = {};
  const visiting = new Set<string>();
  const kindOf = (name: string): Kind | null => {
    if (Object.hasOwn(kinds, name)) return kinds[name]!;
    const placement = findPlacement(workflow, name);
    if (!placement || visiting.has(name)) return null;
    visiting.add(name);
    const sources = workflow.connections.filter(c => c.target === name).map(c => kindOf(c.source));
    visiting.delete(name);
    let input: Kind | undefined | null;
    if (isEntry(workflow, name)) input = sources.length ? null : 'single';
    else if (!sources.length) input = undefined;
    else input = sources.every(k => k !== null && k === sources[0]) ? sources[0] : null;
    const kind = input === null ? null : outputKind(definition, placement.node, input);
    kinds[name] = kind;
    return kind;
  };
  for (const p of workflow.placements) kindOf(p.name);
  return kinds;
}
