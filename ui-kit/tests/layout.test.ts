import { expect, it } from 'vitest';
import { layoutWorkflow } from '../src/lib/layout';
import { deriveKinds, findWorkflow, incoming, isEndpoint, outgoing } from '../src/lib/definition';
import { definition } from './helpers';

it('derives Single/Stream for each placement as the Lean rules do', () => {
  const users = definition('users');
  expect(deriveKinds(users, findWorkflow(users, 'users')!)).toEqual({ fetchAllUsers: 'stream', perUser: 'stream', all: 'single' });
  expect(deriveKinds(users, findWorkflow(users, 'profileFlow')!)).toEqual({ fetch: 'single', format: 'single' });
  const branch = definition('branch');
  expect(deriveKinds(branch, branch.workflows[0]!)).toEqual({ list: 'stream', paid: 'stream', ship: 'stream', receipts: 'single' });
  const merge = definition('merge');
  expect(Object.values(deriveKinds(merge, merge.workflows[0]!)).every(kind => kind === 'single')).toBe(true);
});

it('lays out placements in ranks along connections, with the entry and endpoints marked', () => {
  const users = definition('users');
  const layout = layoutWorkflow(users, 'users');
  const at = (name: string) => layout.nodes.find(n => n.name === name)!;
  expect(at('fetchAllUsers').position.y).toBeLessThan(at('perUser').position.y);
  expect(at('perUser').position.y).toBeLessThan(at('all').position.y);
  expect(at('perUser').height).toBeGreaterThan(at('all').height);
  expect(layout.nodes.filter(n => n.entry).map(n => n.name)).toEqual(['fetchAllUsers']);
  expect(layout.nodes.filter(n => n.endpoint).map(n => n.name)).toEqual(['all']);
  expect(layout.input).toMatchObject({ type: 'Tenant', placement: 'fetchAllUsers' });
  expect(layout.input!.position.y).toBeLessThan(at('fetchAllUsers').position.y);
  expect(layout.edges.map(e => [e.index, e.connection.transform, e.kind])).toEqual([[0, 'user', 'stream'], [1, 'summaries', 'stream']]);
});

it('keeps parallel placements apart, labels branch arms and honours given positions', () => {
  const merge = definition('merge'), w = merge.workflows[0]!;
  const layout = layoutWorkflow(merge, w, { page: { x: 900, y: 900 } });
  const positions = new Map(layout.nodes.map(n => [n.name, n.position]));
  expect(positions.get('sales')!.y).toBe(positions.get('stock')!.y);
  expect(positions.get('sales')!.x).not.toBe(positions.get('stock')!.x);
  expect(positions.get('page')).toEqual({ x: 900, y: 900 });
  expect(layout.input).toBeUndefined();
  expect(layout.nodes.filter(n => n.endpoint).map(n => n.name).sort()).toEqual(['archive', 'notify', 'page']);
  expect(incoming(w, 'widgets').map(c => c.index)).toEqual([0, 3]);
  expect(outgoing(w, 'sales').map(c => c.target)).toEqual(['widgets', 'archive', 'notify']);
  expect(isEndpoint(w, 'widgets')).toBe(false);
  const branch = definition('branch');
  expect(layoutWorkflow(branch, 'shipping').edges[1]!.connection.arm).toBe('paid');
  expect(() => layoutWorkflow(branch, 'nope')).toThrow(TypeError);
});
