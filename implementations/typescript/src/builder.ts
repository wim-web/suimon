import { Engine } from './engine.js';
import { iteratorOf, synchronousTransformResult } from './callbacks.js';
import type { Body, Definition, Policy, Timeout, ValueType, Workflow } from './model-types.js';
import type { Awaitable, Binding, CallContext, EngineOptions, Execution, RecoverableJournal, Report, ResumeOptions, Sequence, StartOptions } from './runtime-types.js';

export class Type<T> {
  declare private readonly invariant: (value: T) => T;
  constructor(readonly schema: ValueType, readonly parse: (value: unknown) => T) {}
}
export function defineType<T>(name: string, parse: (value: unknown) => T): Type<T> {
  if (!name) throw new Error('A type name must not be empty');
  return new Type(name, parse);
}
export function listOf<T>(element: Type<T>): Type<readonly T[]> {
  return new Type<readonly T[]>({ list: element.schema }, value => {
    if (!Array.isArray(value)) throw new TypeError('Expected an array');
    return value.map(item => element.parse(item));
  });
}
function parsedSequence<T>(sequence: Sequence<T>, parse: (value: unknown) => T): AsyncIterable<T> {
  return {
    [Symbol.asyncIterator]() {
      const iterator = iteratorOf(sequence);
      let closing = false;
      return {
        async next() {
          const item = await iterator.next();
          if (item.done) return { done: true, value: undefined };
          return { done: false, value: closing ? item.value : parse(item.value) };
        },
        async return() {
          closing = true;
          return iterator.return ? await iterator.return() : { done: true, value: undefined };
        },
      };
    },
  };
}

export interface ControlSettings { policy: Policy }
export interface FunctionSettings extends ControlSettings { timeout?: Timeout }

class BodyRef<I, O> {
  constructor(readonly owner: DefinitionBuilder, readonly body: Body,
    readonly input: Type<I> | undefined, readonly output: Type<O>) {}
}
export class FunctionRef<I, O> extends BodyRef<I, O> { readonly kind = 'function'; }
export class WorkflowBody<I, O> extends BodyRef<I, O> { readonly kind = 'workflow'; }
export class JudgeRef<I, A extends string> {
  constructor(readonly owner: DefinitionBuilder, readonly id: string,
    readonly input: Type<I>, readonly arms: readonly A[]) {}
}
export class TransformRef<I, O> {
  constructor(readonly owner: DefinitionBuilder, readonly id: string,
    readonly input: Type<I>, readonly output: Type<O>) {}
}
export class Discard<I> {
  readonly id = 'discard';
  readonly output: Type<void> | undefined = undefined;
  constructor(readonly input: Type<I>) {}
}
export function discard<I>(input: Type<I>): Discard<I> { return new Discard(input); }
type InputTransform<I, O> = TransformRef<I, O> | (O extends void ? Discard<I> : never);

interface Target<I> { readonly graph: object; readonly name: string; readonly input: Type<I> | undefined }
export class Source<O> {
  constructor(readonly graph: object, readonly name: string, readonly output: Type<O>, readonly armName?: string) {}
}
export class Node<I, O> extends Source<O> implements Target<I> {
  constructor(graph: object, name: string, readonly input: Type<I> | undefined, output: Type<O>) { super(graph, name, output); }
}
export class Branch<I, A extends string> implements Target<I> {
  constructor(readonly graph: object, readonly name: string, readonly input: Type<I>, readonly arms: readonly A[]) {}
  arm(name: A): Source<I> {
    if (!this.arms.includes(name)) throw new Error(`Unknown branch arm: ${name}`);
    return new Source(this.graph, this.name, this.input, name);
  }
}

interface TaskData { name: string; body: Body; inputTransform?: string; outputTransform?: string; policy: Policy; timeout?: Timeout }
export class IncludedTask<I, O> {
  readonly kind = 'included';
  constructor(readonly owner: DefinitionBuilder, readonly input: Type<I> | undefined,
    readonly output: Type<O>, readonly data: TaskData) {}
}
export class ExcludedTask<I> {
  readonly kind = 'excluded';
  constructor(readonly owner: DefinitionBuilder, readonly input: Type<I> | undefined, readonly data: TaskData) {}
}
type AnyTask<I, O> = IncludedTask<I, O> | ExcludedTask<I>;
interface ConcurrencyOptions<I, O> extends ControlSettings {
  input: Type<I>; element: Type<O>; limit: bigint; tasks: readonly AnyTask<NoInfer<I>, NoInfer<O>>[];
}
interface NoInputConcurrencyOptions<O> extends ControlSettings {
  element: Type<O>; limit: bigint; tasks: readonly AnyTask<void, NoInfer<O>>[];
}

export class DefinitionBuilder {
  private readonly definition: Definition = { main: '', functions: [], judges: [], transforms: [], workflows: [] };
  private readonly bindings: Binding[] = [];
  private readonly names = new Set<string>();

  private reserve(kind: string, id: string): void {
    if (!id) throw new Error('An identifier must not be empty');
    const key = `${kind}:${id}`;
    if (this.names.has(key)) throw new Error(`Duplicate ${kind}: ${id}`);
    this.names.add(key);
  }
  private own(owner: DefinitionBuilder): void {
    if (owner !== this) throw new Error('Handles must belong to the same definition builder');
  }
  func<I, O>(id: string, input: Type<I>, output: Type<O>, run: (input: I, context: CallContext) => Awaitable<O>): FunctionRef<I, O> {
    this.reserve('function', id);
    this.definition.functions.push({ id, input: input.schema, output: { single: output.schema } });
    this.bindings.push({ kind: 'single', id, input: true, run: async (value, context) => output.parse(await run(input.parse(value), context)) });
    return new FunctionRef(this, { type: 'function', function: id }, input, output);
  }
  funcNoInput<O>(id: string, output: Type<O>, run: (context: CallContext) => Awaitable<O>): FunctionRef<void, O> {
    this.reserve('function', id);
    this.definition.functions.push({ id, output: { single: output.schema } });
    this.bindings.push({ kind: 'single', id, input: false, run: async (_value, context) => output.parse(await run(context)) });
    return new FunctionRef(this, { type: 'function', function: id }, undefined, output);
  }
  stream<I, O>(id: string, input: Type<I>, output: Type<O>, run: (input: I, context: CallContext) => Awaitable<Sequence<O>>): FunctionRef<I, O> {
    this.reserve('function', id);
    this.definition.functions.push({ id, input: input.schema, output: { stream: output.schema } });
    this.bindings.push({ kind: 'stream', id, input: true, run: async (value, context) => parsedSequence(await run(input.parse(value), context), output.parse) });
    return new FunctionRef(this, { type: 'function', function: id }, input, output);
  }
  streamNoInput<O>(id: string, output: Type<O>, run: (context: CallContext) => Awaitable<Sequence<O>>): FunctionRef<void, O> {
    this.reserve('function', id);
    this.definition.functions.push({ id, output: { stream: output.schema } });
    this.bindings.push({ kind: 'stream', id, input: false, run: async (_value, context) => parsedSequence(await run(context), output.parse) });
    return new FunctionRef(this, { type: 'function', function: id }, undefined, output);
  }
  transform<I, O>(id: string, input: Type<I>, output: Type<O>, run: (input: I) => O): TransformRef<I, O> {
    if (id === 'discard') throw new Error('discard is reserved');
    this.reserve('transform', id);
    this.definition.transforms.push({ id, input: input.schema, output: output.schema });
    this.bindings.push({ kind: 'transform', id, run: value => output.parse(synchronousTransformResult(run(input.parse(value)))) });
    return new TransformRef(this, id, input, output);
  }
  passthrough<T>(id: string, type: Type<T>): TransformRef<T, T> { return this.transform(id, type, type, value => value); }
  judge<I, const A extends string>(id: string, input: Type<I>, arms: readonly [A, ...A[]], run: (input: I, context: CallContext) => Awaitable<A>): JudgeRef<I, A> {
    this.reserve('judge', id);
    this.definition.judges.push({ id, input: input.schema });
    this.bindings.push({ kind: 'judge', id, run: (value, context) => run(input.parse(value), context) });
    return new JudgeRef(this, id, input, [...arms]);
  }
  workflow<I>(id: string, input: Type<I>): WorkflowBuilder<I>;
  workflow(id: string): WorkflowBuilder<void>;
  workflow<I>(id: string, input?: Type<I>): WorkflowBuilder<I> {
    this.reserve('workflow', id);
    const workflow: Workflow = { id, placements: [], connections: [] };
    this.definition.workflows.push(workflow);
    return new WorkflowBuilder(this, workflow, input);
  }
  task<I, B, R, O>(name: string, body: FunctionRef<B, R>, input: InputTransform<I, NoInfer<B>>, output: TransformRef<NoInfer<R>, O>, settings: FunctionSettings): IncludedTask<I, O>;
  task<I, B, R, O>(name: string, body: WorkflowBody<B, R>, input: InputTransform<I, NoInfer<B>>, output: TransformRef<NoInfer<R>, O>, settings: ControlSettings): IncludedTask<I, O>;
  task<I, B, R, O>(name: string, body: BodyRef<B, R>, input: InputTransform<I, NoInfer<B>>, output: TransformRef<NoInfer<R>, O>, settings: FunctionSettings): IncludedTask<I, O> {
    this.own(body.owner); this.own(output.owner);
    if (input instanceof TransformRef) this.own(input.owner);
    return new IncludedTask(this, input.input, output.output, { name, body: body.body, inputTransform: input.id, outputTransform: output.id, ...settings });
  }
  sideTask<I, B, R>(name: string, body: FunctionRef<B, R>, input: InputTransform<I, NoInfer<B>>, settings: FunctionSettings): ExcludedTask<I>;
  sideTask<I, B, R>(name: string, body: WorkflowBody<B, R>, input: InputTransform<I, NoInfer<B>>, settings: ControlSettings): ExcludedTask<I>;
  sideTask<I, B, R>(name: string, body: BodyRef<B, R>, input: InputTransform<I, NoInfer<B>>, settings: FunctionSettings): ExcludedTask<I> {
    this.own(body.owner);
    if (input instanceof TransformRef) this.own(input.owner);
    return new ExcludedTask(this, input.input, { name, body: body.body, inputTransform: input.id, ...settings });
  }
  taskNoInput<R, O>(name: string, body: FunctionRef<void, R>, output: TransformRef<NoInfer<R>, O>, settings: FunctionSettings): IncludedTask<void, O>;
  taskNoInput<R, O>(name: string, body: WorkflowBody<void, R>, output: TransformRef<NoInfer<R>, O>, settings: ControlSettings): IncludedTask<void, O>;
  taskNoInput<R, O>(name: string, body: BodyRef<void, R>, output: TransformRef<NoInfer<R>, O>, settings: FunctionSettings): IncludedTask<void, O> {
    this.own(body.owner); this.own(output.owner);
    return new IncludedTask(this, undefined, output.output, { name, body: body.body, outputTransform: output.id, ...settings });
  }
  sideTaskNoInput<R>(name: string, body: FunctionRef<void, R>, settings: FunctionSettings): ExcludedTask<void>;
  sideTaskNoInput<R>(name: string, body: WorkflowBody<void, R>, settings: ControlSettings): ExcludedTask<void>;
  sideTaskNoInput<R>(name: string, body: BodyRef<void, R>, settings: FunctionSettings): ExcludedTask<void> {
    this.own(body.owner);
    return new ExcludedTask(this, undefined, { name, body: body.body, ...settings });
  }
  build<I>(main: WorkflowBuilder<I>, options?: EngineOptions): TypedEngine<I> {
    this.own(main.owner);
    const definition = structuredClone({ ...this.definition, main: main.id });
    return new TypedEngine(new Engine(definition, this.bindings.slice(), options), main, main.input);
  }
}

export class WorkflowBuilder<I> {
  constructor(readonly owner: DefinitionBuilder, private readonly workflow: Workflow, readonly input: Type<I> | undefined) {}
  get id(): string { return this.workflow.id; }
  private own(source: { graph: object }): void {
    if (source.graph !== this) throw new Error('A connection must stay within its workflow');
  }
  private add(name: string, body: Body | { type: 'branch'; judge: string; arms: string[] } | { type: 'waitStream' | 'merge'; element: ValueType }, settings: FunctionSettings): void {
    if (this.workflow.placements.some(item => item.name === name)) throw new Error(`Duplicate placement: ${name}`);
    this.workflow.placements.push({ name, node: body, ...settings });
  }
  entry<O>(target: Target<NoInfer<I>> & Source<O>): void;
  entry<A extends string>(target: Branch<NoInfer<I>, A>): void;
  entry(target: Target<I>): void {
    this.own(target);
    if (!this.input) throw new Error('This workflow takes no input');
    if (this.workflow.input) throw new Error('The workflow entry is already set');
    this.workflow.input = { type: this.input.schema, placement: target.name };
  }
  call<A, O>(name: string, body: FunctionRef<A, O>, settings: FunctionSettings): Node<A, O>;
  call<A, O>(name: string, body: WorkflowBody<A, O>, settings: ControlSettings): Node<A, O>;
  call<A, O>(name: string, body: BodyRef<A, O>, settings: FunctionSettings): Node<A, O> {
    if (body.owner !== this.owner) throw new Error('Body belongs to another definition');
    this.add(name, body.body, settings);
    return new Node(this, name, body.input, body.output);
  }
  branch<A, const Arms extends string>(name: string, judge: JudgeRef<A, Arms>, settings: FunctionSettings): Branch<A, Arms> {
    if (judge.owner !== this.owner) throw new Error('Judge belongs to another definition');
    this.add(name, { type: 'branch', judge: judge.id, arms: [...judge.arms] }, settings);
    return new Branch(this, name, judge.input, judge.arms);
  }
  waitStream<T>(name: string, element: Type<T>, settings: ControlSettings): Node<T, readonly T[]> {
    this.add(name, { type: 'waitStream', element: element.schema }, settings);
    return new Node(this, name, element, listOf(element));
  }
  merge<T>(name: string, element: Type<T>, settings: ControlSettings): Node<T, readonly T[]> {
    this.add(name, { type: 'merge', element: element.schema }, settings);
    return new Node(this, name, element, listOf(element));
  }
  connect<A, B>(source: Source<A>, target: Target<B>, via: TransformRef<NoInfer<A>, NoInfer<B>>): void;
  connect<A>(source: Source<A>, target: Target<void>, via: Discard<NoInfer<A>>): void;
  connect<A, B>(source: Source<A>, target: Target<B>, via: TransformRef<A, B> | Discard<A>): void {
    this.own(source); this.own(target);
    if (via instanceof TransformRef && via.owner !== this.owner) throw new Error('Transform belongs to another definition');
    this.workflow.connections.push({ source: source.name, target: target.name, transform: via.id,
      ...(source.armName === undefined ? {} : { arm: source.armName }) });
  }
  concurrency<A, O>(name: string, options: ConcurrencyOptions<A, O> & { output: 'list' }): Node<A, readonly O[]>;
  concurrency<A, O>(name: string, options: ConcurrencyOptions<A, O> & { output: 'stream' }): Node<A, O>;
  concurrency<A, O>(name: string, options: ConcurrencyOptions<A, O> & { output: 'list' | 'stream' }): Node<A, O> | Node<A, readonly O[]> {
    this.addConcurrency(name, options.input.schema, options);
    return options.output === 'list' ? new Node(this, name, options.input, listOf(options.element)) : new Node(this, name, options.input, options.element);
  }
  concurrencyNoInput<O>(name: string, options: NoInputConcurrencyOptions<O> & { output: 'list' }): Node<void, readonly O[]>;
  concurrencyNoInput<O>(name: string, options: NoInputConcurrencyOptions<O> & { output: 'stream' }): Node<void, O>;
  concurrencyNoInput<O>(name: string, options: NoInputConcurrencyOptions<O> & { output: 'list' | 'stream' }): Node<void, O> | Node<void, readonly O[]> {
    this.addConcurrency(name, undefined, options);
    return options.output === 'list' ? new Node(this, name, undefined, listOf(options.element)) : new Node(this, name, undefined, options.element);
  }
  private addConcurrency<A, O>(name: string, input: ValueType | undefined,
    options: ControlSettings & { element: Type<O>; limit: bigint; output: 'list' | 'stream'; tasks: readonly AnyTask<A, O>[] }): void {
    if (this.workflow.placements.some(item => item.name === name)) throw new Error(`Duplicate placement: ${name}`);
    for (const task of options.tasks) if (task.owner !== this.owner) throw new Error('Task belongs to another definition');
    this.workflow.placements.push({ name, policy: options.policy, node: { type: 'concurrency', limit: options.limit,
      tasks: options.tasks.map(task => structuredClone(task.data)), element: options.element.schema, output: options.output,
      ...(input === undefined ? {} : { input }) } });
  }
  body<O>(endpoint: Source<O>): WorkflowBody<I, O> {
    this.own(endpoint);
    if (endpoint.armName !== undefined) throw new Error('A branch arm is not a workflow endpoint');
    if (this.workflow.connections.some(edge => edge.source === endpoint.name)) throw new Error('Subworkflow output must be an endpoint');
    return new WorkflowBody(this.owner, { type: 'subworkflow', workflow: this.id, output: endpoint.name }, this.input, endpoint.output);
  }
}

export class TypedReport {
  constructor(readonly report: Report, private readonly graph: object) {}
  get status() { return this.report.status; }
  get failures() { return this.report.failures; }
  get endpoints() { return this.report.endpoints; }
  get state() { return this.report.state; }
  output<T>(endpoint: Source<T>): T {
    if (endpoint.graph !== this.graph) throw new Error('Output belongs to another workflow');
    if (!this.report.outputs.has(endpoint.name)) throw new Error(`No output: ${endpoint.name}`);
    return endpoint.output.parse(this.report.outputs.get(endpoint.name));
  }
}
export interface TypedExecution { cancel(): void; wait(): Promise<TypedReport> }
export class TypedEngine<I> {
  constructor(private readonly engine: Engine, private readonly graph: object, private readonly input: Type<I> | undefined) {}
  private wrap(execution: Execution): TypedExecution {
    return { cancel: () => execution.cancel(), wait: async () => new TypedReport(await execution.wait(), this.graph) };
  }
  async start(...args: I extends void ? [input?: undefined, options?: StartOptions] : [input: I, options?: StartOptions]): Promise<TypedExecution> {
    const [input, options] = args;
    return this.wrap(await this.engine.start(this.input ? this.input.parse(input) : input, options));
  }
  async run(...args: I extends void ? [input?: undefined, options?: StartOptions] : [input: I, options?: StartOptions]): Promise<TypedReport> {
    return (await this.start(...args)).wait();
  }
  async resume(journal: RecoverableJournal, options?: ResumeOptions): Promise<TypedExecution> {
    return this.wrap(await this.engine.resume(journal, options));
  }
}
