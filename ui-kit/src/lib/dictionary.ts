// Names and ids are arbitrary strings. An object literal inherits from Object.prototype, where a key
// such as `toString` finds a function and assigning `__proto__` replaces the prototype instead of
// adding the key. Dictionaries the kit builds have no prototype; objects a caller supplies are read
// by their own keys.

/** An empty dictionary without a prototype, in which every string is only a key. */
export function dictionary<V>(): Record<string, V> {
  return Object.create(null) as Record<string, V>;
}

/** The value of `key` in an object a caller supplied; an inherited property is not a value. */
export function lookup<V>(object: Readonly<Record<string, V>> | null | undefined, key: string): V | undefined {
  return object != null && Object.hasOwn(object, key) ? object[key] : undefined;
}
