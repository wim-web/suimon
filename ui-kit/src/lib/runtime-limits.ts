/** UI budgets, not engine limits. Ownership depth and opaque path length are independent. */
export const RUNTIME_LIMITS = Object.freeze({
  runs: 10_000,
  runDepth: 64,
  pathSegments: 64,
});
