import type { RunView, Scenario } from './api';
import type { TimelineLane } from './Timeline';

/* The playground keeps the latest run of each scenario with each unit, so that the timeline compares runs with the same unit. */

export const runKey = (scenario: string, unitMs: number) => `${scenario}@${unitMs}`;

/** The latest run of the scenario, if it has run; `latest` holds the unit of the latest run of each scenario. */
/** The unit the unit select shows for a scenario: that of its run while the run is in progress, the
    choice for the next run otherwise. */
export function shownUnit(current: RunView | undefined, next: number): number {
  return current !== undefined && !current.done ? current.unitMs : next;
}

export function latestRun(runs: Readonly<Record<string, RunView>>, latest: Readonly<Record<string, number>>, scenario: string): RunView | undefined {
  const unitMs = latest[scenario];
  return unitMs === undefined ? undefined : runs[runKey(scenario, unitMs)];
}

/**
 * The lanes of the timeline for the scenario: its latest run, and the run of the scenario it
 * compares with that has the same unit. Before the scenario has run, the lanes are for the chosen unit.
 */
export function timelineLanes(scenarios: readonly Scenario[], scenario: Scenario, runs: Readonly<Record<string, RunView>>,
  latest: Readonly<Record<string, number>>, unit: number): TimelineLane[] {
  const current = latestRun(runs, latest, scenario.id);
  const unitMs = current?.unitMs ?? unit;
  const compared = scenario.compare ? scenarios.filter(s => s.id === scenario.id || s.id === scenario.compare) : [scenario];
  return compared.map(s => {
    const r = s.id === scenario.id ? current : runs[runKey(s.id, unitMs)];
    return { key: s.id, label: s.title, unitMs, run: r ? { label: s.title, spans: r.spans, elapsedMs: r.elapsedMs, done: r.done } : null };
  });
}
