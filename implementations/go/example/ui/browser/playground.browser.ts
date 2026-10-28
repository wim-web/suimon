import { expect, test } from '@playwright/test';
import type { Page } from '@playwright/test';

interface RequestMessage { id: number; path: string; method: string; body: string }
const messages = (page: Page): Promise<RequestMessage[]> => page.evaluate(() =>
  (window as unknown as { sentToGo: RequestMessage[] }).sentToGo);
const polls = async (page: Page) => (await messages(page)).filter(message => /\/api\/runs\/[^/]+\?after=/.test(message.path));

test.beforeEach(async ({ page }) => {
  // Observe the native worker's requests without replacing it or its Go runtime.
  await page.addInitScript(() => {
    const sent: unknown[] = [];
    Object.defineProperty(window, 'sentToGo', { value: sent });
    const send = Worker.prototype.postMessage;
    Object.defineProperty(Worker.prototype, 'postMessage', { value: function (...args: unknown[]) {
      sent.push(structuredClone(args[0]));
      return Reflect.apply(send, this, args);
    } });
  });
  await page.goto('/suimon/');
  await expect(page.getByRole('combobox', { name: 'Scenario', exact: true })).toHaveValue('stream');
  expect(page.workers().map(worker => new URL(worker.url()).pathname)).toEqual(['/suimon/wasm-worker.js']);
});

test('changes scenarios, keeps focus after the workbench remounts, and preserves each input', async ({ page }) => {
  const scenario = page.getByRole('combobox', { name: 'Scenario', exact: true });
  const input = page.getByLabel('Input', { exact: true });
  const streamInput = '{"names":["stream-edited"]}';
  const batchInput = '{"names":["batch-edited"]}';
  await input.fill(streamInput);
  await scenario.selectOption('batch');
  await expect(scenario).toBeFocused();
  await expect(input).not.toHaveValue(streamInput);
  await expect(page.locator('.sui-sidebar')).toContainText('produceAll');
  await input.fill(batchInput);
  await scenario.selectOption('stream');
  await expect(scenario).toBeFocused();
  await expect(input).toHaveValue(streamInput);
  await expect(page.locator('.sui-sidebar')).toContainText('produce');
  await scenario.selectOption('batch');
  await expect(scenario).toBeFocused();
  await expect(input).toHaveValue(batchInput);
});

test('sends the chosen unit and input to Go, disables an active run, and polls through its report', async ({ page }) => {
  const unit = page.locator('#run-unit');
  const input = page.getByLabel('Input', { exact: true });
  await expect(unit).toHaveValue('600');
  await unit.selectOption('1000');
  await input.fill('{"names":["alpha","bravo","charlie"]}');
  await page.getByRole('button', { name: 'Run', exact: true }).click();
  await expect(page.getByRole('button', { name: 'Running…', exact: true })).toBeDisabled();
  await expect(unit).toBeDisabled();
  await expect(input).toBeDisabled();
  await expect(page.getByRole('button', { name: 'Cancel', exact: true })).toBeVisible();
  const starts = (await messages(page)).filter(message => message.path === '/api/runs');
  expect(starts).toHaveLength(1);
  expect(starts[0]!.method).toBe('POST');
  expect(JSON.parse(starts[0]!.body)).toEqual({ scenario: 'stream', input: { names: ['alpha', 'bravo', 'charlie'] }, unitMs: 1000 });

  const output = page.locator('.app-output pre');
  await expect(output).toBeVisible({ timeout: 15_000 });
  expect(JSON.parse(await output.innerText()).sort((a: { index: number }, b: { index: number }) => a.index - b.index)).toEqual([
    { index: 0, result: 'ALPHA' }, { index: 1, result: 'BRAVO' }, { index: 2, result: 'CHARLIE' },
  ]);
  await expect(page.getByRole('button', { name: 'Run', exact: true })).toBeEnabled();
  await expect(unit).toBeEnabled();
  await expect(unit).toHaveValue('1000');
  await expect(input).toBeEnabled();
  await expect(page.getByRole('alert')).toHaveCount(0);
  const receivedPolls = await polls(page);
  expect(receivedPolls.length).toBeGreaterThan(1);
  expect(receivedPolls[0]!.path).toMatch(/\?after=0$/);
  expect(receivedPolls.some(message => Number(new URL(message.path, page.url()).searchParams.get('after')) > 0)).toBe(true);
  expect((await messages(page)).filter(message => message.path.endsWith('/report'))).toHaveLength(1);
  // Completion must stop the 100ms polling loop, including after several possible timer ticks.
  await page.waitForTimeout(350);
  expect(await polls(page)).toHaveLength(receivedPolls.length);
});

test('cancels the active Go run and finishes polling its cancelled report', async ({ page }) => {
  await page.locator('#run-unit').selectOption('1000');
  await page.getByRole('button', { name: 'Run', exact: true }).click();
  await page.getByRole('button', { name: 'Cancel', exact: true }).click();
  const report = page.locator('.app-side .sui-sidebar-section').filter({ has: page.getByText('Report', { exact: true }) });
  await expect(report).toContainText('cancelled');
  await expect(page.getByRole('button', { name: 'Run', exact: true })).toBeEnabled();
  await expect(page.locator('#run-unit')).toBeEnabled();
  expect((await messages(page)).filter(message => message.path.endsWith('/cancel')).map(({ method, body }) => ({ method, body })))
    .toEqual([{ method: 'POST', body: '' }]);
  await expect(page.getByRole('alert')).toHaveCount(0);
  const count = (await polls(page)).length;
  await page.waitForTimeout(350);
  expect(await polls(page)).toHaveLength(count);
});
