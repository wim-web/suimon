import { expect, test } from '@playwright/test';
import type {} from '../bench/main';

for (const count of [10_000, 100_000]) test(`${count} records: bounded rows, updates, navigation and filtering`, async ({ page }, info) => {
  const errors: string[] = [];
  page.on('pageerror', error => errors.push(error.message));
  await page.goto('/');
  await page.waitForFunction(() => !!window.bench);
  await page.evaluate(() => window.bench.load(100));
  const coldLoadMs = await page.evaluate(n => window.bench.load(n), count);
  const loadSamples: number[] = [];
  for (let i = 0; i < 5; i++) loadSamples.push(await page.evaluate(n => window.bench.load(n), count));
  const loadMs = [...loadSamples].sort((a, b) => a - b)[2]!;
  const openMs = await page.evaluate(() => window.bench.measure(() => document.querySelector<HTMLButtonElement>('button[aria-label="Execution records"]')!.click()));
  const rows = page.locator('.sui-record-row');
  await expect(rows.first()).toHaveAttribute('data-record-seq', '1');
  expect(await rows.count()).toBeLessThan(40);
  const initialRows = await rows.count();
  const geometry = await rows.first().evaluate(el => el.getBoundingClientRect().height);
  expect(geometry).toBe(34);

  const scrollMs = await page.evaluate(() => window.bench.measure(() => {
    const list = document.querySelector<HTMLElement>('.sui-record-table')!;
    list.scrollTop = list.scrollHeight;
  }));
  await expect(rows.last()).toHaveAttribute('data-record-seq', String(count * 2 - 1));
  await expect(rows.last()).toBeInViewport();
  expect(await rows.count()).toBeLessThan(40);
  await rows.last().focus();
  const detailMs = await page.evaluate(() => window.bench.measure(() => (document.activeElement as HTMLButtonElement).click()));
  await expect(page.locator('.sui-record-inspector')).toContainText(`RECORD ${count * 2 - 1}`);
  await expect(page.locator('.sui-record-inspector .sui-json-tree')).toHaveCount(0);
  await page.locator('.sui-record-inspector .sui-value > summary').first().click();
  await expect(page.locator('.sui-record-inspector .sui-json-tree').first()).toContainText(`"item": ${count - 1}`);
  await page.getByRole('button', { name: 'Previous record', exact: true }).click();
  await expect(page.locator('.sui-record-row.is-selected')).toHaveAttribute('data-record-seq', String(count * 2 - 3));
  await expect(page.locator('.sui-record-row.is-selected')).toBeInViewport();

  // Focus and select records beyond the currently mounted range without a mouse.
  await page.locator('.sui-record-row.is-selected').focus();
  await page.keyboard.press('Home');
  await expect(rows.first()).toBeFocused();
  await page.keyboard.press('Shift+Tab');
  await expect(page.getByLabel('Execution record list', { exact: true })).toBeFocused();
  await page.keyboard.press('Shift+Tab');
  await expect(page.getByRole('button', { name: 'Close records', exact: true })).toBeFocused();
  await page.keyboard.press('Tab');
  await page.keyboard.press('ArrowDown');
  await expect(rows.first()).toBeFocused();
  await page.keyboard.press('Enter');
  await expect(page.locator('.sui-record-inspector')).toContainText('RECORD 1');
  await page.keyboard.press('End');
  await expect(rows.last()).toBeFocused();
  await page.keyboard.press('ArrowUp');
  await expect(page.locator(`[data-record-seq="${count * 2 - 3}"]`)).toBeFocused();
  await page.keyboard.press('PageUp');
  await page.keyboard.press('Enter');
  await expect(page.locator('.sui-record-row.is-selected')).toBeFocused();

  const appendMs: number[] = [];
  for (let i = 0; i < 3; i++) appendMs.push(await page.evaluate(() => window.bench.append()));
  const snapshotMs = await page.evaluate(() => window.bench.snapshot());
  expect(await rows.count()).toBeLessThan(40);
  // Shrinking the filtered dataset while scrolled far down must not leave a blank viewport.
  await page.evaluate(() => window.bench.tear());
  await page.getByLabel('Commit state', { exact: true }).selectOption('uncommitted');
  await expect(rows).toHaveCount(1);
  await expect(rows.first()).toContainText('uncommitted');
  await expect(rows.first()).toBeInViewport();
  await page.getByLabel('Commit state', { exact: true }).selectOption('all');
  await page.getByLabel('Run', { exact: true }).selectOption('[]');
  expect(await rows.count()).toBeLessThan(40);
  await page.locator('.sui-record-panel').evaluate(el => { (el as HTMLElement).style.flexBasis = '500px'; });
  await expect.poll(() => rows.count()).toBeGreaterThan(initialRows);
  expect(await rows.count()).toBeLessThan(50);

  // Large placement details must use the index too (50 invocation previews, not 50 full scans).
  const placementMs = await page.evaluate(() => window.bench.measure(() => document.querySelector<HTMLButtonElement>('.sui-sidebar-node')!.click()));
  await expect(page.locator('.sui-placement-inspector')).toContainText('Invocations');
  await expect(page.locator('.sui-invocation')).toHaveCount(50);
  expect(errors).toEqual([]);
  const metrics = { count, initialRows, coldLoadMs, loadMs, loadSamples, openMs, scrollMs, detailMs, appendMs, snapshotMs, placementMs };
  console.log(JSON.stringify(metrics));
  await info.attach('timings', { body: JSON.stringify(metrics, null, 2), contentType: 'application/json' });
  await page.screenshot({ path: info.outputPath('workbench.png') });
  await page.evaluate(() => { const list = document.querySelector<HTMLElement>('.sui-record-table')!; list.scrollTop = list.scrollHeight; });
  await page.evaluate(() => window.bench.load(5));
  await expect(rows).toHaveCount(5);
  await expect(rows.first()).toBeInViewport();
  await page.evaluate(() => window.bench.load(0));
  await expect(rows).toHaveCount(0);
  await expect(page.getByText('No execution records', { exact: true })).toBeVisible();
});
