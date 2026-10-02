import { expect, test } from '@playwright/test';
import type {} from '../bench/main';

test.beforeEach(async ({ page }) => {
  await page.goto('/');
  await page.waitForFunction(() => !!window.bench);
});

test('pages all invocations and results independently, preserving the page on updates', async ({ page }) => {
  await page.evaluate(() => window.bench.load(123));
  await page.locator('.sui-sidebar-node').click();
  const invocations = page.getByRole('region', { name: 'Invocations', exact: true });
  const results = page.getByRole('region', { name: 'Results', exact: true });
  await expect(invocations.locator('.sui-invocation')).toHaveCount(50);
  await expect(results.locator('details.sui-value')).toHaveCount(50);
  await expect(page.locator('.sui-placement-inspector .sui-json-tree')).toHaveCount(0);
  await expect(page.getByText(/more not shown/)).toHaveCount(0);
  await page.getByRole('button', { name: 'Next page of Invocations', exact: true }).click();
  await expect(invocations.locator('.sui-invocation').first()).toContainText('#51');
  await expect(results.locator('.sui-value-label').first()).toHaveText('#1');
  await page.getByLabel('Page of Results', { exact: true }).fill('3');
  await page.getByLabel('Page of Results', { exact: true }).press('Enter');
  await expect(results.locator('details.sui-value')).toHaveCount(23);
  await expect(results.locator('.sui-value-label').first()).toHaveText('#101');
  await results.locator('summary').last().click();
  await expect(results.locator('.sui-json-tree')).toContainText('"item": 122');
  await page.getByRole('button', { name: 'Last page of Invocations', exact: true }).click();
  await expect(invocations.locator('.sui-invocation')).toHaveCount(23);
  await page.evaluate(() => window.bench.snapshot());
  await expect(invocations.locator('.sui-invocation').first()).toContainText('#101');
  await expect(results.locator('.sui-json-tree')).toContainText('"item": 122');
  await page.evaluate(() => window.bench.load(5));
  await expect(invocations.locator('.sui-invocation')).toHaveCount(5);
  await expect(results.locator('details.sui-value')).toHaveCount(5);
  await expect(page.locator('.sui-placement-inspector .sui-json-tree')).toHaveCount(0);
  await page.evaluate(() => window.bench.load(123));
  await expect(invocations.locator('.sui-invocation').first()).toContainText('#1');
});

test('expands large JSON by properties and index ranges, with no text pagination or download', async ({ page }) => {
  await page.getByRole('button', { name: 'Large JSON', exact: true }).click();
  await page.locator('.sui-sidebar-node').click();
  const results = page.getByRole('region', { name: 'Results', exact: true });
  await expect(results.locator('.sui-json-tree')).toHaveCount(0);
  await results.locator('summary').click();
  const tree = results.locator('.sui-json-tree');
  await expect(tree).toContainText('"id": 9007199254740993');
  await expect(tree.locator('.sui-json-member')).toHaveCount(1);
  await tree.locator('summary').filter({ hasText: '"items"' }).click();
  await expect(tree).toContainText('Array · 150000 items');
  await expect(tree.locator('.sui-tree-range')).toHaveCount(15);
  await tree.getByText('[140000 … 149999]', { exact: true }).click();
  await tree.getByText('[149900 … 149999]', { exact: true }).click();
  await expect(tree.locator('.sui-json-member')).toHaveCount(101);
  await expect(tree).toContainText('[149999]: "large result value with extra text"');
  await expect(results.getByRole('navigation')).toHaveCount(0);
  await expect(page.locator('[download]')).toHaveCount(0);
  await results.locator(':scope > .sui-paged-content > details > summary').click();
  await expect(tree).toHaveCount(0);

  await page.getByRole('button', { name: 'Execution records', exact: true }).click();
  await page.locator('.sui-record-row').click();
  const record = page.locator('.sui-record-inspector');
  await expect(record.locator('.sui-json-tree')).toHaveCount(0);
  await record.locator('.sui-json > summary').click();
  await expect(record.locator('.sui-json')).toContainText('"seq": 1');
  expect(await record.locator('.sui-json').evaluate(el => el.textContent!.length)).toBeLessThan(1000);
  await record.locator('.sui-json > summary').click();
  await expect(record.locator('.sui-json-tree')).toHaveCount(0);

  await page.evaluate(() => window.bench.payload('{"id":9007199254740993,"text":"<b>done</b>","a":1,"a":2}'));
  await record.locator('.sui-value > summary').click();
  const members = record.locator('.sui-json-member');
  await expect(members).toHaveText(['"id": 9007199254740993', '"text": "<b>done</b>"', '"a": 1', '"a": 2']);
  await expect(record.locator('.sui-json-tree b')).toHaveCount(0);
});

test('keeps the workbench when loading a large list and expands only requested ranges', async ({ page }) => {
  await page.getByRole('button', { name: 'Large list', exact: true }).click();
  await expect(page.locator('.sui-workbench')).toBeVisible();
  await page.locator('.sui-sidebar-node').filter({ hasText: 'collected' }).click();
  const results = page.getByRole('region', { name: 'Results', exact: true });
  const root = results.locator('details.sui-value').first();
  await expect(root).toContainText('List · 100000 items');
  await expect(root.locator('details.sui-value')).toHaveCount(0);
  await root.locator(':scope > summary').click();
  await expect(root.locator('details.sui-value')).toHaveCount(0);
  await root.getByText('Items 90001–100000', { exact: true }).click();
  await root.getByText('Items 99901–100000', { exact: true }).click();
  const items = root.locator('details.sui-value');
  await expect(items).toHaveCount(100);
  await expect(root.locator('.sui-json-tree')).toHaveCount(0);
  await items.last().locator(':scope > summary').click();
  await expect(root.locator('.sui-json-tree')).toContainText('"item": 99999');
  await root.locator(':scope > summary').click();
  await expect(root.locator('details.sui-value')).toHaveCount(0);
  await page.getByRole('button', { name: 'Append 100', exact: true }).click();
  await expect(root).toContainText('List · 100100 items');
  await expect(page.locator('.sui-workbench')).toBeVisible();
  await page.getByRole('button', { name: 'Load 10,000', exact: true }).click();
  await expect(page.locator('.sui-workbench')).toBeVisible();
  await expect(page.locator('.sui-sidebar-node')).toContainText('work');
});
