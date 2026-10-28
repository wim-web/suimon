import { defineConfig } from '@playwright/test';

export default defineConfig({
  testDir: './browser', testMatch: '**/*.browser.ts', fullyParallel: false, workers: 1,
  use: {
    baseURL: 'http://127.0.0.1:4177/suimon/', viewport: { width: 1440, height: 1000 },
    ...(process.env.PLAYWRIGHT_CHROMIUM_EXECUTABLE_PATH ? { launchOptions: { executablePath: process.env.PLAYWRIGHT_CHROMIUM_EXECUTABLE_PATH } } : {}),
  },
  webServer: {
    command: 'pnpm --filter @suimon/ui-kit build && pnpm build:wasm && pnpm exec vite preview --host 127.0.0.1 --port 4177 --strictPort --base /suimon/',
    url: 'http://127.0.0.1:4177/suimon/', reuseExistingServer: false, timeout: 120_000,
  },
});
