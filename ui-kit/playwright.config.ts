import { defineConfig } from '@playwright/test';
export default defineConfig({
  testDir: './browser', testMatch: '**/*.browser.ts', fullyParallel: false, workers: 1,
  use: { baseURL: 'http://127.0.0.1:4176', viewport: { width: 1440, height: 1000 },
    ...(process.env.PLAYWRIGHT_CHROMIUM_EXECUTABLE_PATH ? { launchOptions: { executablePath: process.env.PLAYWRIGHT_CHROMIUM_EXECUTABLE_PATH } } : {}) },
  webServer: { command: 'pnpm exec vite build --config bench/vite.config.ts && pnpm exec vite preview --config bench/vite.config.ts --host 127.0.0.1 --port 4176 --strictPort', url: 'http://127.0.0.1:4176', reuseExistingServer: false },
});
