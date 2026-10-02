import { fileURLToPath } from 'node:url';
import { defineConfig } from 'vite';
export default defineConfig({
  root: fileURLToPath(new URL('.', import.meta.url)),
  // Native filesystem events may be unavailable in a sandboxed local preview.
  server: { watch: { usePolling: true, useFsEvents: false, interval: 300 } },
  build: { outDir: '../.bench-dist', emptyOutDir: true },
});
