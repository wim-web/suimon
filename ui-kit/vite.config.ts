import { defineConfig } from 'vite';

export default defineConfig({
  build: {
    lib: { entry: 'src/index.ts', formats: ['es'], fileName: 'index', cssFileName: 'styles' },
    rolldownOptions: {
      external: [/^react(?:\/|$)/, /^react-dom(?:\/|$)/, '@xyflow/react', 'lucide-react'],
      output: { banner: '"use client";' },
    },
  },
});
