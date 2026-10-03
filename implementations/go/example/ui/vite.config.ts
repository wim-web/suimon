import { defineConfig } from 'vite';

const apiOrigin = 'http://127.0.0.1:8080';

export default defineConfig({
  base: './',
  server: {
    host: '127.0.0.1',
    proxy: {
      '/api': {
        target: apiOrigin,
        changeOrigin: true,
        configure(proxy) {
          proxy.on('proxyReq', (proxyReq, req) => {
            // Translate only the dev UI's own origin; preserve foreign origins for rejection.
            if (req.headers.origin === `http://${req.headers.host}`) proxyReq.setHeader('Origin', apiOrigin);
          });
        },
      },
    },
  },
});
