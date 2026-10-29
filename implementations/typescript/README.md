# suimon TypeScript 実装

[Suimon の制御仕様](https://github.com/wim-web/suimon/blob/main/docs/suimon-spec.md)を TypeScript で実装し、Node.js に組み込むライブラリです。

入口は `@suimon/engine` の[公開 API](src/index.ts)です。使い方は動く例の [workflow.mjs](examples/workflow.mjs) を参照してください。

## 検証

リポジトリ直下で実行します。

```sh
pnpm install --frozen-lockfile
pnpm --filter @suimon/engine typecheck
pnpm --filter @suimon/engine test
pnpm --filter @suimon/engine test:conformance
pnpm --filter @suimon/engine test:package
```

`test:conformance` には Go が必要です。Lean とも比較する場合は、`lake build suimon` 後に `SUIMON_LEAN_CLI` でその実行ファイルの絶対パスを指定してください。
