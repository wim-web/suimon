# Suimon TypeScript

[Suimon の制御仕様](../../docs/suimon-spec.md)を Node.js で実行するライブラリ。関数、Stream、分岐、並列、サブworkflow、合流、キャンセル、タイムアウトと現行 journal からの復元を扱う。

入口は `@suimon/engine`。型付き構築と復元の動く例は [workflow.mjs](examples/workflow.mjs)、永続化 adapter の契約は [runtime-types.ts](src/runtime-types.ts) を参照する。JSON の値を保存するため、大きなデータは保存先のキーなどで渡す。callback は AbortSignal に応じて終了する。

リポジトリのルートで実行する。

```sh
pnpm install --frozen-lockfile
pnpm --filter @suimon/engine typecheck
pnpm --filter @suimon/engine test
pnpm --filter @suimon/engine test:conformance
pnpm --filter @suimon/engine test:package
```

`test:conformance` は Go が必要。Lean も比較する場合は `lake build suimon` 後に `SUIMON_LEAN_CLI` へその実行ファイルの絶対パスを渡す。`test:package` は pack した配布物を一時的な Node プロジェクトへインストールし、同じサンプルを実行する。レジストリへ公開しない。
