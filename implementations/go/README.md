# suimon Go 実装

suimon の Go 実装です。[実行 API](src/workflow.go)、[利用例](example/README.md)、[共通の設計理由](../../docs/suimon-design.md)を参照してください。

## 実行

リポジトリ直下で実行します。

```sh
go -C implementations/go run ./example
```

CLI の入口は `go -C implementations/go run ./cmd/suimon --help` です。

## 検証

Lean の定義と Go 実装のずれを検出するため、リポジトリ直下から [bin/test-go](../../bin/test-go) を実行します。この比較は、Go 実装全体の形式的な同値性を証明するものではありません。
