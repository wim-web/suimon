# suimon Go 実装

[Lean の定義](../../Suimon/)を Go に移した実装と、それを使って workflow構成を Go の関数で実行するランタイムです。ランタイムは移した状態遷移だけで実行を進め、[実行記録](../../schema/trace.schema.json)から再開します。

入口は [Engine](src/engine.go) と [Registry](src/registry.go)、ホスト側の資源上限は [Limits](src/limits.go) です。動く例として [playground](example/README.md) と [ランタイムのテスト](src/runtime_test.go) を参照してください。

ビルドには [.go-version](../../.go-version) の Go を使ってください。`go.mod` の `go` 行はライブラリの最低要件であり、ビルドに使う Go は指定しません。[eMudhra 中間 CA の信頼を拒否する修正](https://go.dev/doc/devel/release#go1.27.3)を取り込むには、HTTPS を利用するアプリ側も修正済みの Go で再ビルド・再配布する必要があります。

## 検証

リポジトリ直下で実行します。

```sh
bin/test-go unit
bin/test-go conformance
```

`conformance` は Lean CLI と比べますが、Lean CLI をビルドしません。先に `lake build suimon` を実行するか、`SUIMON_LEAN_CLI` で Lean CLI を指定してください。記録で確かめる範囲は[設計理由](../../docs/suimon-spec.md#他言語の実装を記録で確かめる理由)を参照してください。

CLI のオプションは `go -C implementations/go run ./cmd/suimon --help` で確認できます。
