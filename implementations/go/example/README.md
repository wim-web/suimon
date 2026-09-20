# Go playground

上流の生成と下流の処理が重なる効果を見比べるためのサンプルです。外部サービスに依存せず待ち時間を再現できるよう、sleep で I/O を模擬します。stream / batch は入力と待ち時間を揃え、途中出力の有無による下流の開始時刻の違いを観察します。

## 起動

リポジトリ直下で実行します。

```sh
pnpm install
pnpm build
go -C implementations/go run ./example -ui
```

[http://127.0.0.1:8080](http://127.0.0.1:8080) を開き、Streaming pipeline と Batch comparison を同じ入力・待ち時間で実行して比較してください。Go だけで実行する場合は [Go README](../README.md#実行) を参照してください。

[サンプルのコード](scenarios.go) / [UI kit の組み込み例](ui/src/)
