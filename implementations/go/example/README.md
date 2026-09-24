# Go playground

Go ランタイムの動きを手元で観察するためのサンプルです。外部サービスなしで待ち時間を再現できるよう、I/O は sleep で模擬しています。

中心は Stream と Batch の比較で、同じ入力・同じ待ち時間のまま、下流の処理が始まる時刻・最初の結果が出る時刻・全体の所要時間をタイムラインで見比べます。

UI の実行状態と実行記録は、ランタイムが書いた実行記録の行を `Check` で再生して求めています。UI がエンジン内部を覗かず、実行記録を読む側と同じ手順で状態を得るためです。

## 起動

リポジトリ直下で実行します。

```sh
pnpm install
pnpm --filter '@suimon/go-example-ui...' build
go -C implementations/go run ./example -ui
```

[http://127.0.0.1:8080](http://127.0.0.1:8080) を開きます。オプションは `go -C implementations/go run ./example -h` で確認できます。

[workflow構成](definitions/) / [関数と登録](scenarios.go) / [API](server.go) / [UI](ui/src/)
