# 2つのノードを作って実行する例

リポジトリ直下で実行します。Go だけで動きます。

```sh
go -C implementations/go run ./example
```

```text
trim: "  hello suimon  " -> "hello suimon"
uppercase: "hello suimon" -> "HELLO SUIMON"
result: HELLO SUIMON
status: succeeded
```

[main.go](main.go) に次の流れをまとめています。

1. `Node` で `trim` と `uppercase` を作る。
2. `Graph.Edges` で `trim.out` を `uppercase.in` につなぎ、入口と出口を決める。
3. `start` で入力のアイテム ID を渡す。
4. 各ノードを `activate` → `claim` → 処理関数 → `complete` の順に進める。
5. `idle` で完了を判定し、出口のアイテム ID から結果を読む。

実際の文字列はアプリ側の `values` に保存し、ノードの処理関数は `handlers` に置きます。`leaf` はこの例の中でノード定義を簡潔に書くための関数です。

この例は直列の2ノードを定義順に実行します。時刻も固定した短い処理の例で、実アプリでは時計に合わせた `Credentials.Now` の更新や、処理時間に応じた lease の更新も実行側で行います。
