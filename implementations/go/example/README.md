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

[main.go](main.go) はグラフを作って実行するだけです。

```go
func main() {
    graph := createGraph()
    graph.run()
}
```

| ファイル | 役割 |
| --- | --- |
| [graph.go](graph.go) | ノードと接続、入力値、処理関数の割り当てを定義する |
| [nodes.go](nodes.go) | `trim` と `uppercase` の処理を書く |
| [runner.go](runner.go) | 状態遷移を進めて処理関数を呼び、結果を表示する |

構成や入力を変える場合は `createGraph`、ノードの処理を変える場合は `nodes.go` を編集します。`leaf` はこの例の中でノード定義を簡潔に書くための関数です。

`run` はこのexample内の実行用メソッドです。内部では `start` の後に各ノードを `activate` → `claim` → 処理関数 → `complete` の順に進め、最後に `idle` で完了を判定します。実際の文字列は `values` に保存し、Suimon にはそのアイテム ID を渡します。

この例は直列の2ノードを定義順に実行します。時刻も固定した短い処理の例で、実アプリでは時計に合わせた `Credentials.Now` の更新や、処理時間に応じた lease の更新も実行側で行います。
