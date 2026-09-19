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
    printResult(graph.Run(context.Background()))
}
```

| ファイル | 役割 |
| --- | --- |
| [graph.go](graph.go) | ノードと接続、入力値、処理関数の割り当てを定義する |
| [nodes.go](nodes.go) | `trim` と `uppercase` の処理を書く |
| [result.go](result.go) | 実行結果を表示する |

構成や入力を変える場合は `createGraph`、ノードの処理を変える場合は `nodes.go` を編集します。`leaf` はこの例の中でノード定義を簡潔に書くための関数です。

`createGraph` が返すのはライブラリの `suimon.Workflow` です。`Run` は `src` に実装されており、配線と状態に従って実行可能なノードを選びます。exampleには実行ループや `Step` の呼び出しはありません。

処理関数は `Task.DecodeInput` で入力を読み、`Values` でplain出力を返します。ストリーム出力には `Task.Emit` を使います。時刻、lease、再試行、インスタンス作成、完了判定は実行器が担当します。[実行APIの詳細](../runtime.md)を参照してください。
