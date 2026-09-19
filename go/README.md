# suimon Go 実装

Lean の実行可能な定義から生成した、標準ライブラリだけに依存する Go パッケージです。Go 1.23 以降で使えます。実行時に Lean・C ABI・cgo は必要ありません。

グラフ検証、全 23 種類の操作、状態遷移の不変条件検査、候補列挙、探索、履歴生成、v2 JSONL の検査と未コミット末尾の回復を実装しています。ノードの利用者コードや外部副作用を実行する worker は、Lean 版と同様に含みません。

## CLI

リポジトリ直下で実行します。

```sh
go -C go run ./cmd/suimon check ../Test/traces/minimal.jsonl --graph ../Test/graphs/minimal.json
go -C go run ./cmd/suimon explore --graph ../Test/graphs/streaming.json --depth 8 --workers 2 --tick 1
go -C go run ./cmd/suimon gen --graph ../Test/graphs/streaming.json --seed 17 --count 30 > /tmp/suimon-go.jsonl
go -C go run ./cmd/suimon check /tmp/suimon-go.jsonl --graph ../Test/graphs/streaming.json
CGO_ENABLED=0 go -C go build -o /tmp/suimon-go ./cmd/suimon
```

ビルドした CLI のオプションと終了コードは Lean 版と共通です。JSON のキー順・空白・数値の表記は異なる場合があります。構造と値を比較してください。JSON 構文エラーの説明文は Go の parser に依存し、診断コードと確定境界は共通です。

## パッケージ

```go
import suimon "github.com/wim-web/suimon/go"

graph, err := suimon.ParseGraph(graphJSON)
if err != nil {
    return err
}
state := suimon.Initial(graph)
next, rejected := suimon.Step(state, suimon.Op{
    Kind: "start",
    Inputs: suimon.InputValues(graph),
})
if rejected != nil {
    return rejected
}
state = next
```

`Step` と `Transaction` は入力の状態を変更しません。拒否時には入力の状態と `*Reject` を返します。`Initial` を直接呼ぶ場合は、先に `Graph.Validate` を通してください。公開構造体や返されたスライス・ポインタを利用側で直接変更せず、状態更新には `Step` を使います。

`Nat` は Lean の自然数に合わせた多倍長整数です。小さい値は `suimon.N(30)`、大きい値は `suimon.ParseNat("18446744073709551616")` で作れます。数値の加減算は `Add` / `Sub` / `Inc`、比較は `Cmp` を使います。`Sub` はゼロで打ち切ります。

履歴の記録には `RecordTransaction`、逐次検査には `NewCursor` → `CheckTextLine` → `Finish` を使います。`Recover` は読めたイベントをすべて検査したうえで最後の commit 境界を返します。物理的に途中で切れた最終行の扱いは呼び出し側の責務です。

## 対応する原本と検証

| Lean の原本 | Go |
| --- | --- |
| `Graph.lean` | `types.go`, `graph.go` |
| `State.lean`, `Oracle.lean` | `types.go`, `state.go` |
| `Op.lean`, `Step.lean` | `types.go`, `step.go` |
| `Invariants.lean` | `invariants.go` |
| `Candidates.lean`, `Explore.lean` | `explore.go` |
| `Trace/` の公開形式・記録・検査 | `trace.go`, `json.go` |
| `Main.lean` | `cmd/suimon/main.go` |

Lean との比較を含む検証は、リポジトリ直下で実行します。

```sh
bin/test-go
```

このコマンドは元の `bin/test` も実行します。既存の回帰テストで用いる操作とその前後の状態・拒否理由・facts を出力して Go で再検査し、全例グラフに対する候補操作と不正操作、履歴生成、探索結果も Lean と比較します。Go が出した JSONL を Lean で読む交差検査、破損履歴と未コミット末尾の検査も含みます。

Go だけの検証は `go -C go test ./...` です。この場合、Lean が必要な比較テストは明示的に skip します。CI では `bin/test-go` を使って比較を必須にしています。

## Lean 定義を変更したとき

この Go 実装は AI による今回の翻訳結果です。任意の Lean を Go に変換する汎用コンパイラや、意味を自動で再生成するコマンドは含みません。

変更した Lean 定義に対応する Go ファイルを再生成・更新し、`bin/test-go` の比較を通してください。生成元は `lean-sources.json` の SHA-256 と toolchain で固定しています。原本が変わると `TestLeanSourceSnapshot` が失敗するため、Go の対応更新を確認してから snapshot を更新します。

Lean 側の形式的な証明が Go に移るわけではありません。この Go 実装の一致は上記の比較テストで確認しており、変換全体の形式的な証明はありません。
