# suimon

逐次・ForEach・Concurrency・Sub に加え、実行中にアイテムを出す yield と、全件の処理完了を待つ AllWait を同じワークフローで扱う、Lean 4 による制御仕様とGo実装です。Leanには状態遷移、イベント履歴の検査器、有界探索器を置き、Goの `Workflow.Run` がその制御モデルを使ってノードの処理関数を実行します。

[設計理由](docs/suimon-design.md) / [保証の読み方](docs/implementation.md) / [イベント履歴の利用](docs/trace-format.md)

動作仕様は Lean の定義です。[Graph.lean](Suimon/Graph.lean) がグラフと検証、[State.lean](Suimon/State.lean) が状態、[Op.lean](Suimon/Op.lean) と [Step.lean](Suimon/Step.lean) が操作と遷移への入口です。定理の主張と証明は [Theorems/](Suimon/Theorems/) にあります。

## 実行

Lean のバージョンは [lean-toolchain](lean-toolchain) に固定しています。Lean の標準ライブラリのみを使用します。`elan` と `lake` を PATH に追加してください。以下はリポジトリ直下で実行します。

```sh
lake build
lake exe suimon check Test/traces/minimal.jsonl --graph Test/graphs/minimal.json
lake exe suimon explore --graph Test/graphs/streaming.json --depth 8 --workers 2 --tick 1
lake exe suimon gen --graph Test/graphs/streaming.json --seed 17 --count 30 > /tmp/suimon.jsonl
lake exe suimon check /tmp/suimon.jsonl --graph Test/graphs/streaming.json
```

`check` の結果の読み方は [イベント履歴の利用](docs/trace-format.md) を参照してください。`explore` は指定深さを完走した場合だけ 0 を返し、反例と `--max-states` による打ち切りは 1 です。`gen` は最大 `count` 操作の再現可能な履歴を標準出力へ出します。終端に到達すると早く終了します。全オプションは `lake exe suimon --help` で確認できます。

## Go 実装

各言語の実装は `implementations/{language}/` にまとめています。Go 版は `implementations/go/` にあり、ライブラリ本体を `src/`、実行例を `example/` に分けています。

Lean の実行可能な定義から生成した [Go パッケージと CLI](implementations/go/README.md) も利用できます。グラフと処理関数・入力を設定して `Workflow.Run` を呼ぶと、配線に従ってストリームや並列処理を進めます。実行時に Lean や cgo は不要です。[実行APIと対応範囲](implementations/go/runtime.md)を参照してください。

```sh
go -C implementations/go run ./cmd/suimon check ../../Test/traces/minimal.jsonl --graph ../../Test/graphs/minimal.json
```

原本は引き続き Lean の定義です。Go 版との一致は `bin/test-go` で比較検証します。

[Go の実行例](implementations/go/example/README.md)では、時間差の Emit、Filter、ForEach の並列処理、Collect（AllWait）による全件待ちを確認できます。`-scenario batch` で全件生成後に送る方式と比較し、`-scenario basic` で2ノードの基本例を実行できます。

```sh
go -C implementations/go run ./example
```

`pnpm install` と `pnpm build` で画面をビルドし、`-ui` を付けて example を起動すると、ブラウザでサンプルを切り替え、途中の入出力や並列実行数を確認できます。共通部品は [ui-kit](ui-kit/README.md)、Go 専用の画面は [implementations/go/example/ui](implementations/go/example/ui/) にあります。

## 検証

Lean 仕様のテストは `elan` / `lake` とシェルで実行できます。

```sh
bin/test
```

`bin/test` は未完の証明・独自の未検証公理の検出、Lean のビルド、回帰テスト、Schema 検証、破損履歴の拒否、全例グラフの有界探索を実行します。`LAKE` で実行ファイルを指定できます。同じ検証を GitHub Actions に設定しています。

Go 版との比較も含める場合は、Go を用意して `bin/test-go` を実行してください。GitHub Actions もこのコマンドで両実装を検証します。

決定性の定理は [Adequacy.lean](Suimon/Theorems/Adequacy.lean) の `schedule_determinism` です。同じ oracle に適合する成功・drain 実行を比較します。定理の前提・限界と、有限の回帰検査との違いは [保証の読み方](docs/implementation.md) を参照してください。

期限の保持・起床と条件付きのメンテナンス試行は [Scheduler.lean](Suimon/Theorems/Scheduler.lean) で証明しています。Goの実行器は対応する期限ポリシーを使い、stall中もretryやlease期限を処理します。Goへの翻訳と実行環境との接続は比較・実行テストで検証します。

M2〜M4 の受入条件は達成済みです。停止判定の完全性、JSONL の往復、未コミット末尾の回復を含む証明と検証結果は、[受入状況](docs/implementation.md#受入状況) に記録しています。

例グラフは [Test/Examples.lean](Test/Examples.lean) が原本です。共用する JSON は [Test/graphs/](Test/graphs/)、履歴は [Test/traces/](Test/traces/) に置きます。フィクスチャを更新するときは次を実行します。

```sh
lake exe suimon_test --write-fixtures
```
