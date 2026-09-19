# suimon

逐次・ForEach・Concurrency・Sub に加え、実行中にアイテムを出す yield と、全件の処理完了を待つ AllWait を同じワークフローで扱う、Lean 4 による制御仕様です。ノードのコードを実行する製品ライブラリではなく、実行可能な状態遷移、イベント履歴の検査器、有界探索器を提供します。

[設計書](docs/suimon-design.md) / [実装上の決定・証明の範囲](docs/implementation.md) / [イベント形式](docs/trace-format.md)

説明には設計書 §3 の部品名を使います。Lean と JSON の名前は §4 のままで、AllWait は `collect`、Sub は `subworkflow`、yield は stream 出力を持つ `leaf` の `emit` 操作に対応します。Concurrency は配線で並列に分け、`waitAll` で合流します。Coalesce（`coalesce`）は単一 Branch の排他的な arm を合流させ、body 内の Branch では必須です。独立した処理同士を Coalesce に繋ぐ配線は拒否します。

## 実行

Lean は `lean-toolchain` の **4.34.0** に固定しています。Lean の標準ライブラリのみを使用し、Mathlib や外部 Lake パッケージは不要です。`elan` と `lake` を PATH に追加してください。以下はリポジトリ直下で実行します。

```sh
lake build
lake exe suimon check Test/traces/minimal.jsonl --graph Test/graphs/minimal.json
lake exe suimon explore --graph Test/graphs/streaming.json --depth 8 --workers 2 --tick 1
lake exe suimon gen --graph Test/graphs/streaming.json --seed 17 --count 30 > /tmp/suimon.jsonl
lake exe suimon check /tmp/suimon.jsonl --graph Test/graphs/streaming.json
```

`check` は適合で 0、履歴違反で 1、引数・グラフのエラーで 2 を返します。完了前の合法な履歴も適合です。`explore` は指定深さを完走した場合だけ 0。反例と、`--max-states`（既定 100,000）による打ち切りは 1 です。`gen` は最大 `count` 操作の再現可能な履歴を標準出力へ出します。終端に到達すると早く終了します。

## 検証

テストも Lean で実装しています。`elan` / `lake` とシェルで実行できます。

```sh
bin/test
```

`bin/test` は未完の証明・独自の未検証公理の検出、Lean のビルド、回帰テスト、Schema 検証、破損履歴の拒否、全例グラフの深さ 8 探索を実行します。`LAKE` で実行ファイルを指定できます。同じ検証を GitHub Actions に設定しています。

trace は v2 の公開 facts を厳密照合します。内部 Instance のカウンタ等は command から復元するため、内部フィールドの追加だけでは履歴形式を変更しません。T9 は Lean の一般定理として証明済みです。回帰として、固定 oracle に適合する4,032通りの成功・drain 実行で、操作順を変えた各線の多重集合比較も行います。lease 失効・retryable fail からの再 claim と、消費済みアイテムの yield 再送を含みます。

Schema 検証はこのリポジトリのスキーマで使うキーワードに対応しています。未対応のキーワードを追加するとテストは失敗します。

例グラフは `Test/Examples.lean` が原本です。共用する JSON は `Test/graphs/`、履歴は `Test/traces/` に置きます。フィクスチャを更新するときは次を実行します。

```sh
lake exe suimon_test --write-fixtures
```

## 現在の範囲

設計書の全ノード種別と操作、入れ子、lease、再試行、キャンセル、トランザクション replay を実装しています。受理された `step` の分解、コミット時の不変条件保持、成功済みインスタンスの再実行禁止などを Lean で証明しています。

T9 全体を [Adequacy.lean](Suimon/Theorems/Adequacy.lean) の `schedule_determinism : ScheduleDeterminism` で証明しました。`frame_adequacy` が実際の受理操作列から ForEach・Loop・DAG を含む `GraphEval` を構成し、`GraphEval.functional` で2実行の全チャネルの多重集合を一致させます。子 frame の entry / edge / exit、lease 失効、再送、Loop の `manualRetry` を含み、候補列挙や探索深さには制限しません。比較対象は同じ oracle に適合した成功・drain 実行です。

設計書の **M1 と M3 の T9 受入条件は完了**。T12 の全 Op に対する候補列挙の完全性や、M4 のイベント codec と回復の一般証明は引き続き未完です。詳しい対応と、元の T2/T9 に必要な前提の修正は [implementation.md](docs/implementation.md) を参照してください。M5 の実装言語は選定していません。
