# イベント履歴の利用

外部実装の履歴を suimon のモデルと照合するための案内。イベントのフィールドや操作の受理条件は、次の定義を参照する。

| 調べる内容 | 定義 |
| --- | --- |
| グラフの JSON 形式 | [graph.schema.json](../schema/graph.schema.json) |
| イベントの JSON 形式と version | [events.schema.json](../schema/events.schema.json) |
| 操作と引数 | [Op.lean](../Suimon/Op.lean) |
| facts の公開フィールド | [Trace/Projection.lean](../Suimon/Trace/Projection.lean) |
| command・facts・commit の生成と順序 | [Trace/Event.lean](../Suimon/Trace/Event.lean) |
| JSONL の符号化・行ごとの復号と検査 | [Trace/Wire.lean](../Suimon/Trace/Wire.lean) |
| 履歴の受理条件と診断 | [Trace/Check.lean](../Suimon/Trace/Check.lean) |

## 生成して検査する

リポジトリ直下で実行する。必要なツールは [README](../README.md#実行) を参照。

```sh
lake exe suimon gen --graph Test/graphs/streaming.json --seed 17 --count 30 > /tmp/suimon.jsonl
lake exe suimon check /tmp/suimon.jsonl --graph Test/graphs/streaming.json
```

最小の入力例は [minimal.jsonl](../Test/traces/minimal.jsonl) と [minimal.json](../Test/graphs/minimal.json)。再試行を含む例は [loop-retry.jsonl](../Test/traces/loop-retry.jsonl) と [loop.json](../Test/graphs/loop.json)。JSON を手で組み立てる前に、生成結果とこれらの fixture を参照するとよい。

## 外部実装を対応付ける

外部実装の ID は、モデルの論理 instance・channel・item ID に対応付ける必要がある。構成は [State.lean](../Suimon/State.lean) の `instanceId` と `Frame.channels`、出力例は fixture を参照。worker や再試行ごとの ID を、論理的な出力 occurrence の ID と混同しない。

Lean から履歴を作る場合は `Trace.recordTransaction` を使い、各イベントを `Trace.encodeEvent` で文字列にして改行区切りで書き出す。空の操作列、空の transaction ID、記録時刻より古い時刻を持つ操作は拒否される。これが記録する command はモデルを再実行するための操作、facts はその効果を照合するための公開情報、commit は確定境界を表す。外部実装では自身のデータ構造から facts を対応付け、検査器に渡す。内部 State 全体の JSON 化を要求しない設計の理由は [設計理由](suimon-design.md#履歴に内部状態をそのまま出さない理由) を参照。

facts だけから内部状態を復元する契約ではない。また、診断に含まれる `boundary` は開発用の状態要約であり、安定した facts の形式とは分けて扱う。

## 結果と回復を読む

`check` の終了コードは適合で 0、履歴違反で 1、引数・グラフのエラーで 2。不適合時は標準エラーに JSON の診断を出す。最初に拒否された位置と理由、直前の確定境界を確認できる。未確定の transaction が末尾に残る場合は `TRUNCATED_TRANSACTION` になる。

適合という結果は、記録された履歴がモデルに従うことを示す。実行全体の成功や、利用者の処理が oracle の期待する値をすべて生成したことまで示すものではない。決定性に必要な追加の前提は [保証の読み方](implementation.md#決定性で保証するもの) を参照。

`Trace.recover` は、読み取れたイベント列から最後の確定境界の状態を得る API。壊れた行や不正な既存レコードを黙って読み飛ばすためには使わない。永続化層で未確定末尾の読み取りを処理し、完全に読めたイベント列を渡す。操作列の replay と外部ストレージの保証の違いは [保証の読み方](implementation.md#replay-と外部環境) を参照。

文字列の行を渡す場合は `Trace.checkText` / `Trace.recoverText` を使う。前者は最後の commit を要求し、後者は受理された未コミット末尾の変更を捨てる。従来の v2 fixture や標準 JSON の別表記も読める。キー順と数値の字面は契約に含めず、公開フィールドと値は引き続き schema v2 に従う。

## 形式を変更するとき

現在の形式は v2。内部構造へのフィールド追加だけでは履歴形式を変えず、公開フィールドや意味を変える場合に version を上げる。

v1 の履歴を移す場合は、旧版の検査器で適合を確認した command とトランザクション境界を使い、v2 の記録関数で facts を再生成する。version を付け替えるだけでは移行にならない。公開形式の回帰検査は [TraceProjection.lean](../Test/TraceProjection.lean) を参照。
