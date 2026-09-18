# イベント形式 v2

各行は `schema/events.schema.json` に適合し、`schema_version: 2` を持つ JSON オブジェクト。v1 の内部状態を含む facts から公開射影へ変更したため、v1 と version のない行は拒否する。今後、内部構造のフィールド追加だけではこの形式を変更しない。公開フィールドや意味を変える場合は version を上げる。

```json
{"schema_version":2,"sequence":1,"txn":"t1","recorded_at":0,"type":"execution.started","op":{"start":{"inputs":[]}},"data":{}}
{"schema_version":2,"sequence":2,"txn":"t1","recorded_at":0,"type":"transaction.committed","op":null,"data":{}}
```

上記は entries がないグラフの開始例。通常の例は `Test/traces/minimal.jsonl` を参照。

## トランザクション

1. **command**: `op` を持つ操作レコード。`data` は `{}`。`type` は操作に対応した名前。
2. **facts**: command の効果の公開射影。`op` は `null`。`Trace.Projection` の明示的なフィールドだけを出力し、`Trace.effects` が生成する順序と内容を完全に照合する。facts 自体は必須。
3. **commit**: `type` が `transaction.committed`、`op` が `null`、`data` が `{}` のレコード。

1 transaction に複数の command とそれぞれの facts を含められる。ひとつ前の command の facts が完了してから次の command を置く。commit は transaction の最後にちょうど 1 つ必要。空 transaction は不可。

全レコードの `sequence` は 1 始まりの連番。`txn` は空でなく、連続する transaction の外で再利用できない。`recorded_at` は単調な非負整数時刻。実時刻の文字列ではない。時間付き Op の `now` は command の `recorded_at` と一致する。

トークン等の facts は、(1) instance 作成、(2) attempt 作成・状態変更、(3) lease 更新、(4) 配置、(5) 消費、(6) execution 状態変更の順。各区分内は instance ID / attempt ID / instance ID / channel ID / (channel ID, index) の昇順。ID は文字列順、index は数値順。配置は同じ channel 内で末尾へ増えた token 順を保つ。内部 State の格納順と JSON object のキー順には依存しない。

## facts の公開契約

| type | data の必須フィールド |
| --- | --- |
| `instance.created` | `id`, `node`, `path`, `trigger`（値なしは null） |
| `attempt.started` | `attempt`（下記の6フィールド）, `lease_until` |
| `attempt.finished` | `id`, `instance`, `no`, `status`, `token`, `worker` |
| `lease.renewed` | `instance`, `lease`（`attempt`, `token`, `lease_until`） |
| `token.placed` | `edge`, `token`, `by_instance` |
| `token.consumed` | `channel`, `index`, `item`, `by_instance` |
| `execution.state_changed` | `status`, `reason`（値なしは null） |

`attempt.started.attempt` も `id`, `instance`, `no`, `status`, `token`, `worker` を持つ。status は開始時 running、終了時 succeeded / failed / abandoned / cancelled。型・列挙値は Schema を原本とする。追加キー、必須キーの欠落、値の不一致を拒否する。

公開レコードのフィールド名は snake_case に統一する。配置・消費の主体はいずれも `by_instance`、lease の期限はいずれも `lease_until`。Lean 内部の `byInstance` / `until_` は公開しない。Op の識別タグは §4 の操作名（`expireLease` 等）を維持する。

Instance の status、inputs、lease、retryAt、各種カウンタ、Frame、Receipt、Decision は facts に出さない。これらは command 列から Lean が再構築する。外部実装は自分のデータ構造からこの公開契約と論理 ID に射影する。facts だけから内部状態を復元する契約ではない。診断の `boundary` は開発用の内部状態要約で、安定した facts の契約には含めない。

## Op の符号化

Lean の `ToJson` / `FromJson` に従う。引数なしの操作は文字列 `"idle"` / `"cancel"`。それ以外は `{ "操作名": { "引数名": 値 } }`。

設計書 §3 の yield は `emit`、AllWait は `fireCollect`、Concurrency の合流は `fireWaitAll`、Branch 後の Coalesce は `fireCoalesce`、Sub の完了は `finishSubworkflow` に対応する。イベントに書く操作名は §4 の名前を使う。`fireCoalesce` は `path`, `node`, `edge`, `item` を引数に取る。

```json
{"activate":{"path":[],"node":"work"}}
{"claim":{"auth":{"instance":"instance-id","attempt":"attempt-1","token":"lease-1","now":0},"worker":"worker-1"}}
{"emit":{"auth":{"instance":"instance-id","attempt":"attempt-1","token":"lease-1","now":1},"port":"out","item":"item-1"}}
{"complete":{"auth":{"instance":"instance-id","attempt":"attempt-1","token":"lease-1","now":2},"outputs":[{"port":"result","items":["result-1"]}]}}
```

complete の `outputs` は **plain 出力だけ**を含め、各ポートにつき item がちょうど 1 つ必要。yield した item は `emit` で記録済みなので complete の引数には含めない。complete が全出力を EOS で閉じる。

instance ID は `instanceId`、channel ID は `Frame.channels` が決定する JSON 文字列。任意の実装では、自前の ID をこの論理 ID に射影してから履歴を検査する。使用例の fixture はそのまま入力可能。

`token` は `{"item":{"id":"item-1"}}` または `"eos"`。consume の fact は `channel`, `index`, `item`, `by_instance` を持つ。attempt.started の fact は `attempt` と整数の `lease_until` を持つ。完全な shape は Schema に定義する。

設計書で記載がなかった `retry.promoted`、`retry.requested`、`instance.completed`、`instance.skipped`、`transaction.committed` を追加し、全操作と確定境界を表せるようにした。

Loop の `manualRetry` も `retry.requested` で記録する。内部の `extraIterations` はこの command の replay で復元し、facts には出さない。blocked から running への解除は manualRetry の facts に `execution.state_changed` を含める。自動 resume は設けない。

## 検査・回復

検査器は余分なキーや欠落した必須キーを拒否する。command を `step` に渡し、元の状態との差分を公開契約に射影して期待される facts を生成する。操作や facts の削除・effect の捏造・lease_until の改変も検出する。拒否した操作は State を返さず、直前の commit 境界を診断に載せる。

`check` の不適合出力は標準エラーへ JSON で出す。`sequence`, `txn`, `op`, `reason`（code/message）, `boundary`（直前の確定状態の要約）を含む。途中で切れた transaction は `TRUNCATED_TRANSACTION`。

`Trace.recover` は正常に読めたレコードのうち最後の commit 境界だけを返す。未完の suffix を返さない。壊れた行や不正な既存レコードを黙って読み飛ばす API ではない。永続化層は JSON として読めない torn suffix を切り離してから、完全に読めたイベント列に対して回復を行う。

生成は `Trace.recordTransaction` を使用できる。`gen` コマンドも同じ関数から書き出し、その出力を `check` に再投入できる。

v1 の履歴を移す場合は、旧版の検査器で適合を確認した command とトランザクション境界から、v2 の記録関数で facts を再生成する。単に version を付け足して互換扱いにはしない。このリポジトリの fixture は v2 に更新済み。
