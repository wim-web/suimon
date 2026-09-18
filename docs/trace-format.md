# イベント形式 v1

各行は `schema/events.schema.json` に適合する JSON オブジェクト。

```json
{"sequence":1,"txn":"t1","recorded_at":0,"type":"execution.started","op":{"start":{"inputs":[]}},"data":{}}
{"sequence":2,"txn":"t1","recorded_at":0,"type":"transaction.committed","op":null,"data":{}}
```

上記は entries がないグラフの開始例。通常の例は `Test/traces/minimal.jsonl` を参照。

## トランザクション

1. **command**: `op` を持つ操作レコード。`data` は `{}`。`type` は操作に対応した名前。
2. **facts**: command の効果を表すレコード。`op` は `null`。`Trace.effects` が生成する順序と内容を完全に照合する。
3. **commit**: `type` が `transaction.committed`、`op` が `null`、`data` が `{}` のレコード。

1 transaction に複数の command とそれぞれの facts を含められる。ひとつ前の command の facts が完了してから次の command を置く。commit は transaction の最後にちょうど 1 つ必要。空 transaction は不可。

全レコードの `sequence` は 1 始まりの連番。`txn` は空でなく、連続する transaction の外で再利用できない。`recorded_at` は単調な非負整数時刻。実時刻の文字列ではない。時間付き Op の `now` は command の `recorded_at` と一致する。

トークン等の facts は、(1) instance 作成、(2) attempt 作成・状態変更、(3) lease 更新、(4) 配置、(5) 消費、(6) execution 状態変更の順。各区分内は State の list 順。配置は対象 channel ごとに末尾へ増えた token 順で記録する。JSON object のキー順は問わない。

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

`token` は `{"item":{"id":"item-1"}}` または `"eos"`。consume の fact は `channel`, `index`, `item`, `byInstance` を持つ。attempt.started の fact は `attempt` と整数の `lease_until` を持つ。完全な shape は Schema に定義する。

設計書で記載がなかった `retry.promoted`、`retry.requested`、`instance.completed`、`instance.skipped`、`transaction.committed` を追加し、全操作と確定境界を表せるようにした。

Loop の `manualRetry` も `retry.requested` で記録する。instance の `extraIterations` はその起動に追加した回数上限を表す。blocked から running への解除は manualRetry の facts に `execution.state_changed` を含める。自動 resume は設けない。

## 検査・回復

検査器は余分なキーや欠落した必須キーを拒否する。command を `step` に渡し、期待される facts を元の状態との差分から生成する。操作の削除・effect の捏造・lease_until の改変も検出する。拒否した操作は State を返さず、直前の commit 境界を診断に載せる。

`check` の不適合出力は標準エラーへ JSON で出す。`sequence`, `txn`, `op`, `reason`（code/message）, `boundary`（直前の確定状態の要約）を含む。途中で切れた transaction は `TRUNCATED_TRANSACTION`。

`Trace.recover` は正常に読めたレコードのうち最後の commit 境界だけを返す。未完の suffix を返さない。壊れた行や不正な既存レコードを黙って読み飛ばす API ではない。永続化層は JSON として読めない torn suffix を切り離してから、完全に読めたイベント列に対して回復を行う。

生成は `Trace.recordTransaction` を使用できる。`gen` コマンドも同じ関数から書き出し、その出力を `check` に再投入できる。
