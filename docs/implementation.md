# 保証の読み方

保証の正確な主張と前提は Lean の定理に置く。この文書は、その意味と適用範囲を読むための案内である。設計上の選択理由は [設計理由](suimon-design.md) を参照。

## 決定性で保証するもの

[Execution.lean](../Suimon/Execution.lean) の `ScheduleDeterminism` は、同じグラフ・入力・決定的 oracle に対する成功実行を比較する。証明は [Adequacy.lean](../Suimon/Theorems/Adequacy.lean) の `schedule_determinism`。各論理チャネルに置かれたアイテムの多重集合が一致し、Sub・ForEach・Loop の子 frame の線も比較に含む。

この主張を使うには、次の前提が必要になる。

- グラフが検証を通り、両実行の操作列が同じ oracle に適合している。
- 出力 occurrence の ID が安定しており、worker や attempt の違いで変わらない。
- 両実行が成功し、stream が drain されている。root の結果以外の未消費アイテムがなく、全線が閉じ、子 frame が回収されていることを指す。

oracle への適合には、送った値が期待される集合に入ることだけでなく、complete 時に期待される stream 出力がすべて揃うことも含む。利用者の処理が出すはずの値を省略しても、生の `step` だけではそれを判定できない。[OracleConformance.lean](../Test/OracleConformance.lean) がこの違いを示す。

操作列の長さ、worker 数、再試行回数を有限の探索範囲に制限した定理ではない。lease 失効、再送、leaf・Loop の `manualRetry` を経た実行も、上の前提を満たせば比較できる。一方、任意の途中経過、cancel や失敗で終わった実行、アイテムの到着順、必ず成功まで進むことは保証の対象に含まれない。

証明では、実際の操作列から `frame_adequacy` で完成結果の意味論 `GraphEval` を構成し、[Semantics.lean](../Suimon/Theorems/Semantics.lean) の `GraphEval.functional` で結果の一意性を使う。[完成結果の定義](../Suimon/Semantics.lean) は完了可能性を主張しない。動作仕様の `step` と証明の役割を分けて読むための区別である。

## 安全性の定理を読む

[Safety.lean](../Suimon/Theorems/Safety.lean) の基本定理は、受理された操作や不変条件を満たす状態について述べる。`step_ok_cases` と `preserves_invariants` は、認可・前提・不変条件・履歴の検査を含む `step` が安全性を保持することを示す。検査を外した操作本体 `transition` が常に安全だという主張ではない。

| 関心 | 定理への入口 | 適用範囲の注意 |
| --- | --- | --- |
| 状態と履歴の整合性 | `preserves_invariants`、`preserves_history` | 有効な初期状態と、定理が要求する受理条件を前提に読む |
| plain 入力の順序 | `plain_order`、`coalesce_plain_order` | Coalesce の条件は選択された入力についてのもの |
| 消費の非重複 | `consumption_unique`、`once_only` | 前者は線上の位置ごとの消費記録、後者は同じ instance key の再挿入拒否についての定理 |
| Branch の排他性 | `branch_exclusive` | 非選択 arm に値を流さないルーティング関数についての定理 |
| Loop の有界性 | `loop_bounded` | 手動で追加した回数を含む実効上限。初期上限だけを永久に守るという意味ではない |
| lease の排他性と失効拒否 | `lease_exclusive`、`invalid_lease_rejected` | 成功済み complete の完全に一致する再送は、状態を変えない例外 |
| 終端の保持 | `terminal_absorbing`、`succeeded_retained` | モデル内の終端 execution と成功済み instance の保持 |

lease が制限するのはモデルへの結果の確定である。失効 worker が既に行った外部副作用を取り消したり、外部サービスでの処理を exactly-once にしたりする保証ではない。Loop・Sub の別起動も区別するため、instance の識別では node と trigger に加えて path が重要になる。

[Streams.lean](../Suimon/Theorems/Streams.lean) の `consumed_items_accounted` は、消費に対応する記録が残ることを示す。`channel_history` と合わせたアイテムの保存は安全性の主張であり、「置いたアイテムはいつか必ず消費される」という進行性を意味しない。同ファイルの `eos_final` は EOS の位置について、`spawn_without_eos` は EOS を前提にしない起動準備条件についての局所的な定理である。

## 停止の判定と進行性

`hasWork_iff` は、共有する候補列挙の中に状態を変える受理操作があることと `hasWork` の対応を示す。`idle_step_work` は idle 後も running なら作業があること、`idle_step_enters_blocked_no_work` は running から blocked に入るときに作業がないことを示す。いずれも [Safety.lean](../Suimon/Theorems/Safety.lean) から読める。

[WorkComplete.lean](../Suimon/Theorems/WorkComplete.lean) の `hasWork_iff_all_ops` は、不変条件を満たす start 後の状態について、候補列挙の外も含む任意の通常 Op と `hasWork` の同値を証明する。Op の引数、ID、時刻を有限集合に制限しない。通常 Op は idle / cancel / manualRetry を除く操作で、進行は受理に加えて状態が変わることを指す。

`idle_enters_blocked_no_progress` は、不変条件を満たす running 状態を idle が blocked に変えたなら、その直前に進行できる通常 Op が一つもなかったことを示す。start 済みという条件は受理された idle から導出する。証明では、任意の claim に対する新しい資格情報や、任意の worker 操作に対する lease 失効など、実際に受理され状態を変える候補を構成する。[Work.lean](../Test/Work.lean) の独立した乱択検査も回帰として残す。

worker が実行を続けることや公平性は保証していない。たとえば start 後に一切操作を行わなければ、処理は進まない。

## 期限による起床の保証

[Scheduler.lean](../Suimon/Scheduler.lean) は実際の `State` から lease失効・retry・自動renew の期限を取り出し、待機期限、pollの有効性、stall通知、実行するメンテナンス操作を決める。`service` は選んだ操作を既存の `step` に渡す。証明は [Theorems/Scheduler.lean](../Suimon/Theorems/Scheduler.lean) にある。

| 定理 | 保証 |
| --- | --- |
| `expiry_covered`, `retry_covered` | 対象instanceの期限が期限一覧から欠落しない |
| `pending_keeps_poll_enabled` | 期限があれば、stall通知済みでもpollを無効化しない |
| `stall_keeps_deadlines` | 期限が到来したpollはstall中でも待機を解除する |
| `no_stall_with_due_work` | 判定に用いた時刻でメンテナンス期限が到来済みならstallを新規通知しない |
| `mandatory_before_renewals` | 期限到来済みの失効・retry処理を任意の自動renewより先に選ぶ |
| `message_wakes` | job終了などの通知で待機を解除する |
| `eventually_wakes` | 下記の前提の下で、期限を持つ待機は有限回の機会のうちに解除される |
| `eventually_services` | 下記の前提の下で、待機中の状態に期限処理があれば `step` によるメンテナンスを試行し、状態更新の結果または拒否理由を返す |

進行の前提は `PollProgress` に明記する。時計は単調で、任意の有限時刻にいずれ達し、pollはどの時点以降にも実行機会があることを要求する。対象はメッセージや期限を待つ間の状態であり、メッセージが来たら待機を解除して状態と期限を取り直す。Goでこの前提を満たすには、実行器が停止されず、保存コールなどが戻り、実際にpollが行われる必要がある。固定時計、停止済み実行器、戻らない保存コールについて進行を主張しない。

これは待機からメンテナンス試行へ進む条件付きの証明である。各handlerの終了、各instanceの処理完了、ワークフロー全体の成功を証明したものではない。`step` の拒否はエラーとして明示され、黙って待機し続ける結果にはならない。

Go側はこの期限ポリシーを `src/scheduler.go` に翻訳し、実行ループから使用する。3600通りの時刻・所有権・通知状態などでLeanと比較し、実際のGoループにも「stall中のretry」「外部workerのlease失効」「探索と通知の間の時計の変化」の回帰検査を置く。Goの制御フロー、goroutine、永続化との接続全体をLeanが形式検証したわけではなく、この接続は差分・実行・race検査の対象である。

## replay と外部環境

[Replay.lean](../Suimon/Theorems/Replay.lean) の `replay_append` は、操作列を一括で再生しても途中で分けても同じ結果になることを示す。`replay_durable` は回復した操作列が記録済みのものと等しいという前提を使う。`replay_retains_success` は、再生後の受理操作列でも成功済み instance が保持されることを示す。

イベントの境界まで接続する定理は、次の三つの層に分けて読む。

- [TraceRecording.lean](../Suimon/Theorems/TraceRecording.lean) の `recordTransaction_checked` は、任意の受理された操作列から記録した command・facts・commit を実際の検査器が受理し、同じ境界状態を得ることを示す。トランザクション ID の新規性と時刻の単調性は、接続先の cursor に対する前提である。
- [TraceWire.lean](../Suimon/Theorems/TraceWire.lean) の `recordTransaction_jsonl_roundtrip` は、記録、文字列への符号化、復号、検査を接続する。任意の v2 イベントの codec 往復を補題から証明し、往復することを仮定には置かない。文字列・数値・データの深さ・操作数に探索上限はない。CLI の `gen` と `check` は、この `encodeEvent` と `checkTextLine` を使用する。
- [TraceTorn.lean](../Suimon/Theorems/TraceTorn.lean) の `recordCommands_torn_jsonl` は、生成した未コミットの command・facts 列を任意のレコード位置で切っても、回復結果が直前の確定境界のままであることを示す。切断位置は操作とその facts の間でもよく、その prefix の受理も証明する。[TraceRecovery.lean](../Suimon/Theorems/TraceRecovery.lean) の `check_replays_commands` と `recover_replays_prefix` は、受理された一般のイベント列と操作 replay の接続を与える。

文字列往復の定理は suimon の出力する表記を対象にする。互換入力として受ける別の空白・キー順などは Lean 標準 JSON parser から同じ検査器へ渡す。この互換経路と標準 JSON parser による生成結果の読み取りは、[TraceText.lean](../Test/TraceText.lean) で交差検査する。

回復 API は完全に読めた行を受け取る。物理的に途中で切れた最後の行の検出、DB・ファイルの flush や原子性はストレージ側の責務であり、これらの定理で実ストレージの永続性を証明したことにはならない。定義は [Trace/Check.lean](../Suimon/Trace/Check.lean) と [Trace/Wire.lean](../Suimon/Trace/Wire.lean)、利用方法は [イベント履歴の利用](trace-format.md) を参照。

原子性、時計、ID の一意性、oracle、永続化に関する環境の前提は [Axioms.lean](../Suimon/Axioms.lean) の `Assumptions` に明示する。これを持つこと自体が、外部実装の DB や時計の正しさを証明するわけではない。

## 証明と回帰検査の使い分け

[Determinism.lean](../Test/Determinism.lean) は固定 oracle の下で操作順、lease 失効、再試行、消費後の再送を変えて結果を比較する。[Explore.lean](../Suimon/Explore.lean) は有限の候補と指定した深さで反例を探す。どちらも、探索対象にないグラフ・値・操作列の性質を一般化する根拠にはしない。

[Schema.lean](../Test/Schema.lean) の検証対象は、このリポジトリの Schema が使うキーワードである。JSON Schema 規格全体を実装した検証器ではなく、未対応キーワードはエラーになる。

検証の実行手順は [README](../README.md#検証) を参照。

## 受入状況

2026-09-19 時点で M2〜M4 の受入条件を満たした。

| 段階 | 確認した根拠 |
| --- | --- |
| M2 探索器と基本定理 | I1〜I4、T1・T3・T5・T6・T7・T8・T13 と `step_ok_cases` が未完の証明なしでビルド。全 12 例グラフの深さ 8 探索が完走し、反例ゼロ |
| M3 ストリーム | T2・T4・T10 に加え、T9 は `schedule_determinism`、T12 の逆方向は `idle_enters_blocked_no_progress` で証明。`hasWork_iff_all_ops` が start 後の不変条件を満たす状態で全 Op の完全性を与える |
| M4 再開 | イベント検査と command replay の一致、`recordTransaction_jsonl_roundtrip` による文字列往復、`recordCommands_torn_jsonl` による任意の未コミット prefix の回復を証明 |

`bin/test` は全通過。T9 の 3,948 組の比較、T12 の独立した操作生成、v2 Schema・旧 fixture・破損履歴・CLI・標準 JSON parser との交差検査も通過した。主要定理の公理依存を調べ、Lean 標準の `propext` / `Classical.choice` / `Quot.sound` のみであることを確認した。適用範囲は上記の各節に示した前提に従う。
