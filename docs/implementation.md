# 実装上の決定と検証範囲

2026-09-17。対象は `suimon-design.md` の Lean 仕様と検査・探索ツールである。着手時のリポジトリは設計書のみであり、既存の `formal/`・`python/` は存在しなかった。参照プロジェクトは変更していない。

更新後の §4・§10 に合わせ、Lake プロジェクトはリポジトリ直下に移設済み。`Suimon/` にモジュール、`Test/` にテスト、`Test/graphs/` に例グラフ JSON、`Test/traces/` に履歴を置く。旧 `formal/` 階層は削除した。

説明の部品名は設計書 §3 に合わせる。Lean の型・操作名と JSON の識別子は §4 の名前を使う。主な対応は次のとおり。

| 説明での用語 | Lean モデルでの表現 |
| --- | --- |
| 逐次 | plain の線 |
| ForEach | `forEach` |
| Concurrency | 出力から複数の線を引き、`waitAll` で合流 |
| Coalesce | `coalesce`。発火操作は `fireCoalesce` |
| Sub | `subworkflow` |
| yield できるノード | stream 出力を持つ `leaf`。出力操作は `emit` |
| AllWait | `collect`。発火操作は `fireCollect` |
| ノード種別ごとの全体上限 | `leaf` の `concurrency` 属性 |

## 決めたこと

- **配線の型**: 両端の種別が完全に一致する。plain → stream には plain 入力を受けて yield できるノードを明示的に挟む。stream → plain は AllWait（`collect`）。
- **入力元**: 各入力に edge または graph entry がちょうど 1 つある。未接続入力は定義時に拒否する。名前の重複、cycle、部分グラフの境界と外側の arity の不一致も拒否する。body 内の Branch は、各 arm の全経路が body の出口に達する前に共通の Coalesce に合流することも検査する。逆向きには root / body 両方で Coalesce の入力を検査する。各入力の Branch 選択条件が、共通の Branch の入力条件と異なる arm 1 つの組に一致し、全 arm と1対1になることを要求する。これにより共有の plain 入力と正しく再合流した入れ子を許し、独立した leaf、同じ arm の重複、別 Branch の選択条件の混入を拒否する。
- **境界チャネル**: entry/exits を独立した仮想チャネルで表す。entry のアイテムは start で置く。出口の結果は保持し、root の結果自体は未消費作業として数えない。body の出口は親が回収し、消費記録も残す。
- **スコープ**: `Frame` が部分グラフの実行ごとのチャネルを分離する。インスタンスの一意性は `(node, trigger, path)`。path の要素は親 ID と iteration を符号化したスコープ ID。Loop の同じノードは異なる path で実行される。
- **ノード種別ごとの全体上限**: `leaf` の `concurrency` 属性を、同じ静的なグラフ定義のノードごとに、ForEach の複数起動を横断して適用する。別々の部分グラフに同名のノードがあっても共有しない。
- **AllWait**: `collect` は ItemId の昇順で整列し、JSON で符号化した象徴的なリスト ID を作る。到着順を結果に含めない。Concurrency の合流に使う `waitAll` は入力ポート名と ItemId の組を record の象徴的 ID にする。実データはモデル外。
- **アイテム ID**: 暗号 digest の代わりに JSON 配列を符号化する。実装時に digest を用いる場合、衝突しない抽象識別子への射影が必要。同じ処理・入力・出力番号は同じ ID を使い、再送は同じ occurrence とみなす。別の occurrence は別 ID にする。
- **Merge**: fan-out 後に同じ ItemId が別々の入力線から戻る場合も occurrence を保持するため、入力線と元 ID から新しい ID を作る。同じ線・同じ ID の再送は重複排除する。
- **Branch / Coalesce（D1、2026-09-18 改訂）**: 非選択 arm は EOS のみ。`skip` がその先の plain ノードを cancelled として終端させる。body 内では必ず Coalesce に合流し、出口には値ちょうど 1 個を渡す。root では合流しない Branch も許す。Coalesce は単一 Branch の排他的な合流であり、独立した値の first-wins にはしない。`fireCoalesce` は選択した plain 入力の EOS と上流 succeeded を確認し、先頭アイテムを 1 回だけ転送して出力を EOS で閉じる。非選択経路の EOS がまだ届いていなければ、その到着・skip 完了まで body の回収を待つ。Coalesce 自身の skip は全入力が空の EOS の場合に限る。不正な由来の入力は実行前のグラフ検証で拒否する。
- **body の回収**: 親の inputs/outputs と body の entries/exits は宣言順に対応する。`finishSubworkflow` が Sub / ForEach の完了を親に反映する。ForEach の出力 EOS は入力 EOS と全起動の成功後だけ置く。この EOS を受けて AllWait が発火する。Loop は `loopIterate` が body を回収し、次回の frame を作る。
- **Loop（D3）**: 回数は 1 始まり。上限回の判定が true なら成功、false なら instance を failed、execution を blocked(`LOOP_LIMIT`) にする。`manualRetry` は leaf と loop に対応する。loop はその起動の上限を 1 増やし、最後の body の出力を次の回へ渡して running に戻す。終了済みの回は再実行しない。追加上限を `Instance.extraIterations` に保持し、実効上限は定義の `maxIterations + extraIterations` とする。同じ定義を使う別の Loop 起動の上限は変えない。leaf の試行上限追加と retryWait は従来どおり。
- **lease**: attempt/token/instance と時刻を検証する。`now = until_` は無効。失効は abandoned、再試行待ちは `now + retrySeconds`。期限切れ attempt と期限到来 retry の処理を claim より先に行う。
- **再送**: yield の操作 `emit` は EOS 前に限り、同じ線の同じ ID を重複排除する。complete は成功時の attempt/token/outputs 全体が一致する receipt のみ冪等。成功後の異なる出力は拒否する。終端 execution は状態を変えない（T13）。無効な worker 操作は終端後も拒否し、それ以外の操作は恒等として受理する。
- **キャンセル**: running attempt と未完 instance を cancelled にし、完了・放棄済み attempt の履歴は保持する。
- **idle と解除（D2、2026-09-18 改訂）**: `State.hasWork` は探索器と共有する候補列挙のうち、idle / cancel / manualRetry を除いて、受理され**状態を変える** Op があるかを調べる。冪等な complete の再送と、単に残っている未消費アイテムは作業に数えない。ready の claim、期限に進めた retryWait の promoteRetry、期限切れ lease の回収、activate / spawn、EOS の伝播、Loop の次の回、body の回収を含む。作業があれば idle は状態を維持する。作業がなければ、全 root ノードと出口が終端した場合は succeeded、それ以外は blocked。既存の `LOOP_LIMIT` や失敗理由は保持する。自動 resume は削除した。blocked から running への解除は manualRetry が行う。
- **依存**: Lean 4.34.0 の標準ライブラリだけで実装した。Batteries/Mathlib は追加していない。設計書の Plausible による乱択は未導入で、現在は固定 LCG を用いる。再現性のある seed と有限候補集合による探索を提供する。
- **facts の公開射影（D9、2026-09-19）**: `Suimon/Trace/Projection.lean` が wire format のフィールドを明示する。Instance 作成は id / node / path / trigger のみ。カウンタ・inputs・内部状態等は command の replay から復元する。attempt、lease、token、消費、execution 状態も公開フィールドを明示し、内部構造の ToJson 導出に結合しない。facts は必須で、欠落・余分なフィールド・改変を拒否する。区分内の順序は論理 ID で固定する。破壊的変更として `schema_version: 2` を必須にし、fixture を更新した。公開フィールドは snake_case とし、配置と消費の主体は `by_instance`、lease 期限は開始・更新とも `lease_until` に統一する。内部フィールド追加では wire format を変更しない。詳細は trace-format.md。

## 設計書の命題に必要な修正

### T2 は未来の進行と保存を分ける

`start` の直後に worker が二度と動かなければ、アイテムは未消費のまま execution は running に留まる。元の「必ず消費されるか blocked/cancelled になる」は進行性を含み、公平性なしでは成り立たない。

実装では、置いたトークン列を消さない、消費位置は単調、消費したアイテムには一意な消費記録と下流インスタンスがある、という保存の安全性を検査する。未消費のアイテムが残ることを違反にはしない。Filter が落としたアイテム、skip が終端させた入力にも消費記録がある。

### T3 は path を含める

Loop と Sub では、同じ node と trigger の組が複数のスコープに現れる。非重複の単位は設計書 I2 と同じ `(node, trigger, path)` とし、線の消費は `(channel ID, token index)` で識別する。lease が保証するのは有効な結果の確定の排他性であり、期限切れ worker の外部副作用を取り消すものではない。

### T9 は A4 だけでは足りない

同じ oracle でも、出力前に cancel した実行と正常終了した実行の出力は一致しない。任意の有限 prefix 同士も一致しない。また現モデルの Op は外部から oracle の結果を受け取るため、`Oracle` と Op 列の適合関係を全体の定理の前提に含める必要がある。

全体の決定性には少なくとも、同じ graph/inputs、同じ決定的 oracle に適合した操作列、成功して stream が drain された実行、同じ安定した occurrence ID、再試行時の yield 重複排除、到着順によらない AllWait の結果、という前提が必要。一部を yield したまま失敗した実行との比較も除外する。

現在の `deterministic_item_multiset` / `deterministic_item_counts` は純粋な item 変換が permutation を保存すること、`deterministic_leaf` は A4 の下で leaf の入力 permutation が出力を変えないことを証明する。**これらは状態遷移系全体の合流性の証明ではない。** 完全な T9 は今後の証明課題として残している。

一般命題の型を `Suimon/Execution.lean` の `ScheduleDeterminism` に置いた。同じ graph / inputs とスコープごとの同じ oracle に対する、任意長の受理された2操作列を量化する。候補列挙・worker 数・試行回数・探索深さの制限は付けない。これは証明対象の `Prop` の定義であり、まだその inhabitant を与える定理はない。`ConformingSteps` は実際の `step` の受理と各操作の制約を記録する操作列で、別の遷移意味論ではない。`ConformingSteps.replay` で実際の replay と結び付けた。

`oracleConforms` は emit の所属、complete の plain 出力、Branch / Filter / Loop の選択を固定 oracle と照合する。さらに complete 時、各 stream 出力線の履歴が oracle の指定する多重集合を満たすことを要求する。指定が `[x,y]` でも、生の step は x だけ emit して complete すれば succeeded / drain に至れるため、「送った値は oracle の集合に含まれる」だけでは不十分である。`Test/OracleConformance.lean` はこの到達可能な反例を再現し、完全な通常実行と lease 失効後の再送実行は適合し、途中で打ち切る complete は不適合になることを確認する。`ScopedOracle` は論理 path をキーに含め、occurrence ID が worker や attempt に依存しない形を表す。

`Suimon/Theorems/Determinism.lean` には次を一般補題として追加した。

- `placeToken_duplicate` / `place_duplicate`: 消費位置に関係なく配置履歴全体で再送を排除する。EOS 後は再送も拒否する。
- `emit_duplicate_channels`: 公開 step が受理した既存 occurrence の emit は、全チャネルの全フィールドを保存する。
- `transition_administrative_channels` / `administrative_step_channels`: claim / renew / expireLease / promoteRetry / fail は、実際の操作本体を展開してもチャネルを変えない。
- `retry_fragment_channels` / `retry_fragment_multisets`: これらの管理操作と既存 occurrence の再送だけからなる、任意長の受理された操作列は、全チャネルとその多重集合を保存する。新規 emit、complete、消費や body 操作を含む任意の実行同士の比較ではない。
- `sortedItems_eq_of_perm` / `collect_value_deterministic`: 任意の入力 permutation について、Collect が実際に使う整列済みリストと結果 ID が一致する。Collect の操作列全体の証明とは区別する。

完成時のデータフローを `Suimon/Semantics.lean` の `GraphEval` / `NodeEval` / `LoopEval` として定義した。leaf、Branch、Filter、Merge、Collect、Coalesce の入出力、Sub の回収、ForEach の各 trigger に対応する子評価、Loop の各反復を含む。`Suimon/Theorems/Semantics.lean` の `GraphEval.functional` は、この意味論の完成結果が一意であることを証明する。グラフの位相順序、子評価、Loop の反復について帰納し、子 frame の全チャネルも結果に含める。候補列挙や探索深さの制限は使わない。

実行可能なモデルとの接続には、次の補題を追加した。

- `Graph.validate` をグラフの大きさで停止する全域関数に変更した。`topology_of_validate`、`validate_port_names`、`input_single_source` で、検証成功から DAG の順位、ポート名の一意性、各入力の唯一の接続元を取り出す。`WellFormed` 自体の定義は引き続き検証成功である。
- `ConformingSteps.layout` / `frames_certified` / `unique_frames` は、実際の操作列に沿って、チャネルの配置、frame のグラフの検証成功、scope の一意性を保つ。`retained_node` は既存 scope のグラフ定義が変わらないことを示す。
- `ConformingSteps.completion` / `completedState` は、成功が root の `frameDone` を確認した idle に由来することと、成功時の root・全 frame・チャネルの構造を実際の操作列から取り出す。
- `ConformingSteps.input_snapshot` は、任意長の受理操作列を通じて、既存 instance の node / path / trigger / inputs が変わらないことを、操作本体から証明する。manualRetry も対象に含む。
- `ConformingSteps.retains_closed_channel` は、閉じたチャネルの配置履歴が以後変わらないことを示す。`Effects.place_value` / `place_items` は配置処理の正確な更新と item 集合への効果、`consume_item_receipt` は消費時に追加される記録、`succeededDrained_input_receipt` は drain された入力の全 item に消費記録があることを示す。

配置・入力の消費・body の生成と回収は補助関数へ分解した。EOS・plain cardinality の検査順と再送の重複排除は維持している。内部の通常ノード照合は `State.nodeInstance?` に集約し、`(node, path, trigger = none)` で照合する。外部 trace の ID 形式は変えていない。

**残る証明は、成功・drain された `ConformingSteps` から `GraphEval` の導出を構成し、その結果のチャネルと実際の `channelBags` の一致を示す適合性である。** 各 Op の入出力、ForEach の消費 item と子 frame の対応、Loop の反復間の入力引継ぎを、実行履歴からこの導出へ接続する必要がある。`GraphEval.functional` 単独では `ScheduleDeterminism` の証明にならず、M3 は未完のままである。全線の観測と drain の定義は Execution に集約し、乱択検査も同じ定義を使う。

`Test/Determinism.lean` は12例と共有入力・入れ子の Coalesce の計14グラフに対し、6つの固定 oracle 設定、16通りの schedule seed、故障なし / lease 失効 / retryable fail の3モードを使う。候補列挙から、固定した Branch / Filter / Loop の結果と leaf 出力に適合する操作だけを選ぶ。stream は設定ごとに0〜2個の全 occurrence を出してから complete する。oracle の選択に schedule seed や attempt ID を使わない。故障なしの基準実行と比較し、4,032実行、3,948比較を行う。

再試行モードは最初に claim した leaf に1回の故障を注入する。stream を持つ leaf では、schedule seed が選んだ部分集合または全件を emit した後に失効・失敗させる。`expireLease` の時刻進行で他の lease も失効した場合は、全失効 attempt を回収してから retry 時刻へ進め、promoteRetry を済ませて再 claim する。この有限範囲では2回目の attempt を再び故障させない。

ドライバは attempt ごとの送信済み集合を State と別に記録し、再 claim 後にも同じ occurrence ID の全件を実際に再送してから complete する。重複排除された emit は State を変えなくても試行に残し、同じ attempt では各 ID を1回だけ送って停止性を保つ。再送が channel の履歴を変えないことと、下流で既に消費されたアイテムの再送まで実行したことも検査する。現在の固定 seed 群では1,304失効、1,248 retryable fail、2,552 promoteRetry / 再 claim、506再送（うち消費後482件）を通る。

各試行に256操作の上限を設け、成功・drain に至らない場合は失敗とする。比較できなかった試行を捨てない。全線の EOS、root の出口以外の未消費アイテムなし、子 frame の回収を検査し、論理 channel ID ごとにアイテムを整列して多重集合を比較する。root の線だけでなく、Sub / Loop / ForEach の子 frame の entry / edge / exit も対象。重複数を保持し、格納順は無視する。実際に到着順が変わった比較が存在することも必須にする。反例には graph、両 seed、故障モード、2本の操作列と比較結果を出す。

cancel、恒久失敗、試行上限を超える繰り返し故障、manualRetry はこの有限比較の対象外。任意長の stream、任意の oracle、全 schedule の証明ではない。一般証明に残る課題は、上記の実行履歴と完成時の意味論の適合性である。

検査の感度確認として、Collect を一時的に到着順のままリスト ID を作る実装に変えたところ、streaming の oracle seed 2、schedule seed 1 / 7 の組で多重集合の不一致を検出した。変更は検証後に戻した。

再送の感度確認では、重複排除の対象を配置履歴全体から未消費部分だけに変えた。streaming の oracle seed 1、schedule seed 1、lease 失効モードで、消費済みアイテムの再送時に `INVARIANT` 拒否を検出した。ガードによる拒否も検査失敗として扱うため、壊れた再送を候補から除いて成功扱いにはしない。この変更も検証後に戻した。

## Lean の証明と実行時の検証

`step` は操作の前提と lease を検証し、`transition` の結果を `commit` に渡す。`commit` は不変条件と状態履歴の検査に成功した結果だけを返す。これは仕様の一部であり、ガード無しの `transition` が常に不変条件を保存する、という主張ではない。探索器は `INVARIANT` による拒否も反例として報告するため、ガードで実装の欠陥を隠さない。

全 Lean ファイルに未完証明や独自の未検証公理はない。公理 A1–A5 は `Assumptions` の値として表現し、Lean カーネルに新しい命題を無条件で追加していない。

| 対象 | 現在の証明・検証 |
| --- | --- |
| `step` | `step_ok_cases`。受理された step は、恒等な吸収か、認可・`prepare`・不変条件・履歴検査を全て通った実行のどちらか。独立した関係 `Step` は置かない（D10） |
| I1–I3 | `preserves_invariants` / `replay_invariants`。有効な初期状態からガード付き step/replay が保持。例グラフの初期状態は実行検査 |
| I4 | `preserves_history`。許可された status 遷移、チャネルの prefix 保存、消費位置と時計の単調性 |
| T1 | `plain_order`。activate 受理時の入力 EOS・上流 succeeded の条件。`coalesce_plain_order` は選択した入力について同じ条件を保証 |
| T2 | `channel_history` / `consumed_items_accounted`。上記の保存に関する安全性の形 |
| T3 | `consumption_unique` と `succeeded_retained` / `replay_retains_success`。同じ消費位置の重複記録禁止と成功状態の保持 |
| T4 | `eos_final`。有効な境界で EOS が末尾にある。prefix 保存と併せ、実行検査で EOS 後の配置を拒否 |
| T5 | `once_only`。同じ instance key の再挿入拒否。Concurrency の合流（`waitAll`）/ AllWait（`collect`）/ Coalesce の操作全体については回帰テストも実施 |
| T6 | `branch_exclusive`。実際に使用するルーティング関数が非選択ポートへ値を出さない。操作全体の回帰テストあり |
| T7 | `loop_bounded`。追加分を含む実効上限以下であることと、親に属する body frame 数がカウンタに一致することを保持 |
| T8 | `lease_exclusive` / `invalid_lease_rejected`。running attempt は高々 1、無効な lease は冪等再送以外拒否 |
| T9 | `ScheduleDeterminism` に一般命題を定義。`GraphEval.functional` で ForEach / Loop / DAG を含む完成時意味論の一意性を証明。実 step の再送・構造・入力の保持と完了境界を証明。実行履歴から `GraphEval` と全線の観測一致を構成する適合性は未証明であり、T9 全体は未完。固定 oracle の全線多重集合比較は回帰として継続 |
| T10 | `spawn_without_eos`。入力先頭の item による準備条件に EOS は不要。実際の spawn 受理は回帰テスト |
| T11 | `replay_append` / `replay_durable` / `complete_idempotent` / `replay_retains_success`。Op replay の合成則と成功状態の保持。JSONL の encode/check 逆変換と torn-log 回復は回帰テスト |
| T12 | `idle_step_work`。公開 step の idle 後が running なら `hasWork` が真。`hasWork_iff` / `work_step_eq` で、共有候補中に状態を変える受理操作が存在することを証明。`idle_step_enters_blocked_no_work` は公開 step が新たに blocked にするなら候補内に進行可能な操作がないことを証明。全 Op に対する候補列挙の完全性は未証明 |
| T13 | `terminal_absorbing`。すべての Op に対して終端状態は変わらない |

M1 は完了。M2 の探索と関係の一致・各局所補題は実装済みだが、すべての設計命題を操作列全体について証明し切った状態ではない。M3 の T9、M4 のイベント codec と回復の一般的な対応証明などは未完。M5 は対象外。

## 探索と回帰

探索候補は有限である。各 entry に象徴的アイテム 1 個、yield できるノードの出力に最大 2 種の ID、全 Branch arm、Filter の真偽、Loop の真偽、指定 worker 数、lease 失効、再試行、キャンセルを含める。時間は固定 tick の更新に加え、lease 期限と retryAt に進める。任意の実データ・任意の長さの stream の全探索という意味ではない。

候補列挙を `Suimon/Candidates.lean` に置き、探索と `hasWork` の両方で使う。`hasWork` は標準設定の候補を検査し、idle の判定を含まない実行関数で循環依存を避ける。数える操作についてはこの関数と公開 `step` が一致する。claim 用の ID は使用済み attempt/token を調べて新しいものを選ぶため、外部履歴の ID と偶然衝突して ready を作業なしと判定することはない。この列挙が全 Op の進行を代表できるという完全性までは、これらの定理からは得られない。

`Test/Work.lean` は探索器の候補列挙を使用せず、各種 Op と別の時刻・ID・oracle 結果を生成する。初期状態から実際の Op を適用した状態だけで「通常 Op が受理されて状態が変わるなら hasWork が真」を乱択検査する。claim / fireCoalesce の候補を意図的に抜いた場合に検査が検出することも確認する。Op のコンストラクタ追加時にはこのテストの更新をコンパイル時に要求する。これは完全性の一般証明の代わりではない。

状態そのものを JSON 化して重複を除き、BFS で指定深さまでの到達状態を調べる。深さは primitive token イベント数ではなく Op 数。状態上限に達した場合は `complete: false` と非ゼロ終了を返し、反例ゼロの完走として扱わない。

回帰には菱形の Concurrency、N 字、Branch、Coalesce、共有入力と入れ子の合流、body に Branch → Coalesce を持つ Loop と外側の Sub、上限 2 の Loop と手動再試行、yield できるノード → ForEach → AllWait、Merge、Filter を含む。idle は ready・retryWait・回収待ち frame を見落とさないこと、冪等な再送で終了を妨げないことを確認する。状態の status を直接書き換えた resume テストは削除し、複数失敗の一部を回復させた実際の操作列から、依存停止と残りの manualRetry を確認する。`DEPENDENCIES_UNRESOLVED` がユーザー指定の失敗コードだった場合も、通常操作による自動解除をしない。CLI テストは不正な Coalesce 配線の拒否、JSON Schema 適合、正しい履歴、claim 欠落、EOS 後の yield（`emit`）、偽の token/lease_until、sequence/txn の破損、未確定末尾、seed の再現性を確認する。

`Test/graphs/coalesce-stages.json` は Branch → Coalesce → Branch → Coalesce の多段例で、深さ8の探索で両段を完了できる。前段・後段の arm の全4組み合わせを root と Sub の body で実行し、前段の合流前には後段を動かせないこと、前段の arm を後段の合流へ混ぜた配線を静的に拒否することも回帰に含める。

`DEPENDENCIES_UNRESOLVED` という文字列だけでは「failed インスタンスがない」とは言えない。二つの失敗の片方だけを manualRetry して完了させ、idle に入ると、この理由で止まりつつもう片方を再試行できる。初期状態からこの経路を回帰にしている。`ExecStatus.failed` は予約状態で、現在の遷移からは設定しない。

テストは `Test/Artifacts.lean` で CLI の実プロセスを起動し、`Test/Schema.lean` で現在の JSON Schema が使うキーワードを検証する。Lean の標準ライブラリだけを使う。Schema 検証は Draft 2020-12 全体の実装ではなく、このリポジトリの型・必須フィールド・追加フィールド禁止・参照・選択肢・値や配列の制約に対応する。未対応キーワードや未解決の参照は検証前にエラーとする。

`Test/TraceProjection.lean` は公開フィールドの固定、非公開 Instance フィールド変更と channel 格納順に対する facts の不変性、余分な内部フィールド・改変・facts 欠落・旧 version の拒否、replay が元の内部状態を復元することを検査する。消費と lease 更新の実際の操作列から snake_case の facts を検証し、旧 `byInstance` / `until_` を Schema と検査器の両方が拒否することも確認する。フィールド変更のテストだけは射影関数の入力を意図的に変えたもので、変更後の状態の到達可能性を主張しない。
