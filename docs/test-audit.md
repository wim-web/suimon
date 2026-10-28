# テスト価値監査・対応台帳

2026-10-28更新。監査対象commit: `7d0c9cf0df2aa9ee82c0812eb14bebe77fb513d6`。

**部分統合15項目・補強／置換38項目、計53項目をすべて対応した。未対応は0。** 固有の入力・失敗理由・境界・本番経路の保証を残し、重複assertを統合した。通過だけでなく、保証を壊したときに失敗することも主要な検出漏れで確認した。

全501監査項目は [test-audit.csv](test-audit.csv) に保持している。`file`・`line`・`cases`・`protects`・`production`・`verdict`・`reason`・`action`・`verification` は監査時の記録。対応後は `status`・`resolved_on`・`resolution`・`current_refs`・`resolution_verification`・`resolution_notes` を読む。`current_refs` は更新後のコード位置で、統合して削除したテストから残存する保証へ辿れる。501は監査単位であり、変更後のテスト実行件数ではない。

| 領域 | 部分統合済み | 補強・置換済み | 未対応 |
| --- | ---: | ---: | ---: |
| Lean: core / CLI | 1 | 3 | 0 |
| Lean: trace / schema | 4 | 3 | 0 |
| Go: model / limits | 2 | 5 | 0 |
| Go: runtime / recovery | 2 | 12 | 0 |
| Go: trace / CLI | 5 | 3 | 0 |
| UI kit | 0 | 6 | 0 |
| Playground: Go / UI / WASM | 1 | 6 | 0 |

## 検出力と保証の維持

- no-op除外を通るfixtureを用意し、復旧payload予算は停止位置と保持総量まで検査するようにした。両方とも、監査時に通っていた破壊を現在は検出する。
- runtime recorderは本番の `recordAdmitted` を比較する。拒否後の再利用とstate/index/sequenceの不変性も検査する。state snapshotを全fieldのdeep copyへ変更し、ポインタを介した書き換えの見逃しも解消した。
- FileJournalは既存の再open/truncateに加え、子プロセスの強制終了から新しいEngineで復旧する。排他も別プロセスで検査する。Windowsでは異常終了後のOSによるlock解放待ちだけを期限付きで許容する。
- Sync失敗を独立に注入し、durableになる前にcall/fetchの副作用を公開しないことと、durable prefixからの復旧を確認する。
- UIの同実装同士の比較を独立期待値へ置換し、実subworkflowの生成fixtureを使用する。Playgroundは実Worker・Go WASMを通して、scenario変更、focus、入力保持、unit送信、実行中無効化、結果、cancel、polling停止まで確認する。
- schema検査器は独立したpython-jsonschemaと341ケースで照合する。現行CLI生成recordに加え、小数表記・uint64境界・巨大指数・外部`$ref`を含む。固有のkeyword受理／拒否は固定期待値でも確認する。

本番コードの変更は、Go探索のprivate filter抽出と未使用のprivate recorderメソッド削除に限定した。公開API・実行規則・資源上限を変更してテストを通した箇所はない。失敗していたruntime/replayベンチマークは既定上限で成立する100/1000件を計測し、大小の比較を残した。

## 対応一覧

各IDは監査台帳の同じ行に対応する。旧テストを削除した場合も、残す保証の移動先を示す。

### Lean: core / CLI

| ID | 対応内容 | 対応後の検査・実装 |
| --- | --- | --- |
| TA-006 | explore出力をJSON objectとして読み、許可された終端status・natural件数・合計20・stderr空を確認。各fixtureについて--steps 0のexit1、stdout空、診断も確認。 | [explore summary and exhausted step budget](../Test/Cli.lean#L65) |
| TA-065 | TaskResult pending/failed/valueを固定JSON literalに照合し、そのliteralのdecodeも元のresultに等しいことを確認。同一encoder/decoderの自己一致だけに依存しなくなった。 | [TaskResult JSON fixed shapes](../Test/Step.lean#L291) |
| TA-149 | Validate.resourceLimitsから同じCodec.parseのbyte/depth重複検査を除去。独自差分だった空白だけの上限raw scanはInputLimitsへ移し、既存のexact/over/depthテーブルに集約。 | [depth boundaries across public parsers](../Test/InputLimits.lean#L23)<br>[byte boundaries and raw whitespace](../Test/InputLimits.lean#L37)<br>[definition resource admission remains separate](../Test/Validate.lean#L185) |
| TA-182 | 単発wall-clock<1秒を撤去。validationWorkがallocation heartbeatを数え、8→16段のmerge chain/diamondで32倍以内というscaling上限を確認した後、既存20/40 merge・30diamondのvalidation成功を維持。 | [validationWork](../Test/Validate.lean#L172)<br>[validationGrowth](../Test/Validate.lean#L179)<br>[merge/diamond scaling checks followed by semantic regression cases](../Test/Validate.lean#L306) |

### Lean: trace / schema

| ID | 対応内容 | 対応後の検査・実装 |
| --- | --- | --- |
| TA-032 | Test.Schemaの独自検査器をpython-jsonschema draft2020-12と照合する341ケースのcorpusを追加。使用keywordの受理/拒否、現行CLI生成record、外部$ref経由の小数/uint64境界を独立期待値で検査する。Decimalで丸め・underflowを避ける。bin/test schemaとCIに必須接続。 | [SchemaOracle.run](../Test/SchemaOracle.lean#L9)<br>[main](../Test/schema_oracle.py#L37)<br>[schema suite](../bin/test#L37) |
| TA-045 | SchemaMainのordered fields固定受理caseを、同shapeのCLI encoder生成recordをschemaへ通す既存ループへ統合。canonical順序はTraceのexact text検証で維持。 | [generated record schema validation](../Test/SchemaMain.lean#L67)<br>[exact canonical text](../Test/Trace.lean#L269) |
| TA-077 | header text のexact encoded-text assertionと同一入力のkeys-only assertionを削除。field順序・field名・値・JSON表記を守る既存exact文字列照合を維持。 | [header text](../Test/Trace.lean#L272) |
| TA-078 | op record text のexact encoded-text assertionと同一入力のkeys-only assertionを削除。field順序・field名・値・JSON表記を守る既存exact文字列照合を維持。 | [op record text](../Test/Trace.lean#L269) |
| TA-080 | commit record text のexact encoded-text assertionと同一入力のkeys-only assertionを削除。field順序・field名・値・JSON表記を守る既存exact文字列照合を維持。 | [commit record text](../Test/Trace.lean#L271) |
| TA-133 | 失敗するdecodeHeader/decodeを渡し、work予算不足ならpoison診断よりquotaエラーが先行することを確認。十分な予算でpoisonへ到達する対照例も追加。INPUT_MISMATCHになるstart noneでstep実行前のquota拒否と、予算十分時の具体的step拒否を照合。 | [work before parse/decode/step with poison controls](../Test/TraceBounded.lean#L58)<br>[quota wins over invalid step](../Test/TraceBounded.lean#L80) |
| TA-136 | 捨てられていたcheckBothの結果をcheckedText/rejectedText/rejectedExactlyへ変更し、期待受理/拒否を明示。sequenceとextra payloadの診断・行番号を固定。identity再利用成功時のcommit数/payload不変/result列を確認し、同一・異なるpayload再送の両方を拒否。64/128/256streamもcommit/payload数・完了flag・result列を独立に確認。 | [duplicate key and sequence explicit rejection](../Test/TraceBounded.lean#L98)<br>[identity reuse with and without repeated payload](../Test/TraceBounded.lean#L106)<br>[stream expected counts and results](../Test/TraceBounded.lean#L118) |

### Go: model / limits

| ID | 対応内容 | 対応後の検査・実装 |
| --- | --- | --- |
| TA-328 | TestDefinitionTextLimitsを削除し、固有の未閉鎖array/空白の境界とpreflight優先順をTestInputLimitsの両parser matrixへ統合。深度/byte/文字列escapeの既存境界保証は維持。 | [TestInputLimits](../implementations/go/src/inputlimits_test.go#L13)<br>[TestInputLimitEntryPoints](../implementations/go/src/inputlimits_test.go#L77) |
| TA-333 | 長鎖3ケースのValidate・実Engine.Run・出力x,xの確認は維持し、1秒/5秒のwall-clock性能assertを除去。各caseをsubtestにし、runは30秒context timeoutで停止を検出。性能比較は既存BenchmarkKindChainへ分担。 | [TestLongMergeChains](../implementations/go/src/derive_test.go#L207)<br>[BenchmarkKindChain](../implementations/go/src/definition_limits_test.go#L229) |
| TA-340 | 同seedでのWalkをEncodeOpの全列で比較。最終state・終端・op上限とPRNG固定値の検査も維持。 | [TestExploreValues](../implementations/go/src/identity_test.go#L124) |
| TA-353 | 再開後journalにallのOpSettleが存在しないことと、Check.Valuesのpayload総bytesが再開前保持量retained以下であることを追加し、後続の別quota超過による偽陽性を防いだ。 | [TestQuotaResumeCountsRetainedPayloads](../implementations/go/src/limits_test.go#L268)<br>[all OpSettle不在assert](../implementations/go/src/limits_test.go#L295)<br>[保持payload総量assert](../implementations/go/src/limits_test.go#L304) |
| TA-392 | 全22拒否caseを同一subtest matrixに統合し、各caseのStep呼出前後で全State fieldの独立snapshotを比較。Rejection型/完全codeとresult identity検査も維持。 | [TestStepRejections](../implementations/go/src/step_test.go#L503) |
| TA-393 | 候補生成と拒否/no-op除外をprivate acceptChangesへ分離し、本番と同じfilterに実Stepの拒否Start/no-op Cancel/変更Concludeを入力して唯一の変更候補だけ残ることを確認。Cancel冪等性と候補段階の抑止はTestCancelIsIdempotentへ分離。 | [TestCancelIsIdempotent](../implementations/go/src/step_test.go#L578)<br>[TestAcceptedDropsNoOps](../implementations/go/src/step_test.go#L596)<br>[acceptChanges](../implementations/go/src/explore.go#L254) |
| TA-415 | TestValidateMessagesの重複4ケースを元のsemantic testsの完全一致assertへ統合し、固有のList<List<Org>> entry表示をTestValidateTypesへ移した。誤記two inputsは正しいmissing input caseへ統合。 | [TestValidateTypes](../implementations/go/src/validate_test.go#L189)<br>[TestValidateInputs](../implementations/go/src/validate_test.go#L207)<br>[TestValidateGraph](../implementations/go/src/validate_test.go#L266)<br>[TestValidateBranchArms](../implementations/go/src/validate_test.go#L287) |

### Go: runtime / recovery

| ID | 対応内容 | 対応後の検査・実装 |
| --- | --- | --- |
| TA-321 | サイズを100/1000の10倍比較へ調整。実際の既定Engine/reader上限内で全fixture生成と計測が成立するようにし、benchmark専用の本番上限緩和は行わない。 | [BenchmarkRuntimeStream](../implementations/go/src/bench_test.go#L116) |
| TA-322 | サイズを100/1000の10倍比較へ調整。実際の既定Engine/reader上限内で全fixture生成と計測が成立するようにし、benchmark専用の本番上限緩和は行わない。 | [BenchmarkCheckStream](../implementations/go/src/bench_test.go#L127) |
| TA-323 | サイズを100/1000の10倍比較へ調整。実際の既定Engine/reader上限内で全fixture生成と計測が成立するようにし、benchmark専用の本番上限緩和は行わない。 | [BenchmarkRuntimeUsers](../implementations/go/src/bench_test.go#L186) |
| TA-324 | サイズを100/1000の10倍比較へ調整。実際の既定Engine/reader上限内で全fixture生成と計測が成立するようにし、benchmark専用の本番上限緩和は行わない。 | [BenchmarkCheckUsers](../implementations/go/src/bench_test.go#L197) |
| TA-346 | 既存同一プロセス排他を保持し、親保持中に子がOpenを拒否されるケース、子保持中に親が拒否されるケース、子をKillした後に親が取得できるケースを追加。readiness pipeでOS lock取得を同期。 Windowsの異常終了後だけErrJournalLockedを5秒以内で再試行し、OSによる遅延解放を許容。通常Close後の即時解除、他OS/他errorの即時失敗は保持。 | [TestFileJournalLock](../implementations/go/src/journal_lock_test.go#L13)<br>[startJournalProcess](../implementations/go/src/journal_process_test.go#L35)<br>[openJournalAfterProcessExit](../implementations/go/src/journal_process_test.go#L80) |
| TA-360 | random walk途中のfixtureを明示7操作で到達する状態へ変更。28個の拒否ケースに独立の期待Rejection.Codeを設定し、Stepとmachine双方が拒否すること、入力state・machine state/index/seenとintroduced値が変わらないことを検証。共通agree helperも拒否後のindex/seen整合性を確認する。 State snapshotは標準encoding/jsonでStateの別定義型をdeep copyし、全Go fieldのpointer/path/入れ子sliceを分離。拒否前後のstateはreflect.DeepEqualで比較し、本番Equal/MarshalJSONをoracleにしない。 | [TestMachineRejections](../implementations/go/src/machine_test.go#L129)<br>[agree](../implementations/go/src/machine_test.go#L58)<br>[cloneState](../implementations/go/src/machine_test.go#L21) |
| TA-361 | owned.recordWith比較を本番owned.recordAdmittedへ置換。各walk遷移でadmission callbackが公開Recorderと同じrecordを受け取ることを確認し、一度ErrQuotaExceededで拒否してstate/index/seen/known/seqが不変、同じrecorderで再試行成功することを検証。公開Recorder/Transaction/Checkの比較とpayload/seqの期待値を保持。 State snapshotは標準encoding/jsonでStateの別定義型をdeep copyし、全Go fieldのpointer/path/入れ子sliceを分離。拒否前後のstateはreflect.DeepEqualで比較し、本番Equal/MarshalJSONをoracleにしない。 本番trace.goに残っていた未使用ownedRecorder.recordWithを削除。 | [TestRecordersAgree](../implementations/go/src/machine_test.go#L204)<br>[cloneState](../implementations/go/src/machine_test.go#L21)<br>[ownedRecorder.recordAdmitted](../implementations/go/src/trace.go#L1000) |
| TA-366 | 既存reopen/truncate adapter保証を保持し、子プロセスのEngineが実FileJournalに稼働callをcommit後、returned行の途中を実ファイルに書いてSyncしたところで親がKillするprocess recoveryサブテストを追加。親で新規Engineを構築しResume、Lost先行記録・元call非再実行・prefix保持・正しいfailure/ErrLost・出力なし・replay一致を検証。 Windowsの異常終了後だけErrJournalLockedを5秒以内で再試行し、OSによる遅延解放を許容。通常Close後の即時解除、他OS/他errorの即時失敗は保持。 | [TestFileJournal](../implementations/go/src/recovery_test.go#L330)<br>[tornFileJournal](../implementations/go/src/recovery_test.go#L423)<br>[testFileJournalProcessRecovery](../implementations/go/src/recovery_test.go#L442)<br>[openJournalAfterProcessExit](../implementations/go/src/journal_process_test.go#L80) |
| TA-373 | reported regressionのASCII 1MiBケースだけ削除。at limit、limit plus one、escaped payloadとキャンセル/Check/Resume全assertは保持。 | [TestRuntimeParserRecordSize](../implementations/go/src/runtime_inputlimits_test.go#L46) |
| TA-374 | 到達不能なprivate recordedHeader深さguardをTestRecordedHeaderParserDepthへ分離し、validated次元を削除して63/64/65の3ケースに縮小。公開両constructorのtype depth上限+1拒否、到達可能最大型深さでのRun/Resume、両validatedのbyte上限±1保証を保持。 | [TestRecordedHeaderParserDepth](../implementations/go/src/runtime_inputlimits_test.go#L166)<br>[TestRuntimeParserHeaderLimits](../implementations/go/src/runtime_inputlimits_test.go#L180) |
| TA-377 | users task failureの3人分全payloadをexpectOutputSetで完全比較。通常suiteのlimit枝は上位保証を持つlimit barrierへ統合し、deterministic limit fixtureはrecovery/Lean conformance用に維持。 | [TestRuntimeScenarios](../implementations/go/src/runtime_test.go#L954) |
| TA-379 | 同一Engineの8実行をgenerator barrierで全件同時稼働させる。tenant.Name由来の固有user ID域を使い、各実行の全summary内容を比較してpayload混線を検出。 | [TestRuntimeConcurrentExecutions](../implementations/go/src/runtime_test.go#L1042) |
| TA-382 | Append失敗試験を保持し網羅性の過大コメントを修正。新TestRuntimeJournalSyncFailureでstart/call invoke/2回目fetchのSyncを失敗させ、Sync未完了中と失敗終了後に未durableなcall/pullが走らないことを確認。durable prefixだけからの未開始拒否/正常再開/Lost再開を検証。 | [TestRuntimeJournalFailure](../implementations/go/src/runtime_test.go#L1226)<br>[TestRuntimeJournalSyncFailure](../implementations/go/src/runtime_sync_test.go#L57) |
| TA-384 | プロセス全体のgoroutine総数比較を廃止。driver/call/停止中generatorに帰属するstackを各scenario終了後に直接探し、worker残存を検出。ケース単位で失敗stackを報告し、無関係なgoroutine終了による相殺を防ぐ。 | [runtimeWorkerStacks](../implementations/go/src/runtime_test.go#L1304)<br>[TestRuntimeNoLeaks](../implementations/go/src/runtime_test.go#L1323)<br>[TestRuntimeConcurrentExecutions](../implementations/go/src/runtime_test.go#L1042) |

### Go: trace / CLI

| ID | 対応内容 | 対応後の検査・実装 |
| --- | --- | --- |
| TA-259 | 両生成器の成功、末尾改行、headerとcommitを含む最低行数、生成結果の完全同一を明示assert。同一traceへのsummary/--state再生を両checker各1回へ整理し、それぞれexit0をassert。 | [TestConformanceCheck](../implementations/go/cmd/suimon/conformance_test.go#L507) |
| TA-260 | 生成成功/末尾改行/最低7行を必須化。全切断位置でexit0、破損・順序違反・二重commit・header欠如/重複でexit1と原因fragmentをassert。条件付き破損case実行を廃止。 | [TestConformanceTorn](../implementations/go/cmd/suimon/conformance_test.go#L538) |
| TA-262 | sourceにvalidated flagsを明示。正常fixtureはfalseだけ、39 mutationはfalse/true双方を維持。正常fixtureのtrueはConformanceCheckに集約。 | [TestConformanceUnchecked](../implementations/go/cmd/suimon/conformance_test.go#L773) |
| TA-265 | 旧identity decoderと正規化による診断分類helper群を除去。JSON構造とcanonical文字列のstrict比較は維持し、最初のraw行差分を返す診断へ簡素化。 | [TestConformanceGen](../implementations/go/cmd/suimon/conformance_test.go#L822)<br>[firstDifference](../implementations/go/cmd/suimon/conformance_test.go#L880) |
| TA-270 | exploreの先頭文字検査をJSON object・終端status4種・正の整数count・総和20・空stderrの検査へ置換。 | [TestCLI](../implementations/go/cmd/suimon/main_test.go#L82) |
| TA-395 | 同じ入力をfragmentで再確認していたrejected op/missing payloadの2呼出しを除去。後半exact error表と固有のpending/header/payloadケースを維持。 | [TestTraceRejections](../implementations/go/src/trace_test.go#L313) |
| TA-398 | TestRecordFieldOrderをTestRecordEncodingへ統合。独自のstart input+payload、invoke trigger有無、taskOutputを公開EncodeRecordの固定JSON表で検証。commit/空values/deliverの既存公開assertを維持。 | [TestRecordEncoding](../implementations/go/src/trace_test.go#L484) |
| TA-419 | TestWireTextのleading zero/fraction/empty/lone surrogateの弱い拒否4件を除去。全4入力のexact error/offset検査をTestWireParseErrorsに保持。 | [TestWireText](../implementations/go/src/wire_test.go#L55)<br>[TestWireParseErrors](../implementations/go/src/trace_test.go#L526) |

### UI kit

| ID | 対応内容 | 対応後の検査・実装 |
| --- | --- | --- |
| TA-431 | failureボタンのdanger classでstatus判定が空振りしないよう、failure=0のfailed statusとfailure=2のrunning statusのラベル・要素classを分離して検証。 | [renders the toolbar status and failure count](../ui-kit/tests/components.test.tsx#L91) |
| TA-449 | 定義timeoutを2^60、2^64直前、uint64 max、2^64、次の表現可能数の共通表へ置換。object/text両入口で数値丸めと境界を検証し、callMs/elementMs双方の超過を拒否確認。 | [bounds definition timeouts with JavaScript number rounding: %s](../ui-kit/tests/parse.test.ts#L46) |
| TA-454 | state timeoutにも同じ5境界ケースを適用し、transportでのJSON.parse後の丸めを検証。unchecked stateの0/null/省略は別テストで維持。 | [bounds state timeouts after JavaScript number rounding: %s](../ui-kit/tests/parse.test.ts#L108)<br>[allows zero and absent timeouts in unchecked runtime state](../ui-kit/tests/parse.test.ts#L120) |
| TA-468 | users-aの全op種・全出現についてrun/placement/task/connection/childRunの独立期待表と完全比較。users-bの実失敗3opとfailed/lost/taskInputFailed/transformFailed/unknown/cancelの参照解決ケースを追加。 | [relates every op of a completed run to a run and placement through the state](../ui-kit/tests/records.test.ts#L25)<br>[relates failure reports to their actual call, execution and connection owners](../ui-kit/tests/records.test.ts#L70) |
| TA-471 | index有無で同じ実装を比較するassertを撤去し、run順・depth・ordinalの固定期待、List memberのfixture別期待、raw配列の直接scanによるoverlay/producer比較に置換。lookup比較とsnapshot変更のcountsを維持。 | [matches fixture expectations and direct scans across immutable snapshots](../ui-kit/tests/runtime-index.test.ts#L9) |
| TA-490 | 仮のinvocation/result差し込みを、最小subworkflowを実際に実行したLean CLI生成fixtureへ置換。親callerへのproducer帰属、子run ownership、子のcall結果と親の返り値、invocationResults分離を検証。 | [attributes a sub-workflow call result to the invocation that called the workflow](../ui-kit/tests/status.test.ts#L94) |

### Playground: Go / UI / WASM

| ID | 対応内容 | 対応後の検査・実装 |
| --- | --- | --- |
| TA-275 | 全9 scenario caseで期待payload全体を比較。JSON objectをcanonical化して配列外側だけsortし、完了順の差を許容しつつ全field・重複を検査する。 | [TestScenarios](../implementations/go/example/scenarios_test.go#L164) |
| TA-277 | 3倍率のシナリオ一式の反復を、10msのjournal順序検査と600msのprocess直接検査1件へ分離・統合。順序、各itemのdelay下限、run単位の伝播、戻り値を維持。 | [TestProcessUsesRunUnit](../implementations/go/example/scenarios_test.go#L295)<br>[TestStreamAndBatchInvocationOrder](../implementations/go/example/scenarios_test.go#L320) |
| TA-291 | 本物Engineのcallbackをchannelで保留し、SSE初回eventを受信してから解除。5秒request deadlineとscanner.Errを加え、複数event・連続offset・最終Done・pollとの全記録一致を維持。 | [TestServerEvents](../implementations/go/example/server_test.go#L176) |
| TA-301 | parseReport正常系を全体toEqualへ変更しstatus/outputs/endpointsとoptional taskを持つ失敗を検証。既存のtaskなしtimeout失敗と異常endpoints拒否も維持。 | [parses a report](../implementations/go/example/ui/tests/api.test.ts#L102) |
| TA-305 | SSRのscenario option隣接HTML完全一致をvalue/selected/textの意味的比較へ変更し、可視ラベルが各scenario.titleと一致することを維持。説明は渡したfixtureのdescriptionとの接続のみ確認。初期画面保証の名称へ変更。実DOMのscenario切替、workbench remount後focus、scenarioごとの編集input保持を実WASM browserで追加。 | [initially shows the scenario choice in the header and its workflow and input in the left pane](../implementations/go/example/ui/tests/playground.test.tsx#L26)<br>[changes scenarios, keeps focus after the workbench remounts, and preserves each input](../implementations/go/example/ui/browser/playground.browser.ts#L25) |
| TA-306 | unit optionの隣接HTMLと説明文全文の固定を削り、200/600/1000の値・各可視ラベルの200ms/600ms/1000ms表示・600選択・timeline伝達を維持。実DOMで1000を選択→input編集→Go run body送信、実行中unit/input/Run disable、成功report、復帰まで検証。実worker/Go/polling/cancelも同suiteで到達。 | [initially offers the run units in the left pane and uses 600ms for both timeline lanes](../implementations/go/example/ui/tests/playground.test.tsx#L43)<br>[sends the chosen unit and input to Go, disables an active run, and polls through its report](../implementations/go/example/ui/browser/playground.browser.ts#L45)<br>[cancels the active Go run and finishes polling its cancelled report](../implementations/go/example/ui/browser/playground.browser.ts#L81) |
| TA-311 | Timelineのmarker個数/labelに加え、共通152ms軸のmarker left・bar left/widthとproducer内50%/100%のmark leftをassert。leftを0固定やbarの幅誤計算で失敗する。 | [marks the first downstream start in each lane, and shows a lane that has not run](../implementations/go/example/ui/tests/timeline.test.tsx#L17) |

## 実行結果

macOS arm64、Go 1.27.3、Lean 4.34.0、pnpm 12.15.0、Node 26.12.1で確認した。

| 検証 | 結果 |
| --- | --- |
| `bin/test all` | Lean実行テスト・proof build・schema suite通過 |
| `Test/schema_oracle.py`（専用venv） | 外部validatorとの341ケース一致。`bin/test schema`にも接続 |
| `bin/test-go all` | 全package通常テスト、src/example race、go vet、相互互換、全benchmarkの1回実行が通過 |
| snapshot修正後の影響4テスト | MachineAgreesWithStep・MachineRejections・RecordersAgree・QuotaAdmissionLeavesMachineUnchangedが通常／raceとも通過 |
| process helper修正後 | FileJournal／FileJournalLockがrace付きで通過 |
| `pnpm build` / `pnpm test` | build/typecheck通過、Vitest 17ファイル165ケース通過。可視ラベル修正後もexample UI 23件を再確認 |
| UI kit `test:browser` | Chromiumで5ケース通過 |
| Playground `test:browser` | 実Go WASMを使うChromiumで3ケース通過 |
| Playground `test:wasm` | Nodeで実Go WASMの3ケース通過 |
| Windows向けGo test binary | cross-compile通過。Windowsでの実行は未実施 |
| script／workflow／差分 | Bash構文、workflow YAML構文、`git diff --check`通過 |

snapshotの最終修正後は、変更した共通helperを使う全4テストとprocess関連を再実行した。processの単位伝播検査を補強した後もexample package全体をrace付きで再確認した。依存の`use client` directiveに関するbundler警告は残るが、build/typecheck/testの失敗ではない。

### 破壊を注入して失敗を確認した検査

一時overlayまたは隔離コピーで実施し、変異した本番コードは残していない。CSVの`SUIMON_TEST_OVERLAY`・`SUIMON_TEST_COPY`は記載した故障を注入した一時ファイル／コピー、`SUIMON_TEST_OUTPUT`は生成binaryの出力先を表す。

| 対象 | 注入した変更 | 結果 |
| --- | --- | --- |
| TA-393 | no-op filterのstate同値判定を除去 | 余分なCancel候補を検出して失敗 |
| TA-353 | Resumeの保持payload積算を除去 | 不正なsettleと保持量超過を検出して失敗 |
| TA-360 / TA-361 | 拒否時にRun.Inputをポインタ経由で書き換える | state不変性の検査が失敗 |
| TA-382 | Sync前に副作用を公開する | invoke/fetchの両ケースで失敗 |
| TA-270 | explore出力を空objectへ置換 | 集計件数の検査が失敗 |
| TA-259 / TA-260 / TA-265 | Go生成をexit 1・空stdoutへ置換、または生成headerのvalidatedを反転 | 生成成功の前提検査、またはraw差分を伴う互換性検査が失敗（個別条件はCSV） |
| TA-275 | 出力個数を保って値をWRONGへ置換 | stream/batchのpayload比較が失敗 |
| TA-277 | processからrun contextを除去して既定250ms単位で待機 | 600ms単位での処理時間下限の検査が失敗 |
| TA-182 | Leanのkind導出最適化を無効化 | heartbeat増加率の検査が失敗 |
| TA-032 | schema検査器のminLength判定を無効化 | 外部oracleと不一致になり失敗 |

## 継続して実行する経路

[Go標準script](../bin/test-go#L24) はsrcだけでなくexampleにもrace検査を行い、benchmarkを`-benchtime=1x`で実行する。大サイズfixtureの準備が資源上限で失敗する状態を、通常のCIで見逃さない。

[UI CI](../.github/workflows/ci.yml#L103) はUI kitのブラウザ5件を実行し、[playground CI](../.github/workflows/pages.yml#L57) はWASM smokeに続いて実ブラウザ3件を実行する。既存の通常テストやWASM smokeを置き換えず追加した。

[schema script](../bin/test#L37) は`.lake/schema-venv`に独立したPython環境を作り、[固定した依存](../Test/schema-requirements.txt)でoracleを実行する。初回にはPython 3と依存取得が必要。`PYTHON`で環境作成に使うinterpreterを選べる。

長時間fuzz、安定した性能分布の測定、電源断、Windows実機の動作確認は今回の実行結果に含めない。今回のbenchmark成功は全サイズで計測が成立することの確認であり、実時間性能の上限保証ではない。
