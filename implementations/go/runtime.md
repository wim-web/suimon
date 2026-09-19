# Go でワークフローを実行する

`Workflow` にグラフ、処理関数、入力を設定して `Run(ctx)` を呼びます。依存関係の解決、stream の配送、並列数の制御、再試行、終了判定は `src` の実行器が担当します。

```go
func main() {
    graph := createGraph()
    printResult(graph.Run(context.Background()))
}
```

この形で動く例が [example/](example/) にあります。[graph.go](example/graph.go) が組み立て、[nodes.go](example/nodes.go) が利用者の処理です。実行順や状態遷移を example に書く必要はありません。

## 処理関数と値

パッケージは `suimon "github.com/wim-web/suimon/implementations/go/src"` として import します。`Workflow.Graph` は既存の `Graph` 構造体でも、`ParseGraph` で読んだ JSON でも指定できます。

`Workflow.Bindings` は処理が必要なノードの定義パスと関数を対応付けます。たとえば `Path{"each", "work"}` は ForEach の body 内の `work` です。各アイテムや Loop の反復には同じ関数を使い、実際の呼び出しは `Task.ID` / `Task.Path` で区別します。`Task.Definition` は登録時の定義パスです。

```go
func uppercase(ctx context.Context, task *suimon.Task) (suimon.Values, error) {
    var input string
    if err := task.DecodeInput("in", &input); err != nil {
        return nil, err
    }
    return suimon.Values{"out": strings.ToUpper(input)}, nil
}
```

返す `Values` のキーは plain 出力ポート名です。すべての plain 出力を一度に返し、stream 出力は `Emit` します。値は JSON に変換できる必要があります。入力と出力はコピーされ、処理関数からモデルの状態を直接変更することはありません。

```go
func emit(ctx context.Context, task *suimon.Task) (suimon.Values, error) {
    for i, value := range []string{"one", "two", "three"} {
        if err := task.Emit("out", strconv.Itoa(i), value); err != nil {
            return nil, err
        }
    }
    return suimon.Values{}, nil
}
```

`Emit` はアイテムの確定まで待ちます。確定すると下流を起動でき、producer の関数終了を待ちません。正常 return が stream の EOS を確定します。`Emit` 自体は下流の処理完了までは待ちません。

`Emit` の `key` は論理的な出力 occurrence を識別します。同じ呼び出し・ポート・key の再送は重複を作らず、異なる値での再送は拒否します。再試行でも同じ key を使ってください。確定済みの stream は試行をまたいで残るため、再試行で確定済みの先頭部分を再送する必要はありません。異なる key に同じ値を出した場合は別アイテムです。

最初の入力は `Workflow.Inputs` の `ValueInput` で与えます。各 `InputItem` に安定した ID と値を設定し、同じ ID は同じ値に対応させます。入力 stream は start 時に与えた一覧で閉じます。実行中に増えるデータは、上の producer のように leaf から出します。

`RunResult.Output(node, port)` でグラフの出口の `DataItem` を取得し、`Decode(&value)` で読みます。モデルの stream は到着順ではなくアイテムの多重集合を扱います。順序が必要なアプリケーションでは、値に順序キーを含めてください。

## 全ノード種別

| NodeKind | 実行時の動作 | 登録する関数 |
| --- | --- | --- |
| `leaf` | plain 入力が揃うと claim し、処理を起動。yield、complete、fail を状態に反映 | `Leaf(context.Context, *Task) (Values, error)` |
| `waitAll` | 全 plain 入力が揃ってから、ポート名をキーとする JSON object を出力 | なし |
| `branch` | 入力を関数が選んだ arm に流し、選ばれなかった出力を閉じる | `Branch(context.Context, DecisionTask) (string, error)` |
| `coalesce` | 排他的な入力経路の結果を合流。グラフ検証が排他性を検査 | なし |
| `loop` | body を実行し、結果から終了判定。継続時は結果を次の反復へ渡す | `Loop(context.Context, DecisionTask) (bool, error)`。`true` が終了 |
| `subworkflow` | 入力を子フレームへ渡し、body の完了と drain を待って結果を返す | body 内の各ノードに登録 |
| `forEach` | stream の各アイテムで body を起動。全 body 完了と上流 EOS 後に出力を閉じる | body 内の各ノードに登録 |
| `collect` | stream の全件到着・EOS を待ち、アイテム ID でソートした JSON array を出力 | なし |
| `filter` | 到着した各アイテムを判定し、`true` のアイテムを流す | `Filter(context.Context, DecisionTask) (bool, error)` |
| `merge` | 各入力 stream の到着アイテムを合流。別入力上の同一 ID も別 occurrence として保持 | なし |

判定関数の入力値は `DecisionTask.Item.Decode` で読みます。Loop では `Iteration` も取得できます。不要な Binding、存在しない定義パス、関数の種類の間違い、必須関数の欠落は実行前に拒否します。

## スケジューリングと全操作

処理関数は goroutine で動きます。状態更新は単一の制御ループで `RecordTransaction` / `Step` を通し、各操作について不変条件を検査します。グラフのノード記述順に依存せず、実行可能な制御操作と ready な処理を巡回して選びます。

leaf の `Concurrency` は同じ定義パスの running attempt 数にかかり、ForEach の body をまたいで共有します。失効した attempt の権限は取り消します。`RunOptions.Workers` は処理・判定関数の同時呼び出し数の追加上限です。既定の `0` は追加上限なしです。失効した処理が終了するまでは、その呼び出しもこの上限に数えます。

| Op | 実行器での契機 |
| --- | --- |
| `start` | 入力の確定 |
| `activate` | leaf / Loop / Sub の依存が解決 |
| `spawn` | ForEach へのアイテム到着 |
| `claim` | ready な leaf に実行枠が空く |
| `renew` | 自動更新、または `Task.Renew()` |
| `expireLease` | lease の期限到来 |
| `promoteRetry` | 再試行の待機期限到来 |
| `emit` | `Task.Emit` |
| `complete` | leaf の正常 return |
| `fail` | leaf のエラー・panic・不正な出力 |
| `fireWaitAll`, `fireCollect` | それぞれの全入力条件が成立 |
| `fireBranch`, `fireFilter` | 判定関数の結果 |
| `fireCoalesce`, `fireMerge` | 合流可能なアイテムの到着 |
| `propagateEos` | stream の終了条件が成立 |
| `finishSubworkflow` | 子フレームの完了・drain |
| `loopIterate` | body 完了後の Loop 判定 |
| `skip` | 閉じた空の入力などにより実行不要と確定 |
| `idle` | 動作を進められない時点の成功・blocked 判定 |
| `cancel` | 実行 context のキャンセル、または `Execution.Cancel` |
| `manualRetry` | `Execution.ManualRetry` |

`Execution.Apply(ctx, op, payloads)` でも全23操作を渡せます。外部から指定した操作も同じ検査・保存を通り、`payloads` はアイテム ID をキーとします。失効 credentials は拒否し、確定済み complete の同一内容の再送や終端での操作吸収もモデルの規則に従います。

## 再試行・停止・キャンセル

leaf が `&suimon.TaskError{Code: "TEMPORARY", Retryable: true}` を返すと、ノードの `RetryPolicy` に従って待機・再試行します。通常の error は `HANDLER_FAILED`、panic は `HANDLER_PANIC` として非再試行の失敗を記録します。上限到達や非再試行の失敗は、モデルに従って `blocked` に至り、`Run` / `Wait` は `ErrBlocked` を返します。

手動再開や実行中の操作が必要なら `Start` を使います。

```go
execution, err := workflow.Start(ctx)
if err != nil {
    return err
}
defer execution.Stop()

result, err := execution.Wait(ctx)
// blocked の原因を確認した後、対象 instance を指定して再開できる。
if errors.Is(err, suimon.ErrBlocked) {
    if err := execution.ManualRetry(ctx, instanceID); err != nil {
        return err
    }
    result, err = execution.Wait(ctx)
}
```

`ManualRetry` は対象の試行回数、または Loop の反復上限を拡張します。成功済みの下流処理や過去の反復を最初からやり直しません。`Start` の実行器は blocked / 終端でも操作を受け付け、`Stop` で終了します。`Run` は `Wait` 後の `Stop` まで行う簡略 API です。

`Execution.Cancel` と実行 context のキャンセルはモデルに `cancel` を記録し、動作中の関数の context をキャンセルします。`Execution.Stop` は実行器を停止して context をキャンセルしますが、モデルを終端にせず、保存した状態からの復元を可能にします。`Wait` にだけ渡した context の終了は待機を止めるだけです。途中状態は `Result()`、特定条件までの待機は `WaitFor(ctx, predicate)` で取得できます。

branch / filter / loop の判定エラーは実行器のエラーとして停止します。モデルにはこれらの判定自体の retry 操作がないため、最後の確定状態から、関数や外部条件を修正して復元します。

時計は自然数の秒です。既定では起動時の Unix 時刻に単調な経過秒を加え、保存済みの時刻より戻さずに使います。`Now` と `PollInterval` で差し替えられます。lease は期限前に延長できる場合に自動更新し、`DisableAutoRenew` で無効化できます。整数秒で `LeaseSeconds: 1` を指定すると期限前に延長できる時刻がないため、長い処理には余裕のある期限を指定してください。

処理関数は context の終了に対応してください。lease 失効やキャンセルは古い結果の確定を防ぎますが、任意の Go コードを強制終了する仕組みではありません。外部サービスの副作用を exactly-once にするには、アプリケーション側でも論理 ID による冪等化が必要です。これは Lean の[環境に関する前提](../../Suimon/Axioms.lean)と同じ境界です。

## 保存と復元

`RunOptions.Commit` を指定すると、新しい状態・イベント・値を公開する前に、完全な `Snapshot` を渡します。保存処理は snapshot 全体を原子的に確定してから `nil` を返す契約です。エラー時は `CommitError` で停止し、提案した状態と値をメモリ上で公開しません。保存結果が不確かなエラーの場合は、保存先を読み直して復元します。

```go
store := suimon.SnapshotFile{Path: "checkpoint.json"}
workflow.Options.Commit = store.Save
result, err := workflow.Run(ctx)
```

プロセス再起動後は次のように再開します。

```go
snapshot, err := store.Load(ctx)
if err != nil {
    return err
}
result, err := workflow.Resume(ctx, snapshot)
```

`Restore(ctx, snapshot)` は `Resume` の実行ハンドル版です。復元時はグラフの一致、履歴、必要な値を検査し、最後の commit まで復元します。検査を通る未コミット末尾は捨てます。不正なイベントや必要な値の欠落は拒否します。成功済み処理は再実行せず、中断された running attempt は lease 失効と retry 規則に従って再開します。

`SnapshotFile` は同じディレクトリの一時ファイルに書き、sync・rename・ディレクトリの sync で置き換えます。親ディレクトリをあらかじめ作り、同じパスの writer は1つにしてください。標準の実行器は1プロセス内で動きます。snapshot には全履歴と値を保持するため、stream のサイズに応じたメモリ削減や履歴の圧縮を行う実装ではありません。

## Lean との対応と検証

`ScopedOracle` / `OracleConforms` / `ChannelBags` / `SucceededDrained` は [Execution.lean](../../Suimon/Execution.lean) の実行可能な条件に対応します。任意の関数の決定性を Go が証明することはありません。同一入力・論理パスに同じ出力と判定を返す処理を使ってください。

`RunOptions.Oracle` を設定すると、指定された oracle と emit / complete / 分岐 / filter / Loop の判定を照合します。stream の complete では、全試行を通して確定したアイテムの多重集合が予定された全件と一致することも検査します。これにより予定した stream の途中打ち切りを拒否できます。oracle は ID を扱い、アプリケーションの値そのものは扱いません。必要な oracle 関数を副作用のない決定的な関数として登録してください。

`bin/test-go` は既存のモデル差分・CLI 比較に加え、次を検査します。

| 対象 | 検査 |
| --- | --- |
| 全10ノード種別・全23操作 | Lean のコンストラクタ一覧を読み、実処理が作った履歴で全種類を通ることを確認 |
| 全例グラフ | ノード定義順を逆にして実行し、成功・drain を確認 |
| 実処理の履歴 | Go と Lean の checker で状態、channel の多重集合、drain 条件を比較 |
| stream と並行実行 | 上流終了前の下流起動、全件待機、共有並列上限、速い producer による下流の実行遅延を検査 |
| 実行順の変化 | worker 数・アイテム到着順・定義順を変え、結果を比較 |
| 失敗と復旧 | retry 待機、renew、失効結果の拒否、手動再開、キャンセル、処理中の停止と復元 |
| 保存と境界 | 未確定状態の非公開、破損の拒否、未コミット末尾、成功済み処理の保持、complete の再送 |
| oracle | 条件を Lean と差分比較し、不完全な stream の成功を拒否 |
| メモリ上の並行処理 | `go test -race` |

これは Go 実装の比較・実行テストです。Lean の定理が Go の実行器やストレージへ自動的に移るわけではありません。形式的な保証の前提は[保証の読み方](../../docs/implementation.md)を参照してください。
