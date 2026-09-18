# suimon 設計書: ストリーム部品を持つワークフロー制御の Lean 仕様

2026-09-17。suimon は、ノードを線でつないで組むワークフローの**制御部分**を Lean 4 で仕様化・証明するプロジェクトである。逐次・ForEach・Concurrency（並列にして全部終わったら次へ）・Sub といった一般のワークフローライブラリにある部品に加えて、一般には無い **yield**（ノードが実行中にアイテムを1件ずつ出し、下流が1件ごとに動く）と **AllWait**（yield された全件の処理完了を待つ合流点）を持ち、両方を同じグラフの中で混ぜて使えることを仕様の中心に置く。

**本体は Lean である。** 動くライブラリは Lean だけからは出てこない。どの言語で実装するかは別の判断であり（§11 M5）、この文書は言語を特定しない。実装が満たすべき条件だけを §9 に置く。

**参照実装**: `ai-ultra-research`（`/Users/wim/program/ghq/github.com/wim-web/ai-ultra-research`）の `src/research_state/pipeline/` は、lease・再試行・途中再開の意味を確認するための**読み物**として使う。読み取り専用で、編集しない。あちらは graph 方式の永続 scheduler を持つが、suimon はそれを移植しない。

**この文書より前に作られたファイルについて**: このリポジトリには、前の版の設計書（graph 方式の移植計画、および入れ子方式の計画）に基づいて作られた `formal/suimon/Suimon/*.lean` と `python/suimon/*.py` がある。本文書の §4 の型とは一致しない。M1 着手時に、Lake プロジェクトを §10 の配置（リポジトリ root）へ移し、§4 の型に合わせて書き直す（`Graph.lean` のポート・線の骨格は流用できる可能性がある。`Join` や `WorkState.superseded` など参照実装由来の型は捨てる）。`formal/` ディレクトリは移設後に削除する。`python/` は本文書の範囲外で、実装言語が決まるまで触らない。

## 1. 目的と非目的

### 目的

1. ノードと線で組むワークフローの制御の意味論を Lean 4 の定義として持つ。
2. 普通の線（前が終わったら値を渡す）とストリームの線（アイテムを逐次流し、終端で締める）を1つの遷移系で定義し、それぞれの性質を証明する。
3. 途中で落ちても再開できること（永続化、lease、再試行）を仕様に含め、再開後の二重実行が無いことを証明する。
4. 仕様から実行可能な検査器と探索器を作り、将来どの言語で実装しても適合を判定できるようにする。

### 非目的

- ノードの中身（利用者が書く処理）の仕様化。不透明な関数として扱う。
- Branch や Loop の条件式の中身の証明。結果だけを受け取る。
- liveness の証明。必要な性質は safety の形に落とす（§5 T12）。
- 実装言語の選定、実装そのもの、UI。
- `ai-ultra-research` の編集。

## 2. 用語

| 用語 | 意味 |
| --- | --- |
| ノード | グラフの頂点。利用者が書く **leaf** と、suimon が提供する **制御ノード** の2種類 |
| ポート | ノードの入口・出口。名前を持つ。**plain** か **stream** のどちらかの種別を持つ |
| 線 | 出力ポートから入力ポートへの有向辺。両端のポート種別は一致する |
| アイテム | 線の上を流れる値1個。識別子を持つ |
| EOS | 線の終端信号。「この線にはもうアイテムが来ない」 |
| plain の線 | アイテム1個の後に EOS が来る線。「前が終わったら値を渡す」を表す |
| stream の線 | 0個以上のアイテムの後に EOS が来る線 |
| インスタンス | ノードが1回動いた分。yield された記事1件に対する「取得 → 評価」の1回分、のような単位。Lean モデル内の用語で、§3 では使わない |
| attempt | leaf インスタンスの1回の実行試行。lease を持つ |
| execution | ワークフロー1回分の実行全体 |

内部的には plain は「アイテム1個 + EOS」の stream なので、遷移系は1本で書く。ただし API と文書では plain と stream を別物として見せ、plain の性質（下流は上流の完了後にしか動かない）を独立の定理として持つ。

## 3. 提供する部品

利用者は自分のノードとこれらを線でつなぐ。任意の形（菱形、N 字）を書ける。この節は利用者向けの語彙であり、§4 のノードと配線への糖衣を含む。各部品の形式モデルへの対応は末尾の表に従う。

### 普通の部品（一般のワークフローライブラリにもあるもの）

| 部品 | 意味 |
| --- | --- |
| 逐次（既定） | 線でつないだ順に1つずつ動く。部品ではなく既定の動き |
| ForEach | 入ってきたアイテムごとに、中に入れた処理を起こす。処理は重なって動ける。同時数は各 leaf の concurrency で制限し、ForEach 自体に既定の逐次制約は設けない |
| Concurrency | 複数の経路を並列に動かし、**全部終わってから**次へ進む配線の表現。独立したノード種別ではない |
| Sub | 複数のノードをまとめて1つのノードとして扱う |
| Branch | 条件で進む先を1つ選ぶ。選ばれなかった先には「来ない」印だけが流れる |
| Coalesce | 単一の Branch の排他的な arm を合流させる。選択された arm の値1個を通し、非選択側は「来ない」印で閉じる。独立した値を競争させる first-wins ではない。各入口は同じ Branch の異なる arm に由来し、arm と入口を1対1に対応させる。Branch を body（Loop / ForEach / Sub の中）に置くときは必ずこれで合流させる |
| Loop | 中の処理を、終了条件が真になるか上限回数に達するまで繰り返す。上限到達は失敗 |

### suimon が足す部品（一般には無いもの）

| 部品 | 意味 |
| --- | --- |
| **yield できるノード** | 実行中にアイテムを1件ずつ出せる。ノードが終わるのを待たず、下流は yield された1件ごとに動く。yield 元が終わったとき、その線に「もう来ない」印（EOS）が付く |
| **AllWait** | yield された全件の処理が終わるまで待つ合流点。「全件」は yield 元が終わるまで確定しないので、後から届く分も待つ。全部揃ったら1回だけ次へ進む |
| **Merge** | 複数の yield 元を1本にまとめる。全部の yield 元が終わったら EOS |
| **Filter** | 流れてくるアイテムのうち条件が真のものだけ通す |
| **ノード種別ごとの全体上限** | あるノードは、どの経路で動いていても同時に N 個まで、という制限。取得は 8、評価は 2、のように段ごとに分けられる |

### なぜ yield と AllWait が要るか

Concurrency と Sub だけでも、記事ごとの「取得 → 評価」を並列にし、全部終わってから Plan へ進む、は書ける。yield が無いと書けないのは、**並列処理の中で次の段の材料が作られる**場合である。Scan が記事を見つけながら進むとき、yield が無ければ Scan が終わるまで1件目の取得も始まらない。Scan が数秒なら差は無いが、何分もかけて出し続けるノードでは差が大きい。段ごとの同時実行数の違いも、yield で段を分けておかないと付けられない。

### Lean モデル（§4）との対応

§4 の型は上の部品を次のように表す。§3 の語彙を変えても §4 は変えない。

| §3 の部品 | §4 での表現 |
| --- | --- |
| 逐次 | plain の線（アイテム1個 + EOS） |
| ForEach | `forEach`（入力は stream。plain のリスト値を回す場合の昇格は §12） |
| Concurrency | 1つの出力から複数の線を引き、出口を `waitAll` で合流する |
| Sub | `subworkflow`（定義時に平坦化してもよい。implementation.md 参照） |
| Branch / Coalesce / Loop | `branch` / `coalesce` / `loop` |
| yield できるノード | stream 出力ポートを持つ `leaf`（emit 型） |
| AllWait | `collect`（全入力の EOS と全処理の完了で1回発火） |
| Merge / Filter | `merge` / `filter` |
| ノード種別ごとの全体上限 | `leaf` の `concurrency` 属性 |

### ノードに付く属性

| 属性 | 意味 |
| --- | --- |
| retry | 最大試行回数と再試行間隔。失敗時は上限までやり直す |
| lease | 1回の実行が保持できる時間。切れたら別の worker が引き継げる |
| concurrency | 上の「ノード種別ごとの全体上限」 |

## 4. 形式モデル（Lean 4）

Lake プロジェクトはリポジトリ root に置く。`Suimon/` は Lean のモジュール root（Lake の慣習で大文字始まり）。

```
suimon/                 # リポジトリ root = Lake プロジェクト root
  lean-toolchain
  lakefile.lean
  Suimon/
    Graph.lean          # §4.1
    State.lean          # §4.2
    Oracle.lean         # §4.3
    Step.lean           # §4.4 遷移関係（Prop）と実行可能版（Except）
    Axioms.lean         # §4.5
    Invariants.lean     # §5 の不変条件
    Theorems/*.lean     # §5 の定理
    Explore.lean        # §6
    Trace/Event.lean    # §7 イベント型と JSON
    Trace/Check.lean    # §7 再生と判定
  Main.lean             # CLI: check / explore / gen
  Test/                 # 例グラフと回帰
```

### 4.1 Graph

```lean
namespace Suimon

abbrev NodeId := String
abbrev PortName := String

inductive PortKind | plain | stream
deriving DecidableEq, Repr

structure Port where
  name : PortName
  kind : PortKind
deriving DecidableEq, Repr

structure PortRef where
  node : NodeId
  port : PortName
deriving DecidableEq, Repr

structure RetryPolicy where
  maxAttempts : Nat
  leaseSeconds : Nat
  retrySeconds : Nat

mutual
inductive NodeKind
  | leaf (retry : RetryPolicy) (concurrency : Nat)   -- 利用者の処理。emit 型かは出力ポートの kind で決まる
  | waitAll
  | branch (arms : List PortName)
  | loop (body : Graph) (maxIterations : Nat)
  | subworkflow (body : Graph)
  | forEach (body : Graph)
  | collect
  | filter
  | merge
  | coalesce

structure Node where
  id : NodeId
  kind : NodeKind
  inputs : List Port
  outputs : List Port

structure Edge where
  src : PortRef
  dst : PortRef

structure Graph where
  nodes : List Node
  edges : List Edge
  entries : List PortRef   -- execution 開始時に入力を受ける入力ポート
  exits : List PortRef     -- execution の結果とみなす出力ポート
end

end Suimon
```

`Graph.WellFormed`: ノード ID は一意。線の両端は存在するポートで、種別が一致する（plain → stream の昇格は §12 の決定に従う。stream → plain は不可、Collect を挟む）。入力ポートに入る線は高々1本（stream の合流は Merge を使う）。部分グラフ（loop / subworkflow / forEach の body）も WellFormed。グラフに cycle は無い（繰り返しは Loop 部品で表す）。Coalesce は root / body ともに、全入力が単一の Branch の互いに異なる arm の選択を必要とし、各 arm と1対1で対応することを要求する。共有の plain 入力を読む処理や、各 arm 内で再合流する入れ子の Branch は許す。独立した leaf の合流、同じ arm の二重接続、別々の Branch の混在は拒否する。

### 4.2 State

```lean
abbrev ItemId := String
abbrev InstanceId := String
abbrev AttemptId := String
abbrev LeaseToken := String
abbrev Time := Nat
abbrev Path := List InstanceId

inductive Token | item (id : ItemId) | eos
deriving DecidableEq, Repr

structure Channel where          -- 線1本の中身
  id : String
  edge : Edge
  path : Path
  kind : PortKind
  entry : Bool
  exit : Bool
  placed : List Token            -- 置かれた順
  consumed : Nat                 -- 先頭から消費済みの個数
deriving Repr

inductive InstanceStatus
  | waitingInputs | ready | running | retryWait | succeeded | failed | cancelled
deriving DecidableEq, Repr

structure Lease where
  attempt : AttemptId
  token : LeaseToken
  until_ : Time
deriving Repr

structure Instance where
  id : InstanceId
  node : NodeId
  path : Path                    -- 親 ID と iteration を符号化した scope ID の列
  trigger : Option ItemId        -- forEach の場合、起動元のアイテム
  status : InstanceStatus
  attemptCount : Nat
  lease : Option Lease
  retryAt : Option Time
  iteration : Nat                -- loop の現在回数
  extraAttempts : Nat
  extraIterations : Nat
  inputs : List (PortName × ItemId)
deriving Repr

inductive AttemptStatus | running | succeeded | failed | abandoned | cancelled
deriving DecidableEq, Repr

structure Attempt where
  id : AttemptId
  «instance» : InstanceId
  no : Nat
  status : AttemptStatus
  token : LeaseToken
  worker : String
deriving Repr

inductive ExecStatus | running | blocked | succeeded | failed | cancelled
deriving DecidableEq, Repr

structure State where
  status : ExecStatus
  channels : List Channel
  instances : List Instance
  attempts : List Attempt
  frames : List Frame
  consumed : List Consumption
  receipts : List Receipt
  decisions : List Decision
  now : Time
  started : Bool
  reason : Option String
```

`Frame` は `path`, `graph`, 静的なノード定義の経路 `definition`, 親の `owner`, `closed` を持つ。`Consumption` は `channel`, `index`, `item`, `byInstance`、`Receipt` は `instance`, `attempt`, `token`, `outputs`、`Decision` は oracle の `key`, `value` を持つ。正確な型・既定値・JSON 導出は `Suimon/State.lean` を原本とする。

`ExecStatus.failed` は現在の操作からは設定しない予約済みの終端状態。処理失敗は instance.failed と execution.blocked で表し、manualRetry の余地を残す。`reason` は診断文字列であり、その値だけから「どの操作で blocked になったか」を判定しない。外部 facts は §12 D9 の公開射影を使う。`extraIterations` などの内部フィールドは command の replay で復元し、追加だけで外部形式や fixture を変更しない。

### 4.3 不透明関数（oracle）

利用者や条件式が決める部分。Lean は結果だけを遷移の引数として受け取る。

| oracle | 誰が決めるか | Lean での型 |
| --- | --- | --- |
| leaf の出力 | 利用者の処理 | 各出力ポートに置くアイテム ID の列 |
| Branch の選択 | 条件式 | 選んだ出力ポート名 |
| Loop の終了判定 | 条件式 | `Bool` |
| Filter の判定 | 条件式 | `Bool` |
| アイテムの識別子 | 実装 | `ItemId`。同じ入力から同じ処理で作られたアイテムは同じ ID（A4） |

前提 `Oracle.Deterministic`（A4）: 同じ入力アイテムに対して同じ結果を返す。ストリームの到着順に依存しない。決定性（T9）はこの前提の下で証明する。

### 4.4 Step

遷移は「1 トランザクション = 原始 Step の列」として扱い、不変条件はトランザクション境界で述べる。実行可能な `step : State → Op → Except Reject State` を唯一の遷移定義とし、性質はこの関数について直接証明する。独立した関係 `Step` は置かない（§12 D10）。

| Op | 前提 | 効果 |
| --- | --- | --- |
| `start inputs` | status = running、インスタンス無し | entries の各線に入力アイテム + EOS を置く |
| `activate n` | n の全 plain 入力線に未消費のアイテムがあり、n のインスタンスが無い | インスタンスを ready で作り、入力アイテムを消費 |
| `spawn n itemId` | n は forEach。入力線の先頭に未消費アイテム | body のインスタンスをそのアイテムで作り、消費 |
| `claim inst worker now` | inst.ready、期限切れ lease と期限到来 retry が無い | attempt を作り running、lease を付与 |
| `renew inst now` | `ValidLease` | lease の期限を延ばす |
| `expireLease inst now` | inst.running ∧ lease.until ≤ now | attempt → abandoned。試行回数が上限なら inst → failed、status → blocked。そうでなければ retryWait |
| `promoteRetry inst now` | inst.retryWait ∧ retryAt ≤ now | inst → ready |
| `emit inst port itemId` | `ValidLease` ∧ port は inst のノードの stream 出力 | その出力線にアイテムを置く |
| `complete inst outputs` | `ValidLease`（または同じ attempt の冪等な再送） | plain 出力線にアイテムを置き、全出力線に EOS。inst → succeeded。lease 解放 |
| `fail inst code retryable` | `ValidLease` | attempt → failed。retryable ∧ 回数未満なら retryWait、そうでなければ failed かつ status → blocked |
| `fireWaitAll n` | n の全入力線に未消費アイテム | record を1個出力線に置き、EOS。1回だけ |
| `fireBranch n arm` | n の入力線に未消費アイテム | 選ばれた arm の線にアイテム、全 arm に EOS。選ばれなかった arm の先の plain ノードは skip で cancelled にして終端させる |
| `fireCoalesce n edge itemId` | n は未発火。選択した plain 入力線が EOS で閉じ、上流が succeeded（または entry）で、先頭に指定の未消費アイテムがある | そのアイテムを出力線に置き、EOS。1回だけ。他の入力線は EOS または skip で閉じていることを body 回収時に要求する |
| `fireCollect n` | n の入力線に EOS が置かれ、全アイテム未処理 | アイテム列を1個のアイテムとして出力線に置き、EOS |
| `fireFilter n itemId keep` | 入力線の先頭に未消費アイテム | keep なら出力線に置く。消費 |
| `fireMerge n edge itemId` | いずれかの入力線の先頭に未消費アイテム | 出力線に置く。消費 |
| `propagateEos n` | n の全入力線に EOS ∧ n の全インスタンス完了 | n の全出力線に EOS（stream ノード） |
| `loopIterate inst done` | inst は loop、body 完了 | done なら出力へ。iteration = max で未完なら inst → failed、status → blocked(LOOP_LIMIT)。`manualRetry` で回数上限を増やして再開できる |
| `idle` | status ∈ {running, blocked} | `hasWork` が偽なら、全ノードと exits が終端済みなら succeeded、その他は blocked。既存の失敗理由は保持し、新たな依存停止は DEPENDENCIES_UNRESOLVED とする。`hasWork` が意味する作業は「idle / cancel / manualRetry 以外の、状態を変える受理操作」。冪等な再送は含めない。実行可能版は候補列挙で判定し、全 Op に対する列挙の完全性は未決6で扱う |
| `cancel` | status ∈ {running, blocked} | 全 attempt → cancelled、全未完 inst → cancelled、status → cancelled |
| `manualRetry inst` | inst.failed（leaf または loop） | leaf は試行上限を増やし retryWait。loop は回数上限を増やし body を再開。いずれも status → running |

自動 `resume` は設けない。blocked から running に戻す操作は `manualRetry`。再試行できる failed インスタンスが無ければ、介入手段は cancel になる。複数失敗のうち一方を再試行した後など、`DEPENDENCIES_UNRESOLVED` にも failed インスタンスが残ることがあるため、この理由文字列だけで「cancel しか出口がない」とは断定しない。

`ValidLease s inst now`: status ∈ {running, blocked} ∧ inst.running ∧ inst.lease = some l ∧ l.token 一致 ∧ l.attempt 一致 ∧ now < l.until。参照実装の `Store.require_lease` と同じ条件。

Reject は状態を変えない。

### 4.5 公理

- A1 原子性: 1 トランザクション内の Step 列は途中状態が観測されない。
- A2 時計: `now` は単調非減少。
- A3 識別子: attempt id と lease token は一意。
- A4 oracle 決定性: §4.3。
- A5 永続性: イベントログに追記されたイベントは失われない。再開はログの replay で行う。

## 5. 証明する性質

不変条件（トランザクション境界で成り立つ）:

- I1 各線で `consumed ≤ placed.length`。EOS の後にトークンは置かれない。
- I2 各 `(node, trigger, path)` にインスタンスは高々1つ。
- I3 running なインスタンスは lease を持ち、その attempt は running。
- I4 インスタンスの状態遷移は許可表の範囲。

定理（すべて safety）:

| ID | 内容 | 前提 |
| --- | --- | --- |
| T1 plain の順序 | activate / WaitAll / Branch は全 plain 入力が終端し、上流が succeeded になってから受理する。Coalesce は選択した入力について同じ条件を要求する（entry を除く） | — |
| T2 アイテム不喪失 | 線に置かれたアイテムは、下流ノードのインスタンスに1回消費されるか、execution が blocked / cancelled になる | — |
| T3 アイテム非重複 | 同じアイテムが同じ線で2回消費されない。同じ `(node, trigger)` の leaf が2回 succeeded にならない | I2 |
| T4 EOS 健全性 | あるノードが出力に EOS を置くのは、その出力に置かれ得る全アイテムが既に置かれた後。下流は EOS の後にアイテムを見ない | I1 |
| T5 WaitAll / Collect は1回 | 各インスタンスにつき発火は高々1回 | I2 |
| T6 Branch 排他 | アイテムは選ばれた1本の arm にだけ置かれる | — |
| T7 Loop 有界 | body の実行回数は `maxIterations` 以下 | — |
| T8 lease 排他と失効拒否 | 1インスタンスに running な attempt は高々1つ。`ValidLease` を満たさない emit / complete / fail / renew は Reject | I3 |
| T9 決定性 | 同じ graph / inputs と決定的 oracle に適合し、成功して drain された2実行では、各論理線に置かれたアイテムの多重集合が一致する | A4、安定した occurrence ID、再試行時の重複排除、到着順によらない Collect。一般証明は未完 |
| T10 ストリームの前進 | forEach のインスタンスは、入力線の EOS を待たずに作られる（アイテムが届けば spawn できる） | — |
| T11 再開の冪等 | ログを replay した状態は、crash 直前の最後のトランザクション境界の状態と一致する。succeeded なインスタンスは再開後に再実行されない | A1, A5 |
| T12 停止の明示（liveness の代替） | idle 直後に status = running なら `hasWork` が真。idle が running から blocked へ変えるのは、状態を変える通常操作が無いときだけ。既に blocked の状態を維持する場合はこの逆の対象外 | 全 Op についての逆方向には候補列挙の完全性が必要。現時点では候補内の定理と独立生成による回帰検査 |
| T13 終端吸収 | status ∈ {succeeded, failed, cancelled} の後はどの Op も状態を変えない | — |

T9 は順序までは一致しないので多重集合で述べる。Collect は D5 の ItemId 昇順。drain は root の出口を結果として残し、それ以外の線に未消費アイテムがなく、全線に EOS があり、子 frame が回収済みであること。任意の prefix、cancel、yield の一部を残して終了した失敗とは比較しない。`Test/Determinism.lean` が候補列挙内の固定 oracle に適合する成功実行を乱択し、子 frame の線を含めて比較する。故障なしに加え、leaf の lease 失効 / retryable fail → promoteRetry → 再 claim と同じ occurrence ID の yield 再送を含む。再送先で消費済みの場合も検査する。繰り返し故障による試行上限超過、manualRetry、恒久失敗、cancel はこの有限検査の対象外。

一般命題の型は `Suimon/Execution.lean` の `ScheduleDeterminism`。`oracleConforms` は個々の emit が指定集合に入ることに加え、complete 時に全 stream 出力が指定どおり揃っていることを要求する。生の step の成功・drain だけでは、利用者コードが出すはずだった値の省略を排除できない。ForEach / Loop / DAG を含む完成時の意味論については `GraphEval.functional` で一意性を証明した。実 step の任意長列については、再送・管理操作のチャネル不変性、入力の保持、frame とチャネルの構造、成功時の完了境界を証明している。実際の成功実行から `GraphEval` の導出と全線の観測一致を構成する適合性は未証明であり、T9 全体の証明完了とはしない。

## 6. 有界探索器

`Explore.lean`。実行可能 `step` の上に、有界の全探索とランダム探索を実装する。

- 入力: `Test/graphs/` の例グラフ。普通の菱形（leaf → 2 leaf → WaitAll）、N 字、Branch、Loop（上限 2）、emit 型 leaf → ForEach → Collect、Merge、を1つずつ含む小さなグラフを複数用意する。
- worker 数、時間刻み、深さを引数にとり、BFS で到達状態を列挙。§5 を決定可能な述語として検査し、違反への Op 列を JSON で出す。
- ランダム探索は seed 付きの自前乱数で、状態に応じた候補から Op 列を生成する。`Plausible` の導入は T9 の補題着手時に判断する（型駆動の生成は状態依存の Op に向かず、shrink は反例が出るまで出番がないため）。
- 用途: 証明前は反例探し（設計の穴か証明の腕かを切り分ける）。証明後は §9 のテスト生成器。

## 7. Trace 検査

将来の実装が吐くイベント履歴（jsonl）を Step 列として再生し、仕様の許す遷移かを判定する。

### 7.1 イベント

`schema/events.schema.json` で定義する。すべてに `schema_version: 2`、`sequence`、`txn`（トランザクション識別子）、`recorded_at` を持つ。command と、D9 の必須の公開 facts、commit の順に記録する。具体的なフィールドと順序は [trace-format.md](trace-format.md) を原本とする。

| イベント | Op |
| --- | --- |
| `execution.started` | `start` |
| `instance.created` | `activate` / `spawn` |
| `attempt.started`（`lease_until` を含む） | `claim` |
| `attempt.finished` outcome ∈ {succeeded, failed, abandoned, cancelled} | `complete` / `fail` / `expireLease` / `cancel` |
| `lease.renewed`（`lease_until`） | `renew` |
| `token.placed`（edge, item_id または eos, by_instance） | `emit` / `complete` / `fire*` / `propagateEos` |
| `token.consumed`（edge, item_id, by_instance） | `activate` / `spawn` / `fire*` |
| `branch.taken`（instance, arm） | `fireBranch` の oracle |
| `loop.iterated`（instance, iteration, done） | `loopIterate` の oracle |
| `filter.judged`（instance, item_id, keep） | `fireFilter` の oracle |
| `execution.state_changed` | `idle` / blocked / cancel / manualRetry |

oracle の結果（Branch の選択、Loop の判定、Filter の判定、leaf が置いたアイテム ID）はイベントに含める。検査器は利用者のコードを実行できないため。

### 7.2 判定

適合なら exit 0。違反なら、最初に Reject になったイベントの `sequence`、適用しようとした Op、Reject 理由、直前のトランザクション境界の状態要約を出す。§5 の不変条件は各トランザクション境界で評価する。

## 8. 例: 参照実装の日次パイプラインを suimon の部品で書く

意味論が現実の要件を満たすかの確認用。実装するものではない。

```
Concurrency( source ごとに Scan )         # Scan は記事を見つけ次第 yield する
    │ yield された記事1件ごとに
    ▼
取得 → Loop≤2( 評価 → Branch(保留 → 確認) → Coalesce )  # 記事ごとに動く。評価ノードは全体上限で同時 2 まで
    │
AllWait                                   # 全 Scan の終了 + 全記事の処理完了で1回進む
    │
Plan                                      # 記事の束を yield する
    │ 束1つごとに
    ▼
Loop≤2( 執筆 → 検査 )
    │
AllWait
    │
Publish
```

- Scan は yield できるノード。source ごとに並列で、記事を見つけるたびに下流へ流す。3本の source の線は Merge で1本にする（§4 では `merge`）。
- 記事ごとの取得 → 評価は、他の記事や他の source の Scan の完了を待たない。参照実装の P04 → P06 → P07 が候補ごとの work になっているのと同じ。
- AllWait は「全 Scan の EOS」と「yield された全記事の処理完了」の両方を待つ。参照実装の B1 join（seal = 全 scan 完了、drain = 全評価完了）に対応する。手で待つ相手を登録する仕組みは要らない。
- 保留 → 確認 → 再評価（参照実装の P07 → P08/P09 → P07）と、執筆 ↔ 検査は Loop（上限 2）。
- Loop 内の Branch は Coalesce で合流し、選択された経路の値1個を Loop の出口へ渡す。
- profile や writing_settings のような全体で共有する値は、Prepare の出力を必要なノードへ線で引く。

## 9. 実装が満たすべき条件（言語非依存）

将来どの言語で実装しても、次を満たせば suimon の実装とみなす。

1. `schema/graph.schema.json` に適合するグラフ定義を受け取り、§3 の部品を提供する。
2. §7.1 のイベントを、トランザクション境界ごとに `txn` を揃えて jsonl に出せる。
3. そのイベント履歴が §7 の検査器で適合になる。少なくとも次の順序を意図的に踏むテストを持つ: lease 失効後の再 claim、失効 worker の遅延 complete、EOS 後の emit（Reject）、ForEach が EOS 前に spawn する、Loop 上限到達、Branch、cancel、crash 後の再開。
4. §6 の探索器が出す Op 列を受け取り、同じ操作を適用して状態を §4.2 の形に射影し、Lean 側と一致する（model-based testing）。
5. 永続化はイベントログ、または同等の「トランザクション境界の状態が復元できる」方式。lease と再試行の意味は §4.4 に従う。

言語固有のもの（スレッドか async か、DB は何か、例外型）は条件に含めない。

## 10. リポジトリ配置・ツールチェーン・CI

```
suimon/
  lakefile.lean
  lean-toolchain
  Suimon/                 # Lean モジュール（§4 の構成）
  Main.lean               # CLI
  Test/                   # 例グラフと回帰
  schema/
    graph.schema.json
    events.schema.json
  docs/suimon-design.md
  bin/test                # lake build、探索器、検査器の回帰
```

例グラフ JSON は `Test/graphs/` に置き、将来の実装もそこを読む。

- Lean: `lean-toolchain` で固定。外部依存は現在なし（D7）。必要になった時点で判断を記録して追加する。
- CLI: `lake exe suimon check <trace.jsonl> --graph <graph.json>`、`lake exe suimon explore --graph <graph.json> --depth N`、`lake exe suimon gen --seed S --count N`。
- CI: `lake build`（`sorry` 残数をマイルストーンごとに減らす）、探索器の反例ゼロ、検査器の回帰。

## 11. マイルストーンと受入条件

### M1 型と実行可能 step

- §4.1〜4.4 の型と `step` がある。既存の `formal/suimon/` は root へ移し、§4 に合わせて書き直す。
- `schema/graph.schema.json`、`schema/events.schema.json` があり、例グラフが適合する。
- 手書きの最小 trace を適合と判定し、壊した trace（`attempt.started` を削る、EOS 後に `token.placed`）を違反と判定する。

### M2 探索器と基本定理

- 探索器が全例グラフで深さ 8 以上を完走し、反例ゼロ。反例があれば内容と対処を `docs/` に記録。
- I1〜I4、T1、T3、T5、T6、T7、T8、T13 が `sorry` なし。
- 受理された `step` の分解補題（`step_ok_cases`: 恒等な吸収か、認可・前提・不変条件・履歴検査を通った実行）。

### M3 ストリームの定理

- T2、T4、T10、T12。
- T9（決定性）が §5 の前提の下で成立。有限範囲の乱択検査だけではこの受入条件を満たさない。

### M4 再開

- T11。イベントログからの replay の定義と、境界状態との一致。

### M5 実装（別判断）

- 言語を決め、§9 の条件を満たす実装を作る。この文書の範囲外。着手時に言語と配置を決めて追記する。既存の `python/` を使うか捨てるかもその時に決める。

## 12. 決定事項と未決事項

### 決定済み（2026-09-17、D1 / D2 は 2026-09-18 改訂、D9 は 2026-09-19 追加）

| # | 事項 | 決定 |
| --- | --- | --- |
| D1 | Branch の排他的合流 | Coalesce は独立した処理の first-wins にしない。root / body の双方で、入力が単一の Branch の異なる arm と1対1で対応し、選択 arm に由来することを WellFormed に加える。body 内の Branch は Coalesce に合流し、出口の値をちょうど1個とする。合流しない Branch は root のみ許す |
| D2 | idle の判定と解除 | `hasWork` が対象にするのは idle / cancel / manualRetry 以外の**状態を変える受理操作**。候補内の定理と全 Op の完全性は区別する。自動 resume を削除し、blocked から running への解除は manualRetry に統一する。対象の failed インスタンスがなければ cancel。理由文字列だけでは到達経路や再試行可否を判定しない |
| D3 | Loop の上限到達 | failed + blocked(LOOP_LIMIT) のまま。ただし `manualRetry` を loop にも許し、回数上限を増やして再開できるようにする |
| D4 | plain → stream の昇格 | 暗黙にしない。plain 入力・stream 出力の emit 型 leaf を明示的に挟む（implementation.md の決定を採用） |
| D5 | Collect の出力順 | ItemId の昇順。到着順は結果に含めない（同上） |
| D6 | アイテム識別子 | 「同じ処理・同じ入力・同じ出力番号なら同じ ID」。モデルでは JSON 配列の符号化、実装で digest を使う場合は衝突しない射影を要求（同上） |
| D7 | Mathlib | 使わない。Lean 標準ライブラリのみ（同上） |
| D8 | Concurrency の表現 | §3 の Concurrency 箱は §4 では「1つの出力から複数の線 + waitAll」で表す。独立の NodeKind は作らない |
| D9 | facts の公開射影 | command と公開 facts は必須。facts は `Trace.Projection` に列挙したフィールドだけを厳密照合し、内部構造を直接 JSON 化しない。Instance 作成は id / node / path / trigger。各種カウンタ等は command replay で復元する。区分内は論理 ID 順。公開フィールドは snake_case、主体は by_instance、lease 期限は lease_until。v2 に移行し、今後の内部フィールド追加では公開形式を変えない |
| D10 | 遷移関係 `Step` | 置かない。`step` は結果が一意に決まる関数であり、関係を別に書いても同じ内容の重複になる。定理は `step` について直接証明し、受理の分解は補題 `step_ok_cases` で行う（2026-09-19） |

### 判断状況（旧未決番号を維持）

1. 最初の実装言語。M5 で決める。
2. **解決済み（D9）**。facts は公開射影に決定。command / facts / commit は必須のまま、内部構造との結合を除く。
3. **解決済み（D10）**。関係 `Step` は削除し、`step` 関数を唯一の遷移定義とする。
4. `Graph.WellFormed` を `validate = .ok ()` から構造的定義へ書き直すか。定理で使う段になったら判断する。
5. 参照実装との対応で確認済みの事項: `ValidLease` の条件、再試行の回数計算、lease 失効時の attempt 放棄。今後の確認は必要になった時点で行う。
6. 候補列挙の完全性。`hasWork` が偽なら全ての通常 Op が状態を変えられない、という逆方向の一般証明は未完。探索器と独立した Op 生成で、受理され状態が変わるなら hasWork が真、という乱択回帰を行う。`Op` の追加時はこの独立生成も更新する。

### 実装への指示（D1〜D3）

- `coalesce` を `NodeKind` に追加し、`fireCoalesce` を実装する。`Test/graphs/` に「Loop の body に Branch → Coalesce」を含む例を足し、`finishSubworkflow` が拒否しないことを回帰にする。
- `State.hasWork` を D2 の定義に合わせ、自動 resume と状態を直接 blocked に書き換える復帰テストを削除する。初期状態から実際の操作列で再試行・依存停止を確認する。
- Coalesce への逆向きの arm 由来検査と、選択した plain 入力の順序検査を加える。独立 leaf / 異なる Branch / 同じ arm の重複を拒否し、共有入力と入れ子の合流を回帰にする。
- T12 の候補内の逆方向を証明し、全 Op については独立した乱択回帰と完全性未証明の記録を追加する。
- `manualRetry` の `NOT_LEAF` 判定を外し、loop のときは `maxIterations` の加算にする。
- implementation.md の「idle」「Loop」「Branch」の項を D1〜D3 に合わせて更新する。

## 13. 実装状況の補足（2026-09-17）

実行可能な Lean モデル、CLI、例グラフ、Schema、回帰と CI を追加した。未決事項の選択、設計上必要だった追加操作、T2/T9 の前提の問題、証明済みの正確な範囲は [implementation.md](implementation.md) に記録する。イベントの具体的な wire format は [trace-format.md](trace-format.md) を参照。M1 は完了し、M2–M4 の全受入条件の達成はまだ宣言していない。
