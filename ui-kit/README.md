# suimon UI kit

React + TypeScript のワークフロー UI コンポーネント集です。React Flow によるノードキャンバスと、実行 trace の表示部品を提供します。Go / Python / Rust などのバックエンドとは、既存の graph v1・events v2 と item の値を JSON で接続します。

## 開発とビルド

Node.js 22.12 以降、pnpm 10 を使います。リポジトリ直下で実行します。

```sh
pnpm install
pnpm --filter @suimon/ui-kit build
```

このパッケージは共通部品のみを提供します。Go 専用の画面・入力フォーム・通信は [implementations/go/example/ui](../implementations/go/example/ui/) にあり、`@suimon/ui-kit` を workspace dependency として利用します。[Go example の起動手順](../implementations/go/example/README.md)を参照してください。

ビルドはライブラリ（`dist/index.js`・型宣言・`dist/styles.css`）を生成します。React と React DOM は peer dependency で、ライブラリのバンドルには含めません。リポジトリ全体の `pnpm build` は、kit → Go example UI の依存順でそれぞれをビルドします。

## コンポーネント

| 公開コンポーネント | 責務 |
| --- | --- |
| `WorkflowWorkbench` | 下記の部品を組み合わせた画面。選択・パネルの表示・グラフ階層を管理 |
| `WorkflowCanvas` | 配線、ノードの選択・表示位置の移動、ズーム、全体表示 |
| `WorkflowNode` / `BoundaryNode` | React Flow のノード表示と入出力ポート |
| `NodeSidebar` | ノードの検索・種別フィルタ・一覧・接続一覧 |
| `WorkflowToolbar` | タイトル、実行ステータス、アクション領域、エクスポート |
| `NodeInspector` | ノードの入力・出力値、接続先、種類・設定 |
| `NodeIOPanel` | ポートごとの入力・出力値と item の詳細 |
| `TracePanel` | command / fact / commit の一覧、イベント選択とフィルタ |
| `EventInspector` | 選択イベントの値・メタデータ・JSON |
| `NodeIcon` | ノード種別のアイコン |

各部品は [src/components/](src/components/) の独立した TSX ファイルです。公開 props とデータ型はパッケージから import できます。モデル表示用の純粋関数は [src/lib/](src/lib/) にあります。

## 組み込み

ローカルのパッケージを workspace / file dependency で参照します。パッケージはまだレジストリへ公開していません。

```tsx
import { WorkflowWorkbench, parseSnapshot } from '@suimon/ui-kit';
import '@suimon/ui-kit/styles.css';

const data = parseSnapshot(await response.json());

<WorkflowWorkbench
  data={data}
  title="My workflow"
  actions={<button onClick={run}>Run</button>}
  sidebarContent={<MyInputForm />}
  onSelectEvent={event => console.log(event.sequence)}
/>;
```

`data` は `{ graph, events, values? }`。Go の `RunResult.Snapshot` をそのまま使えます。`events: []` で実行前のグラフを表示します。`parseGraph` / `parseSnapshot` はネットワーク境界で形式と数値範囲を確認するための関数です。`parseTraceEvents` はイベント配列だけを検証するため、差分配信の追加分にも使えます。モデル全体の適合検査は各言語の `suimon check` に任せます。

kit に完全な Snapshot を渡すことと、ネットワークで全履歴を送ることは別です。[Go example の接続層](../implementations/go/example/ui/src/api.ts)は追加イベント・値だけを受信し、既存の履歴に追記した Snapshot を作ります。通信形式・再接続方針は利用側の責務で、kit は HTTP や Go 固有の配信形式に依存しません。

各ノードの `IN` / `OUT` にポート名と値のプレビューを表示します。IN は確定済みの `token.placed` に基づく到着履歴で、受信側の instance 作成や消費を待たずに表示します。`token.consumed` は同じ channel / token index の入力を消費済みに更新します。ノードを選ぶと、右側の `INPUT` / `OUTPUT` で全文、接続元・接続先、stream の待機件数と EOS を確認できます。複数の値は一覧になり、未記録と値の未提供を区別します。

`nodeIO(graph, node, events, values, scope)` は確定済みイベントからポートごとの値を集める純粋関数で、`NodeIOPanel` に単独で渡すこともできます。入力 item の `consumed`、`consumedSequence` は消費状態、`channel` / `tokenIndex` は入力 occurrence を表します。未消費なら `instance` は未設定です。`scope` はノード定義の階層です（例: `['loop']`）。入出力表示はこの階層を使って同名ノードを区別します。

表示名・説明・色は `presentations={{ nodeId: { label, description, accent } }}` で渡せます。独自画面では部品を直接組み合わせられます。

`presentations[nodeId].position` で初期の表示位置、`inputSide` / `outputSide` でハンドルの向き（`top` / `bottom` / `left` / `right`）を指定できます。既定は上から入力・下から出力です。左右のハンドルは対応する IN / OUT の行に揃います。`showBoundaryNodes={false}` はグラフの入口・出口の補助カードだけを非表示にします。グラフやポートの意味は変えません。値の逐次更新時は `data.graph` の参照を維持すると、ドラッグした表示位置を保てます。

`createWorkflowView(graph, events, values, scope)` は trace の索引・全ノードの I/O・実行件数・関連イベントをまとめて計算します。独自の進捗表示にも使う場合は、同じ結果を `<WorkflowWorkbench data={data} view={view} />` に渡すと計算を共有できます。`traceIndex(events)` の結果を `events` の代わりに渡せるため、複数の階層を表示するときも索引を再利用できます。入力データは変更せず、新しい snapshot ごとに作成してください。キャンバスは表示内容に変更のないノードのオブジェクトを保持します。

```tsx
import { WorkflowCanvas, NodeSidebar } from '@suimon/ui-kit';
import '@suimon/ui-kit/styles.css';

<div className="suimon-ui" style={{ display: 'flex', height: 600 }}>
  <NodeSidebar graph={graph} onSelectNode={setSelected} />
  <div style={{ flex: 1 }}>
    <WorkflowCanvas graph={graph} selectedNode={selected} onSelectNode={setSelected} />
  </div>
</div>;
```

単独利用時も `.suimon-ui` の内側に置きます。CSS クラスは `sui-` で名前空間を分けています。Workbench は既定で画面全体を使います。必要なら `.sui-workbench` の高さを変更します。

## テーマ

`<WorkflowWorkbench theme="light" />` でライトテーマに切り替えられます（既定は `dark`）。部品を単独で使う場合は外側を `<div className="suimon-ui" data-theme="light">` とし、`WorkflowCanvas` にも `theme="light"` を渡します。

背景・文字・境界線・状態色・キャンバスの配線とグリッドは [src/tokens.css](src/tokens.css) の意味別トークンを参照します。CSS は React Flow の標準スタイルも含めて `suimon` レイヤーにまとめているため、利用側のレイヤーなし CSS で上書きでき、`!important` は不要です。

```css
.suimon-ui {
  --sui-accent: #70d6c6;
  --sui-accent-strong: #237a6f;
  --sui-accent-soft: #70d6c626;
  --sui-focus: #70d6c6;
}
```

主なトークンは `--sui-bg` / `--sui-panel` / `--sui-raised`、`--sui-text` / `--sui-text-secondary` / `--sui-muted`、`--sui-border`、`--sui-accent` / `--sui-accent-strong` / `--sui-on-accent`、`--sui-success` / `--sui-warning` / `--sui-danger` です。状態色には対応する `-bg` もあります。ノードごとに指定した `presentations[nodeId].accent` はテーマより優先します。

## ランタイムとの分離

`src/` は HTTP API を呼びません。実行ボタン、通信、エラー処理、入力フォームは [Go example の App.tsx](../implementations/go/example/ui/src/App.tsx) の責務です。他言語を追加するときは公開 JSON を返す API と接続部分を用意し、コンポーネントを再利用します。kit の `nodeActivity(events, scope)` は確定済みの attempt から実行中・完了・失敗の件数を集計し、コンテナ内の並列処理も表示します。

キャンバスはグラフと trace の閲覧用です。ドラッグは表示位置だけを変更します。ノード追加・配線編集・位置の永続化は含みません。実行ステータスは確定済みの trace から取得し、ノード選択は関係する確定済みイベントを絞り込みます。命令の実行元だけでなく、チャネルの送信元・宛先も関連づけるため、Collect の instance ができる前の到着も trace に現れます。`Node / route` 列で送信元と宛先を確認できます。`TracePanel` を単独で利用するときも `view` を渡すと同じ絞り込みを使えます。内部状態の再実装はありません。

同名ノードが複数の body にある場合も、表示中の定義の階層（`scope`）で trace と I/O を区別します。同じ定義を繰り返し実行した履歴はまとめて表示し、各 instance の `path` / ID はイベント JSON で区別できます。自然数は JavaScript の安全な整数範囲（`0`〜`2^53 - 1`）に限り、範囲外は parse 時に拒否します。

## 検証

```sh
pnpm --dir ui-kit typecheck
pnpm --dir ui-kit test
pnpm --dir ui-kit build
go -C implementations/go test ./example
```

共用 Lean fixture のイベント対応、commit 境界、値、DAG 配置、形式エラー、コンポーネントの単独利用を検証します。CI でも型チェック・テスト・ビルドを実行します。
