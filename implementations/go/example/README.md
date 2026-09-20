# Go playground

時間差で生成する stream、アイテムごとの並列処理、全件待ちを実際の Go runtime で動かすサンプルです。

## 起動

リポジトリ直下で実行します。Node.js 22.12 以降と pnpm 10 は UI のビルドに使います。

```sh
pnpm install
pnpm build
go -C implementations/go run ./example -ui
```

`http://127.0.0.1:8080` を開き、右上のサンプルと待ち時間を選んで **Run workflow** を押します。ノードの IN / OUT、実行中・完了件数、上部の進行状況、trace が途中から更新されます。ForEach の「内側のグラフを開く」で worker の入出力も確認できます。

`-listen 127.0.0.1:8081` でポート、`-ui-dir /path/to/suimon/implementations/go/example/ui/dist` で配信ディレクトリを変更できます。UI を編集するときは、Go サーバーを起動したまま `pnpm --filter @suimon/go-example-ui dev` を実行します。Vite が `/api` をポート 8080 に転送します。

## サンプル

| サンプル | 観察すること |
| --- | --- |
| Streaming pipeline | 1件ずつ Emit し、生成が続いている間に下流が処理を開始する |
| Batch comparison | 同じ値・同じ待ち時間で、全件生成後に Emit する。下流の開始が遅くなる |
| Text processing | `trim → uppercase` の基本例。sleep は使わない |

stream / batch は同じグラフです。

```text
Source ─items(stream)→ Filter → ForEach → Collect ─out(plain)→ 結果の配列
```

- **Source** は基準の待ち時間ごとに値を生成し、最後の1ステップも待ってから正常 return します。return が stream の EOS を確定します。
- **Filter** は `#` で始まる項目を除外します。既定入力の6件中、5件が下流に進みます。
- **ForEach** の body は uppercase の leaf。共通の Concurrency=2 により最大2件を同時処理し、待ち時間はアイテムごとに基準の2〜4倍です。後から始めた処理が先に完了することもあります。
- **Collect（設計上の AllWait）** は全 body の完了と上流 EOS を待ち、結果を配列にします。到着した値は入力チャネルに蓄積されます。UI の IN には到着時点から値を表示し、待機件数・消費済み件数と EOS の到着状況も確認できます。OUT は全件到着後に出ます。

入力は空白区切りで最大12件。基準時間は UI で200 / 600 / 1000msから選べます。sleep は context に対応した timer で模擬しているため、ブラウザの切断時には処理を終了できます。実行結果の `index` は生成順を示します。stream の意味は到着順の保証ではないため、表示や利用時に順序が必要ならこのキーを使ってください。

同じ入力と待ち時間で stream / batch を順に実行すると、左側に「下流開始」と「全体」の実測値を比較表示します。「下流開始」は最初の worker を観測した時刻です。上部の時間表示もこの2項目に揃えています。時刻は約100msごとの画面通知で観測した値です。

## CLI

Go だけでも実行できます。ログの時刻で生成と worker の重なりを確認できます。

```sh
go -C implementations/go run ./example
go -C implementations/go run ./example -scenario batch
go -C implementations/go run ./example -scenario streaming -delay 200ms
go -C implementations/go run ./example -scenario basic
```

## 構成

| 場所 | 責務 |
| --- | --- |
| `scenarios.go` | サンプル一覧、stream グラフ、生成・フィルタ・加工処理 |
| `graph.go` / `nodes.go` | 2ノードの基本例 |
| `main.go` / `result.go` | CLI の選択・実行・結果表示 |
| `ui.go` | 静的ファイル配信、サンプル取得、Go runtime の実行と逐次通知 |
| `ui/src/App.tsx` | Go 専用画面。`@suimon/ui-kit` を利用 |
| `ui/src/api.ts` | HTTP / NDJSON と kit の公開 JSON の接続 |
| リポジトリ直下の `ui-kit/` | 再利用するコンポーネントと表示用関数のみ |

`GET /api/samples` はグラフとサンプル情報を返します。`POST /api/run` は `{ scenario, input, delay_ms? }` を受け取り、`Accept: application/x-ndjson` の場合は `{ graph?, event_offset, events, values, elapsed_ms, done, outputs?, error? }` を改行区切りで通知します。Accept の指定がない場合は完了後の Snapshot を返します。既存の `GET /api/graph` と scenario 省略時の基本例も利用できます。

各レスポンスの先頭だけに `graph` があり、`event_offset` はそのフレームより前に送信したイベント数（初回は0）です。`events` は追加分だけで、空またはトランザクションの commit で終わります。`values` も新しく追加された item ID の値だけです。グラフ・イベント・値を毎回再送しないため、通信量は履歴全体の大きさに比例します。

最後の `done: true` フレームには `outputs` と、失敗時の `error` を付けます。イベントが増えずに完了した場合も、空の `events` / `values` で完了を通知します。最終フレームでも履歴全体は再送しません。

`outputs` は `{ port: { node, port }, items: [{ id, value }] }` の配列です。フロントエンドは各ポートと値の形式を検証し、すべての exit と item を表示します。

`ui/src/api.ts` は追加分だけを検証して既存の履歴に追記し、kit に渡す完全な Snapshot を組み立てます。受信済みイベントとグラフの参照は保持し、過去のフレームは変更しません。offset・sequence の欠落／重複、値の再送、未確定の末尾、完了前の切断はエラーとして扱います。各実行は独立したレスポンスで、切断後の自動再接続・途中再開は行いません。

通知は約100msごとのポーリングで変更があった場合に送り、複数の commit を1フレームにまとめることがあります。`ui-kit` 自体は通信・待ち時間・Go runtime に依存しません。

## 検証

```sh
pnpm build
pnpm test
go -C implementations/go test ./example
go -C implementations/go test -race ./example
```

時間ではなく同期ゲートを使い、生成中の並列実行・同時実行上限・EOS 前の Collect 待機・batch の送信境界を検証します。HTTP の差分を結合した履歴の適合性、イベントと値の重複送信がないこと、途中通知・最終結果・切断キャンセル、UI の差分読込と不正な連番の拒否も検査します。
