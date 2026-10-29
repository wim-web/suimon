# Suimon TypeScript の実装契約

Node 向けの独立した `@suimon/engine` を `implementations/typescript` に追加する。仕様の基準は [suimon-spec.md](../../suimon-spec.md)、保存形式は既存の [definition](../../../schema/definition.schema.json) と [trace](../../../schema/trace.schema.json)。Go の制御を TypeScript へ移し、独立サービスや業務処理は持ち込まない。Neo は既存の Go 実装を継続利用するため、この TS 実装への導入・migration を完了条件に含めない。

公開入口は `@suimon/engine`。既存構成には `parseDefinition` と `Engine` を使い、型付き構築には `defineType(name, parse)`、関数・transform の登録と workflow builder を使う。実行は `start(input, {journal, signal})`、`run(input, options)`、`resume(journal, {signal})`。実行ハンドルは `cancel()` と `wait()` を持つ。構成検証を省く場合は `Engine` の `validate: false` を明示し、同じ実行器を使う。正確な型は [model-types.ts](../../../implementations/typescript/src/model-types.ts) と [runtime-types.ts](../../../implementations/typescript/src/runtime-types.ts) に置く。

永続化する利用側は `RecoverableJournal` を実装する。保存内容は現行 JSONL のバイト列で、append、sync、上限付き contents、永続的な truncate を提供する。一つの実行の writer と復元を排他的に所有する責任は利用側にある。DB の接続、DDL、移行、lease の具体方式はこのパッケージの対象外。

Go と同じ構成で同じ形式の journal を再生する。完了済み処理を呼び直さず、プロセス終了時に実行中だった呼び出しは lost として記録する。破棄するのは spec が未確定と定義する末尾だけである。旧形式の識別、変換、既存状態の削除は追加しない。現在の形式でない実データが見つかった場合は、その対象と扱いを別途確認する。

検証は既存定義・記録・状態の fixture と Go／Lean の実行結果を比較する。非同期実行では sync 前に副作用が出ないこと、停止後の遅い結果、生成器の終了、concurrency の枠、復元時の非再実行を実際の callback で確認する。最後に pack したパッケージを別の Node プロジェクトから使用する。
