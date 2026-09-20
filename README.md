# suimon

ワークフローの制御を Lean 4 で定義・検証し、各言語の実装で利用するためのプロジェクトです。

[設計理由](docs/suimon-design.md) / [仕様と証明](Suimon/) / [各言語の実装](implementations/) / [UI kit](ui-kit/README.md) / [データ形式](schema/)

## 実行

`elan` と `lake` に PATH を通し、リポジトリ直下で実行します。

```sh
lake build
lake exe suimon check Test/traces/minimal.jsonl --graph Test/graphs/minimal.json
```

CLI のオプションは `lake exe suimon --help` で確認できます。

## 検証

リポジトリ直下で [bin/test](bin/test) を実行します。各言語の実装の検証手順は、それぞれの README を参照してください。
