# suimon

ワークフローの制御を Lean 4 で定義・検証し、各言語の実装で利用するためのプロジェクトです。

[仕様](docs/suimon-spec.md) / [設計理由](docs/suimon-design.md) / [定義と証明](Suimon/) / [各言語の実装](implementations/) / [UI kit](ui-kit/README.md) / [データ形式](schema/)

## 実行

`elan` と `lake` に PATH を通し、リポジトリ直下で実行します。

```sh
lake build
lake exe suimon validate Test/definitions/users.json
lake exe suimon gen Test/definitions/users.json --seed 1 > /tmp/users.jsonl
lake exe suimon check /tmp/users.jsonl
```

CLI のオプションは `lake exe suimon --help` で確認できます。

## 検証

リポジトリ直下で [bin/test](bin/test) を実行します。未完成の証明の検出に `rg`（ripgrep）を使います。各言語の実装の検証手順は、それぞれの README を参照してください。
