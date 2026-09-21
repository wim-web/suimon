import Lake
open Lake DSL
package suimon where
  version := v!"0.1.0"
lean_lib Suimon
lean_lib Test
@[default_target] lean_exe suimon where
  root := `Main
lean_exe suimon_test where
  root := `Test.Main
  needs := #[`@/suimon]
lean_exe suimon_schema_test where
  root := `Test.SchemaMain
  needs := #[`@/suimon]
lean_exe suimon_go_oracle where
  root := `Test.GoOracle
lean_exe suimon_go_corpus where
  root := `Test.GoCorpusMain
