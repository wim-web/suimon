import Test.Validate
import Test.Step
import Test.WireText
import Test.Trace
import Test.TraceBounded
import Test.Cli

def main : IO Unit := do
  Suimon.Test.Validate.run
  Suimon.Test.Step.run
  Suimon.Test.WireText.run
  Suimon.Test.Trace.run
  Suimon.Test.TraceBounded.run
  Suimon.Test.Cli.run
