import Test.Artifacts
import Test.TraceProjection
import Test.TraceText

def main : IO Unit := do
  Suimon.Test.Artifacts.run
  Suimon.Test.TraceProjection.run
  Suimon.Test.TraceText.run
