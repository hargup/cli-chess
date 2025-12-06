import Chess.Interface
import Chess.Core

-- We can define main here or use the one from Interface if we move it there.
-- Since I defined 'main' in the previous Chess.lean which is now Main.lean...

open Chess.Interface
open Chess.Core

def main : IO Unit := do
  IO.println "=== Chess Game ==="
  IO.println "Move format: e2e4 or e2-e4"
  IO.println "Type 'resign' to resign"
  IO.println ""
  gameLoop initialState
