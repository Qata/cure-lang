import Lake
open Lake DSL

package cure_lean_bridge

require lean4lean from "../../lean4lean"

@[default_target]
lean_exe «cure-lean-bridge» where
  root := `CureLeanBridge
