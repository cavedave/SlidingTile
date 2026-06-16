import Lake
open Lake DSL

package sliding where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

@[default_target]
lean_lib Sliding where
  globs := #[.submodules `Sliding]

lean_exe sliding where
  root := `Main

lean_exe sliding4x4 where
  root := `Main4x4
