import Lake
open Lake DSL

package «math190formalize» where
  -- add package configuration options here

lean_lib «Math190formalize» where
  -- add library configuration options here

@[default_target]
lean_exe «math190formalize» where
  root := `Main

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ s!"v{Lean.versionString}"
