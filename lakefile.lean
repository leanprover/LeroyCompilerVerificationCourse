import Lake
open Lake DSL
require "leanprover-community" / "batteries" @ git "main"
package «leroy» where
  -- add package configuration options here

lean_lib «Leroy» where
  -- add library configuration options here

@[default_target]
lean_exe «leroy» where
  root := `Main
