import Lake
open Lake DSL

package "LeanTool" where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require Hammer from git "https://github.com/JOSHCLUNE/LeanHammer" @ "v4.22.0"


require "leanprover-community" / "mathlib" @ git "v4.22.0"


@[default_target]
lean_lib «LeanTool» where
  -- add any library configuration options here
