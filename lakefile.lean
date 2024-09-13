import Lake
open Lake DSL

package «game_theory» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require batteries from git
  "https://github.com/leanprover-community/batteries" @ "main"

@[default_target]
lean_lib «GameTheory» where
  -- add any library configuration options here
