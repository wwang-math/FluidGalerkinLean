import Lake
open Lake DSL

package FluidGalerkin where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib PDEIdeas

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "8d6f23e07b24c7dda53bb66ba1acaf7b99c9adf6"
