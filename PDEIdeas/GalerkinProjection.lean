import PDEIdeas.GalerkinDynamics
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

open Real InnerProductSpace

noncomputable section

/-- A finite-dimensional Galerkin projection together with its target subspace.
This is the natural interface between the abstract Hilbert-space energy method
and the concrete coefficient ODE on a finite-dimensional Galerkin space. -/
structure GalerkinProjection (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  space : Submodule ℝ H
  proj : H →L[ℝ] H
  finiteDimensional_space : FiniteDimensional ℝ space
  mem_space : ∀ u : H, proj u ∈ space
  fix_space : ∀ u : H, u ∈ space → proj u = u

attribute [instance] GalerkinProjection.finiteDimensional_space

namespace GalerkinProjection

/-- The projector is orthogonal with respect to the ambient inner product.
This is the identity used when testing a projected Galerkin equation by a
vector in the Galerkin space. -/
def IsOrthogonal
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (G : GalerkinProjection H) : Prop :=
  ∀ x : H, ∀ y : G.space, ⟪G.proj x, (y : H)⟫_ℝ = ⟪x, (y : H)⟫_ℝ

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [GalerkinSystem H]

/-- The projected Galerkin vector field on a finite-dimensional subspace. -/
def projectedRHS
    (G : GalerkinProjection H)
    (F : ℝ → H) (U : H) (t : ℝ) : H :=
  G.proj (abstractRHS F U t)

namespace IsOrthogonal

/-- Orthogonality removes the projector when the projected vector field is
tested against a Galerkin state. -/
theorem inner_projectedRHS
    {G : GalerkinProjection H}
    (hG : G.IsOrthogonal)
    (F : ℝ → H) (U : G.space) (t : ℝ) :
    ⟪G.projectedRHS F U t, (U : H)⟫_ℝ =
      ⟪abstractRHS F U t, (U : H)⟫_ℝ :=
  hG _ U

end IsOrthogonal

/-- By construction the projected Galerkin vector field takes values in the
chosen Galerkin subspace. -/
theorem projectedRHS_mem
    (G : GalerkinProjection H)
    (F : ℝ → H) (U : H) (t : ℝ) :
    G.projectedRHS F U t ∈ G.space :=
  G.mem_space _

/-- If the forcing and both operators preserve the chosen Galerkin space, then
the projected vector field agrees with the unprojected abstract right-hand
side on that space. -/
theorem projectedRHS_eq_abstractRHS
    (G : GalerkinProjection H)
    (F : ℝ → H)
    (hLin : ∀ u : H, u ∈ G.space → GalerkinSystem.linOp u ∈ G.space)
    (hBil : ∀ u : H, u ∈ G.space → ∀ v : H, v ∈ G.space →
        GalerkinSystem.bilin u v ∈ G.space)
    (hF : ∀ t : ℝ, F t ∈ G.space)
    {U : H} (hU : U ∈ G.space) (t : ℝ) :
    G.projectedRHS F U t = abstractRHS F U t := by
  apply G.fix_space
  dsimp [GalerkinProjection.projectedRHS, abstractRHS]
  have hA : GalerkinSystem.linOp U ∈ G.space := hLin U hU
  have hB : GalerkinSystem.bilin U U ∈ G.space := hBil U hU U hU
  have hSum : -(GalerkinSystem.linOp U) - GalerkinSystem.bilin U U ∈ G.space := by
    simpa [sub_eq_add_neg] using G.space.add_mem (G.space.neg_mem hA) (G.space.neg_mem hB)
  exact G.space.add_mem hSum (hF t)

/-- The projected finite-dimensional Galerkin vector field is locally Lipschitz
on bounded sets, with a constant amplified by the projector norm. -/
theorem projectedRHS_lipschitz
    (G : GalerkinProjection H)
    (F : ℝ → H)
    (R : ℝ) (hR : 0 < R) :
    ∃ L : ℝ, 0 ≤ L ∧
    ∀ U V : H, ‖U‖ ≤ R → ‖V‖ ≤ R → ∀ t : ℝ,
      ‖G.projectedRHS F U t - G.projectedRHS F V t‖ ≤ L * ‖U - V‖ := by
  rcases abstract_galerkin_lipschitz (H := H) F R hR with ⟨L, hL, hLip⟩
  refine ⟨‖G.proj‖ * L, mul_nonneg (norm_nonneg _) hL, ?_⟩
  intro U V hU hV t
  dsimp [GalerkinProjection.projectedRHS]
  calc
    ‖G.proj (abstractRHS F U t) - G.proj (abstractRHS F V t)‖
        = ‖G.proj (abstractRHS F U t - abstractRHS F V t)‖ := by
            rw [map_sub]
    _ ≤ ‖G.proj‖ * ‖abstractRHS F U t - abstractRHS F V t‖ := G.proj.le_opNorm _
    _ ≤ ‖G.proj‖ * (L * ‖U - V‖) := by
          exact mul_le_mul_of_nonneg_left (hLip U V hU hV t) (norm_nonneg _)
    _ = (‖G.proj‖ * L) * ‖U - V‖ := by ring

end Abstract

end GalerkinProjection
