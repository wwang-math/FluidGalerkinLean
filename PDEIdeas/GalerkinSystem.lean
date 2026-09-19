import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

open InnerProductSpace

noncomputable section

/-- An abstract evolution system admitting a Galerkin energy estimate. -/
class GalerkinSystem (H : Type*)
    [NormedAddCommGroup H] [NormedSpace ℝ H] [InnerProductSpace ℝ H] [CompleteSpace H] where
  linOp    : H →L[ℝ] H
  bilin    : H →L[ℝ] (H →L[ℝ] H)
  selfAdj  : ∀ u v : H, ⟪linOp u, v⟫_ℝ = ⟪u, linOp v⟫_ℝ
  coercive : ∀ u : H, 0 ≤ ⟪linOp u, u⟫_ℝ
  cancel   : ∀ u : H, ⟪bilin u u, u⟫_ℝ = 0

/-- Any skew-symmetric transport form gives the cubic cancellation used in energy methods. -/
theorem cancel_of_skew
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [InnerProductSpace ℝ H]
    (B : H →L[ℝ] (H →L[ℝ] H))
    (hSkew : ∀ u v w : H, ⟪B u v, w⟫_ℝ = -⟪B u w, v⟫_ℝ)
    (u : H) :
    ⟪B u u, u⟫_ℝ = 0 := by
  have h := hSkew u u u
  have hsum : ⟪B u u, u⟫_ℝ + ⟪B u u, u⟫_ℝ = 0 := by
    simpa using (eq_neg_iff_add_eq_zero.mp h)
  have hmul : (2 : ℝ) * ⟪B u u, u⟫_ℝ = 0 := by
    simpa [two_mul] using hsum
  rcases mul_eq_zero.mp hmul with htwo | hzero
  · norm_num at htwo
  · exact hzero

/-- Build a `GalerkinSystem` from coercivity/self-adjointness plus transport skew-symmetry. -/
@[reducible] def GalerkinSystem.ofSkew
    (H : Type*)
    [NormedAddCommGroup H] [NormedSpace ℝ H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →L[ℝ] H)
    (B : H →L[ℝ] (H →L[ℝ] H))
    (hSA : ∀ u v : H, ⟪A u, v⟫_ℝ = ⟪u, A v⟫_ℝ)
    (hCoer : ∀ u : H, 0 ≤ ⟪A u, u⟫_ℝ)
    (hSkew : ∀ u v w : H, ⟪B u v, w⟫_ℝ = -⟪B u w, v⟫_ℝ) :
    GalerkinSystem H where
  linOp := A
  bilin := B
  selfAdj := hSA
  coercive := hCoer
  cancel := cancel_of_skew B hSkew
