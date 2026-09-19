import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Operator.Compact

/-!
# Compact Gelfand triples

This file packages a dense compact injection `V -> H` and the canonical pivot
map `H -> V'` induced by the inner product on `H`.
-/

open Function InnerProductSpace
open scoped RealInnerProductSpace

noncomputable section

variable (V H : Type*)
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The pivot map `H -> V'` induced by a continuous injection `J : V -> H`. -/
def gelfandPivot (J : V →L[ℝ] H) : H →L[ℝ] V →L[ℝ] ℝ :=
  ContinuousLinearMap.bilinearComp
    (isBoundedBilinearMap_inner (𝕜 := ℝ)).toContinuousLinearMap
    (ContinuousLinearMap.id ℝ H) J

@[simp]
theorem gelfandPivot_apply
    (J : V →L[ℝ] H) (h : H) (v : V) :
    gelfandPivot V H J h v = ⟪h, J v⟫_ℝ :=
  rfl

/-- A compact evolution triple with a contractive dense injection. The dual
embedding is the canonical pivot map constructed from `embedding`. -/
structure CompactGelfandTriple where
  embedding : V →L[ℝ] H
  embedding_injective : Injective embedding
  embedding_denseRange : DenseRange embedding
  embedding_compact : IsCompactOperator embedding
  embedding_contractive : ∀ v : V, ‖embedding v‖ ≤ ‖v‖

namespace CompactGelfandTriple

variable {V H : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The canonical injection of the pivot space into the energy dual. -/
def pivot (G : CompactGelfandTriple V H) : H →L[ℝ] V →L[ℝ] ℝ :=
  gelfandPivot V H G.embedding

@[simp]
theorem pivot_apply (G : CompactGelfandTriple V H) (h : H) (v : V) :
    G.pivot h v = ⟪h, G.embedding v⟫_ℝ :=
  rfl

/-- The pivot pairing is bounded by the product of the pivot and energy
norms. -/
theorem norm_pivot_apply_le
    (G : CompactGelfandTriple V H) (h : H) (v : V) :
    ‖G.pivot h v‖ ≤ ‖h‖ * ‖v‖ := by
  rw [G.pivot_apply, Real.norm_eq_abs]
  exact (abs_real_inner_le_norm h (G.embedding v)).trans
    (mul_le_mul_of_nonneg_left (G.embedding_contractive v) (norm_nonneg h))

/-- Density of `V` in `H` makes the canonical pivot map injective. -/
theorem pivot_injective (G : CompactGelfandTriple V H) :
    Injective G.pivot := by
  intro x y hxy
  apply G.embedding_denseRange.eq_of_inner_left (𝕜 := ℝ)
  intro v
  have hv := congrArg (fun ell : V →L[ℝ] ℝ => ell v) hxy
  simpa only [G.pivot_apply] using hv

/-- The pivot pairing restricted to two energy vectors is the `H` inner
product of their embedded states. -/
@[simp]
theorem pivot_embedding_apply
    (G : CompactGelfandTriple V H) (u v : V) :
    G.pivot (G.embedding u) v =
      ⟪G.embedding u, G.embedding v⟫_ℝ :=
  rfl

end CompactGelfandTriple

end
