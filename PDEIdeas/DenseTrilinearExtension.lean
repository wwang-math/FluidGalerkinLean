import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Extension of trilinear forms from a dense normed subspace

A continuous trilinear form extends along a dense uniform embedding by
successively extending and permuting its three arguments. The extension
agrees with the original form on the dense subspace and preserves skew
symmetry in the last two variables.
-/

noncomputable section

namespace ContinuousLinearMap

variable {D V : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Successive extension of the three variables of a continuous trilinear
form along one dense uniform embedding. -/
def trilinearExtend
    (T : D →L[ℝ] D →L[ℝ] D →L[ℝ] ℝ)
    (i : D →L[ℝ] V) :
    V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ := by
  let T₁ : V →L[ℝ] D →L[ℝ] D →L[ℝ] ℝ :=
    ContinuousLinearMap.extend (𝕜₂ := ℝ) (E := D) (Eₗ := V)
      (F := D →L[ℝ] D →L[ℝ] ℝ) T i
  let T₂ : V →L[ℝ] V →L[ℝ] D →L[ℝ] ℝ := T₁.flip.extend i
  let T₃ : V →L[ℝ] D →L[ℝ] V →L[ℝ] ℝ :=
    (flipₗᵢ ℝ V D ℝ).toContinuousLinearEquiv.toContinuousLinearMap.comp T₂
  let T₄ : V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ := T₃.flip.extend i
  let T₅ : V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ := T₄.flip
  let T₆ : V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ :=
    (flipₗᵢ ℝ V V ℝ).toContinuousLinearEquiv.toContinuousLinearMap.comp T₅
  exact T₆.flip

@[simp]
theorem trilinearExtend_apply
    (T : D →L[ℝ] D →L[ℝ] D →L[ℝ] ℝ)
    (i : D →L[ℝ] V)
    (hiDense : DenseRange i)
    (hiUniform : IsUniformInducing i)
    (u v w : D) :
    T.trilinearExtend i (i u) (i v) (i w) = T u v w := by
  simp [trilinearExtend, ContinuousLinearMap.extend_eq, hiDense, hiUniform]

/-- Skew symmetry in the last two variables passes from a dense subspace to
the trilinear extension. -/
theorem trilinearExtend_skew
    (T : D →L[ℝ] D →L[ℝ] D →L[ℝ] ℝ)
    (i : D →L[ℝ] V)
    (hiDense : DenseRange i)
    (hiUniform : IsUniformInducing i)
    (hskew : ∀ u v w, T u v w = -T u w v) :
    ∀ u v w, T.trilinearExtend i u v w = -T.trilinearExtend i u w v := by
  intro u v w
  refine DenseRange.induction_on₃ hiDense
    (p := fun u v w =>
      T.trilinearExtend i u v w = -T.trilinearExtend i u w v) ?_ ?_ u v w
  · let C := T.trilinearExtend i
    apply isClosed_eq
    · exact ((C.continuous.comp continuous_fst).clm_apply
        (continuous_fst.comp continuous_snd)).clm_apply
          (continuous_snd.comp continuous_snd)
    · exact (((C.continuous.comp continuous_fst).clm_apply
        (continuous_snd.comp continuous_snd)).clm_apply
          (continuous_fst.comp continuous_snd)).neg
  · intro a b c
    simp only [trilinearExtend_apply T i hiDense hiUniform]
    exact hskew a b c

/-- A continuous trilinear form on the ambient space is determined by its
values on a dense subspace in all three variables. -/
theorem trilinearExtend_unique
    (T : D →L[ℝ] D →L[ℝ] D →L[ℝ] ℝ)
    (i : D →L[ℝ] V)
    (hiDense : DenseRange i)
    (hiUniform : IsUniformInducing i)
    (S : V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ)
    (hS : ∀ u v w, S (i u) (i v) (i w) = T u v w) :
    T.trilinearExtend i = S := by
  ext u v w
  refine DenseRange.induction_on₃ hiDense
    (p := fun u v w => T.trilinearExtend i u v w = S u v w) ?_ ?_ u v w
  · apply isClosed_eq
    · let C := T.trilinearExtend i
      exact ((C.continuous.comp continuous_fst).clm_apply
        (continuous_fst.comp continuous_snd)).clm_apply
          (continuous_snd.comp continuous_snd)
    · exact ((S.continuous.comp continuous_fst).clm_apply
        (continuous_fst.comp continuous_snd)).clm_apply
          (continuous_snd.comp continuous_snd)
  · intro a b c
    rw [trilinearExtend_apply T i hiDense hiUniform]
    exact (hS a b c).symm

section Span

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A trilinear map on a generated submodule vanishes everywhere when it
vanishes on all triples of generators. -/
theorem trilinear_eq_zero_of_span
    (s : Set X)
    (T : Submodule.span ℝ s →L[ℝ]
      Submodule.span ℝ s →L[ℝ] Submodule.span ℝ s →L[ℝ] ℝ)
    (hT : ∀ x (hx : x ∈ s) y (hy : y ∈ s) z (hz : z ∈ s),
      T ⟨x, Submodule.subset_span hx⟩
        ⟨y, Submodule.subset_span hy⟩
        ⟨z, Submodule.subset_span hz⟩ = 0) :
    ∀ u v w, T u v w = 0 := by
  intro u
  refine Submodule.span_induction
    (p := fun x hx => ∀ v w, T ⟨x, hx⟩ v w = 0) ?_ ?_ ?_ ?_ u.property
  · intro x hx v
    refine Submodule.span_induction
      (p := fun y hy => ∀ w, T ⟨x, Submodule.subset_span hx⟩ ⟨y, hy⟩ w = 0)
      ?_ ?_ ?_ ?_ v.property
    · intro y hy w
      refine Submodule.span_induction
        (p := fun z hz => T
          ⟨x, Submodule.subset_span hx⟩
          ⟨y, Submodule.subset_span hy⟩ ⟨z, hz⟩ = 0)
        ?_ ?_ ?_ ?_ w.property
      · intro z hz
        exact hT x hx y hy z hz
      · change T ⟨x, Submodule.subset_span hx⟩
          ⟨y, Submodule.subset_span hy⟩
          ⟨0, Submodule.zero_mem _⟩ = 0
        rw [show (⟨0, Submodule.zero_mem _⟩ : Submodule.span ℝ s) = 0 by rfl]
        simp
      · intro z q hz hq hiz hiq
        rw [show (⟨z + q, Submodule.add_mem _ hz hq⟩ : Submodule.span ℝ s) =
          ⟨z, hz⟩ + ⟨q, hq⟩ by rfl]
        rw [map_add]
        simp only [hiz, hiq, add_zero]
      · intro c z hz hiz
        rw [show (⟨c • z, Submodule.smul_mem _ c hz⟩ : Submodule.span ℝ s) =
          c • ⟨z, hz⟩ by rfl]
        rw [map_smul]
        simp only [hiz, smul_zero]
    · intro w
      rw [show (⟨0, Submodule.zero_mem _⟩ : Submodule.span ℝ s) = 0 by rfl]
      simp
    · intro y z hy hz hiy hiz w
      rw [show (⟨y + z, Submodule.add_mem _ hy hz⟩ : Submodule.span ℝ s) =
        ⟨y, hy⟩ + ⟨z, hz⟩ by rfl]
      rw [map_add]
      simp only [ContinuousLinearMap.add_apply, hiy w, hiz w, add_zero]
    · intro c y hy hiy w
      rw [show (⟨c • y, Submodule.smul_mem _ c hy⟩ : Submodule.span ℝ s) =
        c • ⟨y, hy⟩ by rfl]
      rw [map_smul]
      simp only [ContinuousLinearMap.smul_apply, hiy w, smul_zero]
  · intro v w
    rw [show (⟨0, Submodule.zero_mem _⟩ : Submodule.span ℝ s) = 0 by rfl]
    simp
  · intro x y hx hy hix hiy v w
    rw [show (⟨x + y, Submodule.add_mem _ hx hy⟩ : Submodule.span ℝ s) =
      ⟨x, hx⟩ + ⟨y, hy⟩ by rfl]
    rw [map_add]
    simp only [ContinuousLinearMap.add_apply, hix v w, hiy v w, add_zero]
  · intro c x hx hix v w
    rw [show (⟨c • x, Submodule.smul_mem _ c hx⟩ : Submodule.span ℝ s) =
      c • ⟨x, hx⟩ by rfl]
    rw [map_smul]
    simp only [ContinuousLinearMap.smul_apply, hix v w, smul_zero]

/-- Defect of skew symmetry in the last two variables. -/
def skewDefectLast
    (T : D →L[ℝ] D →L[ℝ] D →L[ℝ] ℝ) :
    D →L[ℝ] D →L[ℝ] D →L[ℝ] ℝ :=
  T + (flipₗᵢ ℝ D D ℝ).toContinuousLinearEquiv.toContinuousLinearMap.comp T

@[simp]
theorem skewDefectLast_apply
    (T : D →L[ℝ] D →L[ℝ] D →L[ℝ] ℝ) (u v w : D) :
    skewDefectLast T u v w = T u v w + T u w v :=
  rfl

/-- Skew symmetry on generator triples extends to the submodule they span. -/
theorem trilinear_skew_of_span
    (s : Set X)
    (T : Submodule.span ℝ s →L[ℝ]
      Submodule.span ℝ s →L[ℝ] Submodule.span ℝ s →L[ℝ] ℝ)
    (hT : ∀ x (hx : x ∈ s) y (hy : y ∈ s) z (hz : z ∈ s),
      T ⟨x, Submodule.subset_span hx⟩
        ⟨y, Submodule.subset_span hy⟩
        ⟨z, Submodule.subset_span hz⟩ =
      -T ⟨x, Submodule.subset_span hx⟩
        ⟨z, Submodule.subset_span hz⟩
        ⟨y, Submodule.subset_span hy⟩) :
    ∀ u v w, T u v w = -T u w v := by
  have hzero : ∀ u v w, skewDefectLast T u v w = 0 := by
    apply trilinear_eq_zero_of_span s (skewDefectLast T)
    intro x hx y hy z hz
    change T ⟨x, Submodule.subset_span hx⟩
      ⟨y, Submodule.subset_span hy⟩
      ⟨z, Submodule.subset_span hz⟩ +
      T ⟨x, Submodule.subset_span hx⟩
        ⟨z, Submodule.subset_span hz⟩
        ⟨y, Submodule.subset_span hy⟩ = 0
    rw [hT x hx y hy z hz]
    exact neg_add_cancel _
  intro u v w
  have h := hzero u v w
  rw [skewDefectLast_apply] at h
  exact eq_neg_of_add_eq_zero_left h

end Span

end ContinuousLinearMap

end
