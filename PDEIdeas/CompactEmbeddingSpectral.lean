import PDEIdeas.CompactGelfandTriple
import PDEIdeas.GalerkinStrongCompactness
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Spectral coordinates for compact Hilbert embeddings

A compact, injective, dense linear map between separable real Hilbert spaces
admits singular coordinates. The construction applies the compact
self-adjoint spectral theorem to the Gram operator `J†J`, chooses an
orthonormal basis in each eigenspace, and normalizes the images under `J`.

The index type is allowed to be any countable type. An increasing finite
exhaustion then supplies the finite-dimensional Galerkin heads without
assuming in advance that the Hilbert spaces are infinite-dimensional.
-/

open Filter Function Metric Set InnerProductSpace Module
open scoped BigOperators NNReal RealInnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false

theorem Orthonormal.countable_index
    {ι E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [TopologicalSpace.SeparableSpace E]
    {v : ι → E} (hv : Orthonormal ℝ v) : Countable ι := by
  apply Pairwise.countable_of_isOpen_disjoint
    (s := fun i => Metric.ball (v i) (1 / 2 : ℝ))
  · intro i j hij
    apply Metric.ball_disjoint_ball
    have hinner : ⟪v i, v j⟫_ℝ = 0 := hv.2 hij
    have hsq := norm_sub_sq_eq_norm_sq_add_norm_sq_real hinner
    have hnormi : ‖v i‖ = 1 := hv.1 i
    have hnormj : ‖v j‖ = 1 := hv.1 j
    rw [hnormi, hnormj] at hsq
    have hdist : 1 ≤ dist (v i) (v j) := by
      rw [dist_eq_norm]
      nlinarith [norm_nonneg (v i - v j)]
    norm_num at hdist ⊢
    exact hdist
  · intro i
    exact Metric.isOpen_ball
  · intro i
    exact ⟨v i, Metric.mem_ball_self (by norm_num)⟩

section EigenBasis

variable {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [TopologicalSpace.SeparableSpace V]

def compactGramIndex (A : V →L[ℝ] V) :=
  Σ μ : ℝ, Fin (finrank ℝ (Module.End.eigenspace A.toLinearMap μ))

@[reducible] noncomputable def compactGramEigenspaceFiniteDimensional
    (A : V →L[ℝ] V) (hAcompact : IsCompactOperator A)
    (hAinjective : Function.Injective A) (μ : ℝ) :
    FiniteDimensional ℝ (Module.End.eigenspace A.toLinearMap μ) := by
  by_cases hμ : μ = 0
  · rw [hμ, Module.End.eigenspace_zero]
    rw [LinearMap.ker_eq_bot.mpr hAinjective]
    infer_instance
  · exact ContinuousLinearMap.finite_dimensional_eigenspace hAcompact μ hμ

noncomputable def compactGramEigenspaceBasis
    (A : V →L[ℝ] V) (hAcompact : IsCompactOperator A)
    (hAinjective : Function.Injective A) (μ : ℝ) :
    OrthonormalBasis
      (Fin (finrank ℝ (Module.End.eigenspace A.toLinearMap μ))) ℝ
      (Module.End.eigenspace A.toLinearMap μ) := by
  letI : FiniteDimensional ℝ (Module.End.eigenspace A.toLinearMap μ) :=
    compactGramEigenspaceFiniteDimensional A hAcompact hAinjective μ
  exact stdOrthonormalBasis ℝ (Module.End.eigenspace A.toLinearMap μ)

noncomputable def compactGramEigenVector
    (A : V →L[ℝ] V) (hAcompact : IsCompactOperator A)
    (hAinjective : Function.Injective A)
    (i : compactGramIndex A) : V :=
  compactGramEigenspaceBasis A hAcompact hAinjective i.1 i.2

theorem compactGramEigenVector_orthonormal
    (A : V →L[ℝ] V) (hAcompact : IsCompactOperator A)
    (hAinjective : Function.Injective A) (hAsymm : A.IsSymmetric) :
    Orthonormal ℝ (compactGramEigenVector A hAcompact hAinjective) := by
  simpa [compactGramEigenVector] using
    hAsymm.orthogonalFamily_eigenspaces.orthonormal_sigma_orthonormal
      (fun μ =>
        (compactGramEigenspaceBasis A hAcompact hAinjective μ).orthonormal)

theorem compactGramEigenVector_mem_eigenspace
    (A : V →L[ℝ] V) (hAcompact : IsCompactOperator A)
    (hAinjective : Function.Injective A) (i : compactGramIndex A) :
    compactGramEigenVector A hAcompact hAinjective i ∈
      Module.End.eigenspace A.toLinearMap i.1 :=
  (compactGramEigenspaceBasis A hAcompact hAinjective i.1 i.2).property

theorem compactGramEigenVector_apply
    (A : V →L[ℝ] V) (hAcompact : IsCompactOperator A)
    (hAinjective : Function.Injective A) (i : compactGramIndex A) :
    A (compactGramEigenVector A hAcompact hAinjective i) =
      i.1 • compactGramEigenVector A hAcompact hAinjective i :=
  Module.End.mem_eigenspace_iff.mp
    (compactGramEigenVector_mem_eigenspace A hAcompact hAinjective i)

theorem compactGramEigenVector_iSup_eigenspace_le_span
    (A : V →L[ℝ] V) (hAcompact : IsCompactOperator A)
    (hAinjective : Function.Injective A) :
    (⨆ μ : ℝ, Module.End.eigenspace A.toLinearMap μ) ≤
      Submodule.span ℝ
        (Set.range (compactGramEigenVector A hAcompact hAinjective)) := by
  refine iSup_le fun μ x hx => ?_
  let b := compactGramEigenspaceBasis A hAcompact hAinjective μ
  let x' : Module.End.eigenspace A.toLinearMap μ := ⟨x, hx⟩
  have hsum :
      ∑ i, (b.repr x').ofLp i • (b i : V) = x := by
    simpa [x'] using congrArg Subtype.val (b.sum_repr x')
  rw [← hsum]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact ⟨⟨μ, i⟩, rfl⟩

theorem compactGramEigenVector_span_orthogonal_eq_bot
    (A : V →L[ℝ] V) (hAcompact : IsCompactOperator A)
    (hAinjective : Function.Injective A) (hAsymm : A.IsSymmetric) :
    (Submodule.span ℝ
      (Set.range (compactGramEigenVector A hAcompact hAinjective)))ᗮ = ⊥ := by
  apply le_antisymm
  · rw [← ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
      hAcompact hAsymm]
    exact Submodule.orthogonal_le
      (compactGramEigenVector_iSup_eigenspace_le_span A hAcompact hAinjective)
  · exact bot_le

noncomputable def compactGramEigenBasis
    (A : V →L[ℝ] V) (hAcompact : IsCompactOperator A)
    (hAinjective : Function.Injective A) (hAsymm : A.IsSymmetric) :
    HilbertBasis (compactGramIndex A) ℝ V :=
  HilbertBasis.mkOfOrthogonalEqBot
    (compactGramEigenVector_orthonormal A hAcompact hAinjective hAsymm)
    (compactGramEigenVector_span_orthogonal_eq_bot
      A hAcompact hAinjective hAsymm)

@[simp] theorem compactGramEigenBasis_apply
    (A : V →L[ℝ] V) (hAcompact : IsCompactOperator A)
    (hAinjective : Function.Injective A) (hAsymm : A.IsSymmetric)
    (i : compactGramIndex A) :
    compactGramEigenBasis A hAcompact hAinjective hAsymm i =
      compactGramEigenVector A hAcompact hAinjective i := by
  simp [compactGramEigenBasis]

@[reducible] noncomputable def compactGramIndexCountable
    (A : V →L[ℝ] V) (hAcompact : IsCompactOperator A)
    (hAinjective : Function.Injective A) (hAsymm : A.IsSymmetric) :
    Countable (compactGramIndex A) :=
  Orthonormal.countable_index
    (compactGramEigenVector_orthonormal A hAcompact hAinjective hAsymm)

section CompactEmbedding

variable {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]

def compactEmbeddingGram (J : V →L[ℝ] H) : V →L[ℝ] V :=
  J.adjoint.comp J

theorem compactEmbeddingGram_isCompactOperator
    (J : V →L[ℝ] H) (hJcompact : IsCompactOperator J) :
    IsCompactOperator (compactEmbeddingGram J) := by
  simpa only [compactEmbeddingGram, ContinuousLinearMap.coe_comp'] using
    hJcompact.clm_comp J.adjoint

theorem compactEmbeddingGram_injective
    (J : V →L[ℝ] H) (hJinjective : Function.Injective J) :
    Function.Injective (compactEmbeddingGram J) := by
  simpa only [compactEmbeddingGram, ContinuousLinearMap.coe_comp'] using
    (J.adjoint_comp_self_injective_iff.mpr hJinjective)

theorem compactEmbeddingGram_positive (J : V →L[ℝ] H) :
    (compactEmbeddingGram J).IsPositive :=
  ContinuousLinearMap.isPositive_adjoint_comp_self J

theorem compactEmbeddingGram_symmetric (J : V →L[ℝ] H) :
    (compactEmbeddingGram J).IsSymmetric :=
  (compactEmbeddingGram_positive J).isSymmetric

def compactEmbeddingIndex (J : V →L[ℝ] H) :=
  compactGramIndex (compactEmbeddingGram J)

noncomputable def compactEmbeddingSourceVector
    (J : V →L[ℝ] H) (hJcompact : IsCompactOperator J)
    (hJinjective : Function.Injective J) : compactEmbeddingIndex J → V :=
  compactGramEigenVector (compactEmbeddingGram J)
    (compactEmbeddingGram_isCompactOperator J hJcompact)
    (compactEmbeddingGram_injective J hJinjective)

theorem compactEmbeddingSourceVector_orthonormal
    (J : V →L[ℝ] H) (hJcompact : IsCompactOperator J)
    (hJinjective : Function.Injective J) :
    Orthonormal ℝ (compactEmbeddingSourceVector J hJcompact hJinjective) :=
  compactGramEigenVector_orthonormal (compactEmbeddingGram J)
    (compactEmbeddingGram_isCompactOperator J hJcompact)
    (compactEmbeddingGram_injective J hJinjective)
    (compactEmbeddingGram_symmetric J)

theorem compactEmbeddingSourceVector_apply
    (J : V →L[ℝ] H) (hJcompact : IsCompactOperator J)
    (hJinjective : Function.Injective J) (i : compactEmbeddingIndex J) :
    compactEmbeddingGram J
        (compactEmbeddingSourceVector J hJcompact hJinjective i) =
      i.1 • compactEmbeddingSourceVector J hJcompact hJinjective i :=
  compactGramEigenVector_apply (compactEmbeddingGram J)
    (compactEmbeddingGram_isCompactOperator J hJcompact)
    (compactEmbeddingGram_injective J hJinjective) i

theorem compactEmbedding_image_sourceVector_norm_sq
    (J : V →L[ℝ] H) (hJcompact : IsCompactOperator J)
    (hJinjective : Function.Injective J) (i : compactEmbeddingIndex J) :
    ‖J (compactEmbeddingSourceVector J hJcompact hJinjective i)‖ ^ 2 = i.1 := by
  let e := compactEmbeddingSourceVector J hJcompact hJinjective i
  have heig := compactEmbeddingSourceVector_apply J hJcompact hJinjective i
  have henorm :=
    (compactEmbeddingSourceVector_orthonormal J hJcompact hJinjective).norm_eq_one i
  calc
    ‖J e‖ ^ 2 = ⟪J e, J e⟫_ℝ := (real_inner_self_eq_norm_sq (J e)).symm
    _ = ⟪e, J.adjoint (J e)⟫_ℝ := (J.adjoint_inner_right e (J e)).symm
    _ = ⟪e, compactEmbeddingGram J e⟫_ℝ := rfl
    _ = ⟪e, i.1 • e⟫_ℝ := by rw [heig]
    _ = i.1 * ‖e‖ ^ 2 := by rw [inner_smul_right, real_inner_self_eq_norm_sq]
    _ = i.1 := by rw [henorm]; norm_num

theorem compactEmbedding_eigenvalue_pos
    (J : V →L[ℝ] H) (hJcompact : IsCompactOperator J)
    (hJinjective : Function.Injective J) (i : compactEmbeddingIndex J) :
    0 < i.1 := by
  have hsq := compactEmbedding_image_sourceVector_norm_sq
    J hJcompact hJinjective i
  have hnonneg : 0 ≤ i.1 := by
    rw [← hsq]
    positivity
  have hne : i.1 ≠ 0 := by
    intro hi
    let e := compactEmbeddingSourceVector J hJcompact hJinjective i
    have heig := compactEmbeddingSourceVector_apply J hJcompact hJinjective i
    have hAe : compactEmbeddingGram J e = 0 := by simpa [hi] using heig
    have he : e = 0 :=
      compactEmbeddingGram_injective J hJinjective (by simpa using hAe)
    exact (compactEmbeddingSourceVector_orthonormal J hJcompact hJinjective).ne_zero i he
  exact lt_of_le_of_ne hnonneg hne.symm

noncomputable def compactEmbeddingWeight
    (J : V →L[ℝ] H) : compactEmbeddingIndex J → ℝ :=
  fun i => Real.sqrt i.1

theorem compactEmbeddingWeight_pos
    (J : V →L[ℝ] H) (hJcompact : IsCompactOperator J)
    (hJinjective : Function.Injective J) (i : compactEmbeddingIndex J) :
    0 < compactEmbeddingWeight J i := by
  exact Real.sqrt_pos.2
    (compactEmbedding_eigenvalue_pos J hJcompact hJinjective i)

theorem compactEmbeddingWeight_ne_zero
    (J : V →L[ℝ] H) (hJcompact : IsCompactOperator J)
    (hJinjective : Function.Injective J) (i : compactEmbeddingIndex J) :
    compactEmbeddingWeight J i ≠ 0 :=
  ne_of_gt (compactEmbeddingWeight_pos J hJcompact hJinjective i)

theorem compactEmbeddingWeight_sq
    (J : V →L[ℝ] H) (hJcompact : IsCompactOperator J)
    (hJinjective : Function.Injective J) (i : compactEmbeddingIndex J) :
    compactEmbeddingWeight J i ^ 2 = i.1 := by
  exact Real.sq_sqrt
    (compactEmbedding_eigenvalue_pos J hJcompact hJinjective i).le

noncomputable def compactEmbeddingSourceBasis
    (J : V →L[ℝ] H) (hJcompact : IsCompactOperator J)
    (hJinjective : Function.Injective J) :
    HilbertBasis (compactEmbeddingIndex J) ℝ V :=
  compactGramEigenBasis (compactEmbeddingGram J)
    (compactEmbeddingGram_isCompactOperator J hJcompact)
    (compactEmbeddingGram_injective J hJinjective)
    (compactEmbeddingGram_symmetric J)

@[simp] theorem compactEmbeddingSourceBasis_apply
    (J : V →L[ℝ] H) (hJcompact : IsCompactOperator J)
    (hJinjective : Function.Injective J) (i : compactEmbeddingIndex J) :
    compactEmbeddingSourceBasis J hJcompact hJinjective i =
      compactEmbeddingSourceVector J hJcompact hJinjective i := by
  exact compactGramEigenBasis_apply (compactEmbeddingGram J)
    (compactEmbeddingGram_isCompactOperator J hJcompact)
    (compactEmbeddingGram_injective J hJinjective)
    (compactEmbeddingGram_symmetric J) i

@[reducible] noncomputable def compactEmbeddingIndexCountable
    (J : V →L[ℝ] H) (hJcompact : IsCompactOperator J)
    (hJinjective : Function.Injective J) : Countable (compactEmbeddingIndex J) :=
  compactGramIndexCountable (compactEmbeddingGram J)
    (compactEmbeddingGram_isCompactOperator J hJcompact)
    (compactEmbeddingGram_injective J hJinjective)
    (compactEmbeddingGram_symmetric J)

theorem compactEmbedding_image_sourceVector_inner
    (J : V →L[ℝ] H) (hJcompact : IsCompactOperator J)
    (hJinjective : Function.Injective J) (i j : compactEmbeddingIndex J) :
    ⟪J (compactEmbeddingSourceVector J hJcompact hJinjective i),
      J (compactEmbeddingSourceVector J hJcompact hJinjective j)⟫_ℝ =
      j.1 *
        ⟪compactEmbeddingSourceVector J hJcompact hJinjective i,
          compactEmbeddingSourceVector J hJcompact hJinjective j⟫_ℝ := by
  let ei := compactEmbeddingSourceVector J hJcompact hJinjective i
  let ej := compactEmbeddingSourceVector J hJcompact hJinjective j
  have hej := compactEmbeddingSourceVector_apply J hJcompact hJinjective j
  calc
    ⟪J ei, J ej⟫_ℝ = ⟪ei, J.adjoint (J ej)⟫_ℝ :=
      (J.adjoint_inner_right ei (J ej)).symm
    _ = ⟪ei, compactEmbeddingGram J ej⟫_ℝ := rfl
    _ = ⟪ei, j.1 • ej⟫_ℝ := by rw [hej]
    _ = j.1 * ⟪ei, ej⟫_ℝ := by rw [inner_smul_right]

theorem compactEmbedding_image_sourceVector_norm
    (J : V →L[ℝ] H) (hJcompact : IsCompactOperator J)
    (hJinjective : Function.Injective J) (i : compactEmbeddingIndex J) :
    ‖J (compactEmbeddingSourceVector J hJcompact hJinjective i)‖ =
      compactEmbeddingWeight J i := by
  have hsq := compactEmbedding_image_sourceVector_norm_sq
    J hJcompact hJinjective i
  have hweightSq := compactEmbeddingWeight_sq J hJcompact hJinjective i
  have himageNonneg := norm_nonneg
    (J (compactEmbeddingSourceVector J hJcompact hJinjective i))
  have hweightNonneg :=
    (compactEmbeddingWeight_pos J hJcompact hJinjective i).le
  nlinarith

noncomputable def compactEmbeddingStateVector
    (J : V →L[ℝ] H) (hJcompact : IsCompactOperator J)
    (hJinjective : Function.Injective J) : compactEmbeddingIndex J → H :=
  fun i => (compactEmbeddingWeight J i)⁻¹ •
    J (compactEmbeddingSourceVector J hJcompact hJinjective i)

theorem compactEmbedding_basis_map
    (J : V →L[ℝ] H) (hJcompact : IsCompactOperator J)
    (hJinjective : Function.Injective J) (i : compactEmbeddingIndex J) :
    J (compactEmbeddingSourceVector J hJcompact hJinjective i) =
      compactEmbeddingWeight J i •
        compactEmbeddingStateVector J hJcompact hJinjective i := by
  simp [compactEmbeddingStateVector, smul_smul,
    compactEmbeddingWeight_ne_zero J hJcompact hJinjective i]

/-- The state coordinate of an embedded vector is its source coordinate
multiplied by the corresponding singular weight. -/
theorem compactEmbedding_inner_stateVector
    (J : V →L[ℝ] H) (hJcompact : IsCompactOperator J)
    (hJinjective : Function.Injective J)
    (u : V) (i : compactEmbeddingIndex J) :
    ⟪J u, compactEmbeddingStateVector J hJcompact hJinjective i⟫_ℝ =
      compactEmbeddingWeight J i *
        ⟪u, compactEmbeddingSourceVector J hJcompact hJinjective i⟫_ℝ := by
  let e := compactEmbeddingSourceVector J hJcompact hJinjective i
  let w := compactEmbeddingWeight J i
  have heig := compactEmbeddingSourceVector_apply J hJcompact hJinjective i
  have hwsq := compactEmbeddingWeight_sq J hJcompact hJinjective i
  have hwne := compactEmbeddingWeight_ne_zero J hJcompact hJinjective i
  calc
    ⟪J u, compactEmbeddingStateVector J hJcompact hJinjective i⟫_ℝ =
        w⁻¹ * ⟪J u, J e⟫_ℝ := by
      rw [compactEmbeddingStateVector, inner_smul_right]
    _ = w⁻¹ * ⟪u, J.adjoint (J e)⟫_ℝ := by
      rw [J.adjoint_inner_right]
    _ = w⁻¹ * ⟪u, compactEmbeddingGram J e⟫_ℝ := rfl
    _ = w⁻¹ * ⟪u, i.1 • e⟫_ℝ := by rw [heig]
    _ = w⁻¹ * (i.1 * ⟪u, e⟫_ℝ) := by rw [inner_smul_right]
    _ = w * ⟪u, e⟫_ℝ := by
      dsimp [w] at hwsq hwne ⊢
      rw [← hwsq]
      field_simp [hwne]

theorem compactEmbeddingStateVector_orthonormal
    (J : V →L[ℝ] H) (hJcompact : IsCompactOperator J)
    (hJinjective : Function.Injective J) :
    Orthonormal ℝ (compactEmbeddingStateVector J hJcompact hJinjective) := by
  constructor
  · intro i
    rw [compactEmbeddingStateVector, norm_smul,
      compactEmbedding_image_sourceVector_norm J hJcompact hJinjective i]
    have hw := compactEmbeddingWeight_pos J hJcompact hJinjective i
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos hw, inv_mul_cancel₀ hw.ne']
  · intro i j hij
    rw [compactEmbeddingStateVector, compactEmbeddingStateVector,
      inner_smul_left, inner_smul_right,
      compactEmbedding_image_sourceVector_inner J hJcompact hJinjective i j]
    rw [(compactEmbeddingSourceVector_orthonormal J hJcompact hJinjective).2 hij]
    simp

theorem compactEmbeddingStateVector_span_orthogonal_eq_bot
    (J : V →L[ℝ] H) (hJcompact : IsCompactOperator J)
    (hJinjective : Function.Injective J) (hJdense : DenseRange J) :
    (Submodule.span ℝ
      (Set.range (compactEmbeddingStateVector J hJcompact hJinjective)))ᗮ = ⊥ := by
  apply le_antisymm
  · intro x hx
    change x = 0
    have hadjoint : J.adjoint x = 0 := by
      let b := compactEmbeddingSourceBasis J hJcompact hJinjective
      apply b.repr.injective
      ext i
      have hstate :
          ⟪compactEmbeddingStateVector J hJcompact hJinjective i, x⟫_ℝ = 0 :=
        hx _ (Submodule.subset_span ⟨i, rfl⟩)
      have himage :
          ⟪J (compactEmbeddingSourceVector J hJcompact hJinjective i), x⟫_ℝ = 0 := by
        rw [compactEmbedding_basis_map J hJcompact hJinjective i,
          inner_smul_left, hstate, mul_zero]
      simpa [HilbertBasis.repr_apply_apply, b,
        compactEmbeddingSourceBasis_apply] using
        (J.adjoint_inner_right
          (compactEmbeddingSourceVector J hJcompact hJinjective i) x).trans himage
    apply hJdense.eq_zero_of_inner_right (𝕜 := ℝ)
    intro v
    rw [← J.adjoint_inner_right, hadjoint, inner_zero_right]
  · exact bot_le

noncomputable def compactEmbeddingStateBasis
    (J : V →L[ℝ] H) (hJcompact : IsCompactOperator J)
    (hJinjective : Function.Injective J) (hJdense : DenseRange J) :
    HilbertBasis (compactEmbeddingIndex J) ℝ H :=
  HilbertBasis.mkOfOrthogonalEqBot
    (compactEmbeddingStateVector_orthonormal J hJcompact hJinjective)
    (compactEmbeddingStateVector_span_orthogonal_eq_bot
      J hJcompact hJinjective hJdense)

@[simp] theorem compactEmbeddingStateBasis_apply
    (J : V →L[ℝ] H) (hJcompact : IsCompactOperator J)
    (hJinjective : Function.Injective J) (hJdense : DenseRange J)
    (i : compactEmbeddingIndex J) :
    compactEmbeddingStateBasis J hJcompact hJinjective hJdense i =
      compactEmbeddingStateVector J hJcompact hJinjective i := by
  simp [compactEmbeddingStateBasis]

theorem compactEmbeddingWeight_norm_le_one
    (J : V →L[ℝ] H) (hJcompact : IsCompactOperator J)
    (hJinjective : Function.Injective J)
    (hJcontractive : ∀ v, ‖J v‖ ≤ ‖v‖)
    (i : compactEmbeddingIndex J) :
    ‖compactEmbeddingWeight J i‖ ≤ 1 := by
  have h := hJcontractive
    (compactEmbeddingSourceVector J hJcompact hJinjective i)
  rw [compactEmbedding_image_sourceVector_norm J hJcompact hJinjective i,
    (compactEmbeddingSourceVector_orthonormal J hJcompact hJinjective).norm_eq_one i]
    at h
  simpa [Real.norm_eq_abs, abs_of_pos
    (compactEmbeddingWeight_pos J hJcompact hJinjective i)] using h

end CompactEmbedding

end EigenBasis


/-- Singular coordinates for a compact dense injection. -/
structure CompactEmbeddingSpectralRepresentation
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (J : V →L[ℝ] H) where
  Index : Type
  exhaustion : HilbertBasisExhaustion Index
  energyBasis : HilbertBasis Index ℝ V
  stateBasis : HilbertBasis Index ℝ H
  weight : Index → ℝ
  weight_norm_le_one : ∀ i, ‖weight i‖ ≤ 1
  weight_ne_zero : ∀ i, weight i ≠ 0
  basis_map : ∀ i, J (energyBasis i) = weight i • stateBasis i
  coordinate_map : ∀ u i,
    ⟪J u, stateBasis i⟫_ℝ = weight i * ⟪u, energyBasis i⟫_ℝ
  embedding_injective : Function.Injective J
  embedding_denseRange : DenseRange J
  embedding_compact : IsCompactOperator J

namespace CompactEmbeddingSpectralRepresentation

variable {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {J : V →L[ℝ] H}

/-- The finite source-space head selected by the exhaustion. -/
def energySpace (S : CompactEmbeddingSpectralRepresentation J) (m : ℕ) :
    Submodule ℝ V :=
  GalerkinProjectorSequence.finitePartialSpace
    S.energyBasis (S.exhaustion.head m)

/-- The finite state-space head selected by the exhaustion. -/
def stateSpace (S : CompactEmbeddingSpectralRepresentation J) (m : ℕ) :
    Submodule ℝ H :=
  GalerkinProjectorSequence.finitePartialSpace
    S.stateBasis (S.exhaustion.head m)

/-- Orthogonal projection onto the finite source-space head. -/
noncomputable def energyProjection
    (S : CompactEmbeddingSpectralRepresentation J) (m : ℕ) : V →L[ℝ] V :=
  GalerkinProjectorSequence.finitePartialProjection
    S.energyBasis (S.exhaustion.head m)

/-- Orthogonal projection onto the finite state-space head. -/
noncomputable def stateProjection
    (S : CompactEmbeddingSpectralRepresentation J) (m : ℕ) : H →L[ℝ] H :=
  GalerkinProjectorSequence.finitePartialProjection
    S.stateBasis (S.exhaustion.head m)

/-- The exhausted source-basis projector sequence. -/
noncomputable def energyProjectorSequence
    (S : CompactEmbeddingSpectralRepresentation J) :
    GalerkinProjectorSequence V :=
  GalerkinProjectorSequence.ofHilbertBasisExhaustion
    S.energyBasis S.exhaustion

/-- The exhausted state-basis projector sequence. -/
noncomputable def stateProjectorSequence
    (S : CompactEmbeddingSpectralRepresentation J) :
    GalerkinProjectorSequence H :=
  GalerkinProjectorSequence.ofHilbertBasisExhaustion
    S.stateBasis S.exhaustion

end CompactEmbeddingSpectralRepresentation

/-- Construction of singular coordinates from compactness, injectivity,
density, and contractivity of an embedding. -/
noncomputable def compactEmbeddingSpectralRepresentation
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [TopologicalSpace.SeparableSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (J : V →L[ℝ] H)
    (hJcompact : IsCompactOperator J)
    (hJinjective : Function.Injective J)
    (hJdense : DenseRange J)
    (hJcontractive : ∀ v, ‖J v‖ ≤ ‖v‖) :
    CompactEmbeddingSpectralRepresentation J where
  Index := compactEmbeddingIndex J
  exhaustion := by
    letI : Countable (compactEmbeddingIndex J) :=
      compactEmbeddingIndexCountable J hJcompact hJinjective
    exact HilbertBasisExhaustion.ofCountable
  energyBasis := compactEmbeddingSourceBasis J hJcompact hJinjective
  stateBasis := compactEmbeddingStateBasis J hJcompact hJinjective hJdense
  weight := compactEmbeddingWeight J
  weight_norm_le_one :=
    compactEmbeddingWeight_norm_le_one J hJcompact hJinjective hJcontractive
  weight_ne_zero :=
    compactEmbeddingWeight_ne_zero J hJcompact hJinjective
  basis_map := by
    intro i
    rw [compactEmbeddingSourceBasis_apply,
      compactEmbeddingStateBasis_apply]
    exact compactEmbedding_basis_map J hJcompact hJinjective i
  coordinate_map := by
    intro u i
    rw [compactEmbeddingSourceBasis_apply,
      compactEmbeddingStateBasis_apply]
    exact compactEmbedding_inner_stateVector J hJcompact hJinjective u i
  embedding_injective := hJinjective
  embedding_denseRange := hJdense
  embedding_compact := hJcompact

namespace CompactGelfandTriple

variable {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [TopologicalSpace.SeparableSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]

/-- Every compact Gelfand triple between separable Hilbert spaces has
singular coordinates. -/
noncomputable def spectralRepresentation
    (G : CompactGelfandTriple V H) :
    CompactEmbeddingSpectralRepresentation G.embedding :=
  compactEmbeddingSpectralRepresentation
    G.embedding G.embedding_compact G.embedding_injective
      G.embedding_denseRange G.embedding_contractive

end CompactGelfandTriple

end
