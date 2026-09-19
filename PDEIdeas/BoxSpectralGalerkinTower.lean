import PDEIdeas.BoxSpectralCompactness

/-!
# The spectral Galerkin tower on a rectangular box

The singular coordinates of the compact box embedding determine increasing
finite-dimensional Galerkin spaces. An arbitrary countable basis index is
handled by an increasing finite exhaustion, so the construction covers both
finite- and infinite-dimensional Hilbert spaces without a hard-coded
enumeration.
-/

open InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

variable {n : ℕ}

local instance boxSpectralTowerStateUniform
    (I : BoxIntegral.Box (Fin (n + 1))) :
    IsUniformAddGroup (BoxL2Sigma I) :=
  (smoothBoxVelocityCore I).topologicalClosure.toAddSubgroup.isUniformAddGroup

local instance boxSpectralTowerEnergyUniform
    (I : BoxIntegral.Box (Fin (n + 1))) :
    IsUniformAddGroup (BoxH1ZeroSigma I) :=
  (smoothBoxGraphCore I).topologicalClosure.toAddSubgroup.isUniformAddGroup

namespace BoxCompactSpectralRepresentation

def energyMode
    {I : BoxIntegral.Box (Fin (n + 1))}
    (S : BoxCompactSpectralRepresentation I) (k : S.Index) :
    BoxH1ZeroSigma I :=
  (S.weight k)⁻¹ • S.energyBasis k

@[simp]
theorem boxEnergyToState_energyBasis
    {I : BoxIntegral.Box (Fin (n + 1))}
    (S : BoxCompactSpectralRepresentation I) (k : S.Index) :
    boxEnergyToState I (S.energyBasis k) =
      S.weight k • S.stateBasis k :=
  S.basis_map k

@[simp]
theorem boxEnergyToState_energyMode
    {I : BoxIntegral.Box (Fin (n + 1))}
    (S : BoxCompactSpectralRepresentation I) (k : S.Index) :
    boxEnergyToState I (S.energyMode k) = S.stateBasis k := by
  rw [energyMode, map_smul, S.boxEnergyToState_energyBasis]
  rw [inv_smul_smul₀ (S.weight_ne_zero k)]

abbrev CoefficientSpace
    {I : BoxIntegral.Box (Fin (n + 1))}
    (S : BoxCompactSpectralRepresentation I) (m : ℕ) :=
  S.stateSpace m

@[reducible] def coefficientSpaceNormedAddCommGroup
    {I : BoxIntegral.Box (Fin (n + 1))}
    (S : BoxCompactSpectralRepresentation I) (m : ℕ) :
    NormedAddCommGroup (S.CoefficientSpace m) :=
  Submodule.normedAddCommGroup (S.CoefficientSpace m)

@[reducible] def coefficientSpaceNormedSpace
    {I : BoxIntegral.Box (Fin (n + 1))}
    (S : BoxCompactSpectralRepresentation I) (m : ℕ) :
    NormedSpace ℝ (S.CoefficientSpace m) :=
  Submodule.normedSpace (S.CoefficientSpace m)

@[reducible] def coefficientSpaceInnerProductSpace
    {I : BoxIntegral.Box (Fin (n + 1))}
    (S : BoxCompactSpectralRepresentation I) (m : ℕ) :
    InnerProductSpace ℝ (S.CoefficientSpace m) :=
  Submodule.innerProductSpace (S.CoefficientSpace m)

@[reducible] noncomputable def coefficientSpaceFiniteDimensional
    {I : BoxIntegral.Box (Fin (n + 1))}
    (S : BoxCompactSpectralRepresentation I) (m : ℕ) :
    FiniteDimensional ℝ (S.CoefficientSpace m) :=
  GalerkinProjectorSequence.finitePartialSpace_finiteDimensional
    S.stateBasis (S.exhaustion.head m)

/-- Finite reconstruction from state coordinates to their energy
representatives. -/
noncomputable def energyHeadReconstruction
    {I : BoxIntegral.Box (Fin (n + 1))}
    (S : BoxCompactSpectralRepresentation I) (m : ℕ) :
    BoxL2Sigma I →L[ℝ] BoxH1ZeroSigma I :=
  ∑ i ∈ S.exhaustion.head m,
    InnerProductSpace.rankOne ℝ (S.energyMode i) (S.stateBasis i)

@[simp]
theorem energyHeadReconstruction_apply
    {I : BoxIntegral.Box (Fin (n + 1))}
    (S : BoxCompactSpectralRepresentation I) (m : ℕ)
    (x : BoxL2Sigma I) :
    S.energyHeadReconstruction m x =
      ∑ i ∈ S.exhaustion.head m,
        ⟪S.stateBasis i, x⟫_ℝ • S.energyMode i := by
  exact ContinuousLinearMap.sum_apply
    (S.exhaustion.head m)
    (fun i => InnerProductSpace.rankOne ℝ (S.energyMode i) (S.stateBasis i)) x

set_option maxHeartbeats 800000 in
@[simp]
theorem boxEnergyToState_energyHeadReconstruction_of_mem
    {I : BoxIntegral.Box (Fin (n + 1))}
    (S : BoxCompactSpectralRepresentation I) (m : ℕ)
    (x : BoxL2Sigma I) (hx : x ∈ S.stateSpace m) :
    boxEnergyToState I (S.energyHeadReconstruction m x) = x := by
  calc
    boxEnergyToState I (S.energyHeadReconstruction m x) =
        ∑ i ∈ S.exhaustion.head m,
          ⟪S.stateBasis i, x⟫_ℝ • S.stateBasis i := by
      rw [S.energyHeadReconstruction_apply, map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_smul, S.boxEnergyToState_energyMode]
    _ = S.stateProjection m x := by
      rw [CompactEmbeddingSpectralRepresentation.stateProjection,
        GalerkinProjectorSequence.finitePartialProjection_apply_eq_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [real_inner_comm]
      rfl
    _ = x := by
      exact GalerkinProjectorSequence.finitePartialProjection_fixed
        S.stateBasis (S.exhaustion.head m) x hx

def energySynthesis
    {I : BoxIntegral.Box (Fin (n + 1))}
    (S : BoxCompactSpectralRepresentation I) (m : ℕ) :
    S.CoefficientSpace m →L[ℝ] BoxH1ZeroSigma I :=
  (S.energyHeadReconstruction m).comp (S.stateSpace m).subtypeL

def stateSynthesis
    {I : BoxIntegral.Box (Fin (n + 1))}
    (S : BoxCompactSpectralRepresentation I) (m : ℕ) :
    S.CoefficientSpace m →L[ℝ] BoxL2Sigma I :=
  (S.stateSpace m).subtypeL

@[simp]
theorem stateSynthesis_apply
    {I : BoxIntegral.Box (Fin (n + 1))}
    (S : BoxCompactSpectralRepresentation I) (m : ℕ)
    (u : S.CoefficientSpace m) :
    S.stateSynthesis m u = (u : BoxL2Sigma I) :=
  rfl

@[simp]
theorem boxEnergyToState_energySynthesis
    {I : BoxIntegral.Box (Fin (n + 1))}
    (S : BoxCompactSpectralRepresentation I) (m : ℕ)
    (u : S.CoefficientSpace m) :
    boxEnergyToState I (S.energySynthesis m u) = S.stateSynthesis m u := by
  exact S.boxEnergyToState_energyHeadReconstruction_of_mem
    m (u : BoxL2Sigma I) u.property

@[simp]
theorem norm_stateSynthesis
    {I : BoxIntegral.Box (Fin (n + 1))}
    (S : BoxCompactSpectralRepresentation I) (m : ℕ)
    (u : S.CoefficientSpace m) :
    ‖S.stateSynthesis m u‖ = ‖u‖ :=
  rfl

theorem stateSynthesis_isometry
    {I : BoxIntegral.Box (Fin (n + 1))}
    (S : BoxCompactSpectralRepresentation I) (m : ℕ) :
    Isometry (S.stateSynthesis m) := by
  intro u v
  rfl

theorem energySynthesis_injective
    {I : BoxIntegral.Box (Fin (n + 1))}
    (S : BoxCompactSpectralRepresentation I) (m : ℕ) :
    Function.Injective (S.energySynthesis m) := by
  intro u v huv
  apply Subtype.ext
  have h := congrArg (boxEnergyToState I) huv
  simpa only [S.boxEnergyToState_energySynthesis, S.stateSynthesis_apply] using h

theorem coefficientSpace_monotone
    {I : BoxIntegral.Box (Fin (n + 1))}
    (S : BoxCompactSpectralRepresentation I) :
    Monotone S.CoefficientSpace := by
  intro m k hmk
  exact GalerkinProjectorSequence.finitePartialSpace_mono S.stateBasis
    (S.exhaustion.monotone hmk)

theorem coefficientSpace_dense
    {I : BoxIntegral.Box (Fin (n + 1))}
    (S : BoxCompactSpectralRepresentation I) :
    ⊤ ≤ (⨆ m, S.CoefficientSpace m).topologicalClosure :=
  GalerkinProjectorSequence.finitePartialSpace_exhaustion_dense
    S.stateBasis S.exhaustion

@[reducible] noncomputable def coefficientSpaceCompleteSpace
    {I : BoxIntegral.Box (Fin (n + 1))}
    (S : BoxCompactSpectralRepresentation I) (m : ℕ) :
    CompleteSpace (S.CoefficientSpace m) := by
  letI : IsUniformAddGroup (BoxL2Sigma I) :=
    (smoothBoxVelocityCore I).topologicalClosure.toAddSubgroup.isUniformAddGroup
  letI : FiniteDimensional ℝ (S.CoefficientSpace m) :=
    S.coefficientSpaceFiniteDimensional m
  letI : IsUniformAddGroup (S.CoefficientSpace m) :=
    (S.CoefficientSpace m).toAddSubgroup.isUniformAddGroup
  exact FiniteDimensional.complete ℝ _

noncomputable def testProjection
    {I : BoxIntegral.Box (Fin (n + 1))}
    (S : BoxCompactSpectralRepresentation I) (m : ℕ) :
    BoxH1ZeroSigma I →L[ℝ] S.CoefficientSpace m := by
  let P : BoxL2Sigma I →L[ℝ] S.CoefficientSpace m :=
    (S.stateProjection m).codRestrict (S.stateSpace m) fun x => by
      change GalerkinProjectorSequence.finitePartialProjection
          S.stateBasis (S.exhaustion.head m) x ∈
        GalerkinProjectorSequence.finitePartialSpace
          S.stateBasis (S.exhaustion.head m)
      rw [← GalerkinProjectorSequence.range_finitePartialProjection]
      exact ⟨x, rfl⟩
  exact P.comp (boxEnergyToState I)

/-- Orthogonal state projection is invisible when paired against a
coefficient state already in the finite spectral space. -/
theorem inner_testProjection_eq_state_inner
    {I : BoxIntegral.Box (Fin (n + 1))}
    (S : BoxCompactSpectralRepresentation I) (m : ℕ)
    (u : S.CoefficientSpace m) (φ : BoxH1ZeroSigma I) :
    ⟪u, S.testProjection m φ⟫_ℝ =
      ⟪S.stateSynthesis m u, boxEnergyToState I φ⟫_ℝ := by
  change
    ⟪(u : BoxL2Sigma I),
      (S.stateProjectorSequence.galerkinProjectionAt m).proj
        (boxEnergyToState I φ)⟫_ℝ =
      ⟪(u : BoxL2Sigma I), boxEnergyToState I φ⟫_ℝ
  have horth :=
    (GalerkinProjectorSequence.ofHilbertBasisExhaustion_isOrthogonal
      S.stateBasis S.exhaustion m) (boxEnergyToState I φ) u
  calc
    ⟪(u : BoxL2Sigma I),
        (S.stateProjectorSequence.galerkinProjectionAt m).proj
          (boxEnergyToState I φ)⟫_ℝ =
        ⟪(S.stateProjectorSequence.galerkinProjectionAt m).proj
          (boxEnergyToState I φ), (u : BoxL2Sigma I)⟫_ℝ := real_inner_comm _ _
    _ = ⟪boxEnergyToState I φ, (u : BoxL2Sigma I)⟫_ℝ := horth
    _ = ⟪(u : BoxL2Sigma I), boxEnergyToState I φ⟫_ℝ := real_inner_comm _ _

theorem inner_testProjection_energyMode
    {I : BoxIntegral.Box (Fin (n + 1))}
    (S : BoxCompactSpectralRepresentation I) (m : ℕ) (i : S.Index)
    (u : S.CoefficientSpace m) :
    ⟪u, S.testProjection m (S.energyMode i)⟫_ℝ =
      ⟪S.stateSynthesis m u, S.stateBasis i⟫_ℝ := by
  calc
    ⟪u, S.testProjection m (S.energyMode i)⟫_ℝ =
        ⟪S.stateSynthesis m u,
          boxEnergyToState I (S.energyMode i)⟫_ℝ :=
      S.inner_testProjection_eq_state_inner m u (S.energyMode i)
    _ = ⟪S.stateSynthesis m u, S.stateBasis i⟫_ℝ :=
      congrArg (⟪S.stateSynthesis m u, ·⟫_ℝ)
        (S.boxEnergyToState_energyMode i)

/-- Spectral coordinates of the box embedding are multiplied by the singular
weights. -/
theorem inner_boxEnergyToState_stateBasis
    {I : BoxIntegral.Box (Fin (n + 1))}
    (S : BoxCompactSpectralRepresentation I)
    (u : BoxH1ZeroSigma I) (k : S.Index) :
    ⟪boxEnergyToState I u, S.stateBasis k⟫_ℝ =
      S.weight k * ⟪u, S.energyBasis k⟫_ℝ :=
  S.coordinate_map u k

theorem energyHeadReconstruction_stateBasis_of_mem
    {I : BoxIntegral.Box (Fin (n + 1))}
    (S : BoxCompactSpectralRepresentation I) {m : ℕ} {i : S.Index}
    (hi : i ∈ S.exhaustion.head m) :
    S.energyHeadReconstruction m (S.stateBasis i) = S.energyMode i := by
  apply boxEnergyToState_injective I
  have himem : S.stateBasis i ∈ S.stateSpace m :=
    Submodule.subset_span ⟨i, hi, rfl⟩
  rw [S.boxEnergyToState_energyHeadReconstruction_of_mem m _ himem,
    S.boxEnergyToState_energyMode]

set_option maxHeartbeats 800000 in
/-- Reconstruction of the common state-space test projection is precisely
the source-basis orthogonal projection. -/
theorem energySynthesis_testProjection_eq_partialProjection
    {I : BoxIntegral.Box (Fin (n + 1))}
    (S : BoxCompactSpectralRepresentation I) (m : ℕ)
    (u : BoxH1ZeroSigma I) :
    S.energySynthesis m (S.testProjection m u) =
      S.energyProjection m u := by
  change S.energyHeadReconstruction m
      (S.stateProjection m (boxEnergyToState I u)) =
    S.energyProjection m u
  calc
    S.energyHeadReconstruction m
        (S.stateProjection m (boxEnergyToState I u)) =
        S.energyHeadReconstruction m
          (∑ i ∈ S.exhaustion.head m,
            ⟪boxEnergyToState I u, S.stateBasis i⟫_ℝ • S.stateBasis i) := by
      congr 1
      exact GalerkinProjectorSequence.finitePartialProjection_apply_eq_sum
        S.stateBasis (S.exhaustion.head m) (boxEnergyToState I u)
    _ = ∑ i ∈ S.exhaustion.head m,
        ⟪u, S.energyBasis i⟫_ℝ • S.energyBasis i := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_smul, S.energyHeadReconstruction_stateBasis_of_mem hi,
        S.inner_boxEnergyToState_stateBasis]
      simp only [energyMode, smul_smul]
      congr 1
      field_simp [S.weight_ne_zero i]
    _ = S.energyProjection m u := by
      symm
      exact GalerkinProjectorSequence.finitePartialProjection_apply_eq_sum
        S.energyBasis (S.exhaustion.head m) u

/-- The reconstructed common test projection is a contraction in the box
energy norm, uniformly in the spectral level. -/
theorem norm_energySynthesis_testProjection_le
    {I : BoxIntegral.Box (Fin (n + 1))}
    (S : BoxCompactSpectralRepresentation I) (m : ℕ)
    (u : BoxH1ZeroSigma I) :
    ‖S.energySynthesis m (S.testProjection m u)‖ ≤ ‖u‖ := by
  rw [S.energySynthesis_testProjection_eq_partialProjection]
  let P := S.energyProjection m
  calc
    ‖P u‖ ≤ ‖P‖ * ‖u‖ := P.le_opNorm u
    _ ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right
      (GalerkinProjectorSequence.finitePartialProjection_norm_le
        S.energyBasis (S.exhaustion.head m))
      (norm_nonneg u)
    _ = ‖u‖ := one_mul _

end BoxCompactSpectralRepresentation

end
