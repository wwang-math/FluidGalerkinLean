import PDEIdeas.CompactEmbeddingSpectral

/-!
# Abstract spectral Galerkin towers

A `CompactEmbeddingSpectralRepresentation J` already carries the singular
coordinates of a compact dense injection `J : V → H`, together with an
increasing finite exhaustion of the basis index.  The finite-dimensional
Galerkin data built from that package -- the normalized energy modes, the
reconstruction operator from state coordinates to energy representatives,
the synthesis pair on a finite head, and the common test projection -- do not
refer to the underlying domain at all.

This file isolates those identities and bounds for an arbitrary
representation.  A concrete tower on a new domain therefore only has to
produce the representation; the finite-level algebra below is inherited.
-/

open InnerProductSpace
open scoped BigOperators RealInnerProductSpace

noncomputable section

namespace CompactEmbeddingSpectralRepresentation

variable {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {J : V →L[ℝ] H}
    (S : CompactEmbeddingSpectralRepresentation J)

/-! ### Normalized energy modes -/

/-- The energy basis vector rescaled so that its image under `J` is exactly
the corresponding state basis vector. -/
def energyMode (i : S.Index) : V := (S.weight i)⁻¹ • S.energyBasis i

@[simp]
theorem embedding_energyMode (i : S.Index) :
    J (S.energyMode i) = S.stateBasis i := by
  rw [energyMode, map_smul, S.basis_map i,
    inv_smul_smul₀ (S.weight_ne_zero i)]

theorem norm_energyMode (i : S.Index) :
    ‖S.energyMode i‖ = |S.weight i|⁻¹ := by
  rw [energyMode, norm_smul, S.energyBasis.orthonormal.norm_eq_one i,
    Real.norm_eq_abs, abs_inv, mul_one]

theorem stateBasis_mem_stateSpace {m : ℕ} {i : S.Index}
    (hi : i ∈ S.exhaustion.head m) : S.stateBasis i ∈ S.stateSpace m :=
  Submodule.subset_span ⟨i, hi, rfl⟩

theorem energyBasis_mem_energySpace {m : ℕ} {i : S.Index}
    (hi : i ∈ S.exhaustion.head m) : S.energyBasis i ∈ S.energySpace m :=
  Submodule.subset_span ⟨i, hi, rfl⟩

theorem energyMode_mem_energySpace {m : ℕ} {i : S.Index}
    (hi : i ∈ S.exhaustion.head m) : S.energyMode i ∈ S.energySpace m :=
  Submodule.smul_mem _ _ (S.energyBasis_mem_energySpace hi)

/-! ### Contractivity of the embedding -/

include S in
/-- Singular weights bounded by one force the embedding to be a contraction:
no separate contractivity hypothesis is needed once a representation exists. -/
theorem norm_embedding_le (u : V) : ‖J u‖ ≤ ‖u‖ := by
  rw [← S.stateBasis.repr.norm_map (J u), ← S.energyBasis.repr.norm_map u]
  refine lp.norm_mono (by norm_num) fun i => ?_
  rw [S.stateBasis.repr_apply_apply, S.energyBasis.repr_apply_apply]
  have hcoord : ⟪S.stateBasis i, J u⟫_ℝ =
      S.weight i * ⟪S.energyBasis i, u⟫_ℝ := by
    rw [real_inner_comm, S.coordinate_map u i, real_inner_comm u]
  rw [hcoord, norm_mul]
  calc
    ‖S.weight i‖ * ‖⟪S.energyBasis i, u⟫_ℝ‖ ≤
        1 * ‖⟪S.energyBasis i, u⟫_ℝ‖ :=
      mul_le_mul_of_nonneg_right (S.weight_norm_le_one i) (norm_nonneg _)
    _ = ‖⟪S.energyBasis i, u⟫_ℝ‖ := one_mul _

/-! ### Finite heads -/

theorem stateSpace_finiteDimensional (m : ℕ) :
    FiniteDimensional ℝ (S.stateSpace m) :=
  GalerkinProjectorSequence.finitePartialSpace_finiteDimensional
    S.stateBasis (S.exhaustion.head m)

theorem energySpace_finiteDimensional (m : ℕ) :
    FiniteDimensional ℝ (S.energySpace m) :=
  GalerkinProjectorSequence.finitePartialSpace_finiteDimensional
    S.energyBasis (S.exhaustion.head m)

theorem stateSpace_completeSpace (m : ℕ) : CompleteSpace (S.stateSpace m) := by
  letI : FiniteDimensional ℝ (S.stateSpace m) := S.stateSpace_finiteDimensional m
  letI : IsUniformAddGroup (S.stateSpace m) :=
    (S.stateSpace m).toAddSubgroup.isUniformAddGroup
  exact FiniteDimensional.complete ℝ _

theorem stateSpace_monotone : Monotone S.stateSpace := fun _ _ hmk =>
  GalerkinProjectorSequence.finitePartialSpace_mono S.stateBasis
    (S.exhaustion.monotone hmk)

theorem energySpace_monotone : Monotone S.energySpace := fun _ _ hmk =>
  GalerkinProjectorSequence.finitePartialSpace_mono S.energyBasis
    (S.exhaustion.monotone hmk)

theorem stateSpace_exhaustion_dense :
    ⊤ ≤ (⨆ m, S.stateSpace m).topologicalClosure :=
  GalerkinProjectorSequence.finitePartialSpace_exhaustion_dense
    S.stateBasis S.exhaustion

theorem energySpace_exhaustion_dense :
    ⊤ ≤ (⨆ m, S.energySpace m).topologicalClosure :=
  GalerkinProjectorSequence.finitePartialSpace_exhaustion_dense
    S.energyBasis S.exhaustion

/-! ### Reconstruction of energy representatives -/

/-- Finite reconstruction from state coordinates to their energy
representatives. -/
def energyHeadReconstruction (m : ℕ) : H →L[ℝ] V :=
  ∑ i ∈ S.exhaustion.head m,
    InnerProductSpace.rankOne ℝ (S.energyMode i) (S.stateBasis i)

@[simp]
theorem energyHeadReconstruction_apply (m : ℕ) (x : H) :
    S.energyHeadReconstruction m x =
      ∑ i ∈ S.exhaustion.head m, ⟪S.stateBasis i, x⟫_ℝ • S.energyMode i :=
  ContinuousLinearMap.sum_apply (S.exhaustion.head m)
    (fun i => InnerProductSpace.rankOne ℝ (S.energyMode i) (S.stateBasis i)) x

/-- On the finite state head the reconstruction is a genuine right inverse of
the embedding. -/
@[simp]
theorem embedding_energyHeadReconstruction_of_mem (m : ℕ) (x : H)
    (hx : x ∈ S.stateSpace m) :
    J (S.energyHeadReconstruction m x) = x := by
  calc
    J (S.energyHeadReconstruction m x) =
        ∑ i ∈ S.exhaustion.head m, ⟪S.stateBasis i, x⟫_ℝ • S.stateBasis i := by
      rw [S.energyHeadReconstruction_apply, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, S.embedding_energyMode]
    _ = S.stateProjection m x := by
      rw [stateProjection,
        GalerkinProjectorSequence.finitePartialProjection_apply_eq_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [real_inner_comm]
    _ = x :=
      GalerkinProjectorSequence.finitePartialProjection_fixed
        S.stateBasis (S.exhaustion.head m) x hx

theorem energyHeadReconstruction_stateBasis_of_mem {m : ℕ} {i : S.Index}
    (hi : i ∈ S.exhaustion.head m) :
    S.energyHeadReconstruction m (S.stateBasis i) = S.energyMode i := by
  apply S.embedding_injective
  rw [S.embedding_energyHeadReconstruction_of_mem m _
      (S.stateBasis_mem_stateSpace hi), S.embedding_energyMode]

/-! ### The synthesis pair on a finite head -/

/-- Synthesis of an energy representative from a finite state head. -/
def energySynthesis (m : ℕ) : S.stateSpace m →L[ℝ] V :=
  (S.energyHeadReconstruction m).comp (S.stateSpace m).subtypeL

/-- Synthesis of the state itself from a finite state head. -/
def stateSynthesis (m : ℕ) : S.stateSpace m →L[ℝ] H :=
  (S.stateSpace m).subtypeL

@[simp]
theorem stateSynthesis_apply (m : ℕ) (u : S.stateSpace m) :
    S.stateSynthesis m u = (u : H) := rfl

@[simp]
theorem embedding_energySynthesis (m : ℕ) (u : S.stateSpace m) :
    J (S.energySynthesis m u) = S.stateSynthesis m u :=
  S.embedding_energyHeadReconstruction_of_mem m (u : H) u.property

@[simp]
theorem norm_stateSynthesis (m : ℕ) (u : S.stateSpace m) :
    ‖S.stateSynthesis m u‖ = ‖u‖ := rfl

theorem stateSynthesis_isometry (m : ℕ) : Isometry (S.stateSynthesis m) :=
  fun _ _ => rfl

theorem energySynthesis_injective (m : ℕ) :
    Function.Injective (S.energySynthesis m) := by
  intro u v huv
  apply Subtype.ext
  have h := congrArg (⇑J) huv
  simpa only [S.embedding_energySynthesis, S.stateSynthesis_apply] using h

/-! ### The common test projection -/

/-- The state projection of an embedded energy vector, viewed as an element of
the finite state head. -/
def testProjection (m : ℕ) : V →L[ℝ] S.stateSpace m :=
  ((S.stateProjection m).codRestrict (S.stateSpace m) fun x => by
    change GalerkinProjectorSequence.finitePartialProjection
        S.stateBasis (S.exhaustion.head m) x ∈
      GalerkinProjectorSequence.finitePartialSpace
        S.stateBasis (S.exhaustion.head m)
    rw [← GalerkinProjectorSequence.range_finitePartialProjection]
    exact ⟨x, rfl⟩).comp J

@[simp]
theorem testProjection_apply (m : ℕ) (φ : V) :
    (S.testProjection m φ : H) = S.stateProjection m (J φ) := rfl

/-- Orthogonal state projection is invisible when paired against a state
already in the finite spectral head. -/
theorem inner_testProjection_eq_state_inner (m : ℕ) (u : S.stateSpace m)
    (φ : V) :
    ⟪u, S.testProjection m φ⟫_ℝ = ⟪S.stateSynthesis m u, J φ⟫_ℝ := by
  have hfix :
      GalerkinProjectorSequence.finitePartialProjection S.stateBasis
        (S.exhaustion.head m) (u : H) = (u : H) :=
    GalerkinProjectorSequence.finitePartialProjection_fixed
      S.stateBasis (S.exhaustion.head m) (u : H) u.property
  change ⟪(u : H),
      GalerkinProjectorSequence.finitePartialProjection S.stateBasis
        (S.exhaustion.head m) (J φ)⟫_ℝ = ⟪(u : H), J φ⟫_ℝ
  rw [← GalerkinProjectorSequence.inner_finitePartialProjection_left_eq_right,
    hfix]

theorem inner_testProjection_energyMode (m : ℕ) (i : S.Index)
    (u : S.stateSpace m) :
    ⟪u, S.testProjection m (S.energyMode i)⟫_ℝ =
      ⟪S.stateSynthesis m u, S.stateBasis i⟫_ℝ := by
  rw [S.inner_testProjection_eq_state_inner m u (S.energyMode i),
    S.embedding_energyMode]

/-- Reconstruction of the common state-space test projection is precisely the
energy-basis orthogonal projection. -/
theorem energySynthesis_testProjection_eq_energyProjection (m : ℕ) (u : V) :
    S.energySynthesis m (S.testProjection m u) = S.energyProjection m u := by
  change S.energyHeadReconstruction m (S.stateProjection m (J u)) =
    S.energyProjection m u
  calc
    S.energyHeadReconstruction m (S.stateProjection m (J u)) =
        S.energyHeadReconstruction m
          (∑ i ∈ S.exhaustion.head m,
            ⟪J u, S.stateBasis i⟫_ℝ • S.stateBasis i) := by
      congr 1
      exact GalerkinProjectorSequence.finitePartialProjection_apply_eq_sum
        S.stateBasis (S.exhaustion.head m) (J u)
    _ = ∑ i ∈ S.exhaustion.head m, ⟪u, S.energyBasis i⟫_ℝ • S.energyBasis i := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [map_smul, S.energyHeadReconstruction_stateBasis_of_mem hi,
        S.coordinate_map u i]
      simp only [energyMode, smul_smul]
      congr 1
      field_simp [S.weight_ne_zero i]
    _ = S.energyProjection m u :=
      (GalerkinProjectorSequence.finitePartialProjection_apply_eq_sum
        S.energyBasis (S.exhaustion.head m) u).symm

/-- The two projections intertwine through the embedding. -/
theorem stateProjection_embedding (m : ℕ) (u : V) :
    S.stateProjection m (J u) = J (S.energyProjection m u) := by
  rw [← S.energySynthesis_testProjection_eq_energyProjection m u,
    S.embedding_energySynthesis, S.stateSynthesis_apply, S.testProjection_apply]

/-- The reconstructed common test projection is a contraction in the energy
norm, uniformly in the spectral level. -/
theorem norm_energySynthesis_testProjection_le (m : ℕ) (u : V) :
    ‖S.energySynthesis m (S.testProjection m u)‖ ≤ ‖u‖ := by
  rw [S.energySynthesis_testProjection_eq_energyProjection]
  calc
    ‖S.energyProjection m u‖ ≤ ‖S.energyProjection m‖ * ‖u‖ :=
      (S.energyProjection m).le_opNorm u
    _ ≤ 1 * ‖u‖ :=
      mul_le_mul_of_nonneg_right
        (GalerkinProjectorSequence.finitePartialProjection_norm_le
          S.energyBasis (S.exhaustion.head m)) (norm_nonneg u)
    _ = ‖u‖ := one_mul _

/-- The test projection itself is a contraction from the energy space into the
finite state head. -/
theorem norm_testProjection_le (m : ℕ) (u : V) :
    ‖S.testProjection m u‖ ≤ ‖u‖ := by
  have hproj : ‖S.stateProjection m (J u)‖ ≤ ‖J u‖ := by
    calc
      ‖S.stateProjection m (J u)‖ ≤ ‖S.stateProjection m‖ * ‖J u‖ :=
        (S.stateProjection m).le_opNorm (J u)
      _ ≤ 1 * ‖J u‖ :=
        mul_le_mul_of_nonneg_right
          (GalerkinProjectorSequence.finitePartialProjection_norm_le
            S.stateBasis (S.exhaustion.head m)) (norm_nonneg _)
      _ = ‖J u‖ := one_mul _
  change ‖(S.testProjection m u : H)‖ ≤ ‖u‖
  rw [S.testProjection_apply]
  exact hproj.trans (S.norm_embedding_le u)

end CompactEmbeddingSpectralRepresentation

end
