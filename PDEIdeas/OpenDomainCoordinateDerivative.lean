import PDEIdeas.OpenDomainTimeCompactness
import PDEIdeas.OpenDomainGalerkinDerivativeIdentity

/-!
# Spectral coordinates of the unforced open-domain trajectories and their derivatives

`OpenDomainTimeCompactness.openDomainCompactFamily` asks for three pieces of
coordinate data: a function `coordinate : ℕ → S.Index → ℝ → ℝ`, the identity

`coordinate k i t = ⟪openDomainEnergyToState Ω (u k t), S.stateBasis i⟫_ℝ`,

and, for **every** level `k`, **every** basis index `i` and every time of the
interval, a derivative

`HasDerivWithinAt (coordinate k i) (dual k x (testMode i)) (Icc a b) x`.

This file supplies those three for the actual unforced trajectories chosen in
`PDEIdeas.OpenDomainUnforcedUniformBounds`, with

* `testMode i := S.energyMode i`, the normalized energy mode of the index, and
* `dual k x :=` the tested common-dual right-hand side of
  `PDEIdeas.OpenDomainGalerkinDerivativeIdentity`, which is precisely the path
  whose level-uniform `L²` bound that file proves.

Nothing about the ODE is reproved: the derivative comes from
`OpenDomainGalerkinDerivativeIdentity.hasDerivWithinAt_tested`, and the
identification of its value with the dual functional at the energy mode from
`OpenDomainGalerkinDerivativeIdentity.dualRHS_testProjection_apply`.

## Indices outside the finite head

The requirement quantifies over the **whole** index type, while the level-`k`
trajectory only carries the `head k` coordinates, so the indices outside the
head have to be accounted for rather than assumed away.  They are handled
explicitly here, and they are not a special case of the argument — they are a
degenerate one:

* `stateProjection_stateBasis_eq_zero_of_notMem` — the spectral state
  projection kills a basis vector outside its head;
* `testProjection_energyMode_eq_zero_of_notMem` and
  `energyProjection_energyMode_eq_zero_of_notMem` — hence both projections kill
  the corresponding energy mode;
* `coordinate_eq_zero_of_notMem` — so the coordinate vanishes identically;
* `dualRHS_energyMode_eq_zero_of_notMem` — and the required derivative value
  vanishes too, so the two sides agree for the trivial reason.

`coordinate_hasDerivWithinAt` is proved uniformly in the index and therefore
covers both cases at once; `coordinate_hasDerivWithinAt_of_notMem` records the
degenerate case separately, in the form `HasDerivWithinAt (coordinate k i) 0`.

## Main statements

* `coordinate` — the spectral coordinate of the canonical unforced trajectory.
* `coordinate_eq_inner_testProjection` — the coordinate as the head pairing
  that the derivative identity differentiates.
* `coordinate_eq_energyPath`, `coordinate_eq_of_path` — the `coordinate_eq`
  hypothesis of `openDomainCompactFamily`, for any bounded continuous path
  family agreeing with the lifted energy path.
* `coordinate_hasDerivWithinAt` — the `coordinate_hasDeriv` hypothesis, for
  every index.
* `compactFamilyOfPath` — the coordinate data fed to `openDomainCompactFamily`,
  with the dual hypotheses discharged by the level-uniform `L²` bound already
  proved in `PDEIdeas.OpenDomainGalerkinDerivativeIdentity`.
-/

open BoundedContinuousFunction Filter InnerProductSpace MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

namespace OpenDomainCoordinateDerivative

variable {Q : BoxIntegral.Box (Fin 2)} (Ω : OpenDomainInBox Q)
    (L : BoxLadyzhenskayaRealization Q)
    (S : OpenDomainCompactSpectralRepresentation Ω)
    (u₀ : OpenDomainL2Sigma Ω) {T : ℝ} (hT : 0 ≤ T)

/-- The spectral coordinate of the canonical unforced level-`m` trajectory: the
pivot-space pairing of the trajectory's state with the `i`-th state basis
vector. -/
def coordinate (m : ℕ) (i : S.Index) (t : ℝ) : ℝ :=
  ⟪((OpenDomainUnforcedUniformBounds.solution Ω L.toBoxEnergyL4Realization S m
        u₀ hT).toFun t : OpenDomainL2Sigma Ω), S.stateBasis i⟫_ℝ

/-- The coordinate is the head pairing against the test projection of the
energy mode.  This is the function the derivative identity differentiates. -/
theorem coordinate_eq_inner_testProjection (m : ℕ) (i : S.Index) (t : ℝ) :
    coordinate Ω L S u₀ hT m i t =
      ⟪(OpenDomainUnforcedUniformBounds.solution Ω L.toBoxEnergyL4Realization S m
          u₀ hT).toFun t, S.testProjection m (S.energyMode i)⟫_ℝ :=
  (S.inner_testProjection_energyMode m i _).symm

/-- The coordinate in the shape `openDomainCompactFamily` asks for, along the
lifted energy path of `PDEIdeas.OpenDomainGalerkinDerivativeIdentity`. -/
theorem coordinate_eq_energyPath (m : ℕ) (i : S.Index) (t : ℝ) :
    coordinate Ω L S u₀ hT m i t =
      ⟪openDomainEnergyToState Ω
          (OpenDomainGalerkinDerivativeIdentity.energyPath Ω L S m u₀ hT t),
        S.stateBasis i⟫_ℝ := by
  have hstate :
      openDomainEnergyToState Ω
          (OpenDomainGalerkinDerivativeIdentity.energyPath Ω L S m u₀ hT t) =
        ((OpenDomainUnforcedUniformBounds.solution Ω L.toBoxEnergyL4Realization S m
          u₀ hT).toFun t : OpenDomainL2Sigma Ω) :=
    S.embedding_energySynthesis m _
  rw [hstate]
  rfl

/-- The `coordinate_eq` hypothesis of `openDomainCompactFamily`, for any
bounded continuous path family whose values are the lifted energy paths. -/
theorem coordinate_eq_of_path
    (u : ℕ → Icc (0 : ℝ) T →ᵇ OpenDomainH1ZeroSigma Ω)
    (hu : ∀ k (t : Icc (0 : ℝ) T),
      u k t = OpenDomainGalerkinDerivativeIdentity.energyPath Ω L S k u₀ hT t)
    (k : ℕ) (i : S.Index) (t : Icc (0 : ℝ) T) :
    coordinate Ω L S u₀ hT k i t =
      ⟪openDomainEnergyToState Ω (u k t), S.stateBasis i⟫_ℝ := by
  rw [hu k t]
  exact coordinate_eq_energyPath Ω L S u₀ hT k i t

/-! ### Indices outside the finite head -/

/-- The spectral state projection annihilates a basis vector whose index is
outside its head. -/
theorem stateProjection_stateBasis_eq_zero_of_notMem
    (m : ℕ) {i : S.Index} (hi : i ∉ S.exhaustion.head m) :
    S.stateProjection m (S.stateBasis i) = 0 := by
  classical
  have hsum :
      S.stateProjection m (S.stateBasis i) =
        ∑ j ∈ S.exhaustion.head m,
          ⟪S.stateBasis i, S.stateBasis j⟫_ℝ • S.stateBasis j :=
    GalerkinProjectorSequence.finitePartialProjection_apply_eq_sum
      S.stateBasis (S.exhaustion.head m) (S.stateBasis i)
  rw [hsum]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hne : i ≠ j := by
    intro h
    exact hi (h ▸ hj)
  have hzero : ⟪S.stateBasis i, S.stateBasis j⟫_ℝ = 0 :=
    S.stateBasis.orthonormal.2 hne
  rw [hzero, zero_smul]

/-- Hence the common test projection annihilates the energy mode of an index
outside the head. -/
theorem testProjection_energyMode_eq_zero_of_notMem
    (m : ℕ) {i : S.Index} (hi : i ∉ S.exhaustion.head m) :
    S.testProjection m (S.energyMode i) = 0 := by
  refine Subtype.ext ?_
  rw [S.testProjection_apply, S.embedding_energyMode,
    stateProjection_stateBasis_eq_zero_of_notMem Ω S m hi, ZeroMemClass.coe_zero]

/-- The energy projection annihilates the same mode. -/
theorem energyProjection_energyMode_eq_zero_of_notMem
    (m : ℕ) {i : S.Index} (hi : i ∉ S.exhaustion.head m) :
    S.energyProjection m (S.energyMode i) = 0 := by
  have h :=
    S.energySynthesis_testProjection_eq_energyProjection m (S.energyMode i)
  rw [← h, testProjection_energyMode_eq_zero_of_notMem Ω S m hi, map_zero]

/-- The coordinate of an index outside the head vanishes identically: the
level-`m` trajectory carries no such coordinate. -/
theorem coordinate_eq_zero_of_notMem
    (m : ℕ) {i : S.Index} (hi : i ∉ S.exhaustion.head m) (t : ℝ) :
    coordinate Ω L S u₀ hT m i t = 0 := by
  rw [coordinate_eq_inner_testProjection Ω L S u₀ hT m i t,
    testProjection_energyMode_eq_zero_of_notMem Ω S m hi]
  simp

/-- The tested common-dual right-hand side along the canonical trajectory: the
`dual` argument of `openDomainCompactFamily`, and the path whose level-uniform
`L²` bound `OpenDomainGalerkinDerivativeIdentity.dualDerivative_memLp_and_integral_le`
proves. -/
def dual (m : ℕ) (t : ℝ) : OpenDomainH1ZeroSigma Ω →L[ℝ] ℝ :=
  (OpenDomainGalerkinDerivativeIdentity.unforcedGradientProblem Ω L S m
      (OpenDomainUnforcedUniformBounds.stateHeadProjection S m u₀)).dualRHS
    (S.testProjection m) t
    ((OpenDomainUnforcedUniformBounds.solution Ω L.toBoxEnergyL4Realization S m
      u₀ hT).toFun t)

theorem dual_eq (m : ℕ) (t : ℝ) :
    dual Ω L S u₀ hT m t =
      (OpenDomainGalerkinDerivativeIdentity.unforcedGradientProblem Ω L S m
          (OpenDomainUnforcedUniformBounds.stateHeadProjection S m u₀)).dualRHS
        (S.testProjection m) t
        ((OpenDomainUnforcedUniformBounds.solution Ω L.toBoxEnergyL4Realization S m
          u₀ hT).toFun t) :=
  rfl

/-- The required derivative value vanishes for an index outside the head, so the
two sides of the derivative requirement agree there for the trivial reason. -/
theorem dual_energyMode_eq_zero_of_notMem
    (m : ℕ) {i : S.Index} (hi : i ∉ S.exhaustion.head m) (t : ℝ) :
    dual Ω L S u₀ hT m t (S.energyMode i) = 0 := by
  have happly :=
    OpenDomainGalerkinDerivativeIdentity.dualRHS_testProjection_apply Ω L S m
      (OpenDomainUnforcedUniformBounds.stateHeadProjection S m u₀) t
      ((OpenDomainUnforcedUniformBounds.solution Ω L.toBoxEnergyL4Realization S m
        u₀ hT).toFun t) (S.energyMode i)
  have hval :
      dual Ω L S u₀ hT m t (S.energyMode i) =
        OpenDomainDualDerivative.dualRHS (OpenDomainDualDerivative.diffusionForm Ω)
          (OpenDomainDualDerivative.convectionForm Ω L.toBoxEnergyL4Realization)
          (fun _ => (0 : OpenDomainH1ZeroSigma Ω →L[ℝ] ℝ)) t
          (S.energySynthesis m
            ((OpenDomainUnforcedUniformBounds.solution Ω L.toBoxEnergyL4Realization S m
              u₀ hT).toFun t))
          (S.energyProjection m (S.energyMode i)) := happly
  rw [hval, energyProjection_energyMode_eq_zero_of_notMem Ω S m hi]
  exact map_zero _

/-! ### The derivative of the coordinate -/

/-- **The coordinate derivative required by `openDomainCompactFamily`.**  For
every spectral level, every basis index -- inside or outside the finite head --
and every time of the interval, the coordinate of the actual unforced
trajectory is differentiable within the interval, with derivative the tested
common-dual right-hand side evaluated at the energy mode of the index.

The differentiation is
`OpenDomainGalerkinDerivativeIdentity.hasDerivWithinAt_tested` at the test
vector `S.energyMode i`; the identification of the derivative value is
`dualRHS_testProjection_apply`. -/
theorem coordinate_hasDerivWithinAt (m : ℕ) (i : S.Index) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (coordinate Ω L S u₀ hT m i)
      (dual Ω L S u₀ hT m t (S.energyMode i)) (Icc (0 : ℝ) T) t := by
  have hderiv :=
    OpenDomainGalerkinDerivativeIdentity.hasDerivWithinAt_tested Ω L S m
      (OpenDomainUnforcedUniformBounds.stateHeadProjection S m u₀) hT
      (OpenDomainUnforcedUniformBounds.solution Ω L.toBoxEnergyL4Realization S m u₀ hT)
      (S.energyMode i) t ht
  have happly :=
    OpenDomainGalerkinDerivativeIdentity.dualRHS_testProjection_apply Ω L S m
      (OpenDomainUnforcedUniformBounds.stateHeadProjection S m u₀) t
      ((OpenDomainUnforcedUniformBounds.solution Ω L.toBoxEnergyL4Realization S m
        u₀ hT).toFun t) (S.energyMode i)
  have hfun :
      coordinate Ω L S u₀ hT m i =
        fun s =>
          ⟪(OpenDomainUnforcedUniformBounds.solution Ω L.toBoxEnergyL4Realization S m
              u₀ hT).toFun s, S.testProjection m (S.energyMode i)⟫_ℝ :=
    funext fun s => coordinate_eq_inner_testProjection Ω L S u₀ hT m i s
  have hval :
      dual Ω L S u₀ hT m t (S.energyMode i) =
        OpenDomainDualDerivative.dualRHS (OpenDomainDualDerivative.diffusionForm Ω)
          (OpenDomainDualDerivative.convectionForm Ω L.toBoxEnergyL4Realization)
          (fun _ => (0 : OpenDomainH1ZeroSigma Ω →L[ℝ] ℝ)) t
          (S.energySynthesis m
            ((OpenDomainUnforcedUniformBounds.solution Ω L.toBoxEnergyL4Realization S m
              u₀ hT).toFun t))
          (S.energyProjection m (S.energyMode i)) := happly
  rw [hfun, hval]
  exact hderiv

/-- The degenerate case recorded on its own: outside the head the coordinate is
constant, with derivative zero. -/
theorem coordinate_hasDerivWithinAt_of_notMem (m : ℕ) {i : S.Index}
    (hi : i ∉ S.exhaustion.head m) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (coordinate Ω L S u₀ hT m i) 0 (Icc (0 : ℝ) T) t := by
  have hderiv := coordinate_hasDerivWithinAt Ω L S u₀ hT m i ht
  rwa [dual_energyMode_eq_zero_of_notMem Ω L S u₀ hT m hi t] at hderiv


/-! ### Feeding the coordinate data to the compactness family -/

/-- **The coordinate data is accepted by `openDomainCompactFamily`.**  Given a
bounded continuous path family realizing the lifted energy paths, together with
its uniform state and energy bounds, the coordinate, the `coordinate_eq`
identity and the coordinate derivative proved above -- with `testMode` the
energy modes and `dual` the tested common-dual right-hand side -- complete the
compactness data: the two remaining hypotheses are discharged by the
level-uniform `L²` dual bound of
`OpenDomainGalerkinDerivativeIdentity.dualDerivative_memLp_and_integral_le`.

This records that the derivative supplied here is the one the family asks for;
the state and energy bounds are left as hypotheses because they belong to the
path construction, not to the coordinates. -/
def compactFamilyOfPath
    {μI : Measure (Icc (0 : ℝ) T)} [IsFiniteMeasure μI]
    (u : ℕ → Icc (0 : ℝ) T →ᵇ OpenDomainH1ZeroSigma Ω)
    (hu : ∀ k (t : Icc (0 : ℝ) T),
      u k t = OpenDomainGalerkinDerivativeIdentity.energyPath Ω L S k u₀ hT t)
    (stateRadius : ℝ)
    (state_bound : ∀ k t, ‖openDomainEnergyToState Ω (u k t)‖ ≤ stateRadius)
    (energyRadius : ℝ) (energyRadius_nonneg : 0 ≤ energyRadius)
    (energy_bound : ∀ k,
      ‖BoundedContinuousFunction.toLp (2 : ℝ≥0∞) μI ℝ (u k)‖ ≤ energyRadius) :
    LeraySpectralCompactFamily (I := Icc (0 : ℝ) T)
      (V := OpenDomainH1ZeroSigma Ω) (H := OpenDomainL2Sigma Ω) (μ := μI) := by
  refine OpenDomainTimeCompactness.openDomainCompactFamily S hT u stateRadius
    state_bound energyRadius energyRadius_nonneg energy_bound
    (fun i => S.energyMode i)
    (dual Ω L S u₀ hT) (coordinate Ω L S u₀ hT)
    (coordinate_eq_of_path Ω L S u₀ hT u hu)
    (fun k i x hx => coordinate_hasDerivWithinAt Ω L S u₀ hT k i hx)
    ⟨Real.sqrt (2 * (1 + (boxLpConvectionBound Q * L.constant) * ‖u₀‖) ^ 2 *
        (T * ‖u₀‖ ^ 2 + ‖u₀‖ ^ 2 / 2)), Real.sqrt_nonneg _⟩
    (fun k => ?_) (fun k => ?_)
  · exact (OpenDomainGalerkinDerivativeIdentity.dualDerivative_memLp_and_integral_le
      Ω L S k u₀ hT).1
  · have hnn : (0 : ℝ) ≤ 2 * (1 + (boxLpConvectionBound Q * L.constant) * ‖u₀‖) ^ 2 *
        (T * ‖u₀‖ ^ 2 + ‖u₀‖ ^ 2 / 2) := by positivity
    have hsq := Real.sq_sqrt hnn
    have hbound :=
      (OpenDomainGalerkinDerivativeIdentity.dualDerivative_memLp_and_integral_le
        Ω L S k u₀ hT).2
    show _ ≤ (Real.sqrt _) ^ 2
    rw [hsq]
    exact hbound

end OpenDomainCoordinateDerivative

end
