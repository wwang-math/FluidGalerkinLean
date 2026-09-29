import PDEIdeas.OpenDomainDualDerivative
import PDEIdeas.OpenDomainUnforcedUniformBounds

/-!
# The derivative of an unforced open-domain Galerkin trajectory is the common-dual RHS

`PDEIdeas.OpenDomainUnforcedGalerkin` produces, at every spectral level `m`, an unforced
coefficient trajectory of the subdomain `Ω`, and `PDEIdeas.OpenDomainUnforcedUniformBounds`
reads two level-uniform a priori bounds off its energy identity.
`PDEIdeas.OpenDomainDualDerivative` bounds the common-dual right-hand side

`φ ↦ -⟪DU, Dφ⟫ - b(U, U, φ)`

of `Ω` in `L²`-in-time, given uniform state and energy bounds on an arbitrary path.

This file joins the two: it identifies the time derivative of an **actual** finite-head
trajectory, tested through the common test projection, with that common-dual right-hand
side, and then converts the trajectory bounds into a **level-independent** `L²` bound for
the tested derivative.  Neither the identity nor the bound is assumed.

## The finite-head test projection

At level `m` the coefficient system lives on the spectral head `S.stateSpace m`, and a test
vector `φ` of the energy space enters only through `S.testProjection m φ`.  Lifting that
back with `S.energySynthesis m` is exactly the energy head projection
(`energySynthesis_testProjection_eq_energyProjection`), so the tested derivative is the
**full** `Ω` common-dual functional evaluated at the **head projection** of the test vector:

`d/dt ⟪u_m t, testProjection m φ⟫ = dualRHS t (energySynthesis m (u_m t)) (energyProjection m φ)`.

Since the energy head projection is a contraction uniformly in `m`, the dual norm of the
tested functional is bounded by the dual norm of the full functional — with no constant
depending on the level.  That is what makes the final estimate level independent.

## Main results

Generic layer, for an arbitrary compact spectral representation and the pulled-back
variational problem of `PDEIdeas.AbstractSpectralDynamics`:

* `norm_energyProjection_le` — the energy head projection is a contraction.
* `spectralProblem_dualRHS_testProjection_apply` and `..._eq_comp` — the tested common-dual
  right-hand side of the level-`m` problem **is** the common-dual right-hand side of
  `PDEIdeas.OpenDomainDualDerivative` precomposed with the energy head projection.
* `hasDerivWithinAt_spectralProblem_tested` — the derivative identity along an actual
  solution.
* `norm_spectralProblem_dualRHS_testProjection_le` — the level-independent dual-norm
  comparison.
* `memLp_and_integral_le_of_comp` — an `L²` bound transported along a contraction.

`Ω` layer, for the trajectory selected in `PDEIdeas.OpenDomainUnforcedUniformBounds`:

* `dualRHS_testProjection_apply`, `dualRHS_testProjection_eq_comp`,
  `hasDerivWithinAt_tested`, `norm_dualRHS_testProjection_le` — the four statements above
  at the unforced gradient-diffusion problem of `Ω`.
* `norm_sq_eq_state_add_gradient`, `integral_energyPath_sq_le`, `memLp_energyPath` — the
  trajectory bounds of `PDEIdeas.OpenDomainUnforcedUniformBounds` recast as the state and
  energy hypotheses of `PDEIdeas.OpenDomainDualDerivative`.
* `dualDerivative_memLp_and_integral_le` — **the level-independent `L²` dual-derivative
  bound**: for the canonical unforced trajectory issued from the spectral projection of
  `u₀`, on `[0, T]`, at every level `m`,

  `∫₀ᵀ ‖dualRHS_m t (u_m t)‖² ≤ 2 (1 + c‖u₀‖)² (T‖u₀‖² + ‖u₀‖²/2)`,
  `c = boxLpConvectionBound Q * L.constant`,

  together with membership in `L²([0,T]; (H¹₀σ(Ω))')`.  The right-hand side does not
  mention `m`.

## Scope

Unforced only, viscosity `1`, plane rectangle.  The trajectory is the one selected in
`PDEIdeas.OpenDomainUnforcedUniformBounds`; no new existence statement is made, and nothing
is claimed about limits of the family.
-/

open InnerProductSpace MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace OpenDomainGalerkinDerivativeIdentity

/-! ## Generic layer: the finite head tested through the common test projection -/

section Head

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] {J : V →L[ℝ] H}
    (S : CompactEmbeddingSpectralRepresentation J) (m : ℕ)
    (C : EnergyConvectionForm V) (D : V →L[ℝ] V →L[ℝ] ℝ) (hD : ∀ u, 0 ≤ D u u)
    (F : ℝ → V →L[ℝ] ℝ)

/-- The energy head projection is a contraction, uniformly in the level. -/
theorem norm_energyProjection_le (φ : V) :
    ‖S.energyProjection m φ‖ ≤ ‖φ‖ := by
  rw [← S.energySynthesis_testProjection_eq_energyProjection m φ]
  exact S.norm_energySynthesis_testProjection_le m φ

/-- **The tested common-dual right-hand side, with the finite head accounted for.**  The
level-`m` right-hand side tested against `φ` is the common-dual right-hand side of
`PDEIdeas.OpenDomainDualDerivative`, evaluated at the lifted coefficient state, tested
against the **energy head projection** of `φ`. -/
theorem spectralProblem_dualRHS_testProjection_apply (initial : S.stateSpace m) (t : ℝ)
    (x : S.stateSpace m) (φ : V) :
    (S.spectralProblem m (S.energySynthesis m) C D hD F initial).dualRHS
        (S.testProjection m) t x φ =
      OpenDomainDualDerivative.dualRHS D C.form F t (S.energySynthesis m x)
        (S.energyProjection m φ) := by
  rw [← S.energySynthesis_testProjection_eq_energyProjection m φ]
  rfl

/-- The same statement as an identity of functionals on the common test space: the tested
level-`m` right-hand side is the full right-hand side precomposed with the energy head
projection. -/
theorem spectralProblem_dualRHS_testProjection_eq_comp (initial : S.stateSpace m) (t : ℝ)
    (x : S.stateSpace m) :
    (S.spectralProblem m (S.energySynthesis m) C D hD F initial).dualRHS
        (S.testProjection m) t x =
      (OpenDomainDualDerivative.dualRHS D C.form F t
        (S.energySynthesis m x)).comp (S.energyProjection m) := by
  ext φ
  exact spectralProblem_dualRHS_testProjection_apply S m C D hD F initial t x φ

/-- **The derivative identity along an actual trajectory.**  For a solution of the level-`m`
coefficient system, the derivative of every tested coordinate is the common-dual right-hand
side at the lifted state, tested against the energy head projection of the test vector. -/
theorem hasDerivWithinAt_spectralProblem_tested (initial : S.stateSpace m)
    {tmin tmax : ℝ} {t₀ : Icc tmin tmax}
    (u : (S.spectralProblem m (S.energySynthesis m) C D hD F initial).LocalSolutionOn t₀)
    (φ : V) (t : ℝ) (ht : t ∈ Icc tmin tmax) :
    HasDerivWithinAt (fun s => ⟪u.toFun s, S.testProjection m φ⟫_ℝ)
      (OpenDomainDualDerivative.dualRHS D C.form F t (S.energySynthesis m (u.toFun t))
        (S.energyProjection m φ))
      (Icc tmin tmax) t := by
  have h := u.hasDerivWithinAt_test (S.testProjection m) φ t ht
  rwa [spectralProblem_dualRHS_testProjection_apply S m C D hD F initial t (u.toFun t) φ]
    at h

/-- **Level-independent dual-norm comparison.**  Testing through the finite head cannot
increase the dual norm, because the energy head projection is a contraction. -/
theorem norm_spectralProblem_dualRHS_testProjection_le (initial : S.stateSpace m) (t : ℝ)
    (x : S.stateSpace m) :
    ‖(S.spectralProblem m (S.energySynthesis m) C D hD F initial).dualRHS
        (S.testProjection m) t x‖ ≤
      ‖OpenDomainDualDerivative.dualRHS D C.form F t (S.energySynthesis m x)‖ := by
  rw [spectralProblem_dualRHS_testProjection_eq_comp S m C D hD F initial t x]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun φ => ?_
  calc
    ‖(OpenDomainDualDerivative.dualRHS D C.form F t
        (S.energySynthesis m x)).comp (S.energyProjection m) φ‖
        = ‖OpenDomainDualDerivative.dualRHS D C.form F t (S.energySynthesis m x)
            (S.energyProjection m φ)‖ := rfl
    _ ≤ ‖OpenDomainDualDerivative.dualRHS D C.form F t (S.energySynthesis m x)‖ *
          ‖S.energyProjection m φ‖ :=
      (OpenDomainDualDerivative.dualRHS D C.form F t (S.energySynthesis m x)).le_opNorm _
    _ ≤ ‖OpenDomainDualDerivative.dualRHS D C.form F t (S.energySynthesis m x)‖ * ‖φ‖ :=
      mul_le_mul_of_nonneg_left (norm_energyProjection_le S m φ) (norm_nonneg _)

end Head

/-! ## Generic layer: transport of an `L²` dual bound along a contraction -/

section DualL2

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A path of dual vectors obtained from a square integrable path by precomposition with a
fixed continuous linear map, and dominated by it in norm, is itself square integrable with
the same integral bound. -/
theorem memLp_and_integral_le_of_comp {a b : ℝ} (hab : a ≤ b)
    (Dfull Dtest : ℝ → V →L[ℝ] ℝ) (P : V →L[ℝ] V) (B : ℝ)
    (hfull : MemLp Dfull 2 (volume.restrict (Icc a b)))
    (hfullInt : ∫ t in a..b, ‖Dfull t‖ ^ 2 ≤ B)
    (hcomp : ∀ t, Dtest t = (Dfull t).comp P)
    (hbound : ∀ t, ‖Dtest t‖ ≤ ‖Dfull t‖) :
    MemLp Dtest 2 (volume.restrict (Icc a b)) ∧
      ∫ t in a..b, ‖Dtest t‖ ^ 2 ≤ B := by
  have hmeas : AEStronglyMeasurable Dtest (volume.restrict (Icc a b)) := by
    have hpost : Continuous fun G : V →L[ℝ] ℝ => G.comp P :=
      ((ContinuousLinearMap.compL ℝ V V ℝ).flip P).continuous
    exact (hpost.comp_aestronglyMeasurable hfull.1).congr
      (Filter.Eventually.of_forall fun t => (hcomp t).symm)
  have hmemLp : MemLp Dtest 2 (volume.restrict (Icc a b)) :=
    MemLp.of_le hfull hmeas (Filter.Eventually.of_forall fun t => hbound t)
  refine ⟨hmemLp, ?_⟩
  have hintTest : IntervalIntegrable (fun t => ‖Dtest t‖ ^ 2) volume a b := by
    rw [intervalIntegrable_iff, uIoc_of_le hab]
    exact ((MemLp.norm (f := Dtest) hmemLp).mono_measure
      (Measure.restrict_mono_set volume Ioc_subset_Icc_self)).integrable_sq
  have hintFull : IntervalIntegrable (fun t => ‖Dfull t‖ ^ 2) volume a b := by
    rw [intervalIntegrable_iff, uIoc_of_le hab]
    exact ((MemLp.norm (f := Dfull) hfull).mono_measure
      (Measure.restrict_mono_set volume Ioc_subset_Icc_self)).integrable_sq
  calc
    ∫ t in a..b, ‖Dtest t‖ ^ 2 ≤ ∫ t in a..b, ‖Dfull t‖ ^ 2 := by
      refine intervalIntegral.integral_mono_on hab hintTest hintFull fun t _ht => ?_
      have h := hbound t
      have h0 : (0 : ℝ) ≤ ‖Dtest t‖ := norm_nonneg _
      nlinarith
    _ ≤ B := hfullInt

end DualL2

/-! ## The `Ω` instantiation -/

section OpenDomain

variable {Q : BoxIntegral.Box (Fin 2)} (Ω : OpenDomainInBox Q)
    (L : BoxLadyzhenskayaRealization Q)
    (S : OpenDomainCompactSpectralRepresentation Ω) (m : ℕ)

/-- The convection form of the unforced problem is the one bounded in
`PDEIdeas.OpenDomainDualDerivative`: both restrict the ambient `L4-L2-L4` form along the
canonical isometric inclusion. -/
theorem convectionForm_eq :
    OpenDomainPhysicalConvection.convectionForm Ω L.toBoxEnergyL4Realization =
      OpenDomainDualDerivative.convectionForm Ω L.toBoxEnergyL4Realization := rfl

/-- The gradient diffusion form of the unforced problem is the one bounded in
`PDEIdeas.OpenDomainDualDerivative`. -/
theorem diffusionForm_eq :
    (boxGradientDiffusion Q).bilinearCompSame (openDomainEnergyToBox Ω) =
      OpenDomainDualDerivative.diffusionForm Ω := rfl

/-- The unforced level-`m` problem of `Ω` with the ambient gradient diffusion: the problem
whose trajectories `PDEIdeas.OpenDomainUnforcedUniformBounds` selects. -/
abbrev unforcedGradientProblem (initial : S.stateSpace m) :
    VariationalGalerkinProblem (S.stateSpace m) :=
  OpenDomainUnforcedGalerkin.unforcedProblem Ω L.toBoxEnergyL4Realization
    ((boxGradientDiffusion Q).bilinearCompSame (openDomainEnergyToBox Ω))
    (fun w => boxGradientDiffusion_nonneg Q (openDomainEnergyToBox Ω w)) S m initial

/-- **The tested common-dual right-hand side of `Ω`.**  The level-`m` right-hand side
tested against `φ` is the `Ω` common-dual right-hand side of
`PDEIdeas.OpenDomainDualDerivative`, at the lifted coefficient state, tested against the
energy head projection of `φ`. -/
theorem dualRHS_testProjection_apply (initial : S.stateSpace m) (t : ℝ)
    (x : S.stateSpace m) (φ : OpenDomainH1ZeroSigma Ω) :
    (unforcedGradientProblem Ω L S m initial).dualRHS (S.testProjection m) t x φ =
      OpenDomainDualDerivative.dualRHS (OpenDomainDualDerivative.diffusionForm Ω)
        (OpenDomainDualDerivative.convectionForm Ω L.toBoxEnergyL4Realization)
        (fun _ => (0 : OpenDomainH1ZeroSigma Ω →L[ℝ] ℝ)) t (S.energySynthesis m x)
        (S.energyProjection m φ) :=
  spectralProblem_dualRHS_testProjection_apply S m
    (OpenDomainPhysicalConvection.energyConvectionForm Ω L.toBoxEnergyL4Realization)
    ((boxGradientDiffusion Q).bilinearCompSame (openDomainEnergyToBox Ω))
    (fun w => boxGradientDiffusion_nonneg Q (openDomainEnergyToBox Ω w))
    (fun _ => 0) initial t x φ

/-- The `Ω` identity as an identity of functionals on `H¹₀σ(Ω)`. -/
theorem dualRHS_testProjection_eq_comp (initial : S.stateSpace m) (t : ℝ)
    (x : S.stateSpace m) :
    (unforcedGradientProblem Ω L S m initial).dualRHS (S.testProjection m) t x =
      (OpenDomainDualDerivative.dualRHS (OpenDomainDualDerivative.diffusionForm Ω)
        (OpenDomainDualDerivative.convectionForm Ω L.toBoxEnergyL4Realization)
        (fun _ => (0 : OpenDomainH1ZeroSigma Ω →L[ℝ] ℝ)) t
        (S.energySynthesis m x)).comp (S.energyProjection m) :=
  spectralProblem_dualRHS_testProjection_eq_comp S m
    (OpenDomainPhysicalConvection.energyConvectionForm Ω L.toBoxEnergyL4Realization)
    ((boxGradientDiffusion Q).bilinearCompSame (openDomainEnergyToBox Ω))
    (fun w => boxGradientDiffusion_nonneg Q (openDomainEnergyToBox Ω w))
    (fun _ => 0) initial t x

/-- **The derivative identity along an actual unforced `Ω` trajectory.** -/
theorem hasDerivWithinAt_tested (initial : S.stateSpace m) {T : ℝ} (hT : 0 ≤ T)
    (u : (unforcedGradientProblem Ω L S m initial).LocalSolutionOn
      (⟨0, le_rfl, hT⟩ : Icc (0 : ℝ) T))
    (φ : OpenDomainH1ZeroSigma Ω) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun s => ⟪u.toFun s, S.testProjection m φ⟫_ℝ)
      (OpenDomainDualDerivative.dualRHS (OpenDomainDualDerivative.diffusionForm Ω)
        (OpenDomainDualDerivative.convectionForm Ω L.toBoxEnergyL4Realization)
        (fun _ => (0 : OpenDomainH1ZeroSigma Ω →L[ℝ] ℝ)) t
        (S.energySynthesis m (u.toFun t)) (S.energyProjection m φ))
      (Icc (0 : ℝ) T) t :=
  hasDerivWithinAt_spectralProblem_tested S m
    (OpenDomainPhysicalConvection.energyConvectionForm Ω L.toBoxEnergyL4Realization)
    ((boxGradientDiffusion Q).bilinearCompSame (openDomainEnergyToBox Ω))
    (fun w => boxGradientDiffusion_nonneg Q (openDomainEnergyToBox Ω w))
    (fun _ => 0) initial u φ t ht

/-- **Level-independent dual-norm comparison on `Ω`.** -/
theorem norm_dualRHS_testProjection_le (initial : S.stateSpace m) (t : ℝ)
    (x : S.stateSpace m) :
    ‖(unforcedGradientProblem Ω L S m initial).dualRHS (S.testProjection m) t x‖ ≤
      ‖OpenDomainDualDerivative.dualRHS (OpenDomainDualDerivative.diffusionForm Ω)
        (OpenDomainDualDerivative.convectionForm Ω L.toBoxEnergyL4Realization)
        (fun _ => (0 : OpenDomainH1ZeroSigma Ω →L[ℝ] ℝ)) t (S.energySynthesis m x)‖ :=
  norm_spectralProblem_dualRHS_testProjection_le S m
    (OpenDomainPhysicalConvection.energyConvectionForm Ω L.toBoxEnergyL4Realization)
    ((boxGradientDiffusion Q).bilinearCompSame (openDomainEnergyToBox Ω))
    (fun w => boxGradientDiffusion_nonneg Q (openDomainEnergyToBox Ω w))
    (fun _ => 0) initial t x

/-! ### The trajectory bounds in the form the dual estimate consumes -/

/-- The graph norm splits into the state and gradient norms of the subdomain. -/
theorem norm_sq_eq_state_add_gradient (w : OpenDomainH1ZeroSigma Ω) :
    ‖w‖ ^ 2 =
      ‖openDomainEnergyToState Ω w‖ ^ 2 +
        ‖boxEnergyGradient Q (openDomainEnergyToBox Ω w)‖ ^ 2 := by
  have h := boxEnergy_norm_sq_eq_state_add_gradient Q (openDomainEnergyToBox Ω w)
  rw [OpenDomainDualDerivative.norm_boxEnergyToState_openDomainEnergyToBox Ω w] at h
  exact h

section Trajectory

variable (u₀ : OpenDomainL2Sigma Ω) {T : ℝ} (hT : 0 ≤ T)

/-- The lifted energy path of the canonical unforced level-`m` trajectory. -/
def energyPath (t : ℝ) : OpenDomainH1ZeroSigma Ω :=
  S.energySynthesis m
    ((OpenDomainUnforcedUniformBounds.solution Ω L.toBoxEnergyL4Realization S m u₀ hT).toFun t)

theorem energyPath_continuousOn :
    ContinuousOn (energyPath Ω L S m u₀ hT) (Icc (0 : ℝ) T) :=
  (S.energySynthesis m).continuous.comp_continuousOn
    (OpenDomainUnforcedUniformBounds.solution Ω L.toBoxEnergyL4Realization S m
      u₀ hT).continuousOn

/-- **Uniform state bound along the lifted path**, from the trajectory bound of
`PDEIdeas.OpenDomainUnforcedUniformBounds`. -/
theorem norm_state_energyPath_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ‖openDomainEnergyToState Ω (energyPath Ω L S m u₀ hT t)‖ ≤ ‖u₀‖ := by
  have hstate :
      openDomainEnergyToState Ω (energyPath Ω L S m u₀ hT t) =
        S.stateSynthesis m
          ((OpenDomainUnforcedUniformBounds.solution Ω L.toBoxEnergyL4Realization S m
            u₀ hT).toFun t) :=
    S.embedding_energySynthesis m _
  rw [hstate, S.norm_stateSynthesis]
  exact OpenDomainUnforcedUniformBounds.norm_solution_le Ω L.toBoxEnergyL4Realization S m
    u₀ hT ht

theorem memLp_energyPath :
    MemLp (energyPath Ω L S m u₀ hT) 2 (volume.restrict (Icc (0 : ℝ) T)) := by
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
      (energyPath_continuousOn Ω L S m u₀ hT)
  refine MemLp.of_bound
    ((energyPath_continuousOn Ω L S m u₀ hT).aestronglyMeasurable measurableSet_Icc) C ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht using hC t ht

/-- The gradient bound of `PDEIdeas.OpenDomainUnforcedUniformBounds`, written along the
lifted path of this file. -/
theorem integral_gradient_energyPath_sq_le :
    ∫ s in (0 : ℝ)..T,
        ‖boxEnergyGradient Q
          (openDomainEnergyToBox Ω (energyPath Ω L S m u₀ hT s))‖ ^ 2 ≤ ‖u₀‖ ^ 2 / 2 :=
  OpenDomainUnforcedUniformBounds.integral_gradient_sq_le Ω L.toBoxEnergyL4Realization S m
    u₀ hT (⟨hT, le_rfl⟩ : T ∈ Icc (0 : ℝ) T)

/-- **Uniform energy bound along the lifted path.**  The graph norm splits into the state
norm, bounded by `‖u₀‖`, and the gradient norm, whose square integral is bounded by
`‖u₀‖² / 2`; both bounds are level independent. -/
theorem integral_energyPath_sq_le :
    ∫ t in (0 : ℝ)..T, ‖energyPath Ω L S m u₀ hT t‖ ^ 2 ≤ T * ‖u₀‖ ^ 2 + ‖u₀‖ ^ 2 / 2 := by
  have hgrad := integral_gradient_energyPath_sq_le Ω L S m u₀ hT
  have hcont := energyPath_continuousOn Ω L S m u₀ hT
  have hcontGrad : ContinuousOn
      (fun t => ‖boxEnergyGradient Q
        (openDomainEnergyToBox Ω (energyPath Ω L S m u₀ hT t))‖ ^ 2) (Icc (0 : ℝ) T) := by
    exact ((((boxEnergyGradient Q).continuous.comp
      (openDomainEnergyToBox Ω).continuous).comp_continuousOn hcont).norm).pow 2
  have hcontSq : ContinuousOn
      (fun t => ‖energyPath Ω L S m u₀ hT t‖ ^ 2) (Icc (0 : ℝ) T) := hcont.norm.pow 2
  have huIcc : uIcc (0 : ℝ) T = Icc (0 : ℝ) T := uIcc_of_le hT
  have hintSq : IntervalIntegrable
      (fun t => ‖energyPath Ω L S m u₀ hT t‖ ^ 2) volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]
    exact hcontSq
  have hintGrad : IntervalIntegrable
      (fun t => ‖boxEnergyGradient Q
        (openDomainEnergyToBox Ω (energyPath Ω L S m u₀ hT t))‖ ^ 2) volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]
    exact hcontGrad
  have hintConst : IntervalIntegrable (fun _ : ℝ => ‖u₀‖ ^ 2) volume 0 T :=
    intervalIntegrable_const
  have hmono :
      ∫ t in (0 : ℝ)..T, ‖energyPath Ω L S m u₀ hT t‖ ^ 2 ≤
        ∫ t in (0 : ℝ)..T,
          (‖u₀‖ ^ 2 +
            ‖boxEnergyGradient Q
              (openDomainEnergyToBox Ω (energyPath Ω L S m u₀ hT t))‖ ^ 2) := by
    apply intervalIntegral.integral_mono_on hT hintSq (hintConst.add hintGrad)
    intro t ht
    have hsplit := norm_sq_eq_state_add_gradient Ω (energyPath Ω L S m u₀ hT t)
    have hstate := norm_state_energyPath_le Ω L S m u₀ hT ht
    have hstate0 : (0 : ℝ) ≤ ‖openDomainEnergyToState Ω (energyPath Ω L S m u₀ hT t)‖ :=
      norm_nonneg _
    have hstateSq :
        ‖openDomainEnergyToState Ω (energyPath Ω L S m u₀ hT t)‖ ^ 2 ≤ ‖u₀‖ ^ 2 := by
      nlinarith
    linarith
  have hsplitInt :
      ∫ t in (0 : ℝ)..T,
          (‖u₀‖ ^ 2 +
            ‖boxEnergyGradient Q
              (openDomainEnergyToBox Ω (energyPath Ω L S m u₀ hT t))‖ ^ 2) =
        T * ‖u₀‖ ^ 2 +
          ∫ t in (0 : ℝ)..T,
            ‖boxEnergyGradient Q
              (openDomainEnergyToBox Ω (energyPath Ω L S m u₀ hT t))‖ ^ 2 := by
    rw [intervalIntegral.integral_add hintConst hintGrad,
      intervalIntegral.integral_const]
    simp
  rw [hsplitInt] at hmono
  linarith

/-! ### The level-independent `L²` dual-derivative bound -/

/-- **The `L²`-in-time bound for the tested derivative, uniform in the spectral level.**

The derivative of the level-`m` trajectory, tested through the finite-head projection and
read as an element of the common dual `(H¹₀σ(Ω))'`, is square integrable in time with a
bound that does not mention `m`: the state bound `‖u₀‖` and the energy radius
`T‖u₀‖² + ‖u₀‖²/2` are the level-uniform trajectory bounds, and testing through the head
projection does not increase the dual norm. -/
theorem dualDerivative_memLp_and_integral_le :
    MemLp (fun t =>
        (unforcedGradientProblem Ω L S m
            (OpenDomainUnforcedUniformBounds.stateHeadProjection S m u₀)).dualRHS
          (S.testProjection m) t
          ((OpenDomainUnforcedUniformBounds.solution Ω L.toBoxEnergyL4Realization S m
            u₀ hT).toFun t)) 2 (volume.restrict (Icc (0 : ℝ) T)) ∧
      ∫ t in (0 : ℝ)..T,
          ‖(unforcedGradientProblem Ω L S m
              (OpenDomainUnforcedUniformBounds.stateHeadProjection S m u₀)).dualRHS
            (S.testProjection m) t
            ((OpenDomainUnforcedUniformBounds.solution Ω L.toBoxEnergyL4Realization S m
              u₀ hT).toFun t)‖ ^ 2 ≤
        2 * (1 + (boxLpConvectionBound Q * L.constant) * ‖u₀‖) ^ 2 *
          (T * ‖u₀‖ ^ 2 + ‖u₀‖ ^ 2 / 2) := by
  have hR : (0 : ℝ) ≤ T * ‖u₀‖ ^ 2 + ‖u₀‖ ^ 2 / 2 := by positivity
  have hRsq : Real.sqrt (T * ‖u₀‖ ^ 2 + ‖u₀‖ ^ 2 / 2) ^ 2 =
      T * ‖u₀‖ ^ 2 + ‖u₀‖ ^ 2 / 2 := Real.sq_sqrt hR
  have hfull :=
    OpenDomainDualDerivative.openDomain_dualRHS_memLp_and_integral_le_zeroForcing Ω hT L
      (energyPath Ω L S m u₀ hT) ‖u₀‖ (Real.sqrt (T * ‖u₀‖ ^ 2 + ‖u₀‖ ^ 2 / 2))
      (norm_nonneg u₀)
      (fun t ht => norm_state_energyPath_le Ω L S m u₀ hT ht)
      (memLp_energyPath Ω L S m u₀ hT)
      (by rw [hRsq]; exact integral_energyPath_sq_le Ω L S m u₀ hT)
  refine memLp_and_integral_le_of_comp hT
    (fun t => OpenDomainDualDerivative.dualRHS (OpenDomainDualDerivative.diffusionForm Ω)
      (OpenDomainDualDerivative.convectionForm Ω L.toBoxEnergyL4Realization)
      (fun _ => (0 : OpenDomainH1ZeroSigma Ω →L[ℝ] ℝ)) t (energyPath Ω L S m u₀ hT t))
    _ (S.energyProjection m) _ hfull.1 ?_ ?_ ?_
  · calc
      ∫ t in (0 : ℝ)..T, ‖OpenDomainDualDerivative.dualRHS
          (OpenDomainDualDerivative.diffusionForm Ω)
          (OpenDomainDualDerivative.convectionForm Ω L.toBoxEnergyL4Realization)
          (fun _ => (0 : OpenDomainH1ZeroSigma Ω →L[ℝ] ℝ)) t
          (energyPath Ω L S m u₀ hT t)‖ ^ 2 ≤
          2 * (1 + (boxLpConvectionBound Q * L.constant) * ‖u₀‖) ^ 2 *
            Real.sqrt (T * ‖u₀‖ ^ 2 + ‖u₀‖ ^ 2 / 2) ^ 2 := hfull.2
      _ = 2 * (1 + (boxLpConvectionBound Q * L.constant) * ‖u₀‖) ^ 2 *
            (T * ‖u₀‖ ^ 2 + ‖u₀‖ ^ 2 / 2) := by rw [hRsq]
  · intro t
    exact dualRHS_testProjection_eq_comp Ω L S m
      (OpenDomainUnforcedUniformBounds.stateHeadProjection S m u₀) t _
  · intro t
    exact norm_dualRHS_testProjection_le Ω L S m
      (OpenDomainUnforcedUniformBounds.stateHeadProjection S m u₀) t _

end Trajectory

end OpenDomain

end OpenDomainGalerkinDerivativeIdentity

end
