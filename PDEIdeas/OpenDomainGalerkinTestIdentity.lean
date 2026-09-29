import PDEIdeas.OpenDomainWeakEquationLimit
import PDEIdeas.OpenDomainUnforcedGalerkin

/-!
# The finite-level tested identity of an unforced open-domain Galerkin solution

`PDEIdeas.OpenDomainWeakEquationLimit` passes a tested Galerkin equation to the
limit.  Its hypothesis `hGalerkin` is a *statement about each member of a
sequence*, and that file assumes it.  This file **derives** it, for an actual
solution of the unforced coefficient system produced by
`PDEIdeas.OpenDomainUnforcedGalerkin`.

Nothing about the limit is used here, and the tested equation is never assumed:
the only input is `VariationalGalerkinProblem.LocalSolutionOn`, i.e. a genuine
differentiable solution of the finite coefficient ODE, and the only analytic
tool is the generic integration by parts
`VariationalGalerkinProblem.LocalSolutionOn.timeTested_zeroForcing_identity`.

## The three matching problems

The limit file measures the three terms of the tested equation with

* `OpenDomainWeakEquationLimit.stateTestIntegral`, in the pivot space
  `BoxL2Sigma Q` of the ambient rectangle,
* `OpenDomainWeakEquationLimit.diffusionTestIntegral`, through the restricted
  gradient form `OpenDomainWeakEquationLimit.diffusionForm`,
* `OpenDomainWeakEquationLimit.convectionTestIntegral`, through the physical
  form `OpenDomainPhysicalConvection.convectionForm`,

all three evaluated on an `L²`-in-time energy path, against a **single spatial
test field**, and with the initial term paired in `BoxL2Sigma Q`.  A Galerkin
solution instead lives in coefficients, is tested by the finite test projection
`S.testProjection m`, and pairs its initial datum inside the head.  The three
reconciliations are:

* the time path: `energyPathLp`, the bounded continuous lift of the coefficient
  trajectory, viewed as an `L²` class for the interval subtype measure;
* the spatial test: `S.energySynthesis m (S.testProjection m φ)` is the energy
  projection `S.energyProjection m φ`, so the *projected* test field is the one
  the finite level actually sees;
* the pairing: `inner_testProjection_eq_box_inner`, which moves the coefficient
  inner product to the ambient pivot space along the isometric inclusions.

## Main statements

* `OpenDomainGalerkinTestIdentity.unforcedProblem` — the unforced level-`m`
  problem of `Ω` whose diffusion form is literally
  `OpenDomainWeakEquationLimit.diffusionForm Ω`.
* `OpenDomainGalerkinTestIdentity.energyPathLp` — the solution trajectory as an
  element of `Lp (OpenDomainH1ZeroSigma Ω) 2` over the interval subtype measure.
* `OpenDomainGalerkinTestIdentity.tested_galerkin_identity` — **the derived
  finite-level tested weak equation**, in exactly the shape of the `hGalerkin`
  hypothesis of `OpenDomainWeakEquationLimit.tested_weak_equation_limit`.
* `OpenDomainGalerkinTestIdentity.tested_weak_equation_limit_of_galerkin` — the
  limit theorem with that hypothesis discharged, so no tested equation is
  assumed anywhere along the chain.

`OpenDomainGalerkinTestIdentity.exists_unforcedSolutionOn` records that the
solutions the identity speaks about exist at every level and on every finite
interval, so none of the statements below is vacuous.
-/

open BoundedContinuousFunction Filter InnerProductSpace MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

namespace OpenDomainGalerkinTestIdentity

open OpenDomainPhysicalConvection OpenDomainWeakEquationLimit

variable {Q : BoxIntegral.Box (Fin 2)} {Ω : OpenDomainInBox Q}

/-- Congruence for the three-term shape of the tested equation.  Stated on
plain reals so that the substitution below never rewrites inside the large
space--time terms. -/
theorem testedSum_congr {x₁ x₂ x₃ y₁ y₂ y₃ : ℝ}
    (h₁ : x₁ = y₁) (h₂ : x₂ = y₂) (h₃ : x₃ = y₃) :
    -x₁ + x₂ + x₃ = -y₁ + y₂ + y₃ := by
  rw [h₁, h₂, h₃]

/-! ### The unforced level problem with the limit file's diffusion form -/

/-- The restricted gradient diffusion form is nonnegative, hence admissible as
the diffusion of an unforced level problem.  This is the ambient nonnegativity
read through the energy inclusion; no subdomain-specific fact is used. -/
theorem diffusionForm_nonneg (Ω : OpenDomainInBox Q)
    (u : OpenDomainH1ZeroSigma Ω) : 0 ≤ diffusionForm Ω u u :=
  boxGradientDiffusion_nonneg Q (energyInclusion Ω u)

variable (Ω)

/-- The unforced level-`m` variational problem of the subdomain, with the
diffusion form **taken to be** `OpenDomainWeakEquationLimit.diffusionForm Ω`.
Choosing that form here is what makes the finite-level identity land in the
shape the limit theorem consumes, with no later translation. -/
def unforcedProblem (E : BoxEnergyL4Realization Q)
    (S : OpenDomainCompactSpectralRepresentation Ω) (m : ℕ)
    (initial : S.stateSpace m) : VariationalGalerkinProblem (S.stateSpace m) :=
  OpenDomainUnforcedGalerkin.unforcedProblem Ω E (diffusionForm Ω)
    (diffusionForm_nonneg Ω) S m initial

variable {Ω}

@[simp]
theorem unforcedProblem_initial (E : BoxEnergyL4Realization Q)
    (S : OpenDomainCompactSpectralRepresentation Ω) (m : ℕ)
    (initial : S.stateSpace m) :
    (unforcedProblem Ω E S m initial).initial = initial := rfl

@[simp]
theorem unforcedProblem_diffusion_apply (E : BoxEnergyL4Realization Q)
    (S : OpenDomainCompactSpectralRepresentation Ω) (m : ℕ)
    (initial : S.stateSpace m) (x y : S.stateSpace m) :
    (unforcedProblem Ω E S m initial).system.diffusion x y =
      diffusionForm Ω (S.energySynthesis m x) (S.energySynthesis m y) := rfl

@[simp]
theorem unforcedProblem_convection_apply (E : BoxEnergyL4Realization Q)
    (S : OpenDomainCompactSpectralRepresentation Ω) (m : ℕ)
    (initial : S.stateSpace m) (x y z : S.stateSpace m) :
    (unforcedProblem Ω E S m initial).system.convection x y z =
      convectionForm Ω E (S.energySynthesis m x) (S.energySynthesis m y)
        (S.energySynthesis m z) := rfl

/-- The forcing of the level problem is the zero functional at every time, in
the pointfree form the integration-by-parts theorem asks for. -/
theorem unforcedProblem_forcing_eq_zero (E : BoxEnergyL4Realization Q)
    (S : OpenDomainCompactSpectralRepresentation Ω) (m : ℕ)
    (initial : S.stateSpace m) :
    (unforcedProblem Ω E S m initial).forcing = fun _ => 0 := by
  funext t
  ext x
  rfl

/-- Solutions of this problem exist on every finite interval and at every
level; inherited from `OpenDomainUnforcedGalerkin`, so the identity below is
never vacuous. -/
theorem exists_unforcedSolutionOn (E : BoxEnergyL4Realization Q)
    (S : OpenDomainCompactSpectralRepresentation Ω) (m : ℕ)
    (initial : S.stateSpace m) {a b : ℝ} (hab : a ≤ b) :
    Nonempty ((unforcedProblem Ω E S m initial).LocalSolutionOn
      (⟨a, le_rfl, hab⟩ : Icc a b)) :=
  OpenDomainUnforcedGalerkin.exists_unforcedSolutionOn Ω E (diffusionForm Ω)
    (diffusionForm_nonneg Ω) S m initial hab

/-! ### Moving the finite pairing to the ambient pivot space -/

/-- The energy-to-state map of the subdomain is the ambient one, read through
the isometric inclusion of the state closures. -/
theorem energyToBoxState_eq (Ω : OpenDomainInBox Q)
    (u : OpenDomainH1ZeroSigma Ω) :
    OpenDomainConvectionLimit.energyToBoxState Ω u =
      openDomainStateToBox Ω (openDomainEnergyToState Ω u) :=
  (openDomain_embedding_commutes Ω u).symm

/-- The inclusion of the subdomain state closure into the ambient one preserves
the inner product. -/
theorem inner_openDomainStateToBox (Ω : OpenDomainInBox Q)
    (x y : OpenDomainL2Sigma Ω) :
    ⟪openDomainStateToBox Ω x, openDomainStateToBox Ω y⟫_ℝ = ⟪x, y⟫_ℝ := rfl

/-- The finite test projection does not see the energy projection of its
argument: projecting the spatial test first changes nothing. -/
theorem testProjection_energyProjection
    (S : OpenDomainCompactSpectralRepresentation Ω) (m : ℕ)
    (φ : OpenDomainH1ZeroSigma Ω) :
    S.testProjection m (S.energyProjection m φ) = S.testProjection m φ := by
  apply Subtype.ext
  rw [S.testProjection_apply, S.testProjection_apply,
    ← S.stateProjection_embedding m φ]
  exact GalerkinProjectorSequence.finitePartialProjection_fixed
    S.stateBasis (S.exhaustion.head m) _
    (by
      rw [← GalerkinProjectorSequence.range_finitePartialProjection]
      exact ⟨openDomainEnergyToState Ω φ, rfl⟩)

/-- **The pairing bridge.**  A coefficient paired against the finite test
projection of `φ` is the ambient pivot pairing of the synthesised field against
the **projected** test `S.energyProjection m φ`.  Both replacements happen at
once: the orthogonal projection is absorbed on the left, and the inclusion into
`BoxL2Sigma Q` is an isometry on the right. -/
theorem inner_testProjection_eq_box_inner
    (S : OpenDomainCompactSpectralRepresentation Ω) (m : ℕ)
    (x : S.stateSpace m) (φ : OpenDomainH1ZeroSigma Ω) :
    ⟪x, S.testProjection m φ⟫_ℝ =
      ⟪OpenDomainConvectionLimit.energyToBoxState Ω (S.energySynthesis m x),
        OpenDomainConvectionLimit.energyToBoxState Ω
          (S.energyProjection m φ)⟫_ℝ :=
  calc ⟪x, S.testProjection m φ⟫_ℝ
      = ⟪x, S.testProjection m (S.energyProjection m φ)⟫_ℝ := by
        rw [testProjection_energyProjection]
    _ = ⟪S.stateSynthesis m x,
          openDomainEnergyToState Ω (S.energyProjection m φ)⟫_ℝ :=
        S.inner_testProjection_eq_state_inner m x (S.energyProjection m φ)
    _ = ⟪openDomainEnergyToState Ω (S.energySynthesis m x),
          openDomainEnergyToState Ω (S.energyProjection m φ)⟫_ℝ :=
        congrArg
          (fun z : OpenDomainL2Sigma Ω =>
            ⟪z, openDomainEnergyToState Ω (S.energyProjection m φ)⟫_ℝ)
          (S.embedding_energySynthesis m x).symm
    _ = ⟪OpenDomainConvectionLimit.energyToBoxState Ω (S.energySynthesis m x),
          OpenDomainConvectionLimit.energyToBoxState Ω
            (S.energyProjection m φ)⟫_ℝ := rfl

/-! ### The coefficient trajectory as a time--energy `L²` class -/

section Path

variable {E : BoxEnergyL4Realization Q}
    {S : OpenDomainCompactSpectralRepresentation Ω} {m : ℕ}
    {initial : S.stateSpace m} {a b : ℝ}

/-- The synthesised trajectory of a level solution, as a bounded continuous
energy-space path on the closed time interval. -/
def energyPathBCF (hab : a ≤ b)
    (u : (unforcedProblem Ω E S m initial).LocalSolutionOn
      (⟨a, le_rfl, hab⟩ : Icc a b)) :
    Icc a b →ᵇ OpenDomainH1ZeroSigma Ω :=
  BoundedContinuousFunction.mkOfCompact
    { toFun := fun t => S.energySynthesis m (u.toFun (t : ℝ))
      continuous_toFun :=
        (S.energySynthesis m).continuous.comp u.continuousOn.restrict }

/-- The synthesised trajectory as an element of the time--energy `L²` space
used by the limit theorem. -/
def energyPathLp (hab : a ≤ b)
    (u : (unforcedProblem Ω E S m initial).LocalSolutionOn
      (⟨a, le_rfl, hab⟩ : Icc a b)) :
    Lp (OpenDomainH1ZeroSigma Ω) (2 : ℝ≥0∞)
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) :=
  BoundedContinuousFunction.toLp (2 : ℝ≥0∞)
    (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) ℝ
    (energyPathBCF hab u)

theorem energyPathLp_ae (hab : a ≤ b)
    (u : (unforcedProblem Ω E S m initial).LocalSolutionOn
      (⟨a, le_rfl, hab⟩ : Icc a b)) :
    energyPathLp hab u =ᵐ[
      SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b]
        fun t : Icc a b => S.energySynthesis m (u.toFun (t : ℝ)) := by
  simpa only [energyPathLp, energyPathBCF,
    BoundedContinuousFunction.mkOfCompact_apply, ContinuousMap.coe_mk] using
    BoundedContinuousFunction.coeFn_toLp (2 : ℝ≥0∞)
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) ℝ
      (energyPathBCF hab u)

/-! ### The three tested terms along the trajectory -/

theorem stateTestIntegral_energyPathLp (hab : a ≤ b)
    (u : (unforcedProblem Ω E S m initial).LocalSolutionOn
      (⟨a, le_rfl, hab⟩ : Icc a b))
    (eta : LerayIntervalTimeTest a b) (g : BoxL2Sigma Q) :
    stateTestIntegral eta
        ((OpenDomainConvectionLimit.energyToBoxState Ω).compLpL 2
          (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)
          (energyPathLp hab u)) g =
      ∫ t in a..b,
        ⟪OpenDomainConvectionLimit.energyToBoxState Ω
          (S.energySynthesis m (u.toFun t)), g⟫_ℝ * eta.deriv t := by
  calc stateTestIntegral eta
        ((OpenDomainConvectionLimit.energyToBoxState Ω).compLpL 2
          (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)
          (energyPathLp hab u)) g
      = ∫ t : Icc a b,
          ⟪((OpenDomainConvectionLimit.energyToBoxState Ω).compLpL 2
            (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)
            (energyPathLp hab u)) t, g⟫_ℝ * eta.deriv (t : ℝ)
          ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b := rfl
    _ = ∫ t : Icc a b,
          ⟪OpenDomainConvectionLimit.energyToBoxState Ω
            (S.energySynthesis m (u.toFun (t : ℝ))), g⟫_ℝ * eta.deriv (t : ℝ)
          ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b := by
        refine integral_congr_ae ?_
        filter_upwards [(OpenDomainConvectionLimit.energyToBoxState
            Ω).coeFn_compLpL (energyPathLp hab u),
          energyPathLp_ae hab u] with t h1 h2
        rw [h1, h2]
        rfl
    _ = ∫ t in a..b,
          ⟪OpenDomainConvectionLimit.energyToBoxState Ω
            (S.energySynthesis m (u.toFun t)), g⟫_ℝ * eta.deriv t :=
        SmoothBoxVariationalGalerkinLevel.integral_intervalSubtypeMeasure hab
          (fun t => ⟪OpenDomainConvectionLimit.energyToBoxState Ω
            (S.energySynthesis m (u.toFun t)), g⟫_ℝ * eta.deriv t)

theorem diffusionTestIntegral_energyPathLp (hab : a ≤ b)
    (u : (unforcedProblem Ω E S m initial).LocalSolutionOn
      (⟨a, le_rfl, hab⟩ : Icc a b))
    (eta : IntervalTimeTest a b) (ψ : OpenDomainH1ZeroSigma Ω) :
    diffusionTestIntegral Ω eta (energyPathLp hab u) ψ =
      ∫ t in a..b,
        diffusionForm Ω (S.energySynthesis m (u.toFun t)) ψ * eta.value t := by
  calc diffusionTestIntegral Ω eta (energyPathLp hab u) ψ
      = ∫ t : Icc a b,
          diffusionForm Ω ((energyPathLp hab u) t) ψ * eta.value (t : ℝ)
          ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b := rfl
    _ = ∫ t : Icc a b,
          diffusionForm Ω (S.energySynthesis m (u.toFun (t : ℝ))) ψ *
            eta.value (t : ℝ)
          ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b := by
        refine integral_congr_ae ?_
        filter_upwards [energyPathLp_ae hab u] with t h2
        rw [h2]
    _ = ∫ t in a..b,
          diffusionForm Ω (S.energySynthesis m (u.toFun t)) ψ * eta.value t :=
        SmoothBoxVariationalGalerkinLevel.integral_intervalSubtypeMeasure hab
          (fun t =>
            diffusionForm Ω (S.energySynthesis m (u.toFun t)) ψ * eta.value t)

theorem convectionTestIntegral_energyPathLp (hab : a ≤ b)
    (u : (unforcedProblem Ω E S m initial).LocalSolutionOn
      (⟨a, le_rfl, hab⟩ : Icc a b))
    (eta : IntervalTimeTest a b) (ψ : OpenDomainH1ZeroSigma Ω) :
    convectionTestIntegral Ω E eta (energyPathLp hab u) ψ =
      ∫ t in a..b,
        convectionForm Ω E (S.energySynthesis m (u.toFun t))
          (S.energySynthesis m (u.toFun t)) ψ * eta.value t := by
  calc convectionTestIntegral Ω E eta (energyPathLp hab u) ψ
      = ∫ t : Icc a b,
          convectionForm Ω E ((energyPathLp hab u) t) ((energyPathLp hab u) t) ψ *
            eta.value (t : ℝ)
          ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b := rfl
    _ = ∫ t : Icc a b,
          convectionForm Ω E (S.energySynthesis m (u.toFun (t : ℝ)))
            (S.energySynthesis m (u.toFun (t : ℝ))) ψ * eta.value (t : ℝ)
          ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b := by
        refine integral_congr_ae ?_
        filter_upwards [energyPathLp_ae hab u] with t h2
        exact congrArg
          (fun z : OpenDomainH1ZeroSigma Ω =>
            convectionForm Ω E z z ψ * eta.value (t : ℝ)) h2
    _ = ∫ t in a..b,
          convectionForm Ω E (S.energySynthesis m (u.toFun t))
            (S.energySynthesis m (u.toFun t)) ψ * eta.value t :=
        SmoothBoxVariationalGalerkinLevel.integral_intervalSubtypeMeasure hab
          (fun t =>
            convectionForm Ω E (S.energySynthesis m (u.toFun t))
              (S.energySynthesis m (u.toFun t)) ψ * eta.value t)

/-! ### The finite-level tested identity -/

/-- **The tested weak equation at a finite Galerkin level.**

`u` is an actual solution of the unforced level-`m` coefficient system: a
differentiable path satisfying the finite variational ODE, not a hypothesis
about integrals.  Testing it against a single spatial field `φ` through the
finite projection and against a `C¹` time weight vanishing at the right
endpoint, integrating by parts in time, and transporting every term to the
ambient rectangle gives exactly the tested equation, with the **projected**
spatial test `S.energyProjection m φ` and the initial datum paired in
`BoxL2Sigma Q`.

The statement is verbatim the `hGalerkin` conjunct of
`OpenDomainWeakEquationLimit.tested_weak_equation_limit`. -/
theorem tested_galerkin_identity (hab : a ≤ b)
    (u : (unforcedProblem Ω E S m initial).LocalSolutionOn
      (⟨a, le_rfl, hab⟩ : Icc a b))
    (eta : LerayIntervalTimeTest a b) (heta : eta.value b = 0)
    (φ : OpenDomainH1ZeroSigma Ω) :
    -stateTestIntegral eta
        ((OpenDomainConvectionLimit.energyToBoxState Ω).compLpL 2
          (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)
          (energyPathLp hab u))
        (OpenDomainConvectionLimit.energyToBoxState Ω
          (S.energyProjection m φ)) +
      diffusionTestIntegral Ω eta.toIntervalTimeTest (energyPathLp hab u)
        (S.energyProjection m φ) +
      convectionTestIntegral Ω E eta.toIntervalTimeTest (energyPathLp hab u)
        (S.energyProjection m φ) =
    ⟪OpenDomainConvectionLimit.energyToBoxState Ω
        (S.energySynthesis m initial),
      OpenDomainConvectionLimit.energyToBoxState Ω
        (S.energyProjection m φ)⟫_ℝ * eta.value a := by
  have hzero := u.timeTested_zeroForcing_identity hab (S.testProjection m) φ
    eta.toIntervalTimeTest heta (unforcedProblem_forcing_eq_zero E S m initial)
  have hstate :
      (∫ t in a..b, ⟪u.toFun t, S.testProjection m φ⟫_ℝ * eta.deriv t) =
        stateTestIntegral eta
          ((OpenDomainConvectionLimit.energyToBoxState Ω).compLpL 2
            (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)
            (energyPathLp hab u))
          (OpenDomainConvectionLimit.energyToBoxState Ω
            (S.energyProjection m φ)) :=
    (intervalIntegral.integral_congr fun t _ =>
        congrArg (fun r : ℝ => r * eta.deriv t)
          (inner_testProjection_eq_box_inner S m (u.toFun t) φ)).trans
      (stateTestIntegral_energyPathLp hab u eta
        (OpenDomainConvectionLimit.energyToBoxState Ω
          (S.energyProjection m φ))).symm
  have hdiffusion :
      (∫ t in a..b,
          (unforcedProblem Ω E S m initial).system.diffusion (u.toFun t)
            (S.testProjection m φ) * eta.value t) =
        diffusionTestIntegral Ω eta.toIntervalTimeTest (energyPathLp hab u)
          (S.energyProjection m φ) :=
    (intervalIntegral.integral_congr fun t _ =>
        congrArg (fun r : ℝ => r * eta.value t)
          ((unforcedProblem_diffusion_apply E S m initial (u.toFun t)
              (S.testProjection m φ)).trans
            (congrArg (diffusionForm Ω (S.energySynthesis m (u.toFun t)))
              (S.energySynthesis_testProjection_eq_energyProjection m
                φ)))).trans
      (diffusionTestIntegral_energyPathLp hab u eta.toIntervalTimeTest
        (S.energyProjection m φ)).symm
  have hconvection :
      (∫ t in a..b,
          (unforcedProblem Ω E S m initial).system.convection (u.toFun t)
            (u.toFun t) (S.testProjection m φ) * eta.value t) =
        convectionTestIntegral Ω E eta.toIntervalTimeTest (energyPathLp hab u)
          (S.energyProjection m φ) :=
    (intervalIntegral.integral_congr fun t _ =>
        congrArg (fun r : ℝ => r * eta.value t)
          ((unforcedProblem_convection_apply E S m initial (u.toFun t)
              (u.toFun t) (S.testProjection m φ)).trans
            (congrArg
              (fun z : OpenDomainH1ZeroSigma Ω =>
                convectionForm Ω E (S.energySynthesis m (u.toFun t))
                  (S.energySynthesis m (u.toFun t)) z)
              (S.energySynthesis_testProjection_eq_energyProjection m
                φ)))).trans
      (convectionTestIntegral_energyPathLp hab u eta.toIntervalTimeTest
        (S.energyProjection m φ)).symm
  have hinitial :
      ⟪(unforcedProblem Ω E S m initial).initial, S.testProjection m φ⟫_ℝ =
        ⟪OpenDomainConvectionLimit.energyToBoxState Ω
            (S.energySynthesis m initial),
          OpenDomainConvectionLimit.energyToBoxState Ω
            (S.energyProjection m φ)⟫_ℝ :=
    inner_testProjection_eq_box_inner S m initial φ
  have hinitialMul :
      ⟪(unforcedProblem Ω E S m initial).initial, S.testProjection m φ⟫_ℝ *
          eta.value a =
        ⟪OpenDomainConvectionLimit.energyToBoxState Ω
            (S.energySynthesis m initial),
          OpenDomainConvectionLimit.energyToBoxState Ω
            (S.energyProjection m φ)⟫_ℝ * eta.value a :=
    congrArg (fun r : ℝ => r * eta.value a) hinitial
  exact (testedSum_congr hstate hdiffusion hconvection).symm.trans
    (hzero.trans hinitialMul)

end Path

/-! ### The limit theorem with its Galerkin hypothesis discharged -/

section Limit

variable {Q : BoxIntegral.Box (Fin 2)} {Ω : OpenDomainInBox Q}

/-- **The open-domain tested weak equation in the limit, from actual Galerkin
solutions.**  Every hypothesis of
`OpenDomainWeakEquationLimit.tested_weak_equation_limit` other than the
convergences is supplied here by `tested_galerkin_identity`, so along the whole
chain the tested equation is derived and never assumed.

The spatial tests are the energy projections of one fixed field `φ` onto the
levels `lev k`, the time paths are the synthesised trajectories of the
solutions `u k`, and the initial states are the synthesised initial
coefficients read in `BoxL2Sigma Q`. -/
theorem tested_weak_equation_limit_of_galerkin
    (L : BoxLadyzhenskayaRealization Q)
    (S : OpenDomainCompactSpectralRepresentation Ω)
    {a b : ℝ} (hab : a ≤ b)
    (eta : LerayIntervalTimeTest a b) (heta : eta.value b = 0)
    (lev : ℕ → ℕ) (init : ∀ k, S.stateSpace (lev k))
    (u : ∀ k, (unforcedProblem Ω L.toBoxEnergyL4Realization S (lev k)
      (init k)).LocalSolutionOn (⟨a, le_rfl, hab⟩ : Icc a b))
    (φ : OpenDomainH1ZeroSigma Ω)
    (wLim : Lp (OpenDomainH1ZeroSigma Ω) (2 : ℝ≥0∞)
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b))
    (R : ℝ) (hbound : ∀ k, ‖energyPathLp hab (u k)‖ ≤ R)
    (Rs : ℝ) (hRs : ∀ k,
      ‖(OpenDomainConvectionLimit.energyToBoxState Ω).compLpL 2
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)
        (energyPathLp hab (u k))‖ ≤ Rs)
    (hstate : Tendsto
      (fun k => (OpenDomainConvectionLimit.energyToBoxState Ω).compLpL 2
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)
        (energyPathLp hab (u k)))
      atTop
      (nhds ((OpenDomainConvectionLimit.energyToBoxState Ω).compLpL 2
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) wLim)))
    (hweak : ∀ Λ : Lp (OpenDomainH1ZeroSigma Ω) (2 : ℝ≥0∞)
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) →L[ℝ] ℝ,
      Tendsto (fun k => Λ (energyPathLp hab (u k))) atTop (nhds (Λ wLim)))
    (ψLim : OpenDomainH1ZeroSigma Ω)
    (hψ : Tendsto (fun k => S.energyProjection (lev k) φ) atTop (nhds ψLim))
    (u₀Lim : BoxL2Sigma Q)
    (hu₀ : Tendsto
      (fun k => OpenDomainConvectionLimit.energyToBoxState Ω
        (S.energySynthesis (lev k) (init k))) atTop (nhds u₀Lim)) :
    -stateTestIntegral eta
        ((OpenDomainConvectionLimit.energyToBoxState Ω).compLpL 2
          (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) wLim)
        (OpenDomainConvectionLimit.energyToBoxState Ω ψLim) +
      diffusionTestIntegral Ω eta.toIntervalTimeTest wLim ψLim +
      convectionTestIntegral Ω L.toBoxEnergyL4Realization
        eta.toIntervalTimeTest wLim ψLim =
    ⟪u₀Lim, OpenDomainConvectionLimit.energyToBoxState Ω ψLim⟫_ℝ *
      eta.value a :=
  tested_weak_equation_limit L eta (fun k => energyPathLp hab (u k)) wLim R
    hbound Rs hRs hstate hweak (fun k => S.energyProjection (lev k) φ) ψLim hψ
    (fun k => OpenDomainConvectionLimit.energyToBoxState Ω
      (S.energySynthesis (lev k) (init k))) u₀Lim hu₀
    (fun k => tested_galerkin_identity hab (u k) eta heta φ)

end Limit

end OpenDomainGalerkinTestIdentity
