import PDEIdeas.OpenDomainUnforcedUniformBounds

/-!
# Measurable finite-interval paths of the unforced open-domain family

`PDEIdeas.OpenDomainUnforcedUniformBounds` selects, for fixed initial data
`u₀ : OpenDomainL2Sigma Ω` and a fixed finite interval `[0, T]`, a coefficient
trajectory `OpenDomainUnforcedUniformBounds.solution Ω R S m u₀ hT` at every
spectral level `m`, and reads two a priori bounds off the unforced energy
identity: an `L∞` bound in the pivot norm and an `L²` bound in the gradient
norm.

Those bounds are stated about the *coefficient* trajectory and about an inline
gradient expression.  A compactness argument consumes paths in the ambient
spaces instead, and needs them to be measurable and to lie in `L²` of the
interval.  This file builds those paths and proves exactly that.

## The three paths

All are the selected coefficient trajectory composed with maps that already
exist:

* `statePath` — the trajectory in the pivot space `L²_σ(Ω)`, through the head
  inclusion `CompactEmbeddingSpectralRepresentation.stateSynthesis`;
* `energyPath` — the trajectory in the energy space `H¹_{0,σ}(Ω)`, through the
  energy lift `CompactEmbeddingSpectralRepresentation.energySynthesis`;
* `gradientPath` — its gradient in `BoxGradientL2 Q`, through the isometric
  inclusion `openDomainEnergyToBox Ω` and `boxEnergyGradient Q`.  This is
  definitionally the integrand already bounded by
  `OpenDomainUnforcedUniformBounds.integral_gradient_sq_le`.

## What is proved

Measurability comes from `VariationalGalerkinProblem.LocalSolutionOn.continuousOn`:
each path is continuous on `Icc 0 T`, hence ae strongly measurable for
`volume.restrict (Icc 0 T)`, hence square integrable there, and the squared
norm of each is interval integrable on `[0, T]`.

The uniform bounds are then:

* `integral_norm_statePath_sq_le` — `∫₀ᵀ ‖state‖² ≤ T * ‖u₀‖²`, from the
  `L∞` bound;
* `integral_norm_gradientPath_sq_le` — `∫₀ᵀ ‖grad‖² ≤ ‖u₀‖² / 2`, which is the
  dissipation bound at the right endpoint;
* `integral_norm_energyPath_sq_le` — `∫₀ᵀ ‖energy‖² ≤ T * ‖u₀‖² + ‖u₀‖² / 2`
  in the **graph norm** of `H¹_{0,σ}(Ω)`, obtained by splitting the graph norm
  into its state and gradient parts (`boxEnergy_norm_sq_eq_state_add_gradient`)
  and adding the previous two.  No Poincaré inequality is used, so this holds
  in every dimension `n + 1`.

Every right-hand side mentions only `‖u₀‖` and `T`, so all three are uniform in
the spectral level; `uniform_state_pointwise_bound`, `uniform_state_l2_bound`,
`uniform_gradient_l2_bound` and `uniform_energy_l2_bound` state this against
the predicates `UniformEnergyBoundOn` and `UniformTimeDerivativeBoundOn` of
`PDEIdeas.CompactnessInterface`, and `aubinLionsReady` assembles the existing
`AubinLionsReadyFamily` from two of them.

## On not assuming the bounds

No structure is declared in this file.  `AubinLionsReadyFamily` is the existing
interface of `PDEIdeas.CompactnessInterface`, and `aubinLionsReady` *builds* it
from the two proved bounds through `aubinLionsReady_of_bounds`; its fields are
supplied by proofs, never posited.  Likewise the `L²` memberships
`memLp_statePath`, `memLp_energyPath` and `memLp_gradientPath` are derived from
continuity on a compact interval, not assumed.
-/

open MeasureTheory Set

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

namespace OpenDomainUnforcedLpFamily

variable {n : ℕ} {Q : BoxIntegral.Box (Fin (n + 1))} {Ω : OpenDomainInBox Q}

section Paths

variable (Ω) (R : BoxEnergyL4Realization Q)
    (S : OpenDomainCompactSpectralRepresentation Ω) (m : ℕ)
    (u₀ : OpenDomainL2Sigma Ω) {T : ℝ} (hT : 0 ≤ T)

/-! ### The three finite-interval paths -/

/-- The selected level-`m` coefficient trajectory, as a path in the finite
spectral head. -/
def coefficientPath : ℝ → S.stateSpace m :=
  (OpenDomainUnforcedUniformBounds.solution Ω R S m u₀ hT).toFun

/-- The level-`m` **state path**: the trajectory read in the pivot space
`L²_σ(Ω)` through the head inclusion. -/
def statePath : ℝ → OpenDomainL2Sigma Ω :=
  fun t => S.stateSynthesis m (coefficientPath Ω R S m u₀ hT t)

/-- The level-`m` **energy path**: the trajectory lifted to the energy space
`H¹_{0,σ}(Ω)`. -/
def energyPath : ℝ → OpenDomainH1ZeroSigma Ω :=
  fun t => S.energySynthesis m (coefficientPath Ω R S m u₀ hT t)

/-- The level-`m` **gradient path**: the ambient gradient of the energy path,
read through the isometric energy inclusion. -/
def gradientPath : ℝ → BoxGradientL2 Q :=
  fun t =>
    boxEnergyGradient Q (openDomainEnergyToBox Ω (energyPath Ω R S m u₀ hT t))

@[simp]
theorem coefficientPath_apply (t : ℝ) :
    coefficientPath Ω R S m u₀ hT t =
      (OpenDomainUnforcedUniformBounds.solution Ω R S m u₀ hT).toFun t :=
  rfl

@[simp]
theorem statePath_apply (t : ℝ) :
    statePath Ω R S m u₀ hT t =
      S.stateSynthesis m
        ((OpenDomainUnforcedUniformBounds.solution Ω R S m u₀ hT).toFun t) :=
  rfl

@[simp]
theorem energyPath_apply (t : ℝ) :
    energyPath Ω R S m u₀ hT t =
      S.energySynthesis m
        ((OpenDomainUnforcedUniformBounds.solution Ω R S m u₀ hT).toFun t) :=
  rfl

/-- The gradient path is the subdomain energy gradient of the energy path. -/
theorem gradientPath_eq_openDomainEnergyGradient (t : ℝ) :
    gradientPath Ω R S m u₀ hT t =
      openDomainEnergyGradient Ω (energyPath Ω R S m u₀ hT t) :=
  rfl

/-- The state path is the pivot image of the energy path. -/
theorem openDomainEnergyToState_energyPath (t : ℝ) :
    openDomainEnergyToState Ω (energyPath Ω R S m u₀ hT t) =
      statePath Ω R S m u₀ hT t :=
  S.embedding_energySynthesis m _

/-! ### Continuity and measurability on the interval -/

theorem continuousOn_coefficientPath :
    ContinuousOn (coefficientPath Ω R S m u₀ hT) (Icc (0 : ℝ) T) :=
  (OpenDomainUnforcedUniformBounds.solution Ω R S m u₀ hT).continuousOn

theorem continuousOn_statePath :
    ContinuousOn (statePath Ω R S m u₀ hT) (Icc (0 : ℝ) T) :=
  (S.stateSynthesis m).continuous.comp_continuousOn
    (continuousOn_coefficientPath Ω R S m u₀ hT)

theorem continuousOn_energyPath :
    ContinuousOn (energyPath Ω R S m u₀ hT) (Icc (0 : ℝ) T) :=
  (S.energySynthesis m).continuous.comp_continuousOn
    (continuousOn_coefficientPath Ω R S m u₀ hT)

theorem continuousOn_gradientPath :
    ContinuousOn (gradientPath Ω R S m u₀ hT) (Icc (0 : ℝ) T) :=
  ((boxEnergyGradient Q).continuous.comp
      (openDomainEnergyToBox Ω).continuous).comp_continuousOn
    (continuousOn_energyPath Ω R S m u₀ hT)

theorem aestronglyMeasurable_statePath :
    AEStronglyMeasurable (statePath Ω R S m u₀ hT)
      (volume.restrict (Icc (0 : ℝ) T)) :=
  (continuousOn_statePath Ω R S m u₀ hT).aestronglyMeasurable measurableSet_Icc

theorem aestronglyMeasurable_energyPath :
    AEStronglyMeasurable (energyPath Ω R S m u₀ hT)
      (volume.restrict (Icc (0 : ℝ) T)) :=
  (continuousOn_energyPath Ω R S m u₀ hT).aestronglyMeasurable measurableSet_Icc

theorem aestronglyMeasurable_gradientPath :
    AEStronglyMeasurable (gradientPath Ω R S m u₀ hT)
      (volume.restrict (Icc (0 : ℝ) T)) :=
  (continuousOn_gradientPath Ω R S m u₀ hT).aestronglyMeasurable
    measurableSet_Icc

theorem intervalIntegrable_norm_statePath_sq :
    IntervalIntegrable (fun s => ‖statePath Ω R S m u₀ hT s‖ ^ 2) volume 0 T :=
  ContinuousOn.intervalIntegrable_of_Icc hT
    ((continuousOn_statePath Ω R S m u₀ hT).norm.pow 2)

theorem intervalIntegrable_norm_energyPath_sq :
    IntervalIntegrable (fun s => ‖energyPath Ω R S m u₀ hT s‖ ^ 2) volume 0 T :=
  ContinuousOn.intervalIntegrable_of_Icc hT
    ((continuousOn_energyPath Ω R S m u₀ hT).norm.pow 2)

theorem intervalIntegrable_norm_gradientPath_sq :
    IntervalIntegrable (fun s => ‖gradientPath Ω R S m u₀ hT s‖ ^ 2)
      volume 0 T :=
  ContinuousOn.intervalIntegrable_of_Icc hT
    ((continuousOn_gradientPath Ω R S m u₀ hT).norm.pow 2)

/-! ### Pointwise bounds -/

/-- The state path inherits the `L∞` pivot bound of the trajectory. -/
theorem norm_statePath_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ‖statePath Ω R S m u₀ hT t‖ ≤ ‖u₀‖ :=
  OpenDomainUnforcedUniformBounds.norm_solution_le Ω R S m u₀ hT ht

theorem norm_statePath_sq_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ‖statePath Ω R S m u₀ hT t‖ ^ 2 ≤ ‖u₀‖ ^ 2 := by
  have h := norm_statePath_le Ω R S m u₀ hT ht
  have h0 : (0 : ℝ) ≤ ‖statePath Ω R S m u₀ hT t‖ := norm_nonneg _
  nlinarith

/-- The graph norm of the energy path splits into its state and gradient
parts. -/
theorem norm_energyPath_sq_eq (t : ℝ) :
    ‖energyPath Ω R S m u₀ hT t‖ ^ 2 =
      ‖statePath Ω R S m u₀ hT t‖ ^ 2 +
        ‖gradientPath Ω R S m u₀ hT t‖ ^ 2 := by
  have h := boxEnergy_norm_sq_eq_state_add_gradient Q
    (openDomainEnergyToBox Ω (energyPath Ω R S m u₀ hT t))
  have hstate :
      ‖boxEnergyToState Q
          (openDomainEnergyToBox Ω (energyPath Ω R S m u₀ hT t))‖ =
        ‖statePath Ω R S m u₀ hT t‖ := by
    rw [← openDomainEnergyToState_energyPath Ω R S m u₀ hT t]
    rfl
  rw [hstate] at h
  exact h

/-! ### `L²` membership on the interval -/

private theorem restrict_isFiniteMeasure :
    IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) T)) := by
  rw [isFiniteMeasure_restrict]
  exact measure_Icc_lt_top.ne

theorem memLp_statePath :
    MemLp (statePath Ω R S m u₀ hT) 2 (volume.restrict (Icc (0 : ℝ) T)) := by
  haveI : IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) T)) :=
    restrict_isFiniteMeasure
  refine MemLp.of_bound (aestronglyMeasurable_statePath Ω R S m u₀ hT) ‖u₀‖ ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  exact norm_statePath_le Ω R S m u₀ hT hs

theorem memLp_energyPath :
    MemLp (energyPath Ω R S m u₀ hT) 2 (volume.restrict (Icc (0 : ℝ) T)) := by
  haveI : IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) T)) :=
    restrict_isFiniteMeasure
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
      (continuousOn_energyPath Ω R S m u₀ hT)
  refine MemLp.of_bound (aestronglyMeasurable_energyPath Ω R S m u₀ hT) C ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  exact hC s hs

theorem memLp_gradientPath :
    MemLp (gradientPath Ω R S m u₀ hT) 2 (volume.restrict (Icc (0 : ℝ) T)) := by
  haveI : IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) T)) :=
    restrict_isFiniteMeasure
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
      (continuousOn_gradientPath Ω R S m u₀ hT)
  refine MemLp.of_bound (aestronglyMeasurable_gradientPath Ω R S m u₀ hT) C ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  exact hC s hs

/-! ### The `L²` bounds on the interval -/

/-- **`L²` state bound.**  The right-hand side depends only on `T` and
`‖u₀‖`. -/
theorem integral_norm_statePath_sq_le :
    ∫ s in (0 : ℝ)..T, ‖statePath Ω R S m u₀ hT s‖ ^ 2 ≤ T * ‖u₀‖ ^ 2 := by
  have hmono :
      ∫ s in (0 : ℝ)..T, ‖statePath Ω R S m u₀ hT s‖ ^ 2 ≤
        ∫ _s in (0 : ℝ)..T, ‖u₀‖ ^ 2 :=
    intervalIntegral.integral_mono_on hT
      (intervalIntegrable_norm_statePath_sq Ω R S m u₀ hT)
      intervalIntegrable_const
      (fun s hs => norm_statePath_sq_le Ω R S m u₀ hT hs)
  simpa using hmono

/-- **`L²` gradient bound.**  This is the dissipation bound of
`OpenDomainUnforcedUniformBounds` at the right endpoint. -/
theorem integral_norm_gradientPath_sq_le :
    ∫ s in (0 : ℝ)..T, ‖gradientPath Ω R S m u₀ hT s‖ ^ 2 ≤ ‖u₀‖ ^ 2 / 2 :=
  OpenDomainUnforcedUniformBounds.integral_gradient_sq_le Ω R S m u₀ hT
    (⟨hT, le_rfl⟩ : T ∈ Icc (0 : ℝ) T)

/-- **`L²` energy bound in the graph norm.**  The state and gradient bounds
add; no Poincaré inequality is used, so this holds in every dimension. -/
theorem integral_norm_energyPath_sq_le :
    ∫ s in (0 : ℝ)..T, ‖energyPath Ω R S m u₀ hT s‖ ^ 2 ≤
      T * ‖u₀‖ ^ 2 + ‖u₀‖ ^ 2 / 2 := by
  have hsplit :
      ∫ s in (0 : ℝ)..T, ‖energyPath Ω R S m u₀ hT s‖ ^ 2 =
        (∫ s in (0 : ℝ)..T, ‖statePath Ω R S m u₀ hT s‖ ^ 2) +
          ∫ s in (0 : ℝ)..T, ‖gradientPath Ω R S m u₀ hT s‖ ^ 2 := by
    rw [← intervalIntegral.integral_add
      (intervalIntegrable_norm_statePath_sq Ω R S m u₀ hT)
      (intervalIntegrable_norm_gradientPath_sq Ω R S m u₀ hT)]
    exact intervalIntegral.integral_congr
      (fun s _ => norm_energyPath_sq_eq Ω R S m u₀ hT s)
  have h1 := integral_norm_statePath_sq_le Ω R S m u₀ hT
  have h2 := integral_norm_gradientPath_sq_le Ω R S m u₀ hT
  rw [hsplit]
  linarith

end Paths

/-! ### Uniform bounds for the concrete paths -/

section Family

/-- **Uniform pointwise state bound**, in the shape of
`CompactnessInterface.UniformEnergyBoundOn`. -/
theorem uniform_state_pointwise_bound (Ω : OpenDomainInBox Q)
    (R : BoxEnergyL4Realization Q)
    (S : OpenDomainCompactSpectralRepresentation Ω)
    (u₀ : OpenDomainL2Sigma Ω) {T : ℝ} (hT : 0 ≤ T) :
    UniformEnergyBoundOn (fun m t => statePath Ω R S m u₀ hT t) T (‖u₀‖ ^ 2) :=
  fun m _t ht => norm_statePath_sq_le Ω R S m u₀ hT ht

/-- **Uniform `L²` state bound.** -/
theorem uniform_state_l2_bound (Ω : OpenDomainInBox Q)
    (R : BoxEnergyL4Realization Q)
    (S : OpenDomainCompactSpectralRepresentation Ω)
    (u₀ : OpenDomainL2Sigma Ω) {T : ℝ} (hT : 0 ≤ T) :
    ∀ m, ∫ s in (0 : ℝ)..T, ‖statePath Ω R S m u₀ hT s‖ ^ 2 ≤
      T * ‖u₀‖ ^ 2 :=
  fun m => integral_norm_statePath_sq_le Ω R S m u₀ hT

/-- **Uniform `L²` gradient bound.** -/
theorem uniform_gradient_l2_bound (Ω : OpenDomainInBox Q)
    (R : BoxEnergyL4Realization Q)
    (S : OpenDomainCompactSpectralRepresentation Ω)
    (u₀ : OpenDomainL2Sigma Ω) {T : ℝ} (hT : 0 ≤ T) :
    ∀ m, ∫ s in (0 : ℝ)..T, ‖gradientPath Ω R S m u₀ hT s‖ ^ 2 ≤
      ‖u₀‖ ^ 2 / 2 :=
  fun m => integral_norm_gradientPath_sq_le Ω R S m u₀ hT

/-- **Uniform `L²` energy bound in the graph norm.** -/
theorem uniform_energy_l2_bound (Ω : OpenDomainInBox Q)
    (R : BoxEnergyL4Realization Q)
    (S : OpenDomainCompactSpectralRepresentation Ω)
    (u₀ : OpenDomainL2Sigma Ω) {T : ℝ} (hT : 0 ≤ T) :
    ∀ m, ∫ s in (0 : ℝ)..T, ‖energyPath Ω R S m u₀ hT s‖ ^ 2 ≤
      T * ‖u₀‖ ^ 2 + ‖u₀‖ ^ 2 / 2 :=
  fun m => integral_norm_energyPath_sq_le Ω R S m u₀ hT

end Family

end OpenDomainUnforcedLpFamily

end
