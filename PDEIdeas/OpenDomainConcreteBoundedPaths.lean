import PDEIdeas.OpenDomainUnforcedLpFamily

/-!
# The unforced Galerkin paths as bounded continuous paths on `Icc 0 T`

`PDEIdeas.OpenDomainUnforcedLpFamily` reads the selected unforced coefficient
trajectory `OpenDomainUnforcedUniformBounds.solution Ω R S m u₀ hT` into the
three ambient spaces — the pivot space `L²_σ(Ω)`, the energy space
`H¹_{0,σ}(Ω)`, and the ambient gradient space `BoxGradientL2 Q` — as functions
`ℝ → _` that are continuous on `Icc 0 T`, and proves the a priori bounds there.

A function continuous on a compact interval is a bounded continuous function on
that interval.  This file performs that packaging for the **actual** Galerkin
paths and carries the bounds across:

* `stateMap`, `energyMap`, `gradientMap` — the restrictions to
  `↥(Icc 0 T)` as `ContinuousMap`s, built from
  `OpenDomainUnforcedLpFamily.continuousOn_statePath` and its two companions;
* `stateBounded`, `energyBounded`, `gradientBounded` — the same paths as
  elements of `↥(Icc 0 T) →ᵇ _`, via
  `BoundedContinuousFunction.mkOfCompact`.

Each is *definitionally* the corresponding path of
`PDEIdeas.OpenDomainUnforcedLpFamily` restricted to the interval, so
`stateBounded_apply_solution` and `energyBounded_apply_solution` exhibit them
as the trajectory itself, read through the head inclusion and the energy lift.

## The bounds

Nothing here is posited.  Every bound is the corresponding statement of
`PDEIdeas.OpenDomainUnforcedLpFamily` evaluated at the coerced point of
`Icc 0 T`, or transported across `Set.projIcc`:

* **State bounds.**  `norm_stateBounded_apply_le` is the `L∞` pivot bound at a
  point of the interval; `bddAbove_range_norm_stateBounded` and
  `iSup_norm_stateBounded_le` upgrade it to a bound on the *supremum* of the
  norm along the path.  Both right-hand sides are `‖u₀‖`.  (The supremum is
  written as `⨆ t, ‖f t‖` rather than the sup norm `‖f‖` of the bounded
  continuous function: `Norm (↥(Icc 0 T) →ᵇ _)` does not synthesize for these
  codomains, because the `PseudoMetricSpace` instance that the `→ᵇ` type picks
  up for a submodule of an `Lp` space is the subtype one, which `instNorm`
  cannot reconcile with the submodule's `SeminormedAddCommGroup`.  The `Dist`
  structure of the path is unaffected, and `⨆ t, ‖f t‖` states the same
  bound.)
* **`L²` energy bounds.**  `integral_norm_stateBounded_sq_le`,
  `integral_norm_gradientBounded_sq_le` and `integral_norm_energyBounded_sq_le`
  bound `∫₀ᵀ ‖·‖²` of the bounded path — written as the composition with
  `Set.projIcc 0 T hT`, which is the identity on `[0, T]` — by
  `T * ‖u₀‖²`, `‖u₀‖² / 2` and `T * ‖u₀‖² + ‖u₀‖² / 2` respectively.  The
  transport is `intervalIntegral.integral_congr` together with
  `Set.projIcc_of_mem`; the bounds themselves are the ones already proved in
  `PDEIdeas.OpenDomainUnforcedLpFamily`.
* **Graph-norm split.**  `norm_energyBounded_sq_eq` records that the energy
  bound is exactly the sum of the other two at each point of the interval.

All right-hand sides mention only `‖u₀‖` and `T`, so the `uniform_*` section
restates them as bounds holding at every spectral level `m`.
-/

open MeasureTheory Set
open scoped BoundedContinuousFunction

noncomputable section

/- The ambient spaces here are submodules of `Lp` spaces, and resolving their
normed-group structure inside the larger search for
`Norm (↥(Icc 0 T) →ᵇ _)` exceeds the default `synthInstance` budget.  This is
the same setting used by `PDEIdeas.OpenDomainUnforcedLpFamily` and the other
open-domain Galerkin files. -/
set_option synthInstance.maxHeartbeats 400000

namespace OpenDomainConcreteBoundedPaths

variable {n : ℕ} {Q : BoxIntegral.Box (Fin (n + 1))} {Ω : OpenDomainInBox Q}

section Level

variable (Ω) (R : BoxEnergyL4Realization Q)
    (S : OpenDomainCompactSpectralRepresentation Ω) (m : ℕ)
    (u₀ : OpenDomainL2Sigma Ω) {T : ℝ} (hT : 0 ≤ T)

/-! ### The paths as continuous maps on the compact interval -/

/-- The state path restricted to `Icc 0 T` as a continuous map. -/
def stateMap : C(Icc (0 : ℝ) T, OpenDomainL2Sigma Ω) :=
  ⟨Set.restrict (Icc (0 : ℝ) T)
      (OpenDomainUnforcedLpFamily.statePath Ω R S m u₀ hT),
    (OpenDomainUnforcedLpFamily.continuousOn_statePath Ω R S m u₀ hT).restrict⟩

/-- The energy path restricted to `Icc 0 T` as a continuous map. -/
def energyMap : C(Icc (0 : ℝ) T, OpenDomainH1ZeroSigma Ω) :=
  ⟨Set.restrict (Icc (0 : ℝ) T)
      (OpenDomainUnforcedLpFamily.energyPath Ω R S m u₀ hT),
    (OpenDomainUnforcedLpFamily.continuousOn_energyPath Ω R S m u₀ hT).restrict⟩

/-- The gradient path restricted to `Icc 0 T` as a continuous map. -/
def gradientMap : C(Icc (0 : ℝ) T, BoxGradientL2 Q) :=
  ⟨Set.restrict (Icc (0 : ℝ) T)
      (OpenDomainUnforcedLpFamily.gradientPath Ω R S m u₀ hT),
    (OpenDomainUnforcedLpFamily.continuousOn_gradientPath Ω R S m u₀ hT).restrict⟩

/-! ### The bounded continuous paths -/

/-- The level-`m` state path as a **bounded continuous path** on `Icc 0 T`. -/
def stateBounded : Icc (0 : ℝ) T →ᵇ OpenDomainL2Sigma Ω :=
  BoundedContinuousFunction.mkOfCompact (stateMap Ω R S m u₀ hT)

/-- The level-`m` energy path as a **bounded continuous path** on `Icc 0 T`. -/
def energyBounded : Icc (0 : ℝ) T →ᵇ OpenDomainH1ZeroSigma Ω :=
  BoundedContinuousFunction.mkOfCompact (energyMap Ω R S m u₀ hT)

/-- The level-`m` gradient path as a **bounded continuous path** on
`Icc 0 T`. -/
def gradientBounded : Icc (0 : ℝ) T →ᵇ BoxGradientL2 Q :=
  BoundedContinuousFunction.mkOfCompact (gradientMap Ω R S m u₀ hT)

@[simp]
theorem stateBounded_apply (t : Icc (0 : ℝ) T) :
    stateBounded Ω R S m u₀ hT t =
      OpenDomainUnforcedLpFamily.statePath Ω R S m u₀ hT t := rfl

@[simp]
theorem energyBounded_apply (t : Icc (0 : ℝ) T) :
    energyBounded Ω R S m u₀ hT t =
      OpenDomainUnforcedLpFamily.energyPath Ω R S m u₀ hT t := rfl

@[simp]
theorem gradientBounded_apply (t : Icc (0 : ℝ) T) :
    gradientBounded Ω R S m u₀ hT t =
      OpenDomainUnforcedLpFamily.gradientPath Ω R S m u₀ hT t := rfl

/-- The bounded state path is the selected trajectory itself, read through the
head inclusion. -/
theorem stateBounded_apply_solution (t : Icc (0 : ℝ) T) :
    stateBounded Ω R S m u₀ hT t =
      S.stateSynthesis m
        ((OpenDomainUnforcedUniformBounds.solution Ω R S m u₀ hT).toFun t) :=
  rfl

/-- The bounded energy path is the selected trajectory itself, lifted to the
energy space. -/
theorem energyBounded_apply_solution (t : Icc (0 : ℝ) T) :
    energyBounded Ω R S m u₀ hT t =
      S.energySynthesis m
        ((OpenDomainUnforcedUniformBounds.solution Ω R S m u₀ hT).toFun t) :=
  rfl

/-- The bounded gradient path is the subdomain energy gradient of the bounded
energy path. -/
theorem gradientBounded_eq_openDomainEnergyGradient (t : Icc (0 : ℝ) T) :
    gradientBounded Ω R S m u₀ hT t =
      openDomainEnergyGradient Ω (energyBounded Ω R S m u₀ hT t) :=
  OpenDomainUnforcedLpFamily.gradientPath_eq_openDomainEnergyGradient
    Ω R S m u₀ hT t

/-- The bounded state path is the pivot image of the bounded energy path. -/
theorem openDomainEnergyToState_energyBounded (t : Icc (0 : ℝ) T) :
    openDomainEnergyToState Ω (energyBounded Ω R S m u₀ hT t) =
      stateBounded Ω R S m u₀ hT t :=
  OpenDomainUnforcedLpFamily.openDomainEnergyToState_energyPath
    Ω R S m u₀ hT t

/-! ### State bounds -/

/-- **Pointwise state bound** on the interval. -/
theorem norm_stateBounded_apply_le (t : Icc (0 : ℝ) T) :
    ‖stateBounded Ω R S m u₀ hT t‖ ≤ ‖u₀‖ :=
  OpenDomainUnforcedLpFamily.norm_statePath_le Ω R S m u₀ hT t.2

theorem norm_stateBounded_apply_sq_le (t : Icc (0 : ℝ) T) :
    ‖stateBounded Ω R S m u₀ hT t‖ ^ 2 ≤ ‖u₀‖ ^ 2 :=
  OpenDomainUnforcedLpFamily.norm_statePath_sq_le Ω R S m u₀ hT t.2

/-- The norms along the bounded state path are bounded above by `‖u₀‖`. -/
theorem bddAbove_range_norm_stateBounded :
    BddAbove (Set.range fun t => ‖stateBounded Ω R S m u₀ hT t‖) := by
  refine ⟨‖u₀‖, ?_⟩
  rintro _ ⟨t, rfl⟩
  exact norm_stateBounded_apply_le Ω R S m u₀ hT t

/-- **Supremum state bound.**  The supremum of the norm along the bounded
continuous state path is at most `‖u₀‖`. -/
theorem iSup_norm_stateBounded_le :
    ⨆ t : Icc (0 : ℝ) T, ‖stateBounded Ω R S m u₀ hT t‖ ≤ ‖u₀‖ := by
  haveI : Nonempty (Icc (0 : ℝ) T) := ⟨⟨0, ⟨le_rfl, hT⟩⟩⟩
  exact ciSup_le (norm_stateBounded_apply_le Ω R S m u₀ hT)

/-- The graph norm of the bounded energy path splits pointwise into its state
and gradient parts. -/
theorem norm_energyBounded_sq_eq (t : Icc (0 : ℝ) T) :
    ‖energyBounded Ω R S m u₀ hT t‖ ^ 2 =
      ‖stateBounded Ω R S m u₀ hT t‖ ^ 2 +
        ‖gradientBounded Ω R S m u₀ hT t‖ ^ 2 :=
  OpenDomainUnforcedLpFamily.norm_energyPath_sq_eq Ω R S m u₀ hT t

/-! ### `L²` energy bounds -/

/-- On `[0, T]` the bounded path composed with `Set.projIcc` is the underlying
path, so the two interval integrals of its squared norm agree. -/
private theorem integral_projIcc_congr {X : Type*} [NormedAddCommGroup X]
    (f : Icc (0 : ℝ) T →ᵇ X) (g : ℝ → X)
    (hfg : ∀ (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T), f ⟨s, hs⟩ = g s) :
    ∫ s in (0 : ℝ)..T, ‖f (Set.projIcc 0 T hT s)‖ ^ 2 =
      ∫ s in (0 : ℝ)..T, ‖g s‖ ^ 2 := by
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le hT] at hs
  rw [Set.projIcc_of_mem hT hs, hfg s hs]

/-- **`L²` state bound** for the bounded continuous path. -/
theorem integral_norm_stateBounded_sq_le :
    ∫ s in (0 : ℝ)..T,
        ‖stateBounded Ω R S m u₀ hT (Set.projIcc 0 T hT s)‖ ^ 2 ≤
      T * ‖u₀‖ ^ 2 :=
  (integral_projIcc_congr hT (stateBounded Ω R S m u₀ hT)
      (OpenDomainUnforcedLpFamily.statePath Ω R S m u₀ hT)
      (fun _ _ => rfl)).trans_le
    (OpenDomainUnforcedLpFamily.integral_norm_statePath_sq_le Ω R S m u₀ hT)

/-- **`L²` gradient bound** for the bounded continuous path: the dissipation
bound of the unforced energy identity. -/
theorem integral_norm_gradientBounded_sq_le :
    ∫ s in (0 : ℝ)..T,
        ‖gradientBounded Ω R S m u₀ hT (Set.projIcc 0 T hT s)‖ ^ 2 ≤
      ‖u₀‖ ^ 2 / 2 :=
  (integral_projIcc_congr hT (gradientBounded Ω R S m u₀ hT)
      (OpenDomainUnforcedLpFamily.gradientPath Ω R S m u₀ hT)
      (fun _ _ => rfl)).trans_le
    (OpenDomainUnforcedLpFamily.integral_norm_gradientPath_sq_le Ω R S m u₀ hT)

/-- **`L²` energy bound** for the bounded continuous path, in the graph norm of
`H¹_{0,σ}(Ω)`. -/
theorem integral_norm_energyBounded_sq_le :
    ∫ s in (0 : ℝ)..T,
        ‖energyBounded Ω R S m u₀ hT (Set.projIcc 0 T hT s)‖ ^ 2 ≤
      T * ‖u₀‖ ^ 2 + ‖u₀‖ ^ 2 / 2 :=
  (integral_projIcc_congr hT (energyBounded Ω R S m u₀ hT)
      (OpenDomainUnforcedLpFamily.energyPath Ω R S m u₀ hT)
      (fun _ _ => rfl)).trans_le
    (OpenDomainUnforcedLpFamily.integral_norm_energyPath_sq_le Ω R S m u₀ hT)

end Level

/-! ### The bounds hold at every spectral level -/

section Family

variable (Ω : OpenDomainInBox Q) (R : BoxEnergyL4Realization Q)
    (S : OpenDomainCompactSpectralRepresentation Ω)
    (u₀ : OpenDomainL2Sigma Ω) {T : ℝ} (hT : 0 ≤ T)

/-- **Uniform pointwise state bound**, at every spectral level. -/
theorem uniform_norm_stateBounded_apply_le :
    ∀ (m : ℕ) (t : Icc (0 : ℝ) T),
      ‖stateBounded Ω R S m u₀ hT t‖ ≤ ‖u₀‖ :=
  fun m => norm_stateBounded_apply_le Ω R S m u₀ hT

/-- **Uniform supremum state bound**, at every spectral level. -/
theorem uniform_iSup_norm_stateBounded_le :
    ∀ m, ⨆ t : Icc (0 : ℝ) T, ‖stateBounded Ω R S m u₀ hT t‖ ≤ ‖u₀‖ :=
  fun m => iSup_norm_stateBounded_le Ω R S m u₀ hT

/-- **Uniform `L²` state bound**, at every spectral level. -/
theorem uniform_integral_norm_stateBounded_sq_le :
    ∀ m, ∫ s in (0 : ℝ)..T,
        ‖stateBounded Ω R S m u₀ hT (Set.projIcc 0 T hT s)‖ ^ 2 ≤
      T * ‖u₀‖ ^ 2 :=
  fun m => integral_norm_stateBounded_sq_le Ω R S m u₀ hT

/-- **Uniform `L²` gradient bound**, at every spectral level. -/
theorem uniform_integral_norm_gradientBounded_sq_le :
    ∀ m, ∫ s in (0 : ℝ)..T,
        ‖gradientBounded Ω R S m u₀ hT (Set.projIcc 0 T hT s)‖ ^ 2 ≤
      ‖u₀‖ ^ 2 / 2 :=
  fun m => integral_norm_gradientBounded_sq_le Ω R S m u₀ hT

/-- **Uniform `L²` energy bound**, at every spectral level. -/
theorem uniform_integral_norm_energyBounded_sq_le :
    ∀ m, ∫ s in (0 : ℝ)..T,
        ‖energyBounded Ω R S m u₀ hT (Set.projIcc 0 T hT s)‖ ^ 2 ≤
      T * ‖u₀‖ ^ 2 + ‖u₀‖ ^ 2 / 2 :=
  fun m => integral_norm_energyBounded_sq_le Ω R S m u₀ hT

end Family

end OpenDomainConcreteBoundedPaths

end
