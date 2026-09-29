import PDEIdeas.OpenDomainUnforcedGalerkin
import PDEIdeas.OpenDomainEnergyLimit

/-!
# From unforced Galerkin solutions to the energy-limit hypotheses

`PDEIdeas.OpenDomainEnergyLimit` passes an energy inequality to the Galerkin
limit, taking the finite-level inequality and the convergence of its right-hand
side as explicit hypotheses.  This file discharges those two hypotheses for the
*unforced* subdomain family, from the actual coefficient solutions of
`PDEIdeas.OpenDomainUnforcedGalerkin` and the spectral projections of
`CompactEmbeddingSpectralRepresentation`.

## What is derived, and from what

The energy inequality is **not** assumed.  It is obtained by weakening
`OpenDomainUnforcedGalerkin.energyIdentityAtTime`, which is itself proved from
the coefficient dynamics; the only extra ingredient is nonnegativity of the
diffusion form, which is already a hypothesis of the unforced problem.

The right-hand side is the projected initial energy.  This file supplies the
missing state-side projection — `testProjection` projects an *energy* vector,
whereas an initial datum is a *pivot* vector — as `stateInitialCoefficient`,
and proves its convergence from the generic
`GalerkinProjectorSequence.finitePartialProjection_tendsto`.

## Main results

* `stateInitialCoefficient` — the initial datum in the level-`m` state head,
  with `norm_stateInitialCoefficient_le` and
  `stateInitialCoefficient_tendsto`.
* `tendsto_norm_sq_stateInitialCoefficient` — the projected initial energy
  converges to the initial energy.  This is the `hC` input.
* `finite_energyInequality` — the finite-level inequality at a single time.
* `finite_energyInequality_of_le` — the same with the dissipation accumulated
  only up to an earlier time, which needs interval integrability of the
  dissipation integrand; that integrability is an explicit hypothesis.
* `hfinite_of_unforcedSolutions`, `hC_of_unforcedSolutions`,
  `hinit_of_unforcedSolutions` — the three hypotheses of
  `OpenDomainEnergyLimit.energyLimitOfFiniteLevel`, in its exact shape.

## What is still needed, and is kept explicit

The compactness side is *not* built here.  `hfinite_of_unforcedSolutions` and
`hinit_of_unforcedSolutions` take the family `G` as given, together with three
statements relating it to the concrete solutions:

* `hstate` — `‖G.statePath k t‖` is the norm of the level-`k` solution at `t`;
* `hstate0` — `G.statePath k` starts at the projected initial datum;
* `hdiss` — the family's dissipation over `past t`, in the time measure `μ`, is
  at most the solution's dissipation over the real interval `[0, t]`.

All three are facts about how `G` was constructed, and
`OpenDomainTimeCompactness.openDomainCompactFamily` is the intended source.
`hdiss` in particular carries the transfer between the interval-subtype measure
and the real interval integral, which no file in the subdomain layer sets up
yet.  None of the three is proved here.

## Scope

No solution is constructed and no existence theorem is claimed, for any domain.
This file connects two existing pieces and nothing more.
-/

open BoundedContinuousFunction Filter Function InnerProductSpace MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace Topology

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace OpenDomainEnergyInequalityBridge

/-! ## Spectral initial data -/

section SpectralInitial

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] {J : V →L[ℝ] H}
    (S : CompactEmbeddingSpectralRepresentation J)

/-- The initial datum orthogonally projected into the level-`m` state head.
This is the state-side counterpart of `testProjection`, which projects an
energy vector; here the argument is already a pivot-space vector. -/
def stateInitialCoefficient (m : ℕ) : H →L[ℝ] S.stateSpace m :=
  (S.stateProjection m).codRestrict (S.stateSpace m) fun x => by
    change GalerkinProjectorSequence.finitePartialProjection
        S.stateBasis (S.exhaustion.head m) x ∈
      GalerkinProjectorSequence.finitePartialSpace
        S.stateBasis (S.exhaustion.head m)
    rw [← GalerkinProjectorSequence.range_finitePartialProjection]
    exact ⟨x, rfl⟩

@[simp]
theorem stateInitialCoefficient_coe (m : ℕ) (u₀ : H) :
    (stateInitialCoefficient S m u₀ : H) = S.stateProjection m u₀ := rfl

@[simp]
theorem stateSynthesis_stateInitialCoefficient (m : ℕ) (u₀ : H) :
    S.stateSynthesis m (stateInitialCoefficient S m u₀) =
      S.stateProjection m u₀ := rfl

theorem norm_stateInitialCoefficient_le (m : ℕ) (u₀ : H) :
    ‖stateInitialCoefficient S m u₀‖ ≤ ‖u₀‖ := by
  show ‖S.stateProjection m u₀‖ ≤ ‖u₀‖
  calc ‖S.stateProjection m u₀‖ ≤ ‖S.stateProjection m‖ * ‖u₀‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖u₀‖ :=
        mul_le_mul_of_nonneg_right
          (GalerkinProjectorSequence.finitePartialProjection_norm_le _ _)
          (norm_nonneg _)
    _ = ‖u₀‖ := one_mul _

/-- **The spectral heads recover the initial datum.** -/
theorem stateInitialCoefficient_tendsto (u₀ : H) :
    Tendsto (fun m => (stateInitialCoefficient S m u₀ : H)) atTop (𝓝 u₀) :=
  GalerkinProjectorSequence.finitePartialProjection_tendsto
    S.stateBasis S.exhaustion u₀

/-- **Convergence of the initial-energy right-hand side.**  This is the
`hC` hypothesis of `OpenDomainEnergyLimit.energyLimitOfFiniteLevel` for the
unforced family, where the level-`m` right-hand side is the projected initial
energy. -/
theorem tendsto_norm_sq_stateInitialCoefficient (u₀ : H) :
    Tendsto (fun m => ‖stateInitialCoefficient S m u₀‖ ^ 2) atTop
      (𝓝 (‖u₀‖ ^ 2)) := by
  have h : Tendsto (fun m => ‖(stateInitialCoefficient S m u₀ : H)‖) atTop
      (𝓝 ‖u₀‖) :=
    (continuous_norm.tendsto u₀).comp (stateInitialCoefficient_tendsto S u₀)
  exact h.pow 2

end SpectralInitial

/-! ## The finite-level energy inequality -/

section FiniteLevel

open OpenDomainUnforcedGalerkin

variable {n : ℕ} {Q : BoxIntegral.Box (Fin (n + 1))} {Ω : OpenDomainInBox Q}

variable (Ω) (R : BoxEnergyL4Realization Q)
    (D : OpenDomainH1ZeroSigma Ω →L[ℝ] OpenDomainH1ZeroSigma Ω →L[ℝ] ℝ)
    (hD : ∀ u, 0 ≤ D u u)
    (S : OpenDomainCompactSpectralRepresentation Ω) (m : ℕ)

/-- **The finite-level energy inequality.**  Weakening of the unforced energy
identity `OpenDomainUnforcedGalerkin.energyIdentityAtTime`; the identity is
*derived* there from the coefficient dynamics and is not assumed here. -/
theorem finite_energyInequality (initial : S.stateSpace m)
    {T : ℝ} (hT : 0 ≤ T)
    (u : (unforcedProblem Ω R D hD S m initial).LocalSolutionOn
      (⟨0, le_rfl, hT⟩ : Icc (0 : ℝ) T))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ‖u.toFun t‖ ^ 2
      + 2 * ∫ s in (0 : ℝ)..t,
          D (S.energySynthesis m (u.toFun s)) (S.energySynthesis m (u.toFun s))
      ≤ ‖initial‖ ^ 2 :=
  le_of_eq (energyIdentityAtTime Ω R D hD S m initial hT u ht)

/-- **The finite-level energy inequality with dissipation accumulated only up
to an earlier time.**  The integrability of the dissipation integrand is kept
explicit: the Bochner integral in the identity is well defined regardless, but
splitting the interval needs it. -/
theorem finite_energyInequality_of_le (initial : S.stateSpace m)
    {T : ℝ} (hT : 0 ≤ T)
    (u : (unforcedProblem Ω R D hD S m initial).LocalSolutionOn
      (⟨0, le_rfl, hT⟩ : Icc (0 : ℝ) T))
    {t r : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (hr0 : 0 ≤ r) (hrt : r ≤ t)
    (hint : IntervalIntegrable
      (fun s => D (S.energySynthesis m (u.toFun s))
        (S.energySynthesis m (u.toFun s))) volume 0 t) :
    ‖u.toFun t‖ ^ 2
      + 2 * ∫ s in (0 : ℝ)..r,
          D (S.energySynthesis m (u.toFun s)) (S.energySynthesis m (u.toFun s))
      ≤ ‖initial‖ ^ 2 := by
  have hId := energyIdentityAtTime Ω R D hD S m initial hT u ht
  have hsub1 : Set.uIcc (0 : ℝ) r ⊆ Set.uIcc (0 : ℝ) t := by
    rw [Set.uIcc_of_le hr0, Set.uIcc_of_le ht.1]
    exact Set.Icc_subset_Icc le_rfl hrt
  have hsub2 : Set.uIcc r t ⊆ Set.uIcc (0 : ℝ) t := by
    rw [Set.uIcc_of_le hrt, Set.uIcc_of_le ht.1]
    exact Set.Icc_subset_Icc hr0 le_rfl
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hint.mono_set hsub1) (hint.mono_set hsub2)
  have hnonneg : 0 ≤ ∫ s in r..t,
      D (S.energySynthesis m (u.toFun s))
        (S.energySynthesis m (u.toFun s)) :=
    intervalIntegral.integral_nonneg hrt fun s _ => hD _
  linarith

end FiniteLevel

/-! ## The hypotheses of `energyLimitOfFiniteLevel` -/

section Bridge

open OpenDomainUnforcedGalerkin

variable {n : ℕ} {Q : BoxIntegral.Box (Fin (n + 1))} {Ω : OpenDomainInBox Q}

variable (Ω) (R : BoxEnergyL4Realization Q)
    (D : OpenDomainH1ZeroSigma Ω →L[ℝ] OpenDomainH1ZeroSigma Ω →L[ℝ] ℝ)
    (hD : ∀ u, 0 ≤ D u u)
    (S : OpenDomainCompactSpectralRepresentation Ω)

/-- **The finite-level hypothesis of `energyLimitOfFiniteLevel`, discharged for
the unforced family.**

The level-`k` right-hand side is the projected initial energy
`‖stateInitialCoefficient S (level k) u₀‖ ^ 2`.  Nothing about the energy
inequality is assumed: it comes out of
`OpenDomainUnforcedGalerkin.energyIdentityAtTime`, which is itself derived from
the coefficient dynamics.

Two hypotheses are left explicit because they are exactly the compactness-side
link between the abstract family `G` and the concrete Galerkin solutions, which
`OpenDomainTimeCompactness.openDomainCompactFamily` is what supplies:

* `hstate` — the family's state path at level `k` has the norm of the
  level-`k` solution;
* `hdiss` — the family's dissipation over `past t`, measured in `μ`, is at most
  the solution's dissipation over the real interval `[0, t]`.

Neither is proved here; both are statements about how `G` was built. -/
theorem hfinite_of_unforcedSolutions
    {T : ℝ} (hT : 0 ≤ T)
    {μ : Measure (Icc (0 : ℝ) T)} [IsFiniteMeasure μ]
    (G : LeraySpectralCompactFamily (I := Icc (0 : ℝ) T)
      (V := OpenDomainH1ZeroSigma Ω) (H := OpenDomainL2Sigma Ω) (μ := μ))
    {Grad : Type*} [NormedAddCommGroup Grad] [InnerProductSpace ℝ Grad]
    (grad : OpenDomainH1ZeroSigma Ω →L[ℝ] Grad)
    (past : Icc (0 : ℝ) T → Set (Icc (0 : ℝ) T))
    (level : ℕ → ℕ) (u₀ : OpenDomainL2Sigma Ω)
    (sol : ∀ k : ℕ,
      (unforcedProblem Ω R D hD S (level k)
        (stateInitialCoefficient S (level k) u₀)).LocalSolutionOn
        (⟨0, le_rfl, hT⟩ : Icc (0 : ℝ) T))
    (hstate : ∀ (k : ℕ) (t : Icc (0 : ℝ) T),
      ‖G.statePath k t‖ = ‖(sol k).toFun (t : ℝ)‖)
    (hdiss : ∀ (k : ℕ) (t : Icc (0 : ℝ) T),
      (∫ s in past t, ‖grad (G.energyLp k s)‖ ^ 2 ∂μ)
        ≤ ∫ s in (0 : ℝ)..(t : ℝ),
            D (S.energySynthesis (level k) ((sol k).toFun s))
              (S.energySynthesis (level k) ((sol k).toFun s))) :
    ∀ (t : Icc (0 : ℝ) T) (k : ℕ),
      ‖G.statePath k t‖ ^ 2
          + 2 * ∫ s in past t, ‖grad (G.energyLp k s)‖ ^ 2 ∂μ
        ≤ ‖stateInitialCoefficient S (level k) u₀‖ ^ 2 := by
  intro t k
  have hId := energyIdentityAtTime Ω R D hD S (level k)
    (stateInitialCoefficient S (level k) u₀) hT (sol k) t.2
  have hle := hdiss k t
  rw [hstate k t]
  linarith

/-- **The `hC` hypothesis of `energyLimitOfFiniteLevel`, discharged for the
unforced family.**  Along any level sequence tending to infinity the projected
initial energy converges to the initial energy. -/
theorem hC_of_unforcedSolutions (level : ℕ → ℕ)
    (hlevel : Tendsto level atTop atTop) (u₀ : OpenDomainL2Sigma Ω) :
    Tendsto (fun k => ‖stateInitialCoefficient S (level k) u₀‖ ^ 2) atTop
      (𝓝 (‖u₀‖ ^ 2)) :=
  (tendsto_norm_sq_stateInitialCoefficient S u₀).comp hlevel

/-- **The `hinit` hypothesis of `energyLimitOfFiniteLevel`, discharged for the
unforced family.**  The remaining input `hstate0` says that the family's state
path starts at the projected initial datum, which is again a statement about
how `G` was built. -/
theorem hinit_of_unforcedSolutions
    {T : ℝ} (hT : 0 ≤ T)
    {μ : Measure (Icc (0 : ℝ) T)} [IsFiniteMeasure μ]
    (G : LeraySpectralCompactFamily (I := Icc (0 : ℝ) T)
      (V := OpenDomainH1ZeroSigma Ω) (H := OpenDomainL2Sigma Ω) (μ := μ))
    (level : ℕ → ℕ) (hlevel : Tendsto level atTop atTop)
    (u₀ : OpenDomainL2Sigma Ω)
    (hstate0 : ∀ k : ℕ,
      G.statePath k (⟨0, le_rfl, hT⟩ : Icc (0 : ℝ) T)
        = (stateInitialCoefficient S (level k) u₀ : OpenDomainL2Sigma Ω)) :
    Tendsto (fun k => G.statePath k (⟨0, le_rfl, hT⟩ : Icc (0 : ℝ) T)) atTop
      (𝓝 u₀) := by
  simp only [hstate0]
  exact (stateInitialCoefficient_tendsto S u₀).comp hlevel

end Bridge

end OpenDomainEnergyInequalityBridge
