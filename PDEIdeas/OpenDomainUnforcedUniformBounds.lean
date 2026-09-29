import PDEIdeas.OpenDomainUnforcedGalerkin

/-!
# Level-uniform bounds for the unforced open-domain Galerkin family

`PDEIdeas.OpenDomainUnforcedGalerkin` produces, at every spectral level `m` and
for every initial coefficient in the head `S.stateSpace m`, an unforced
coefficient trajectory on every finite interval, together with the finite-level
energy identity

`‖u t‖ ^ 2 + 2 * ∫ s in 0..t, D (E (u s)) (E (u s)) = ‖initial‖ ^ 2`.

This file starts instead from arbitrary initial data `u₀ : OpenDomainL2Sigma Ω`
in the pivot space, projects it onto each finite head, selects the trajectory
issued from that projection, and reads the two a priori bounds off the identity.

## What is proved

* `stateHeadProjection` — the orthogonal projection of the pivot space onto the
  finite spectral head, with `norm_stateHeadProjection_le` its contractivity.
  This is the only place where the initial data are approximated.
* `solution` — the chosen level-`m` trajectory issued from
  `stateHeadProjection S m u₀`, for the physical convection form of `Ω` and the
  gradient diffusion of the ambient rectangle read through the isometric energy
  inclusion.
* `norm_solution_le` — the **L∞ bound in the pivot norm**: at every time of the
  interval and every level, `‖u_m t‖ ≤ ‖u₀‖`.
* `integral_gradient_sq_le` — the **L² bound in the gradient norm**: at every
  time of the interval and every level,
  `∫ s in 0..t, ‖∇ (E (u_m s))‖ ^ 2 ≤ ‖u₀‖ ^ 2 / 2`.
* `uniform_bounds` — the two bounds packaged under a single `∀ m`, which is the
  form a compactness argument consumes.

## Where the bounds come from

Both are read off the finite-level energy identity; neither is assumed.

The dissipation term of the identity is nonnegative, so the identity gives
`‖u_m t‖ ^ 2 ≤ ‖stateHeadProjection S m u₀‖ ^ 2`; contractivity of the spectral
projection replaces the right-hand side by `‖u₀‖ ^ 2`, and that is the first
bound.  Discarding instead the state term of the same identity gives
`2 * ∫ ‖∇ (E (u_m s))‖ ^ 2 ≤ ‖stateHeadProjection S m u₀‖ ^ 2 ≤ ‖u₀‖ ^ 2`, and
that is the second.  The two right-hand sides do not mention `m`, which is what
makes the bounds uniform in the spectral level; `uniform_bounds` states this
explicitly.

The gradient form of the dissipation comes from `boxGradientDiffusion_self`,
which identifies the ambient diffusion form on the diagonal with the squared
norm of the energy gradient.
-/

open MeasureTheory Set

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

namespace OpenDomainUnforcedUniformBounds

variable {n : ℕ} {Q : BoxIntegral.Box (Fin (n + 1))} {Ω : OpenDomainInBox Q}

/-! ### The finite spectral projection of the initial data -/

/-- Orthogonal projection of the pivot space onto the finite spectral head.
The head is the range of the spectral state projection, so the projection
corestricts to it. -/
def stateHeadProjection (S : OpenDomainCompactSpectralRepresentation Ω) (m : ℕ) :
    OpenDomainL2Sigma Ω →L[ℝ] S.stateSpace m :=
  (S.stateProjection m).codRestrict (S.stateSpace m) fun x => by
    change GalerkinProjectorSequence.finitePartialProjection
        S.stateBasis (S.exhaustion.head m) x ∈
      GalerkinProjectorSequence.finitePartialSpace
        S.stateBasis (S.exhaustion.head m)
    rw [← GalerkinProjectorSequence.range_finitePartialProjection]
    exact ⟨x, rfl⟩

@[simp]
theorem stateHeadProjection_apply
    (S : OpenDomainCompactSpectralRepresentation Ω) (m : ℕ)
    (x : OpenDomainL2Sigma Ω) :
    (stateHeadProjection S m x : OpenDomainL2Sigma Ω) = S.stateProjection m x :=
  rfl

/-- The spectral projection is a contraction of the pivot norm.  This is the
only estimate the initial data have to satisfy. -/
theorem norm_stateHeadProjection_le
    (S : OpenDomainCompactSpectralRepresentation Ω) (m : ℕ)
    (x : OpenDomainL2Sigma Ω) :
    ‖stateHeadProjection S m x‖ ≤ ‖x‖ := by
  change ‖(stateHeadProjection S m x : OpenDomainL2Sigma Ω)‖ ≤ ‖x‖
  rw [stateHeadProjection_apply]
  calc
    ‖S.stateProjection m x‖ ≤ ‖S.stateProjection m‖ * ‖x‖ :=
      (S.stateProjection m).le_opNorm x
    _ ≤ 1 * ‖x‖ :=
      mul_le_mul_of_nonneg_right
        (GalerkinProjectorSequence.finitePartialProjection_norm_le
          S.stateBasis (S.exhaustion.head m)) (norm_nonneg x)
    _ = ‖x‖ := one_mul _

/-! ### The selected level-`m` trajectory -/

section Family

variable (Ω) (R : BoxEnergyL4Realization Q)
    (S : OpenDomainCompactSpectralRepresentation Ω) (m : ℕ)
    (u₀ : OpenDomainL2Sigma Ω)

/-- The chosen unforced trajectory at level `m` issued from the spectral
projection of `u₀`, for the physical convection form of `Ω` and the ambient
gradient diffusion restricted to `Ω`. -/
def solution {T : ℝ} (hT : 0 ≤ T) :
    (OpenDomainUnforcedGalerkin.unforcedProblem Ω R
        ((boxGradientDiffusion Q).bilinearCompSame (openDomainEnergyToBox Ω))
        (fun w => boxGradientDiffusion_nonneg Q (openDomainEnergyToBox Ω w))
        S m (stateHeadProjection S m u₀)).LocalSolutionOn
      (⟨0, le_rfl, hT⟩ : Icc (0 : ℝ) T) :=
  Classical.choice
    (OpenDomainUnforcedGalerkin.exists_gradientDiffusionSolutionOn Ω R S m
      (stateHeadProjection S m u₀) hT)

/-- **L∞ bound in the pivot norm, uniform in the spectral level.**  The state
norm of the level-`m` trajectory never exceeds the pivot norm of the initial
data, at any time of the interval.  The right-hand side does not depend on `m`.

This is the energy identity with its nonnegative dissipation term discarded,
followed by contractivity of the spectral projection. -/
theorem norm_solution_le {T : ℝ} (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ‖(solution Ω R S m u₀ hT).toFun t‖ ≤ ‖u₀‖ :=
  le_trans
    (OpenDomainUnforcedGalerkin.norm_le_initial Ω R
      ((boxGradientDiffusion Q).bilinearCompSame (openDomainEnergyToBox Ω))
      (fun w => boxGradientDiffusion_nonneg Q (openDomainEnergyToBox Ω w))
      S m (stateHeadProjection S m u₀) hT (solution Ω R S m u₀ hT) ht)
    (norm_stateHeadProjection_le S m u₀)

/-- **L² bound in the gradient norm, uniform in the spectral level.**  The
accumulated squared gradient of the lifted trajectory is bounded by half the
squared pivot norm of the initial data, at every time of the interval.  The
right-hand side does not depend on `m`.

This is the energy identity with its nonnegative state term discarded, the
diffusion form rewritten on the diagonal as a squared gradient norm, and
contractivity of the spectral projection. -/
theorem integral_gradient_sq_le {T : ℝ} (hT : 0 ≤ T) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    ∫ s in (0 : ℝ)..t,
        ‖boxEnergyGradient Q
            (openDomainEnergyToBox Ω
              (S.energySynthesis m ((solution Ω R S m u₀ hT).toFun s)))‖ ^ 2
      ≤ ‖u₀‖ ^ 2 / 2 := by
  have hId :=
    OpenDomainUnforcedGalerkin.gradientDiffusion_energyIdentityAtTime Ω R S m
      (stateHeadProjection S m u₀) hT (solution Ω R S m u₀ hT) ht
  simp only [boxGradientDiffusion_self] at hId
  have hinit : ‖stateHeadProjection S m u₀‖ ≤ ‖u₀‖ :=
    norm_stateHeadProjection_le S m u₀
  have hinit0 : (0 : ℝ) ≤ ‖stateHeadProjection S m u₀‖ := norm_nonneg _
  have hinit2 : ‖stateHeadProjection S m u₀‖ ^ 2 ≤ ‖u₀‖ ^ 2 := by nlinarith
  have hstate : (0 : ℝ) ≤ ‖(solution Ω R S m u₀ hT).toFun t‖ ^ 2 := sq_nonneg _
  linarith

end Family

/-- **The two a priori bounds, uniform in the spectral level.**  For fixed
initial data in the pivot space and a fixed finite interval, every level of the
spectral tower carries a trajectory satisfying the same two bounds, with
constants depending only on `‖u₀‖`.  This is the form an Aubin–Lions or
weak-compactness argument consumes. -/
theorem uniform_bounds (Ω : OpenDomainInBox Q) (R : BoxEnergyL4Realization Q)
    (S : OpenDomainCompactSpectralRepresentation Ω)
    (u₀ : OpenDomainL2Sigma Ω) {T : ℝ} (hT : 0 ≤ T) :
    ∀ m : ℕ,
      (∀ t ∈ Icc (0 : ℝ) T, ‖(solution Ω R S m u₀ hT).toFun t‖ ≤ ‖u₀‖) ∧
        (∀ t ∈ Icc (0 : ℝ) T,
          ∫ s in (0 : ℝ)..t,
              ‖boxEnergyGradient Q
                  (openDomainEnergyToBox Ω
                    (S.energySynthesis m
                      ((solution Ω R S m u₀ hT).toFun s)))‖ ^ 2
            ≤ ‖u₀‖ ^ 2 / 2) :=
  fun m =>
    ⟨fun _ ht => norm_solution_le Ω R S m u₀ hT ht,
      fun _ ht => integral_gradient_sq_le Ω R S m u₀ hT ht⟩

end OpenDomainUnforcedUniformBounds

end
