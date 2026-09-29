import PDEIdeas.OpenDomainSpectral
import PDEIdeas.OpenDomainPhysicalConvection
import PDEIdeas.AbstractSpectralDynamics

/-!
# Unforced Galerkin dynamics on the open-domain spectral tower

`PDEIdeas.OpenDomainSpectral` produces the spectral representation
`openDomainCompactSpectralRepresentation Ω` of the compact embedding
`openDomainEnergyToState Ω`, hence the finite state heads `S.stateSpace m` and
the energy lift `S.energySynthesis m`.  `PDEIdeas.OpenDomainPhysicalConvection`
produces the bounded skew form
`OpenDomainPhysicalConvection.energyConvectionForm Ω R` of the subdomain.
`PDEIdeas.AbstractSpectralDynamics` carries the generic finite-dimensional
theory from `PDEIdeas.VariationalGalerkin` onto an arbitrary spectral head.

This file performs one instantiation of that generic theory: **zero forcing**.
Nothing here is reproved.  The coefficient ODE, its energy-driven continuation
and the energy identity are used exactly as they stand; the content is that the
unforced hypotheses discharge, and what they discharge to.

## What zero forcing buys

With `forcing = 0` the two hypotheses of the generic existence theorem collapse:

* the Young-type absorption `2 * F t u ≤ g t + D u u` becomes `0 ≤ D u u`, which
  is the nonnegativity of the diffusion form itself, so the majorant may be
  taken to be `g = 0`;
* the energy budget `‖initial‖ ^ 2 + ∫ g ≤ R ^ 2` then closes with
  `R = ‖initial‖`.

In particular no Poincaré inequality, no Ladyzhenskaya estimate and no
dimension restriction enter: the results below hold on a subdomain of a
rectangle in every dimension `n + 1`, and for **every** element of the head as
initial coefficient — with zero forcing there is no admissibility condition
left to impose.

## Main statements

* `OpenDomainUnforcedGalerkin.unforcedProblem` — the level-`m` variational
  problem of `Ω`: physical convection, a nonnegative diffusion form, zero
  forcing.
* `OpenDomainUnforcedGalerkin.exists_unforcedSolutionOn` — a solution on every
  finite interval `[a, b]`, at every level, for every initial coefficient.
* `OpenDomainUnforcedGalerkin.energyIdentityOn` and `energyIdentityAtTime` —
  the finite-level identity `‖u b‖² + 2 ∫ D = ‖u a‖²`, with the dissipation
  written in the original diffusion form along the lifted trajectory.
* `OpenDomainUnforcedGalerkin.norm_le_initial` — the state norm never exceeds
  the initial coefficient, uniformly in the level.
* `OpenDomainUnforcedGalerkin.exists_gradientDiffusionSolutionOn` and
  `gradientDiffusion_energyIdentityAtTime` — the same two results for the
  ambient gradient diffusion restricted to `Ω`.

The diffusion form is a parameter, subject only to `0 ≤ D u u`.  The last
statement instantiates it with the gradient diffusion of the ambient rectangle
composed with the isometric energy inclusion `openDomainEnergyToBox Ω`.
-/

open MeasureTheory Set

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

namespace OpenDomainUnforcedGalerkin

variable {n : ℕ} {Q : BoxIntegral.Box (Fin (n + 1))} {Ω : OpenDomainInBox Q}

section Level

variable (Ω)
variable (R : BoxEnergyL4Realization Q)
    (D : OpenDomainH1ZeroSigma Ω →L[ℝ] OpenDomainH1ZeroSigma Ω →L[ℝ] ℝ)
    (hD : ∀ u, 0 ≤ D u u)
    (S : OpenDomainCompactSpectralRepresentation Ω) (m : ℕ)

/-- The unforced level-`m` variational problem of the subdomain: the physical
convection form of `Ω`, a nonnegative diffusion form, zero forcing, and a
prescribed initial coefficient in the spectral head. -/
def unforcedProblem (initial : S.stateSpace m) :
    VariationalGalerkinProblem (S.stateSpace m) :=
  S.spectralProblem m (S.energySynthesis m)
    (OpenDomainPhysicalConvection.energyConvectionForm Ω R) D hD
    (fun _ => 0) initial

@[simp]
theorem unforcedProblem_initial (initial : S.stateSpace m) :
    (unforcedProblem Ω R D hD S m initial).initial = initial :=
  rfl

@[simp]
theorem unforcedProblem_forcing_apply (initial : S.stateSpace m)
    (t : ℝ) (x : S.stateSpace m) :
    (unforcedProblem Ω R D hD S m initial).forcing t x = 0 :=
  rfl

@[simp]
theorem unforcedProblem_diffusion_apply (initial : S.stateSpace m)
    (x y : S.stateSpace m) :
    (unforcedProblem Ω R D hD S m initial).system.diffusion x y =
      D (S.energySynthesis m x) (S.energySynthesis m y) :=
  rfl

@[simp]
theorem unforcedProblem_convection_apply (initial : S.stateSpace m)
    (x y z : S.stateSpace m) :
    (unforcedProblem Ω R D hD S m initial).system.convection x y z =
      OpenDomainPhysicalConvection.convectionForm Ω R
        (S.energySynthesis m x) (S.energySynthesis m y)
        (S.energySynthesis m z) :=
  rfl

theorem unforcedProblem_forcing_continuous (initial : S.stateSpace m) :
    Continuous (unforcedProblem Ω R D hD S m initial).forcing :=
  continuous_const

/-- **Unforced existence at every spectral level.**  On every finite time
interval, every spectral head of the subdomain carries a solution of the
unforced coefficient system starting from any initial coefficient.

Only the nonnegativity of the diffusion form is used: with zero forcing the
absorption hypothesis of the generic continuation theorem is exactly
`0 ≤ D u u`, and the energy budget closes with radius `‖initial‖`. -/
theorem exists_unforcedSolutionOn (initial : S.stateSpace m)
    {a b : ℝ} (hab : a ≤ b) :
    Nonempty ((unforcedProblem Ω R D hD S m initial).LocalSolutionOn
      (⟨a, le_rfl, hab⟩ : Icc a b)) := by
  refine S.exists_spectralSolutionOn m (S.energySynthesis m)
    (OpenDomainPhysicalConvection.energyConvectionForm Ω R) D hD
    (fun _ => 0) initial continuous_const hab (fun _ => 0)
    intervalIntegrable_const (fun _ _ => le_rfl) ?_ ‖initial‖ (norm_nonneg _) ?_
  · intro t _ht u
    simpa using hD u
  · simp

/-- **The finite-level unforced energy identity.**  The state norm squared plus
twice the accumulated dissipation is conserved; the dissipation integrand is the
diffusion form evaluated along the lifted trajectory. -/
theorem energyIdentityOn (initial : S.stateSpace m)
    {tmin tmax : ℝ} {t₀ : Icc tmin tmax}
    (u : (unforcedProblem Ω R D hD S m initial).LocalSolutionOn t₀)
    {a b : ℝ} (ha : a ∈ Icc tmin tmax) (hb : b ∈ Icc tmin tmax)
    (hab : a ≤ b) :
    ‖u.toFun b‖ ^ 2
      + 2 * ∫ s in a..b,
          D (S.energySynthesis m (u.toFun s)) (S.energySynthesis m (u.toFun s))
      = ‖u.toFun a‖ ^ 2 := by
  have h := S.spectralSolution_energyIdentityOn m (S.energySynthesis m)
    (OpenDomainPhysicalConvection.energyConvectionForm Ω R) D hD
    (fun _ => 0) initial continuous_const u ha hb hab
  simpa using h

/-- The same identity anchored at the initial coefficient. -/
theorem energyIdentityAtTime (initial : S.stateSpace m)
    {T : ℝ} (hT : 0 ≤ T)
    (u : (unforcedProblem Ω R D hD S m initial).LocalSolutionOn
      (⟨0, le_rfl, hT⟩ : Icc (0 : ℝ) T))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ‖u.toFun t‖ ^ 2
      + 2 * ∫ s in (0 : ℝ)..t,
          D (S.energySynthesis m (u.toFun s)) (S.energySynthesis m (u.toFun s))
      = ‖initial‖ ^ 2 := by
  have h := energyIdentityOn Ω R D hD S m initial u
    (⟨le_rfl, hT⟩ : (0 : ℝ) ∈ Icc (0 : ℝ) T) ht ht.1
  have h0 : u.toFun 0 = initial := u.initial
  rw [h0] at h
  exact h

/-- **Uniform state bound.**  Nonnegative dissipation turns the identity into a
bound by the initial coefficient, at every level and every time. -/
theorem norm_le_initial (initial : S.stateSpace m)
    {T : ℝ} (hT : 0 ≤ T)
    (u : (unforcedProblem Ω R D hD S m initial).LocalSolutionOn
      (⟨0, le_rfl, hT⟩ : Icc (0 : ℝ) T))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ‖u.toFun t‖ ≤ ‖initial‖ := by
  have hId := energyIdentityAtTime Ω R D hD S m initial hT u ht
  have hnonneg :
      0 ≤ ∫ s in (0 : ℝ)..t,
        D (S.energySynthesis m (u.toFun s))
          (S.energySynthesis m (u.toFun s)) :=
    intervalIntegral.integral_nonneg ht.1 fun s _ => hD _
  have hsq : ‖u.toFun t‖ ^ 2 ≤ ‖initial‖ ^ 2 := by linarith
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

end Level

section GradientDiffusion

variable (Ω) (R : BoxEnergyL4Realization Q)
    (S : OpenDomainCompactSpectralRepresentation Ω) (m : ℕ)

/-- **Unforced existence for the physical gradient diffusion.**  Every spectral
head of `Ω` carries a solution on every finite interval when the diffusion form
is the gradient form of the ambient rectangle read through the isometric energy
inclusion `openDomainEnergyToBox Ω`.  The form is written inline, so this file
introduces no second name for it. -/
theorem exists_gradientDiffusionSolutionOn (initial : S.stateSpace m)
    {a b : ℝ} (hab : a ≤ b) :
    Nonempty ((unforcedProblem Ω R
        ((boxGradientDiffusion Q).bilinearCompSame (openDomainEnergyToBox Ω))
        (fun w => boxGradientDiffusion_nonneg Q (openDomainEnergyToBox Ω w))
        S m initial).LocalSolutionOn (⟨a, le_rfl, hab⟩ : Icc a b)) :=
  exists_unforcedSolutionOn Ω R
    ((boxGradientDiffusion Q).bilinearCompSame (openDomainEnergyToBox Ω))
    (fun w => boxGradientDiffusion_nonneg Q (openDomainEnergyToBox Ω w))
    S m initial hab

/-- **The unforced energy identity for the physical gradient diffusion.**  The
dissipation is the ambient gradient diffusion of the included lifted
trajectory. -/
theorem gradientDiffusion_energyIdentityAtTime (initial : S.stateSpace m)
    {T : ℝ} (hT : 0 ≤ T)
    (u : (unforcedProblem Ω R
        ((boxGradientDiffusion Q).bilinearCompSame (openDomainEnergyToBox Ω))
        (fun w => boxGradientDiffusion_nonneg Q (openDomainEnergyToBox Ω w))
        S m initial).LocalSolutionOn (⟨0, le_rfl, hT⟩ : Icc (0 : ℝ) T))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ‖u.toFun t‖ ^ 2
      + 2 * ∫ s in (0 : ℝ)..t,
          boxGradientDiffusion Q
            (openDomainEnergyToBox Ω (S.energySynthesis m (u.toFun s)))
            (openDomainEnergyToBox Ω (S.energySynthesis m (u.toFun s)))
      = ‖initial‖ ^ 2 := by
  simpa only [ContinuousLinearMap.bilinearCompSame_apply] using
    energyIdentityAtTime Ω R
      ((boxGradientDiffusion Q).bilinearCompSame (openDomainEnergyToBox Ω))
      (fun w => boxGradientDiffusion_nonneg Q (openDomainEnergyToBox Ω w))
      S m initial hT u ht

end GradientDiffusion

end OpenDomainUnforcedGalerkin

end
