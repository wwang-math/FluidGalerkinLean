import PDEIdeas.GalerkinCore

open Real MeasureTheory intervalIntegral InnerProductSpace

noncomputable section

section CompactnessInterface

variable {H W : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup W]

/-- Uniform-in-`n` energy control on the whole interval `[0,T]`. -/
def UniformEnergyBoundOn
    (U : ℕ → ℝ → H)
    (T M : ℝ) : Prop :=
  ∀ n : ℕ, ∀ t : ℝ, t ∈ Set.Icc 0 T → ‖U n t‖^2 ≤ M

/-- Uniform-in-`n` time-derivative control in an auxiliary normed space,
intended as the first interface to Aubin--Lions type compactness. -/
def UniformTimeDerivativeBoundOn
    (dU : ℕ → ℝ → W)
    (T M : ℝ) : Prop :=
  ∀ n : ℕ, ∫ s in (0 : ℝ)..T, ‖dU n s‖^2 ≤ M

/-- Uniform-in-`n` dissipation control for a Galerkin family. -/
def UniformDissipationBoundOn
    [GalerkinSystem H]
    (U : ℕ → ℝ → H)
    (T M : ℝ) : Prop :=
  ∀ n : ℕ,
    ∫ s in (0 : ℝ)..T, ⟪GalerkinSystem.linOp (U n s), U n s⟫_ℝ ≤ M

/-- The first compactness-ready package one wants after establishing the
Galerkin energy estimate and time-derivative bounds. This does not yet prove an
Aubin--Lions theorem; it records the exact family of estimates that such a
theorem would consume. -/
structure AubinLionsReadyFamily
    (U : ℕ → ℝ → H)
    (dU : ℕ → ℝ → W)
    (T : ℝ) where
  energyConst : ℝ
  timeDerivConst : ℝ
  energyBound : UniformEnergyBoundOn U T energyConst
  timeDerivBound : UniformTimeDerivativeBoundOn dU T timeDerivConst

/-- A stronger compactness-facing package that records not only the energy and
time-derivative bounds needed for Aubin--Lions, but also the dissipation bound
coming from the Galerkin energy identity. This is closer to the exact family of
estimates used in the classical Leray scheme. -/
structure CompactnessReadyFamily
    [GalerkinSystem H]
    (U : ℕ → ℝ → H)
    (dU : ℕ → ℝ → W)
    (T : ℝ) where
  energyConst : ℝ
  timeDerivConst : ℝ
  dissipationConst : ℝ
  energyBound : UniformEnergyBoundOn U T energyConst
  timeDerivBound : UniformTimeDerivativeBoundOn dU T timeDerivConst
  dissipationBound : UniformDissipationBoundOn U T dissipationConst

/-- If one already has the uniform energy and time-derivative estimates, then
the Galerkin family is packaged in a form ready for a future Aubin--Lions type
compactness theorem. -/
def aubinLionsReady_of_bounds
    (U : ℕ → ℝ → H)
    (dU : ℕ → ℝ → W)
    (T M₀ M₁ : ℝ)
    (hE : UniformEnergyBoundOn U T M₀)
    (hD : UniformTimeDerivativeBoundOn dU T M₁) :
    AubinLionsReadyFamily U dU T where
  energyConst := M₀
  timeDerivConst := M₁
  energyBound := hE
  timeDerivBound := hD

/-- If one has the full collection of energy, dissipation, and time-derivative
bounds, then the Galerkin family is packaged in the form naturally used by the
classical compactness argument. -/
def compactnessReady_of_bounds
    [GalerkinSystem H]
    (U : ℕ → ℝ → H)
    (dU : ℕ → ℝ → W)
    (T M₀ M₁ M₂ : ℝ)
    (hE : UniformEnergyBoundOn U T M₀)
    (hD : UniformTimeDerivativeBoundOn dU T M₁)
    (hA : UniformDissipationBoundOn U T M₂) :
    CompactnessReadyFamily U dU T where
  energyConst := M₀
  timeDerivConst := M₁
  dissipationConst := M₂
  energyBound := hE
  timeDerivBound := hD
  dissipationBound := hA

section AbstractEnergy

variable [GalerkinSystem H]

/-- The abstract a priori estimate immediately yields a uniform-in-`n` energy
bound for a Galerkin family with common initial data and forcing. This is the
first compactness-facing consequence of the abstract energy method. -/
theorem uniform_energy_bound_of_abstract_apriori
    (ν : ℝ) (hν : 0 < ν)
    (hcoer : ∀ U : H, ν * ‖U‖^2 ≤ ⟪GalerkinSystem.linOp U, U⟫_ℝ)
    (F : ℝ → H)
    (U₀ : H)
    (U : ℕ → ℝ → H)
    (hInit : ∀ n : ℕ, U n 0 = U₀)
    (hEnergy : ∀ n : ℕ, ∀ T : ℝ, 0 ≤ T →
        ‖U n T‖^2 + 2 * ∫ s in (0 : ℝ)..T, ⟪GalerkinSystem.linOp (U n s), U n s⟫_ℝ
          = ‖U₀‖^2 + 2 * ∫ s in (0 : ℝ)..T, ⟪F s, U n s⟫_ℝ)
    (hFU_int : ∀ n : ℕ, ∀ T : ℝ, 0 ≤ T →
        IntervalIntegrable (fun s => ⟪F s, U n s⟫_ℝ) volume 0 T)
    (hfint : ∀ T : ℝ, 0 ≤ T →
        IntervalIntegrable (fun s => ‖F s‖^2) volume 0 T)
    (hUint : ∀ n : ℕ, ∀ T : ℝ, 0 ≤ T →
        IntervalIntegrable (fun s => ‖U n s‖^2) volume 0 T)
    (hAint : ∀ n : ℕ, ∀ T : ℝ, 0 ≤ T →
        IntervalIntegrable
          (fun s => ⟪GalerkinSystem.linOp (U n s), U n s⟫_ℝ) volume 0 T)
    (T : ℝ) (hT : 0 ≤ T) :
    UniformEnergyBoundOn U T
      (‖U₀‖^2 + 1 / ν * ∫ s in (0 : ℝ)..T, ‖F s‖^2) := by
  intro n t ht
  have hAt :=
    abstract_apriori_bound ν hν hcoer F U₀ (U n) (hInit n)
      (hEnergy n) (hFU_int n) hfint (hUint n) (hAint n) t ht.1
  have hMono :
      ∫ s in (0 : ℝ)..t, ‖F s‖^2 ≤ ∫ s in (0 : ℝ)..T, ‖F s‖^2 := by
    have hNonneg :
        0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) T)] fun s => ‖F s‖ ^ 2 :=
      Filter.Eventually.of_forall (fun s => sq_nonneg ‖F s‖)
    exact intervalIntegral.integral_mono_interval
      (c := (0 : ℝ)) (d := T) (a := (0 : ℝ)) (b := t)
      le_rfl ht.1 ht.2 hNonneg (hfint T hT)
  have hMono' :
      (1 / ν) * ∫ s in (0 : ℝ)..t, ‖F s‖^2
        ≤ (1 / ν) * ∫ s in (0 : ℝ)..T, ‖F s‖^2 := by
    exact mul_le_mul_of_nonneg_left hMono (by positivity)
  linarith

/-- The same abstract energy method also yields a uniform dissipation bound.
Together with the energy estimate, this is the second half of the standard
compactness input for Galerkin families. -/
theorem uniform_dissipation_bound_of_abstract_apriori
    (ν : ℝ) (hν : 0 < ν)
    (hcoer : ∀ U : H, ν * ‖U‖^2 ≤ ⟪GalerkinSystem.linOp U, U⟫_ℝ)
    (F : ℝ → H)
    (U₀ : H)
    (U : ℕ → ℝ → H)
    (hInit : ∀ n : ℕ, U n 0 = U₀)
    (hEnergy : ∀ n : ℕ, ∀ T : ℝ, 0 ≤ T →
        ‖U n T‖^2 + 2 * ∫ s in (0 : ℝ)..T, ⟪GalerkinSystem.linOp (U n s), U n s⟫_ℝ
          = ‖U₀‖^2 + 2 * ∫ s in (0 : ℝ)..T, ⟪F s, U n s⟫_ℝ)
    (hFU_int : ∀ n : ℕ, ∀ T : ℝ, 0 ≤ T →
        IntervalIntegrable (fun s => ⟪F s, U n s⟫_ℝ) volume 0 T)
    (hfint : ∀ T : ℝ, 0 ≤ T →
        IntervalIntegrable (fun s => ‖F s‖^2) volume 0 T)
    (hUint : ∀ n : ℕ, ∀ T : ℝ, 0 ≤ T →
        IntervalIntegrable (fun s => ‖U n s‖^2) volume 0 T)
    (hAint : ∀ n : ℕ, ∀ T : ℝ, 0 ≤ T →
        IntervalIntegrable
          (fun s => ⟪GalerkinSystem.linOp (U n s), U n s⟫_ℝ) volume 0 T)
    (T : ℝ) (hT : 0 ≤ T) :
    UniformDissipationBoundOn U T
      (‖U₀‖^2 + 1 / ν * ∫ s in (0 : ℝ)..T, ‖F s‖^2) := by
  intro n
  have _ : U n 0 = U₀ := hInit n
  let Aint := ∫ s in (0 : ℝ)..T, ⟪GalerkinSystem.linOp (U n s), U n s⟫_ℝ
  let Fint := ∫ s in (0 : ℝ)..T, ‖F s‖^2
  let Uint := ∫ s in (0 : ℝ)..T, ‖U n s‖^2
  have hE := hEnergy n T hT
  have hYoung :=
    integral_force_work_le ν hν F (U n) (hFU_int n) hfint (hUint n) T hT
  have hAbsorb :=
    integral_coercive_le ν hcoer (U n) (hUint n) (hAint n) T hT
  have hNorm : 0 ≤ ‖U n T‖^2 := sq_nonneg _
  change Aint ≤ ‖U₀‖^2 + (1 / ν) * Fint
  rw [one_div]
  change ‖U n T‖^2 + 2 * Aint =
    ‖U₀‖^2 + 2 * ∫ s in (0 : ℝ)..T, ⟪F s, U n s⟫_ℝ at hE
  change 2 * ∫ s in (0 : ℝ)..T, ⟪F s, U n s⟫_ℝ ≤
    ν⁻¹ * Fint + ν * Uint at hYoung
  change ν * Uint ≤ Aint at hAbsorb
  linarith

/-- Combining the abstract energy, dissipation, and time-derivative bounds
produces the full compactness-ready package that a future Aubin--Lions theorem
would consume. -/
def compactnessReady_of_abstract_apriori
    (ν : ℝ) (hν : 0 < ν)
    (hcoer : ∀ U : H, ν * ‖U‖^2 ≤ ⟪GalerkinSystem.linOp U, U⟫_ℝ)
    (F : ℝ → H)
    (U₀ : H)
    (U : ℕ → ℝ → H)
    (dU : ℕ → ℝ → W)
    (hInit : ∀ n : ℕ, U n 0 = U₀)
    (hEnergy : ∀ n : ℕ, ∀ T : ℝ, 0 ≤ T →
        ‖U n T‖^2 + 2 * ∫ s in (0 : ℝ)..T, ⟪GalerkinSystem.linOp (U n s), U n s⟫_ℝ
          = ‖U₀‖^2 + 2 * ∫ s in (0 : ℝ)..T, ⟪F s, U n s⟫_ℝ)
    (hFU_int : ∀ n : ℕ, ∀ T : ℝ, 0 ≤ T →
        IntervalIntegrable (fun s => ⟪F s, U n s⟫_ℝ) volume 0 T)
    (hfint : ∀ T : ℝ, 0 ≤ T →
        IntervalIntegrable (fun s => ‖F s‖^2) volume 0 T)
    (hUint : ∀ n : ℕ, ∀ T : ℝ, 0 ≤ T →
        IntervalIntegrable (fun s => ‖U n s‖^2) volume 0 T)
    (hAint : ∀ n : ℕ, ∀ T : ℝ, 0 ≤ T →
        IntervalIntegrable
          (fun s => ⟪GalerkinSystem.linOp (U n s), U n s⟫_ℝ) volume 0 T)
    (T : ℝ)
    (M₁ : ℝ)
    (hD : UniformTimeDerivativeBoundOn dU T M₁)
    (hT : 0 ≤ T) :
    CompactnessReadyFamily U dU T := by
  let C₀ := ‖U₀‖^2 + 1 / ν * ∫ s in (0 : ℝ)..T, ‖F s‖^2
  refine compactnessReady_of_bounds U dU T
    C₀
    M₁
    C₀
    ?_ hD ?_
  · exact uniform_energy_bound_of_abstract_apriori ν hν hcoer F U₀ U
      hInit hEnergy hFU_int hfint hUint hAint T hT
  · exact uniform_dissipation_bound_of_abstract_apriori ν hν hcoer F U₀ U
      hInit hEnergy hFU_int hfint hUint hAint T hT

end AbstractEnergy

end CompactnessInterface
