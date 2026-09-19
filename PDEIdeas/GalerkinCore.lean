import PDEIdeas.GalerkinIntegralEstimates
import PDEIdeas.GalerkinScalarAbsorption

open Real MeasureTheory intervalIntegral InnerProductSpace

noncomputable section

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [GalerkinSystem H]

/-- The universal a priori estimate extracted from an energy identity plus coercivity. -/
theorem abstract_apriori_bound
    (ν   : ℝ) (hν : 0 < ν)
    (hcoer : ∀ U : H, ν * ‖U‖^2 ≤ ⟪GalerkinSystem.linOp U, U⟫_ℝ)
    (F  : ℝ → H)
    (U₀ : H)
    (Uₙ : ℝ → H)
    (hInit : Uₙ 0 = U₀)
    (hEnergy : ∀ T : ℝ, 0 ≤ T →
        ‖Uₙ T‖^2 + 2 * ∫ s in (0:ℝ)..T, ⟪GalerkinSystem.linOp (Uₙ s), Uₙ s⟫_ℝ =
        ‖U₀‖^2 + 2 * ∫ s in (0:ℝ)..T, ⟪F s, Uₙ s⟫_ℝ)
    (hFU_int : ∀ T : ℝ, 0 ≤ T →
        IntervalIntegrable (fun s => ⟪F s, Uₙ s⟫_ℝ) volume 0 T)
    (hfint : ∀ T : ℝ, 0 ≤ T → IntervalIntegrable (fun s => ‖F s‖^2) volume 0 T)
    (hUint : ∀ T : ℝ, 0 ≤ T → IntervalIntegrable (fun s => ‖Uₙ s‖^2) volume 0 T)
    (hAint : ∀ T : ℝ, 0 ≤ T →
        IntervalIntegrable (fun s => ⟪GalerkinSystem.linOp (Uₙ s), Uₙ s⟫_ℝ) volume 0 T)
    (T : ℝ) (hT : 0 ≤ T) :
    ‖Uₙ T‖^2 ≤ ‖U₀‖^2 + 1/ν * ∫ s in (0:ℝ)..T, ‖F s‖^2 := by
  have _ : Uₙ 0 = U₀ := hInit
  let Aint := ∫ s in (0 : ℝ)..T, ⟪GalerkinSystem.linOp (Uₙ s), Uₙ s⟫_ℝ
  let Fint := ∫ s in (0 : ℝ)..T, ‖F s‖^2
  have hE := hEnergy T hT
  have hYoungInt :=
    integral_force_work_le ν hν F Uₙ hFU_int hfint hUint T hT
  have hAbsorb :=
    integral_coercive_le ν hcoer Uₙ hUint hAint T hT
  have hA_nonneg : 0 ≤ Aint := by
    apply intervalIntegral.integral_nonneg hT
    intro s _
    exact GalerkinSystem.coercive (Uₙ s)
  have hYoungInt' : 2 * ∫ s in (0 : ℝ)..T, ⟪F s, Uₙ s⟫_ℝ ≤ ν⁻¹ * Fint + Aint := by
    calc
      2 * ∫ s in (0 : ℝ)..T, ⟪F s, Uₙ s⟫_ℝ
          ≤ ν⁻¹ * Fint + ν * ∫ s in (0 : ℝ)..T, ‖Uₙ s‖^2 := by
            simpa [Fint] using hYoungInt
      _ ≤ ν⁻¹ * Fint + Aint := by
        gcongr
  simpa [Fint, Aint, one_div] using
    (apriori_scalar_bound
      (u := ‖Uₙ T‖^2)
      (u0 := ‖U₀‖^2)
      (work := ∫ s in (0 : ℝ)..T, ⟪F s, Uₙ s⟫_ℝ)
      (forcing := ν⁻¹ * Fint)
      (diss := Aint)
      hE hYoungInt' hA_nonneg)

/-- The forced energy estimate with one copy of the integrated dissipation
retained after Young absorption. -/
theorem abstract_apriori_bound_with_dissipation
    (ν   : ℝ) (hν : 0 < ν)
    (F  : ℝ → H)
    (U₀ : H)
    (Uₙ : ℝ → H)
    (hcoer : ∀ t : ℝ,
      ν * ‖Uₙ t‖^2 ≤ ⟪GalerkinSystem.linOp (Uₙ t), Uₙ t⟫_ℝ)
    (hInit : Uₙ 0 = U₀)
    (hEnergy : ∀ T : ℝ, 0 ≤ T →
        ‖Uₙ T‖^2 + 2 * ∫ s in (0:ℝ)..T, ⟪GalerkinSystem.linOp (Uₙ s), Uₙ s⟫_ℝ =
        ‖U₀‖^2 + 2 * ∫ s in (0:ℝ)..T, ⟪F s, Uₙ s⟫_ℝ)
    (hFU_int : ∀ T : ℝ, 0 ≤ T →
        IntervalIntegrable (fun s => ⟪F s, Uₙ s⟫_ℝ) volume 0 T)
    (hfint : ∀ T : ℝ, 0 ≤ T → IntervalIntegrable (fun s => ‖F s‖^2) volume 0 T)
    (hUint : ∀ T : ℝ, 0 ≤ T → IntervalIntegrable (fun s => ‖Uₙ s‖^2) volume 0 T)
    (hAint : ∀ T : ℝ, 0 ≤ T →
        IntervalIntegrable (fun s => ⟪GalerkinSystem.linOp (Uₙ s), Uₙ s⟫_ℝ) volume 0 T)
    (T : ℝ) (hT : 0 ≤ T) :
    ‖Uₙ T‖^2 + ∫ s in (0:ℝ)..T, ⟪GalerkinSystem.linOp (Uₙ s), Uₙ s⟫_ℝ
      ≤ ‖U₀‖^2 + 1/ν * ∫ s in (0:ℝ)..T, ‖F s‖^2 := by
  have _ : Uₙ 0 = U₀ := hInit
  let Aint := ∫ s in (0 : ℝ)..T, ⟪GalerkinSystem.linOp (Uₙ s), Uₙ s⟫_ℝ
  let Fint := ∫ s in (0 : ℝ)..T, ‖F s‖^2
  have hE := hEnergy T hT
  have hYoungInt :=
    integral_force_work_le ν hν F Uₙ hFU_int hfint hUint T hT
  have hAbsorb :
      ν * ∫ s in (0 : ℝ)..T, ‖Uₙ s‖^2 ≤
        ∫ s in (0 : ℝ)..T,
          ⟪GalerkinSystem.linOp (Uₙ s), Uₙ s⟫_ℝ := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hT
    · exact (hUint T hT).const_mul ν
    · exact hAint T hT
    · intro s _
      simpa [mul_comm] using hcoer s
  have hYoungInt' :
      2 * ∫ s in (0 : ℝ)..T, ⟪F s, Uₙ s⟫_ℝ ≤ ν⁻¹ * Fint + Aint := by
    calc
      2 * ∫ s in (0 : ℝ)..T, ⟪F s, Uₙ s⟫_ℝ
          ≤ ν⁻¹ * Fint + ν * ∫ s in (0 : ℝ)..T, ‖Uₙ s‖^2 := by
            simpa [Fint] using hYoungInt
      _ ≤ ν⁻¹ * Fint + Aint := by
        gcongr
  simpa [Fint, Aint, one_div] using
    (apriori_scalar_bound_with_dissipation
      (u := ‖Uₙ T‖^2)
      (u0 := ‖U₀‖^2)
      (work := ∫ s in (0 : ℝ)..T, ⟪F s, Uₙ s⟫_ℝ)
      (forcing := ν⁻¹ * Fint)
      (diss := Aint)
      hE hYoungInt')

/-- Fixed-terminal-time form of the forced energy estimate with one copy of
the integrated dissipation retained. -/
theorem abstract_apriori_bound_with_dissipation_atTime
    (ν : ℝ) (hν : 0 < ν)
    (F : ℝ → H)
    (U₀ : H)
    (Uₙ : ℝ → H)
    (hcoer : ∀ t : ℝ,
      ν * ‖Uₙ t‖^2 ≤ ⟪GalerkinSystem.linOp (Uₙ t), Uₙ t⟫_ℝ)
    (T : ℝ) (hT : 0 ≤ T)
    (hEnergyT :
        ‖Uₙ T‖^2 + 2 * ∫ s in (0 : ℝ)..T,
            ⟪GalerkinSystem.linOp (Uₙ s), Uₙ s⟫_ℝ
          = ‖U₀‖^2 + 2 * ∫ s in (0 : ℝ)..T, ⟪F s, Uₙ s⟫_ℝ)
    (hFU_int : IntervalIntegrable (fun s => ⟪F s, Uₙ s⟫_ℝ) volume 0 T)
    (hfint : IntervalIntegrable (fun s => ‖F s‖^2) volume 0 T)
    (hUint : IntervalIntegrable (fun s => ‖Uₙ s‖^2) volume 0 T)
    (hAint : IntervalIntegrable
      (fun s => ⟪GalerkinSystem.linOp (Uₙ s), Uₙ s⟫_ℝ) volume 0 T) :
    ‖Uₙ T‖^2 + ∫ s in (0 : ℝ)..T,
        ⟪GalerkinSystem.linOp (Uₙ s), Uₙ s⟫_ℝ
      ≤ ‖U₀‖^2 + 1 / ν * ∫ s in (0 : ℝ)..T, ‖F s‖^2 := by
  let Aint := ∫ s in (0 : ℝ)..T,
    ⟪GalerkinSystem.linOp (Uₙ s), Uₙ s⟫_ℝ
  let Fint := ∫ s in (0 : ℝ)..T, ‖F s‖^2
  have hYoung :=
    integral_force_work_le_atTime ν hν F Uₙ T hT hFU_int hfint hUint
  have hAbsorb :
      ν * ∫ s in (0 : ℝ)..T, ‖Uₙ s‖^2 ≤
        ∫ s in (0 : ℝ)..T,
          ⟪GalerkinSystem.linOp (Uₙ s), Uₙ s⟫_ℝ := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hT
    · exact hUint.const_mul ν
    · exact hAint
    · intro s _
      simpa [mul_comm] using hcoer s
  have hYoung' :
      2 * ∫ s in (0 : ℝ)..T, ⟪F s, Uₙ s⟫_ℝ ≤ ν⁻¹ * Fint + Aint := by
    calc
      2 * ∫ s in (0 : ℝ)..T, ⟪F s, Uₙ s⟫_ℝ
          ≤ ν⁻¹ * Fint + ν * ∫ s in (0 : ℝ)..T, ‖Uₙ s‖^2 := by
            simpa [Fint] using hYoung
      _ ≤ ν⁻¹ * Fint + Aint := by
        gcongr
  simpa [Fint, Aint, one_div] using
    (apriori_scalar_bound_with_dissipation
      (u := ‖Uₙ T‖^2)
      (u0 := ‖U₀‖^2)
      (work := ∫ s in (0 : ℝ)..T, ⟪F s, Uₙ s⟫_ℝ)
      (forcing := ν⁻¹ * Fint)
      (diss := Aint)
      hEnergyT hYoung')

/-- A one-time version of the abstract a priori estimate, used when one has an
energy identity only at a fixed terminal time rather than as a globally
packaged theorem. This is the form naturally produced by local Galerkin
solutions on a bounded interval. -/
theorem abstract_apriori_bound_atTime
    (ν   : ℝ) (hν : 0 < ν)
    (hcoer : ∀ U : H, ν * ‖U‖^2 ≤ ⟪GalerkinSystem.linOp U, U⟫_ℝ)
    (F  : ℝ → H)
    (U₀ : H)
    (Uₙ : ℝ → H)
    (hInit : Uₙ 0 = U₀)
    (T : ℝ) (hT : 0 ≤ T)
    (hEnergyT :
        ‖Uₙ T‖^2 + 2 * ∫ s in (0 : ℝ)..T, ⟪GalerkinSystem.linOp (Uₙ s), Uₙ s⟫_ℝ =
        ‖U₀‖^2 + 2 * ∫ s in (0 : ℝ)..T, ⟪F s, Uₙ s⟫_ℝ)
    (hFU_int : IntervalIntegrable (fun s => ⟪F s, Uₙ s⟫_ℝ) volume 0 T)
    (hfint : IntervalIntegrable (fun s => ‖F s‖^2) volume 0 T)
    (hUint : IntervalIntegrable (fun s => ‖Uₙ s‖^2) volume 0 T)
    (hAint : IntervalIntegrable (fun s => ⟪GalerkinSystem.linOp (Uₙ s), Uₙ s⟫_ℝ) volume 0 T) :
    ‖Uₙ T‖^2 ≤ ‖U₀‖^2 + 1/ν * ∫ s in (0:ℝ)..T, ‖F s‖^2 := by
  have _ : Uₙ 0 = U₀ := hInit
  let Aint := ∫ s in (0 : ℝ)..T, ⟪GalerkinSystem.linOp (Uₙ s), Uₙ s⟫_ℝ
  let Fint := ∫ s in (0 : ℝ)..T, ‖F s‖^2
  have hYoungInt :=
    integral_force_work_le_atTime ν hν F Uₙ T hT hFU_int hfint hUint
  have hAbsorb :=
    integral_coercive_le_atTime ν hcoer Uₙ T hT hUint hAint
  have hYoungInt' :
      2 * ∫ s in (0 : ℝ)..T, ⟪F s, Uₙ s⟫_ℝ ≤ ν⁻¹ * Fint + Aint := by
    calc
      2 * ∫ s in (0 : ℝ)..T, ⟪F s, Uₙ s⟫_ℝ
          ≤ ν⁻¹ * Fint + ν * ∫ s in (0 : ℝ)..T, ‖Uₙ s‖^2 := by
            simpa [Fint] using hYoungInt
      _ ≤ ν⁻¹ * Fint + Aint := by
        gcongr
  have hA_nonneg : 0 ≤ Aint := by
    apply intervalIntegral.integral_nonneg hT
    intro s _
    exact GalerkinSystem.coercive (Uₙ s)
  simpa [Fint, Aint, one_div] using
    (apriori_scalar_bound_atTime
      (u := ‖Uₙ T‖^2)
      (u0 := ‖U₀‖^2)
      (work := ∫ s in (0 : ℝ)..T, ⟪F s, Uₙ s⟫_ℝ)
      (forcing := ν⁻¹ * Fint)
      (diss := Aint)
      hEnergyT hYoungInt' hA_nonneg)

end Abstract
