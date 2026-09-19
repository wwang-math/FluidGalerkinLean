import PDEIdeas.GalerkinPointwiseYoung
import PDEIdeas.GalerkinSystem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open Real MeasureTheory intervalIntegral InnerProductSpace

noncomputable section

section IntegralEstimates

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Split an interval integral of a weighted sum into weighted interval
integrals. This isolates the linearity-normalization step that otherwise makes
the energy estimate proof brittle. -/
lemma interval_integral_weighted_sum_eq
    (a b : ℝ) (f g : ℝ → ℝ) (T : ℝ)
    (hf : IntervalIntegrable f volume 0 T)
    (hg : IntervalIntegrable g volume 0 T) :
    ∫ x in (0 : ℝ)..T, (a * f x + b * g x) =
      a * (∫ x in (0 : ℝ)..T, f x) + b * (∫ x in (0 : ℝ)..T, g x) := by
  rw [intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  · exact hf.const_mul a
  · exact hg.const_mul b

/-- Integral form of the forcing estimate obtained by combining the pointwise
Young inequality with interval-integral monotonicity. -/
lemma integral_force_work_le_integral
    (ν : ℝ) (hν : 0 < ν)
    (F U : ℝ → H)
    (hFU_int : ∀ T : ℝ, 0 ≤ T →
        IntervalIntegrable (fun s => ⟪F s, U s⟫_ℝ) volume 0 T)
    (hfint : ∀ T : ℝ, 0 ≤ T → IntervalIntegrable (fun s => ‖F s‖^2) volume 0 T)
    (hUint : ∀ T : ℝ, 0 ≤ T → IntervalIntegrable (fun s => ‖U s‖^2) volume 0 T)
    (T : ℝ) (hT : 0 ≤ T) :
    2 * ∫ s in (0 : ℝ)..T, ⟪F s, U s⟫_ℝ ≤
      ∫ s in (0 : ℝ)..T, (ν⁻¹ * ‖F s‖^2 + ν * ‖U s‖^2) := by
  calc
    2 * ∫ s in (0 : ℝ)..T, ⟪F s, U s⟫_ℝ
        = ∫ s in (0 : ℝ)..T, 2 * ⟪F s, U s⟫_ℝ := by
            rw [← intervalIntegral.integral_const_mul]
    _ ≤ ∫ s in (0 : ℝ)..T, (ν⁻¹ * ‖F s‖^2 + ν * ‖U s‖^2) := by
          apply intervalIntegral.integral_mono_on hT
          · exact (hFU_int T hT).const_mul 2
          · exact (hfint T hT).const_mul _ |>.add ((hUint T hT).const_mul ν)
          · intro s _
            simpa [one_div] using pointwise_young_inner ν hν (F s) (U s)

/-- Split form of the forcing estimate used in the Galerkin energy argument. -/
lemma integral_force_work_le
    (ν : ℝ) (hν : 0 < ν)
    (F U : ℝ → H)
    (hFU_int : ∀ T : ℝ, 0 ≤ T →
        IntervalIntegrable (fun s => ⟪F s, U s⟫_ℝ) volume 0 T)
    (hfint : ∀ T : ℝ, 0 ≤ T → IntervalIntegrable (fun s => ‖F s‖^2) volume 0 T)
    (hUint : ∀ T : ℝ, 0 ≤ T → IntervalIntegrable (fun s => ‖U s‖^2) volume 0 T)
    (T : ℝ) (hT : 0 ≤ T) :
    2 * ∫ s in (0 : ℝ)..T, ⟪F s, U s⟫_ℝ ≤
      ν⁻¹ * (∫ s in (0 : ℝ)..T, ‖F s‖^2) +
      ν * (∫ s in (0 : ℝ)..T, ‖U s‖^2) := by
  calc
    2 * ∫ s in (0 : ℝ)..T, ⟪F s, U s⟫_ℝ
        ≤ ∫ s in (0 : ℝ)..T, (ν⁻¹ * ‖F s‖^2 + ν * ‖U s‖^2) :=
          integral_force_work_le_integral ν hν F U hFU_int hfint hUint T hT
    _ = ν⁻¹ * (∫ s in (0 : ℝ)..T, ‖F s‖^2) +
          ν * (∫ s in (0 : ℝ)..T, ‖U s‖^2) := by
          exact interval_integral_weighted_sum_eq
            (a := ν⁻¹) (b := ν)
            (f := fun s => ‖F s‖^2)
            (g := fun s => ‖U s‖^2)
            T
            (hfint T hT) (hUint T hT)

/-- Fixed-terminal-time form of `integral_force_work_le`. -/
lemma integral_force_work_le_atTime
    (ν : ℝ) (hν : 0 < ν)
    (F U : ℝ → H)
    (T : ℝ) (hT : 0 ≤ T)
    (hFU_int : IntervalIntegrable (fun s => ⟪F s, U s⟫_ℝ) volume 0 T)
    (hfint : IntervalIntegrable (fun s => ‖F s‖^2) volume 0 T)
    (hUint : IntervalIntegrable (fun s => ‖U s‖^2) volume 0 T) :
    2 * ∫ s in (0 : ℝ)..T, ⟪F s, U s⟫_ℝ ≤
      ν⁻¹ * (∫ s in (0 : ℝ)..T, ‖F s‖^2) +
      ν * (∫ s in (0 : ℝ)..T, ‖U s‖^2) := by
  calc
    2 * ∫ s in (0 : ℝ)..T, ⟪F s, U s⟫_ℝ
        = ∫ s in (0 : ℝ)..T, 2 * ⟪F s, U s⟫_ℝ := by
            rw [← intervalIntegral.integral_const_mul]
    _ ≤ ∫ s in (0 : ℝ)..T, (ν⁻¹ * ‖F s‖^2 + ν * ‖U s‖^2) := by
          apply intervalIntegral.integral_mono_on hT
          · exact hFU_int.const_mul 2
          · exact hfint.const_mul _ |>.add (hUint.const_mul ν)
          · intro s _
            simpa [one_div] using pointwise_young_inner ν hν (F s) (U s)
    _ = ν⁻¹ * (∫ s in (0 : ℝ)..T, ‖F s‖^2) +
          ν * (∫ s in (0 : ℝ)..T, ‖U s‖^2) := by
          exact interval_integral_weighted_sum_eq
            (a := ν⁻¹) (b := ν)
            (f := fun s => ‖F s‖^2)
            (g := fun s => ‖U s‖^2)
            T
            hfint hUint

variable [CompleteSpace H] [GalerkinSystem H]

/-- Integral coercivity estimate obtained by integrating the pointwise lower
bound on the dissipative operator. -/
lemma integral_coercive_le
    (ν : ℝ)
    (hcoer : ∀ U : H, ν * ‖U‖^2 ≤ ⟪GalerkinSystem.linOp U, U⟫_ℝ)
    (U : ℝ → H)
    (hUint : ∀ T : ℝ, 0 ≤ T → IntervalIntegrable (fun s => ‖U s‖^2) volume 0 T)
    (hAint : ∀ T : ℝ, 0 ≤ T →
        IntervalIntegrable (fun s => ⟪GalerkinSystem.linOp (U s), U s⟫_ℝ) volume 0 T)
    (T : ℝ) (hT : 0 ≤ T) :
    ν * ∫ s in (0 : ℝ)..T, ‖U s‖^2 ≤
      ∫ s in (0 : ℝ)..T, ⟪GalerkinSystem.linOp (U s), U s⟫_ℝ := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on hT
  · exact (hUint T hT).const_mul ν
  · exact hAint T hT
  · intro s _
    simpa [mul_comm] using hcoer (U s)

/-- Fixed-terminal-time form of `integral_coercive_le`. -/
lemma integral_coercive_le_atTime
    (ν : ℝ)
    (hcoer : ∀ U : H, ν * ‖U‖^2 ≤ ⟪GalerkinSystem.linOp U, U⟫_ℝ)
    (U : ℝ → H)
    (T : ℝ) (hT : 0 ≤ T)
    (hUint : IntervalIntegrable (fun s => ‖U s‖^2) volume 0 T)
    (hAint : IntervalIntegrable (fun s => ⟪GalerkinSystem.linOp (U s), U s⟫_ℝ) volume 0 T) :
    ν * ∫ s in (0 : ℝ)..T, ‖U s‖^2 ≤
      ∫ s in (0 : ℝ)..T, ⟪GalerkinSystem.linOp (U s), U s⟫_ℝ := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on hT
  · exact hUint.const_mul ν
  · exact hAint
  · intro s _
    simpa [mul_comm] using hcoer (U s)

end IntegralEstimates
