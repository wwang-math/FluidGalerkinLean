import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open InnerProductSpace

noncomputable section

section PointwiseYoung

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Pointwise Young inequality in the form used by the Galerkin energy method. -/
lemma pointwise_young_inner
    (ν : ℝ) (hν : 0 < ν)
    (F U : H) :
    2 * ⟪F, U⟫_ℝ ≤ 1 / ν * ‖F‖^2 + ν * ‖U‖^2 := by
  have hCS : ⟪F, U⟫_ℝ ≤ ‖F‖ * ‖U‖ := real_inner_le_norm F U
  have hCS2 : 2 * ⟪F, U⟫_ℝ ≤ 2 * (‖F‖ * ‖U‖) := by
    have hmul := mul_le_mul_of_nonneg_left hCS (by norm_num : 0 ≤ (2 : ℝ))
    simpa [two_mul, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hYoung : 2 * (‖F‖ * ‖U‖) ≤ ν * ‖U‖^2 + ν⁻¹ * ‖F‖^2 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (two_mul_le_add_mul_sq (a := ‖U‖) (b := ‖F‖) hν)
  calc
    2 * ⟪F, U⟫_ℝ ≤ 2 * (‖F‖ * ‖U‖) := hCS2
    _ ≤ ν * ‖U‖^2 + ν⁻¹ * ‖F‖^2 := hYoung
    _ = 1 / ν * ‖F‖^2 + ν * ‖U‖^2 := by
      ring

end PointwiseYoung
