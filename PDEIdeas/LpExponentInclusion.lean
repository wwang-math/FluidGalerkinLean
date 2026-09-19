import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# The finite-measure inclusion from `L4` to `L2`

On a finite measure space, the canonical inclusion of `L4` into `L2` is a
continuous linear map. Its underlying almost-everywhere function is unchanged.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

local instance lpExponentInclusionFactOneLeFour :
    Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance lpExponentInclusionFactOneLeTwo :
    Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

variable {α E : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  (μ : Measure α) [IsFiniteMeasure μ]

/-- The algebraic inclusion from `L4` to `L2` on a finite measure space. -/
def lpFourToTwoLinear :
    Lp E (4 : ℝ≥0∞) μ →ₗ[ℝ] Lp E (2 : ℝ≥0∞) μ where
  toFun f := ⟨f.1, Lp.antitone (by norm_num) f.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem lpFourToTwoLinear_coe
    (f : Lp E (4 : ℝ≥0∞) μ) :
    ((lpFourToTwoLinear μ f : Lp E (2 : ℝ≥0∞) μ) : α →ₘ[μ] E) = f :=
  rfl

/-- Measure factor in the `L4`-to-`L2` estimate. -/
noncomputable def lpFourToTwoConstant : ℝ :=
  (μ Set.univ ^ ((1 : ℝ) / 2 - 1 / 4)).toReal

omit [IsFiniteMeasure μ] in
theorem lpFourToTwoConstant_nonneg : 0 ≤ lpFourToTwoConstant μ :=
  ENNReal.toReal_nonneg

theorem norm_lpFourToTwoLinear_le
    (f : Lp E (4 : ℝ≥0∞) μ) :
    ‖lpFourToTwoLinear μ f‖ ≤ lpFourToTwoConstant μ * ‖f‖ := by
  let M : ℝ≥0∞ := μ Set.univ ^ ((1 : ℝ) / 2 - 1 / 4)
  have hM : M ≠ ∞ := by
    dsimp [M]
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (by finiteness)
  have hnorm := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (f := (f : α → E)) (μ := μ) (by norm_num : (2 : ℝ≥0∞) ≤ 4)
    (Lp.aestronglyMeasurable f)
  have hprod : eLpNorm (f : α → E) (4 : ℝ≥0∞) μ * M ≠ ∞ :=
    ENNReal.mul_ne_top (Lp.eLpNorm_ne_top f) hM
  calc
    ‖lpFourToTwoLinear μ f‖ =
        (eLpNorm (f : α → E) (2 : ℝ≥0∞) μ).toReal := rfl
    _ ≤ (eLpNorm (f : α → E) (4 : ℝ≥0∞) μ * M).toReal :=
      ENNReal.toReal_mono hprod hnorm
    _ = (eLpNorm (f : α → E) (4 : ℝ≥0∞) μ).toReal * M.toReal :=
      ENNReal.toReal_mul
    _ = lpFourToTwoConstant μ * ‖f‖ := by
      rw [mul_comm]
      rfl

/-- Continuous inclusion from `L4` to `L2` on a finite measure space. -/
noncomputable def lpFourToTwo :
    Lp E (4 : ℝ≥0∞) μ →L[ℝ] Lp E (2 : ℝ≥0∞) μ :=
  LinearMap.mkContinuous (lpFourToTwoLinear μ) (lpFourToTwoConstant μ)
    (norm_lpFourToTwoLinear_le μ)

@[simp]
theorem lpFourToTwo_coe
    (f : Lp E (4 : ℝ≥0∞) μ) :
    ((lpFourToTwo μ f : Lp E (2 : ℝ≥0∞) μ) : α →ₘ[μ] E) = f :=
  rfl

theorem lpFourToTwo_injective :
    Function.Injective (lpFourToTwo μ :
      Lp E (4 : ℝ≥0∞) μ → Lp E (2 : ℝ≥0∞) μ) := by
  intro f g hfg
  apply Lp.ext
  have hae :
      (lpFourToTwo μ f : α → E) =ᵐ[μ] (lpFourToTwo μ g : α → E) :=
    Lp.ext_iff.mp hfg
  exact hae

end
