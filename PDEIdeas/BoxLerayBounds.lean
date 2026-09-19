import PDEIdeas.BoxGelfandTriple
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-!
# Space-time energy bounds on a rectangular box

The graph norm on `BoxH1ZeroSigma` splits exactly into its velocity and
gradient components.  This file integrates that identity in time and turns
separate state and gradient estimates into the `L²_t V` bound used by the
spectral compactness theorem.
-/

open BoundedContinuousFunction InnerProductSpace MeasureTheory
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace BoundedContinuousFunction

variable {Time E : Type*}
variable [TopologicalSpace Time] [MeasurableSpace Time] [BorelSpace Time]
variable [SecondCountableTopology Time]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- For a bounded continuous Hilbert-valued path, the square of its `L²`
norm is the integral of the pointwise squared norm. -/
theorem norm_toLp_two_sq_eq_integral_norm_sq
    (μ : Measure Time) [IsFiniteMeasure μ]
    (f : Time →ᵇ E) :
    ‖toLp (2 : ℝ≥0∞) μ ℝ f‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_toLp (2 : ℝ≥0∞) μ ℝ f] with t ht
  rw [ht, real_inner_self_eq_norm_sq]

variable {F G : Type*}
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- A pointwise orthogonal norm splitting of bounded continuous paths remains
an exact orthogonal splitting after passage to `L²`. -/
theorem norm_toLp_two_sq_eq_add_of_pointwise
    (μ : Measure Time) [IsFiniteMeasure μ]
    (f : Time →ᵇ E) (g : Time →ᵇ F) (h : Time →ᵇ G)
    (hsplit : ∀ t, ‖f t‖ ^ 2 = ‖g t‖ ^ 2 + ‖h t‖ ^ 2) :
    ‖toLp (2 : ℝ≥0∞) μ ℝ f‖ ^ 2 =
      ‖toLp (2 : ℝ≥0∞) μ ℝ g‖ ^ 2 +
      ‖toLp (2 : ℝ≥0∞) μ ℝ h‖ ^ 2 := by
  let gLp := toLp (2 : ℝ≥0∞) μ ℝ g
  let hLp := toLp (2 : ℝ≥0∞) μ ℝ h
  have hgIntegrable : Integrable (fun t => ‖g t‖ ^ 2) μ := by
    refine (L2.integrable_inner (𝕜 := ℝ) gLp gLp).congr ?_
    filter_upwards [coeFn_toLp (2 : ℝ≥0∞) μ ℝ g] with t ht
    simp only [gLp, ht, real_inner_self_eq_norm_sq]
  have hhIntegrable : Integrable (fun t => ‖h t‖ ^ 2) μ := by
    refine (L2.integrable_inner (𝕜 := ℝ) hLp hLp).congr ?_
    filter_upwards [coeFn_toLp (2 : ℝ≥0∞) μ ℝ h] with t ht
    simp only [hLp, ht, real_inner_self_eq_norm_sq]
  rw [norm_toLp_two_sq_eq_integral_norm_sq μ f]
  rw [norm_toLp_two_sq_eq_integral_norm_sq μ g]
  rw [norm_toLp_two_sq_eq_integral_norm_sq μ h]
  rw [← integral_add hgIntegrable hhIntegrable]
  exact integral_congr_ae (Filter.Eventually.of_forall hsplit)

end BoundedContinuousFunction

variable {n : ℕ}
variable {Time : Type*} [TopologicalSpace Time]

/-- State component of a bounded continuous energy path. -/
def boxEnergyStatePath
    (I : BoxIntegral.Box (Fin (n + 1)))
    (u : Time →ᵇ BoxH1ZeroSigma I) : Time →ᵇ BoxL2Sigma I :=
  (boxEnergyToState I).compLeftContinuousBounded Time u

/-- Gradient component of a bounded continuous energy path. -/
def boxEnergyGradientPath
    (I : BoxIntegral.Box (Fin (n + 1)))
    (u : Time →ᵇ BoxH1ZeroSigma I) : Time →ᵇ BoxGradientL2 I :=
  (boxEnergyGradient I).compLeftContinuousBounded Time u

@[simp]
theorem boxEnergyStatePath_apply
    (I : BoxIntegral.Box (Fin (n + 1)))
    (u : Time →ᵇ BoxH1ZeroSigma I) (t : Time) :
    boxEnergyStatePath I u t = boxEnergyToState I (u t) :=
  rfl

@[simp]
theorem boxEnergyGradientPath_apply
    (I : BoxIntegral.Box (Fin (n + 1)))
    (u : Time →ᵇ BoxH1ZeroSigma I) (t : Time) :
    boxEnergyGradientPath I u t = boxEnergyGradient I (u t) :=
  rfl

variable [MeasurableSpace Time] [BorelSpace Time]
variable [SecondCountableTopology Time]

/-- The spatial graph-norm identity integrated over time. -/
theorem boxEnergyPath_toLp_norm_sq_eq_state_add_gradient
    (I : BoxIntegral.Box (Fin (n + 1)))
    (μ : Measure Time) [IsFiniteMeasure μ]
    (u : Time →ᵇ BoxH1ZeroSigma I) :
    ‖BoundedContinuousFunction.toLp (2 : ℝ≥0∞) μ ℝ u‖ ^ 2 =
      ‖BoundedContinuousFunction.toLp (2 : ℝ≥0∞) μ ℝ
        (boxEnergyStatePath I u)‖ ^ 2 +
      ‖BoundedContinuousFunction.toLp (2 : ℝ≥0∞) μ ℝ
        (boxEnergyGradientPath I u)‖ ^ 2 := by
  apply BoundedContinuousFunction.norm_toLp_two_sq_eq_add_of_pointwise μ
  intro t
  exact boxEnergy_norm_sq_eq_state_add_gradient I (u t)

/-- Separate `L²_t H` and gradient bounds give the exact Euclidean radius
for the full `L²_t V` graph norm. -/
theorem boxEnergyPath_toLp_norm_le_sqrt
    (I : BoxIntegral.Box (Fin (n + 1)))
    (μ : Measure Time) [IsFiniteMeasure μ]
    (u : Time →ᵇ BoxH1ZeroSigma I)
    (stateRadius gradientRadius : ℝ)
    (hstateRadius : 0 ≤ stateRadius)
    (hgradientRadius : 0 ≤ gradientRadius)
    (hstate :
      ‖BoundedContinuousFunction.toLp (2 : ℝ≥0∞) μ ℝ
        (boxEnergyStatePath I u)‖ ≤ stateRadius)
    (hgradient :
      ‖BoundedContinuousFunction.toLp (2 : ℝ≥0∞) μ ℝ
        (boxEnergyGradientPath I u)‖ ≤ gradientRadius) :
    ‖BoundedContinuousFunction.toLp (2 : ℝ≥0∞) μ ℝ u‖ ≤
      Real.sqrt (stateRadius ^ 2 + gradientRadius ^ 2) := by
  rw [← sq_le_sq₀
    (norm_nonneg
      (BoundedContinuousFunction.toLp (2 : ℝ≥0∞) μ ℝ u))
    (Real.sqrt_nonneg (stateRadius ^ 2 + gradientRadius ^ 2))]
  have hstateSq :
      ‖BoundedContinuousFunction.toLp (2 : ℝ≥0∞) μ ℝ
        (boxEnergyStatePath I u)‖ ^ 2 ≤ stateRadius ^ 2 :=
    (sq_le_sq₀
      (norm_nonneg
        (BoundedContinuousFunction.toLp (2 : ℝ≥0∞) μ ℝ
          (boxEnergyStatePath I u))) hstateRadius).2 hstate
  have hgradientSq :
      ‖BoundedContinuousFunction.toLp (2 : ℝ≥0∞) μ ℝ
        (boxEnergyGradientPath I u)‖ ^ 2 ≤ gradientRadius ^ 2 :=
    (sq_le_sq₀
      (norm_nonneg
        (BoundedContinuousFunction.toLp (2 : ℝ≥0∞) μ ℝ
          (boxEnergyGradientPath I u))) hgradientRadius).2 hgradient
  calc
    ‖BoundedContinuousFunction.toLp (2 : ℝ≥0∞) μ ℝ u‖ ^ 2 =
        ‖BoundedContinuousFunction.toLp (2 : ℝ≥0∞) μ ℝ
          (boxEnergyStatePath I u)‖ ^ 2 +
        ‖BoundedContinuousFunction.toLp (2 : ℝ≥0∞) μ ℝ
          (boxEnergyGradientPath I u)‖ ^ 2 :=
      boxEnergyPath_toLp_norm_sq_eq_state_add_gradient I μ u
    _ ≤ stateRadius ^ 2 + gradientRadius ^ 2 :=
      add_le_add hstateSq hgradientSq
    _ = Real.sqrt (stateRadius ^ 2 + gradientRadius ^ 2) ^ 2 :=
      (Real.sq_sqrt
        (add_nonneg (sq_nonneg stateRadius) (sq_nonneg gradientRadius))).symm

/-- A pointwise state bound yields an explicit state `L²` bound, with the
finite-measure factor supplied by the continuous-to-`L²` embedding. -/
theorem boxEnergyStatePath_toLp_norm_le
    (I : BoxIntegral.Box (Fin (n + 1)))
    (μ : Measure Time) [IsFiniteMeasure μ]
    (u : Time →ᵇ BoxH1ZeroSigma I)
    (stateRadius : ℝ) (hstateRadius : 0 ≤ stateRadius)
    (hstate : ∀ t, ‖boxEnergyToState I (u t)‖ ≤ stateRadius) :
    ‖BoundedContinuousFunction.toLp (2 : ℝ≥0∞) μ ℝ
      (boxEnergyStatePath I u)‖ ≤
      measureUnivNNReal μ ^ ((2 : ℝ≥0∞).toReal)⁻¹ * stateRadius := by
  exact (BoundedContinuousFunction.Lp_norm_le
    (p := (2 : ℝ≥0∞)) (μ := μ) (boxEnergyStatePath I u)).trans
      (mul_le_mul_of_nonneg_left
        ((BoundedContinuousFunction.norm_le hstateRadius).2 hstate)
        (by positivity))

end
