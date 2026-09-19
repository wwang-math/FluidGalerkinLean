import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.MetricSpace.Holder

open Filter MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

/-!
# Half-Hölder control from an L2 time derivative

This file proves the one-dimensional analytic estimate used to turn a
Bochner `L²` derivative bound into finite-mode time equicontinuity.
-/

namespace intervalIntegral

variable {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Cauchy--Schwarz controls a vector-valued interval integral by the length
of the interval and the square integral of the integrand. -/
theorem norm_integral_le_sqrt_mul_sqrt
    {f : ℝ → E} {s t : ℝ} (hst : s ≤ t)
    (hf : MemLp f 2 (volume.restrict (Ioc s t))) :
    ‖∫ x in s..t, f x‖
      ≤ √(t - s) * √(∫ x in s..t, ‖f x‖ ^ 2) := by
  have hfnorm :
      MemLp (fun x => ‖f x‖) (ENNReal.ofReal 2)
        (volume.restrict (Ioc s t)) := by
    simpa using hf.norm
  have hCS :=
    MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
      (μ := volume.restrict (Ioc s t))
      Real.HolderConjugate.two_two
      (memLp_const (1 : ℝ)) hfnorm
  have hnorm :
      ∫ x in s..t, ‖f x‖
        ≤ √(t - s) * √(∫ x in s..t, ‖f x‖ ^ 2) := by
    rw [intervalIntegral.integral_of_le hst,
      intervalIntegral.integral_of_le hst]
    simpa [Real.sqrt_eq_rpow, MeasureTheory.integral_const,
      Real.volume_Ioc, max_eq_left (sub_nonneg.mpr hst),
      ENNReal.toReal_ofReal (sub_nonneg.mpr hst)] using hCS
  exact (intervalIntegral.norm_integral_le_integral_norm hst).trans hnorm

end intervalIntegral

section DerivativeHolder

variable {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A continuous path with an `L²` derivative on a compact interval has
square-root increments. -/
theorem dist_le_sqrt_mul_of_hasDerivWithinAt_of_memLp
    {a b : ℝ} (hab : a ≤ b)
    (f f' : ℝ → E) (M : ℝ≥0)
    (hderiv : ∀ x ∈ Icc a b,
      HasDerivWithinAt f (f' x) (Icc a b) x)
    (hLp : MemLp f' 2 (volume.restrict (Icc a b)))
    (hL2 : ∫ x in a..b, ‖f' x‖ ^ 2 ≤ (M : ℝ) ^ 2) :
    ∀ s t : Icc a b,
      dist (f s) (f t) ≤ (M : ℝ) * √(dist s t) := by
  intro s t
  wlog hst : (s : ℝ) ≤ t generalizing s t
  · rw [dist_comm, dist_comm s t]
    exact this t s (le_of_not_ge hst)
  have hsub : Ioc (s : ℝ) t ⊆ Icc a b := by
    intro x hx
    exact ⟨s.property.1.trans hx.1.le, hx.2.trans t.property.2⟩
  have hLpSub : MemLp f' 2 (volume.restrict (Ioc (s : ℝ) t)) :=
    hLp.mono_measure (Measure.restrict_mono_set volume hsub)
  have hintSub : IntervalIntegrable f' volume (s : ℝ) t := by
    rw [intervalIntegrable_iff, uIoc_of_le hst]
    exact (hLpSub.mono_exponent one_le_two).integrable le_rfl
  have hFTC :
      ∫ x in (s : ℝ)..t, f' x = f t - f s := by
    have hcont : ContinuousOn f (Icc a b) :=
      fun x hx => (hderiv x hx).continuousWithinAt
    apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
      hst (hcont.mono (Icc_subset_Icc s.property.1 t.property.2))
    · intro x hx
      have hxGlobal : x ∈ Ioo a b :=
        ⟨s.property.1.trans_lt hx.1, hx.2.trans_le t.property.2⟩
      exact ((hderiv x ⟨hxGlobal.1.le, hxGlobal.2.le⟩).hasDerivAt
        (Icc_mem_nhds hxGlobal.1 hxGlobal.2)).hasDerivWithinAt
    · exact hintSub
  have hSqSub :
      ∫ x in (s : ℝ)..t, ‖f' x‖ ^ 2 ≤ (M : ℝ) ^ 2 := by
    have hSqInt :
        IntervalIntegrable (fun x => ‖f' x‖ ^ 2) volume a b := by
      rw [intervalIntegrable_iff, uIoc_of_le hab]
      exact (hLp.norm.mono_measure
        (Measure.restrict_mono_set volume Ioc_subset_Icc_self)).integrable_sq
    exact (intervalIntegral.integral_mono_interval
      s.property.1 hst t.property.2
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      hSqInt).trans hL2
  have hIntegral :=
    intervalIntegral.norm_integral_le_sqrt_mul_sqrt hst hLpSub
  rw [hFTC, ← dist_eq_norm] at hIntegral
  have hroot :
      √(∫ x in (s : ℝ)..t, ‖f' x‖ ^ 2) ≤ (M : ℝ) := by
    calc
      √(∫ x in (s : ℝ)..t, ‖f' x‖ ^ 2)
          ≤ √((M : ℝ) ^ 2) := Real.sqrt_le_sqrt hSqSub
      _ = (M : ℝ) := Real.sqrt_sq M.coe_nonneg
  calc
    dist (f s) (f t) = dist (f t) (f s) := dist_comm _ _
    _ ≤ √((t : ℝ) - s) * √(∫ x in (s : ℝ)..t, ‖f' x‖ ^ 2) := hIntegral
    _ ≤ √((t : ℝ) - s) * (M : ℝ) :=
      mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg _)
    _ = (M : ℝ) * √(dist s t) := by
      rw [mul_comm, Subtype.dist_eq, Real.dist_eq,
        abs_of_nonpos (sub_nonpos.mpr hst), neg_sub]

end DerivativeHolder

section SqrtEquicontinuity

variable {X Y A : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [CoeFun A (fun _ => X → Y)]

/-- A function-like family with one square-root modulus is equicontinuous. -/
theorem equicontinuous_subtype_of_uniform_sqrt
    (S : Set A) (M : ℝ≥0)
    (hS : ∀ f : S, ∀ x y,
      dist ((f : A) x) ((f : A) y)
        ≤ (M : ℝ) * √(dist x y)) :
    Equicontinuous ((↑) : S → X → Y) := by
  let modulus : ℝ → ℝ := fun d => (M : ℝ) * √d
  have hmodulus : Tendsto modulus (nhds 0) (nhds 0) := by
    have hcont : Continuous modulus :=
      continuous_const.mul Real.continuous_sqrt
    have hzero : modulus 0 = 0 := by simp [modulus]
    have ht : Tendsto modulus (nhds 0) (nhds (modulus 0)) :=
      hcont.continuousAt
    rw [hzero] at ht
    exact ht
  apply Metric.equicontinuous_of_continuity_modulus modulus hmodulus
  intro x y f
  exact hS f x y

end SqrtEquicontinuity
