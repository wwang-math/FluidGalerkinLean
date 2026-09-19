import PDEIdeas.VariationalGalerkinTimeTest
import PDEIdeas.BoxGalerkinSolutionBounds
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-!
# Space-time test paths for the Leray limit

A scalar interval cutoff induces continuous linear maps from a spatial test
space into time-dependent `L2` and `L-infinity` paths.  Its derivative is
stored in `L2`, matching the strong state convergence used in the weak
equation.
-/

open BoundedContinuousFunction MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Constant vectors as bounded continuous paths. -/
noncomputable def boundedContinuousConstCLM
    (Time E : Type*) [TopologicalSpace Time]
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    E →L[ℝ] Time →ᵇ E :=
  LinearMap.mkContinuous
    { toFun := fun x => BoundedContinuousFunction.const Time x
      map_add' := by
        intro x y
        ext t
        rfl
      map_smul' := by
        intro c x
        ext t
        rfl }
    1 (fun x => by
      simpa only [one_mul] using
        (BoundedContinuousFunction.norm_const_le
          (α := Time) (β := E) x))

namespace IntervalTimeTest

/-- The value of an interval test as a bounded continuous function on the
closed interval subtype. -/
noncomputable def valueBCF
    {a b : ℝ} (eta : IntervalTimeTest a b) : Icc a b →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    { toFun := fun t => eta.value t
      continuous_toFun := eta.continuousOn.restrict }

@[simp]
theorem valueBCF_apply
    {a b : ℝ} (eta : IntervalTimeTest a b) (t : Icc a b) :
    eta.valueBCF t = eta.value t :=
  rfl

/-- Multiplication by the scalar cutoff, viewed as a continuous linear map
from spatial vectors to bounded continuous time paths. -/
noncomputable def valueBCFLift
    {a b : ℝ} (eta : IntervalTimeTest a b)
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    E →L[ℝ] Icc a b →ᵇ E :=
  (ContinuousLinearMap.lsmul ℝ (Icc a b →ᵇ ℝ) eta.valueBCF).comp
    (boundedContinuousConstCLM (Icc a b) E)

@[simp]
theorem valueBCFLift_apply_apply
    {a b : ℝ} (eta : IntervalTimeTest a b)
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (t : Icc a b) :
    eta.valueBCFLift E x t = eta.value t • x :=
  rfl

/-- Multiplication by the scalar cutoff as a continuous map into a
time-dependent `Lp` space. -/
noncomputable def valueLpCLM
    {a b : ℝ} (eta : IntervalTimeTest a b)
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    E →L[ℝ] Lp E p
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) :=
  (BoundedContinuousFunction.toLp p
    (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) ℝ).comp
      (eta.valueBCFLift E)

theorem valueLpCLM_apply_ae
    {a b : ℝ} (eta : IntervalTimeTest a b)
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (x : E) :
    eta.valueLpCLM E p x =ᵐ[
      SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b]
        fun t => eta.value t • x := by
  simpa only [valueLpCLM, valueBCFLift_apply_apply] using
    BoundedContinuousFunction.coeFn_toLp p
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) ℝ
      (eta.valueBCFLift E x)

end IntervalTimeTest

/-- A time cutoff whose derivative belongs to the `L2` test class used by
the limiting state pairing. -/
structure LerayIntervalTimeTest (a b : ℝ) extends IntervalTimeTest a b where
  deriv_memLp_two : MemLp
    (fun t : Icc a b => toIntervalTimeTest.deriv t)
    2 (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)

namespace LerayIntervalTimeTest

variable {a b : ℝ}

/-- The scalar derivative as an `L2` path. -/
noncomputable def derivLp (eta : LerayIntervalTimeTest a b) :
    Lp ℝ (2 : ℝ≥0∞)
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) :=
  eta.deriv_memLp_two.toLp

/-- The derivative cutoff multiplied by a fixed spatial vector. -/
noncomputable def derivVectorLp
    (eta : LerayIntervalTimeTest a b)
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) :
    Lp E (2 : ℝ≥0∞)
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) :=
  (ContinuousLinearMap.toSpanSingleton ℝ x).compLpL 2
    (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) eta.derivLp

theorem derivVectorLp_apply_ae
    (eta : LerayIntervalTimeTest a b)
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) :
    eta.derivVectorLp E x =ᵐ[
      SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b]
        fun t => eta.deriv t • x := by
  filter_upwards [
    (ContinuousLinearMap.toSpanSingleton ℝ x).coeFn_compLpL eta.derivLp,
    eta.deriv_memLp_two.coeFn_toLp] with t hspan hderiv
  change
    ((ContinuousLinearMap.toSpanSingleton ℝ x).compLpL 2
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)
        eta.derivLp) t = eta.deriv t • x
  rw [hspan]
  have hderiv' : eta.derivLp t = eta.deriv t := by
    change (eta.deriv_memLp_two.toLp :
      Lp ℝ (2 : ℝ≥0∞)
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)) t = _
    exact hderiv
  rw [hderiv']
  rfl

end LerayIntervalTimeTest

end
