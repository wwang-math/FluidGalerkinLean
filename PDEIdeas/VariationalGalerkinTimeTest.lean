import PDEIdeas.VariationalGalerkin
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Time-tested variational Galerkin identities

The coefficient ODE is tested against a fixed common-space vector and a
scalar time cutoff.  Integration by parts produces the distributional weak
identity used in the spectral limit passage, including the initial term and
without requiring pointwise convergence at the terminal time.
-/

open InnerProductSpace MeasureTheory Set

noncomputable section

/-- A scalar `C1` time test on an ordered closed interval, represented by its
value, derivative, and the derivative identity needed for integration by
parts. -/
structure IntervalTimeTest (a b : ℝ) where
  value : ℝ → ℝ
  deriv : ℝ → ℝ
  hasDerivWithinAt : ∀ t ∈ Icc a b,
    HasDerivWithinAt value (deriv t) (Icc a b) t
  deriv_intervalIntegrable : IntervalIntegrable deriv volume a b

namespace IntervalTimeTest

theorem continuousOn
    {a b : ℝ} (eta : IntervalTimeTest a b) :
    ContinuousOn eta.value (Icc a b) :=
  HasDerivWithinAt.continuousOn eta.hasDerivWithinAt

theorem value_intervalIntegrable
    {a b : ℝ} (hab : a ≤ b) (eta : IntervalTimeTest a b) :
    IntervalIntegrable eta.value volume a b :=
  ContinuousOn.intervalIntegrable_of_Icc hab eta.continuousOn

end IntervalTimeTest

namespace VariationalGalerkinProblem

variable {W Test : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    [NormedAddCommGroup Test] [NormedSpace ℝ Test]

/-- Integration by parts for one common-space test coordinate of a genuine
variational Galerkin solution. -/
theorem LocalSolutionOn.timeTested_dualRHS_identity
    {P : VariationalGalerkinProblem W}
    {a b : ℝ} (hab : a ≤ b)
    (u : P.LocalSolutionOn (⟨a, le_rfl, hab⟩ : Icc a b))
    (Q : Test →L[ℝ] W) (phi : Test)
    (eta : IntervalTimeTest a b)
    (hdual : IntervalIntegrable
      (fun t => P.dualRHS Q t (u.toFun t) phi) volume a b) :
    ∫ t in a..b,
        P.dualRHS Q t (u.toFun t) phi * eta.value t +
          ⟪u.toFun t, Q phi⟫_ℝ * eta.deriv t =
      ⟪u.toFun b, Q phi⟫_ℝ * eta.value b -
        ⟪u.toFun a, Q phi⟫_ℝ * eta.value a := by
  let Y : ℝ → ℝ := fun t => ⟪u.toFun t, Q phi⟫_ℝ
  let D : ℝ → ℝ := fun t => P.dualRHS Q t (u.toFun t) phi
  have hY : ∀ t ∈ uIcc a b,
      HasDerivWithinAt Y (D t) (uIcc a b) t := by
    rw [uIcc_of_le hab]
    intro t ht
    exact u.hasDerivWithinAt_test Q phi t ht
  have heta : ∀ t ∈ uIcc a b,
      HasDerivWithinAt eta.value (eta.deriv t) (uIcc a b) t := by
    simpa only [uIcc_of_le hab] using eta.hasDerivWithinAt
  simpa only [Y, D] using
    intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivWithinAt
      hY heta hdual eta.deriv_intervalIntegrable

/-- Zero forcing gives the finite-level distributional weak equation with
diffusion, convection, and the projected initial value displayed separately. -/
theorem LocalSolutionOn.timeTested_zeroForcing_identity
    {P : VariationalGalerkinProblem W}
    {a b : ℝ} (hab : a ≤ b)
    (u : P.LocalSolutionOn (⟨a, le_rfl, hab⟩ : Icc a b))
    (Q : Test →L[ℝ] W) (phi : Test)
    (eta : IntervalTimeTest a b)
    (heta_terminal : eta.value b = 0)
    (hforcing : P.forcing = fun _ => 0) :
    -(∫ t in a..b, ⟪u.toFun t, Q phi⟫_ℝ * eta.deriv t) +
        (∫ t in a..b,
          P.system.diffusion (u.toFun t) (Q phi) * eta.value t) +
        (∫ t in a..b,
          P.system.convection (u.toFun t) (u.toFun t) (Q phi) * eta.value t) =
      ⟪P.initial, Q phi⟫_ℝ * eta.value a := by
  let Y : ℝ → ℝ := fun t => ⟪u.toFun t, Q phi⟫_ℝ
  let A : ℝ → ℝ := fun t => P.system.diffusion (u.toFun t) (Q phi)
  let B : ℝ → ℝ := fun t => P.system.convection (u.toFun t) (u.toFun t) (Q phi)
  let fA : ℝ → ℝ := fun t => A t * eta.value t
  let fB : ℝ → ℝ := fun t => B t * eta.value t
  let fY : ℝ → ℝ := fun t => Y t * eta.deriv t
  have hU : ContinuousOn u.toFun (Icc a b) := u.continuousOn
  have hY : ContinuousOn Y (Icc a b) := by
    exact (innerSLFlip ℝ (Q phi)).continuous.comp_continuousOn hU
  have hAcont : ContinuousOn A (Icc a b) :=
    (P.system.diffusion.continuous.comp_continuousOn hU).clm_apply
      continuousOn_const
  have hBcont : ContinuousOn B (Icc a b) :=
    (P.system.convection.continuous₂.comp_continuousOn
      (hU.prodMk hU)).clm_apply continuousOn_const
  have hA : IntervalIntegrable fA volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    exact hAcont.mul eta.continuousOn
  have hB : IntervalIntegrable fB volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    exact hBcont.mul eta.continuousOn
  have hY_uIcc : ContinuousOn Y (uIcc a b) := by
    simpa only [uIcc_of_le hab] using hY
  have hYd : IntervalIntegrable fY volume a b :=
    eta.deriv_intervalIntegrable.continuousOn_mul hY_uIcc
  have hdual_cont : ContinuousOn
      (fun t => P.dualRHS Q t (u.toFun t) phi) (Icc a b) := by
    simpa only [dualRHS_apply, hforcing, ContinuousLinearMap.zero_apply,
      sub_eq_add_neg, add_zero, A, B] using hAcont.neg.sub hBcont
  have hdual : IntervalIntegrable
      (fun t => P.dualRHS Q t (u.toFun t) phi) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab hdual_cont
  have hraw := u.timeTested_dualRHS_identity hab Q phi eta hdual
  have hsplit :
      (∫ t in a..b,
          P.dualRHS Q t (u.toFun t) phi * eta.value t +
            Y t * eta.deriv t) =
        -(∫ t in a..b, fA t) -
          (∫ t in a..b, fB t) +
          ∫ t in a..b, fY t := by
    calc
      (∫ t in a..b,
          P.dualRHS Q t (u.toFun t) phi * eta.value t +
            Y t * eta.deriv t) =
          ∫ t in a..b,
            ((-fA t) - fB t) + fY t := by
            apply intervalIntegral.integral_congr
            intro t _ht
            simp only [dualRHS_apply, hforcing,
              ContinuousLinearMap.zero_apply, add_zero, A, B, fA, fB, fY]
            ring
      _ = (∫ t in a..b, (-fA t) - fB t) +
          ∫ t in a..b, fY t := by
            exact intervalIntegral.integral_add
              (f := fun t => (-fA t) - fB t) (g := fY)
              (hA.neg.sub hB) hYd
      _ = ((∫ t in a..b, -fA t) -
          ∫ t in a..b, fB t) +
          ∫ t in a..b, fY t := by
            exact congrArg (fun x => x + ∫ t in a..b, fY t)
              (intervalIntegral.integral_sub
                (f := fun t => -fA t) (g := fB) hA.neg hB)
      _ = -(∫ t in a..b, fA t) -
          (∫ t in a..b, fB t) +
          ∫ t in a..b, fY t := by
            rw [intervalIntegral.integral_neg (f := fA)]
  rw [show u.toFun a = P.initial from u.initial, heta_terminal,
    mul_zero, zero_sub] at hraw
  rw [hsplit] at hraw
  have hfinal : -(∫ t in a..b, fY t) +
      (∫ t in a..b, fA t) +
      (∫ t in a..b, fB t) =
        ⟪P.initial, Q phi⟫_ℝ * eta.value a := by
    linarith
  simpa only [fY, fA, fB, Y, A, B] using hfinal

end VariationalGalerkinProblem

end
