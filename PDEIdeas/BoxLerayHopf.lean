import PDEIdeas.BoxLadyzhenskayaLimit
import PDEIdeas.LerayTimeTest
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Leray--Hopf limit on a two-dimensional box

The canonical unforced spectral solutions satisfy an exact time-tested
finite equation.  Ladyzhenskaya interpolation and simultaneous strong/weak
compactness pass every term to a common limit trajectory.
-/

open BoundedContinuousFunction Filter InnerProductSpace MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

noncomputable section

local instance box_leray_hopf_fact_one_le_four : Fact (1 ≤ (4 : ℝ≥0∞)) :=
  ⟨by norm_num⟩

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 500000

namespace BoxCompactSpectralRepresentation

variable {I : BoxIntegral.Box (Fin 2)}
    (S : BoxCompactSpectralRepresentation I)

local instance box_leray_hopf_h_complete : CompleteSpace (BoxL2Sigma I) :=
  boxL2Sigma_completeSpace I

local instance box_leray_hopf_v_complete : CompleteSpace (BoxH1ZeroSigma I) :=
  boxH1ZeroSigma_completeSpace I

/-- Coefficient trajectory selected at one canonical unforced spectral
level. -/
def zeroForcingCoefficientTrajectory2D
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I) (m : ℕ) :
    ℝ → S.CoefficientSpace m :=
  S.canonicalSolutionToFun m hab (S.zeroForcingSolution2D hab m u₀)

/-- Energy-space reconstruction of one canonical unforced spectral
trajectory. -/
def zeroForcingEnergyTrajectory2D
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I) (m : ℕ) :
    ℝ → BoxH1ZeroSigma I :=
  fun t => S.energySynthesis m (S.zeroForcingCoefficientTrajectory2D hab u₀ m t)

/-- Pivot-space reconstruction of one canonical unforced spectral
trajectory. -/
def zeroForcingStateTrajectory2D
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I) (m : ℕ) :
    ℝ → BoxL2Sigma I :=
  fun t => S.stateSynthesis m (S.zeroForcingCoefficientTrajectory2D hab u₀ m t)

/-- The projected coefficient pairing is the unprojected physical state
pairing after time integration. -/
theorem zeroForcing_timeTest_state_integral_eq
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I)
    (m : ℕ) (φ : BoxH1ZeroSigma I) (eta : IntervalTimeTest a b) :
    (∫ t in a..b,
      ⟪S.zeroForcingCoefficientTrajectory2D hab u₀ m t,
        S.testProjection m φ⟫_ℝ * eta.deriv t) =
      ∫ t in a..b,
        ⟪S.zeroForcingStateTrajectory2D hab u₀ m t,
          boxEnergyToState I φ⟫_ℝ * eta.deriv t := by
  apply intervalIntegral.integral_congr
  intro t _ht
  dsimp only
  exact congrArg (fun r : ℝ => r * eta.deriv t)
    (S.inner_testProjection_eq_state_inner m
      (S.zeroForcingCoefficientTrajectory2D hab u₀ m t) φ)

/-- Finite diffusion tested by a common energy vector. -/
theorem zeroForcing_timeTest_diffusion_integral_eq
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I)
    (m : ℕ) (φ : BoxH1ZeroSigma I) (eta : IntervalTimeTest a b) :
    (∫ t in a..b,
      (S.zeroForcingProblem2D m u₀).system.diffusion
        (S.zeroForcingCoefficientTrajectory2D hab u₀ m t)
        (S.testProjection m φ) * eta.value t) =
      ∫ t in a..b,
        boxGradientDiffusion I (S.zeroForcingEnergyTrajectory2D hab u₀ m t)
          (S.energyProjection m φ) *
            eta.value t := by
  apply intervalIntegral.integral_congr
  intro t _ht
  dsimp only
  apply congrArg (fun r : ℝ => r * eta.value t)
  calc
    (S.zeroForcingProblem2D m u₀).system.diffusion
        (S.zeroForcingCoefficientTrajectory2D hab u₀ m t)
        (S.testProjection m φ) =
        boxGradientDiffusion I (S.zeroForcingEnergyTrajectory2D hab u₀ m t)
          (S.energySynthesis m (S.testProjection m φ)) := by
      exact S.zeroForcingProblem2D_diffusion_apply m u₀
        (S.zeroForcingCoefficientTrajectory2D hab u₀ m t)
        (S.testProjection m φ)
    _ = boxGradientDiffusion I (S.zeroForcingEnergyTrajectory2D hab u₀ m t)
        (S.energyProjection m φ) :=
      congrArg
        (boxGradientDiffusion I (S.zeroForcingEnergyTrajectory2D hab u₀ m t))
        (S.energySynthesis_testProjection_eq_partialProjection m φ)

/-- Finite convection tested by a common energy vector. -/
theorem zeroForcing_timeTest_convection_integral_eq
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I)
    (m : ℕ) (φ : BoxH1ZeroSigma I) (eta : IntervalTimeTest a b) :
    (∫ t in a..b,
      (S.zeroForcingProblem2D m u₀).system.convection
        (S.zeroForcingCoefficientTrajectory2D hab u₀ m t)
        (S.zeroForcingCoefficientTrajectory2D hab u₀ m t)
        (S.testProjection m φ) * eta.value t) =
      ∫ t in a..b,
        (boxLadyzhenskayaRealization I).toBoxEnergyL4Realization.convectionForm I
          (S.zeroForcingEnergyTrajectory2D hab u₀ m t)
          (S.zeroForcingEnergyTrajectory2D hab u₀ m t)
          (S.energyProjection m φ) *
            eta.value t := by
  apply intervalIntegral.integral_congr
  intro t _ht
  dsimp only
  apply congrArg (fun r : ℝ => r * eta.value t)
  calc
    (S.zeroForcingProblem2D m u₀).system.convection
        (S.zeroForcingCoefficientTrajectory2D hab u₀ m t)
        (S.zeroForcingCoefficientTrajectory2D hab u₀ m t)
        (S.testProjection m φ) =
        (boxLadyzhenskayaRealization I).toBoxEnergyL4Realization.convectionForm I
          (S.zeroForcingEnergyTrajectory2D hab u₀ m t)
          (S.zeroForcingEnergyTrajectory2D hab u₀ m t)
          (S.energySynthesis m (S.testProjection m φ)) := by
      exact S.zeroForcingProblem2D_convection_apply m u₀
        (S.zeroForcingCoefficientTrajectory2D hab u₀ m t)
        (S.zeroForcingCoefficientTrajectory2D hab u₀ m t)
        (S.testProjection m φ)
    _ =
        (boxLadyzhenskayaRealization I).toBoxEnergyL4Realization.convectionForm I
          (S.zeroForcingEnergyTrajectory2D hab u₀ m t)
          (S.zeroForcingEnergyTrajectory2D hab u₀ m t)
          (S.energyProjection m φ) :=
      congrArg
        (fun z =>
          (boxLadyzhenskayaRealization I).toBoxEnergyL4Realization.convectionForm I
            (S.zeroForcingEnergyTrajectory2D hab u₀ m t)
            (S.zeroForcingEnergyTrajectory2D hab u₀ m t) z)
        (S.energySynthesis_testProjection_eq_partialProjection m φ)

/-- The projected initial coefficient pairing is the prescribed physical
initial-state pairing. -/
theorem zeroForcing_initial_test_pairing_eq
    (u₀ : BoxL2Sigma I) (m : ℕ) (φ : BoxH1ZeroSigma I) :
    ⟪(S.zeroForcingProblem2D m u₀).initial, S.testProjection m φ⟫_ℝ =
      ⟪S.stateSynthesis m (S.stateInitialCoefficient m u₀),
        boxEnergyToState I φ⟫_ℝ := by
  change ⟪S.stateInitialCoefficient m u₀, S.testProjection m φ⟫_ℝ = _
  exact S.inner_testProjection_eq_state_inner m
    (S.stateInitialCoefficient m u₀) φ

/-- The canonical energy `Lp` representative agrees almost everywhere with
the physical reconstructed trajectory. -/
theorem zeroForcing_energyLp_eq_trajectory_ae
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I) (m : ℕ) :
    (S.zeroForcingLeraySpectralCompactFamily2D hab u₀).energyLp m =ᵐ[
      SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b]
        fun t => S.zeroForcingEnergyTrajectory2D hab u₀ m t := by
  let G := S.zeroForcingLeraySpectralCompactFamily2D hab u₀
  change BoundedContinuousFunction.toLp (2 : ℝ≥0∞)
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) ℝ
      (G.lift m) =ᵐ[
        SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b] _
  filter_upwards [BoundedContinuousFunction.coeFn_toLp (2 : ℝ≥0∞)
    (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) ℝ
    (G.lift m)] with t ht
  rw [ht, S.zeroForcingLeraySpectralCompactFamily2D_lift_apply]
  rfl

/-- The canonical state `Lp` representative agrees almost everywhere with
the physical reconstructed trajectory. -/
theorem zeroForcing_stateLp_eq_trajectory_ae
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I) (m : ℕ) :
    (S.zeroForcingLeraySpectralCompactFamily2D hab u₀).stateLp m =ᵐ[
      SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b]
        fun t => S.zeroForcingStateTrajectory2D hab u₀ m t := by
  let G := S.zeroForcingLeraySpectralCompactFamily2D hab u₀
  change BoundedContinuousFunction.toLp (2 : ℝ≥0∞)
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) ℝ
      (LeraySpectralCompactFamily.statePath G m) =ᵐ[
        SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b] _
  filter_upwards [BoundedContinuousFunction.coeFn_toLp (2 : ℝ≥0∞)
    (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) ℝ
    (LeraySpectralCompactFamily.statePath G m)] with t ht
  rw [ht]
  change boxEnergyToState I (G.lift m t) = _
  rw [S.zeroForcingLeraySpectralCompactFamily2D_lift_apply,
    S.boxEnergyToState_energySynthesis]
  rfl

/-- Physical form of the finite spectral equation after testing in time and
reconstructing the common-space test projection. -/
theorem zeroForcingSolution2D_timeTested_physical_identity
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I)
    (m : ℕ) (φ : BoxH1ZeroSigma I)
    (eta : IntervalTimeTest a b)
    (heta_terminal : eta.value b = 0) :
    -(∫ t in a..b,
        ⟪S.zeroForcingStateTrajectory2D hab u₀ m t, boxEnergyToState I φ⟫_ℝ *
          eta.deriv t) +
      (∫ t in a..b,
        boxGradientDiffusion I (S.zeroForcingEnergyTrajectory2D hab u₀ m t)
          (S.energyProjection m φ) *
          eta.value t) +
      (∫ t in a..b,
        (boxLadyzhenskayaRealization I).toBoxEnergyL4Realization.convectionForm I
          (S.zeroForcingEnergyTrajectory2D hab u₀ m t)
          (S.zeroForcingEnergyTrajectory2D hab u₀ m t)
          (S.energyProjection m φ) *
            eta.value t) =
      ⟪S.stateSynthesis m (S.stateInitialCoefficient m u₀), boxEnergyToState I φ⟫_ℝ *
        eta.value a := by
  letI : NormedAddCommGroup (S.CoefficientSpace m) :=
    S.coefficientSpaceNormedAddCommGroup m
  letI : InnerProductSpace ℝ (S.CoefficientSpace m) :=
    S.coefficientSpaceInnerProductSpace m
  letI : CompleteSpace (S.CoefficientSpace m) :=
    S.coefficientSpaceCompleteSpace m
  let P := S.zeroForcingProblem2D m u₀
  let u := S.zeroForcingSolution2D hab m u₀
  have hzero : P.forcing = fun _ => 0 := by
    funext t
    exact S.zeroForcingProblem2D_forcing m u₀ t
  have h :=
    @VariationalGalerkinProblem.LocalSolutionOn.timeTested_zeroForcing_identity
      (S.CoefficientSpace m) (BoxH1ZeroSigma I)
      (S.coefficientSpaceNormedAddCommGroup m)
      (S.coefficientSpaceInnerProductSpace m)
      (S.coefficientSpaceCompleteSpace m)
      inferInstance inferInstance P a b hab u
      (S.testProjection m) φ eta heta_terminal hzero
  have hcoeff :
      (-(∫ t in a..b,
          ⟪S.zeroForcingCoefficientTrajectory2D hab u₀ m t,
            S.testProjection m φ⟫_ℝ * eta.deriv t) +
        (∫ t in a..b,
          (S.zeroForcingProblem2D m u₀).system.diffusion
            (S.zeroForcingCoefficientTrajectory2D hab u₀ m t)
            (S.testProjection m φ) * eta.value t) +
        (∫ t in a..b,
          (S.zeroForcingProblem2D m u₀).system.convection
            (S.zeroForcingCoefficientTrajectory2D hab u₀ m t)
            (S.zeroForcingCoefficientTrajectory2D hab u₀ m t)
            (S.testProjection m φ) * eta.value t) =
        ⟪(S.zeroForcingProblem2D m u₀).initial,
          S.testProjection m φ⟫_ℝ * eta.value a) := by
    exact h
  have hstate := S.zeroForcing_timeTest_state_integral_eq hab u₀ m φ eta
  have hdiffusion :=
    S.zeroForcing_timeTest_diffusion_integral_eq hab u₀ m φ eta
  have hconvection :=
    S.zeroForcing_timeTest_convection_integral_eq hab u₀ m φ eta
  have hinitial := S.zeroForcing_initial_test_pairing_eq u₀ m φ
  have hinitialMul := congrArg (fun r : ℝ => r * eta.value a) hinitial
  linarith only [hcoeff, hstate, hdiffusion, hconvection, hinitialMul]

/-- State integral expressed with the canonical state `Lp` representative. -/
theorem zeroForcing_stateLp_time_integral_eq
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I)
    (m : ℕ) (φ : BoxH1ZeroSigma I) (eta : IntervalTimeTest a b) :
    (∫ t : Icc a b,
      ⟪(S.zeroForcingLeraySpectralCompactFamily2D hab u₀).stateLp m t,
        boxEnergyToState I φ⟫_ℝ * eta.deriv t
      ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) =
      ∫ t in a..b,
        ⟪S.zeroForcingStateTrajectory2D hab u₀ m t,
          boxEnergyToState I φ⟫_ℝ * eta.deriv t := by
  let G := S.zeroForcingLeraySpectralCompactFamily2D hab u₀
  let μ := SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b
  calc
    (∫ t : Icc a b,
        ⟪G.stateLp m t, boxEnergyToState I φ⟫_ℝ * eta.deriv t ∂μ) =
        ∫ t : Icc a b,
          ⟪S.zeroForcingStateTrajectory2D hab u₀ m t,
            boxEnergyToState I φ⟫_ℝ * eta.deriv t ∂μ := by
      apply integral_congr_ae
      filter_upwards [S.zeroForcing_stateLp_eq_trajectory_ae hab u₀ m] with t ht
      rw [ht]
    _ = _ :=
      SmoothBoxVariationalGalerkinLevel.integral_intervalSubtypeMeasure hab
        (fun t =>
          ⟪S.zeroForcingStateTrajectory2D hab u₀ m t,
            boxEnergyToState I φ⟫_ℝ * eta.deriv t)

/-- Diffusion integral expressed with the canonical energy `Lp`
representative. -/
theorem zeroForcing_energyLp_diffusion_time_integral_eq
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I)
    (m : ℕ) (φ : BoxH1ZeroSigma I) (eta : IntervalTimeTest a b) :
    (∫ t : Icc a b,
      boxGradientDiffusion I
        ((S.zeroForcingLeraySpectralCompactFamily2D hab u₀).energyLp m t)
        (S.energyProjection m φ) *
          eta.value t
      ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) =
      ∫ t in a..b,
        boxGradientDiffusion I (S.zeroForcingEnergyTrajectory2D hab u₀ m t)
          (S.energyProjection m φ) *
            eta.value t := by
  let G := S.zeroForcingLeraySpectralCompactFamily2D hab u₀
  let μ := SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b
  calc
    (∫ t : Icc a b,
        boxGradientDiffusion I (G.energyLp m t)
          (S.energyProjection m φ) *
            eta.value t ∂μ) =
        ∫ t : Icc a b,
          boxGradientDiffusion I
            (S.zeroForcingEnergyTrajectory2D hab u₀ m t)
            (S.energyProjection m φ) *
              eta.value t ∂μ := by
      apply integral_congr_ae
      filter_upwards [S.zeroForcing_energyLp_eq_trajectory_ae hab u₀ m] with t ht
      rw [ht]
    _ = _ :=
      SmoothBoxVariationalGalerkinLevel.integral_intervalSubtypeMeasure hab
        (fun t =>
          boxGradientDiffusion I
            (S.zeroForcingEnergyTrajectory2D hab u₀ m t)
            (S.energyProjection m φ) *
              eta.value t)

/-- Convection integral expressed with the canonical energy `Lp`
representative. -/
theorem zeroForcing_energyLp_convection_time_integral_eq
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I)
    (m : ℕ) (φ : BoxH1ZeroSigma I) (eta : IntervalTimeTest a b) :
    (∫ t : Icc a b,
      (boxLadyzhenskayaRealization I).toBoxEnergyL4Realization.convectionForm I
        ((S.zeroForcingLeraySpectralCompactFamily2D hab u₀).energyLp m t)
        ((S.zeroForcingLeraySpectralCompactFamily2D hab u₀).energyLp m t)
        (S.energyProjection m φ) *
          eta.value t
      ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) =
      ∫ t in a..b,
        (boxLadyzhenskayaRealization I).toBoxEnergyL4Realization.convectionForm I
          (S.zeroForcingEnergyTrajectory2D hab u₀ m t)
          (S.zeroForcingEnergyTrajectory2D hab u₀ m t)
          (S.energyProjection m φ) *
            eta.value t := by
  let G := S.zeroForcingLeraySpectralCompactFamily2D hab u₀
  let μ := SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b
  calc
    (∫ t : Icc a b,
        (boxLadyzhenskayaRealization I).toBoxEnergyL4Realization.convectionForm I
          (G.energyLp m t) (G.energyLp m t)
          (S.energyProjection m φ) *
            eta.value t ∂μ) =
        ∫ t : Icc a b,
          (boxLadyzhenskayaRealization I).toBoxEnergyL4Realization.convectionForm I
            (S.zeroForcingEnergyTrajectory2D hab u₀ m t)
            (S.zeroForcingEnergyTrajectory2D hab u₀ m t)
            (S.energyProjection m φ) *
              eta.value t ∂μ := by
      apply integral_congr_ae
      filter_upwards [S.zeroForcing_energyLp_eq_trajectory_ae hab u₀ m] with t ht
      rw [ht]
    _ = _ :=
      SmoothBoxVariationalGalerkinLevel.integral_intervalSubtypeMeasure hab
        (fun t =>
          (boxLadyzhenskayaRealization I).toBoxEnergyL4Realization.convectionForm I
            (S.zeroForcingEnergyTrajectory2D hab u₀ m t)
            (S.zeroForcingEnergyTrajectory2D hab u₀ m t)
            (S.energyProjection m φ) *
              eta.value t)

/-- The finite physical equation written directly with the canonical `Lp`
representatives on the interval subtype. -/
theorem zeroForcing_timeTested_Lp_identity
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I)
    (m : ℕ) (φ : BoxH1ZeroSigma I)
    (eta : IntervalTimeTest a b)
    (heta_terminal : eta.value b = 0) :
    (let G := S.zeroForcingLeraySpectralCompactFamily2D hab u₀;
     let μ := SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b;
     -(∫ t : Icc a b,
        ⟪G.stateLp m t, boxEnergyToState I φ⟫_ℝ * eta.deriv t ∂μ) +
      (∫ t : Icc a b,
        boxGradientDiffusion I (G.energyLp m t)
          (S.energyProjection m φ) *
            eta.value t ∂μ) +
      (∫ t : Icc a b,
        (boxLadyzhenskayaRealization I).toBoxEnergyL4Realization.convectionForm I
          (G.energyLp m t) (G.energyLp m t)
          (S.energyProjection m φ) *
            eta.value t ∂μ) =
      ⟪S.stateSynthesis m (S.stateInitialCoefficient m u₀), boxEnergyToState I φ⟫_ℝ *
        eta.value a) := by
  let G := S.zeroForcingLeraySpectralCompactFamily2D hab u₀
  let μ := SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b
  have hstate := S.zeroForcing_stateLp_time_integral_eq hab u₀ m φ eta
  have hdiffusion :=
    S.zeroForcing_energyLp_diffusion_time_integral_eq hab u₀ m φ eta
  have hconvection :=
    S.zeroForcing_energyLp_convection_time_integral_eq hab u₀ m φ eta
  have hphysical :=
    S.zeroForcingSolution2D_timeTested_physical_identity
      hab u₀ m φ eta heta_terminal
  linarith only [hphysical, hstate, hdiffusion, hconvection]

/-- Strong state convergence passes the time-derivative term in the tested
equation. -/
theorem zeroForcing_stateDerivativeIntegral_tendsto
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I)
    (SW : (S.zeroForcingLeraySpectralCompactFamily2D hab u₀).StrongWeakSubsequence)
    (φ : BoxH1ZeroSigma I) (eta : LerayIntervalTimeTest a b) :
    Tendsto
      (fun k => ∫ t : Icc a b,
        ⟪(S.zeroForcingLeraySpectralCompactFamily2D hab u₀).stateLp
            (SW.subseq.idx k) t,
          boxEnergyToState I φ⟫_ℝ * eta.deriv t
        ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)
      atTop
      (nhds (∫ t : Icc a b,
        ⟪SW.stateLimit t, boxEnergyToState I φ⟫_ℝ * eta.deriv t
        ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)) := by
  let μ := SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b
  let A : BoxL2Sigma I →L[ℝ] BoxL2Sigma I →L[ℝ] ℝ :=
    (isBoundedBilinearMap_inner (𝕜 := ℝ)).toContinuousLinearMap
  let psi : Lp (BoxL2Sigma I) (2 : ℝ≥0∞) μ :=
    eta.derivVectorLp (BoxL2Sigma I) (boxEnergyToState I φ)
  have heq (w : Lp (BoxL2Sigma I) (2 : ℝ≥0∞) μ) :
      (∫ t, A (w t) (psi t) ∂μ) =
        ∫ t : Icc a b,
          ⟪w t, boxEnergyToState I φ⟫_ℝ * eta.deriv t ∂μ := by
    apply integral_congr_ae
    filter_upwards [eta.derivVectorLp_apply_ae
      (BoxL2Sigma I) (boxEnergyToState I φ)] with t ht
    change ⟪w t, psi t⟫_ℝ = _
    rw [ht]
    exact (real_inner_smul_right
      (w t) (boxEnergyToState I φ) (eta.deriv t)).trans
        (mul_comm _ _)
  have hbase := SW.stateBilinearIntegral_tendsto A psi
  change Tendsto
    (fun k => ∫ t,
      A ((S.zeroForcingLeraySpectralCompactFamily2D hab u₀).stateLp
        (SW.subseq.idx k) t) (psi t) ∂μ)
    atTop (nhds (∫ t, A (SW.stateLimit t) (psi t) ∂μ)) at hbase
  have hseq :
      (fun k => ∫ t,
        A ((S.zeroForcingLeraySpectralCompactFamily2D hab u₀).stateLp
          (SW.subseq.idx k) t) (psi t) ∂μ) =
      (fun k => ∫ t : Icc a b,
        ⟪(S.zeroForcingLeraySpectralCompactFamily2D hab u₀).stateLp
            (SW.subseq.idx k) t,
          boxEnergyToState I φ⟫_ℝ * eta.deriv t ∂μ) := by
    funext k
    exact heq _
  rw [hseq, heq SW.stateLimit] at hbase
  exact hbase

/-- A scalar time cutoff may be placed in the second diffusion argument or
outside the scalar pairing. -/
theorem diffusion_valueLp_integral_eq
    {a b : ℝ} (eta : IntervalTimeTest a b)
    (w : Lp (BoxH1ZeroSigma I) (2 : ℝ≥0∞)
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b))
    (x : BoxH1ZeroSigma I) :
    (∫ t,
      boxGradientDiffusion I (w t)
        ((eta.valueLpCLM (BoxH1ZeroSigma I) 2 x) t)
      ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) =
      ∫ t : Icc a b,
        boxGradientDiffusion I (w t) x * eta.value t
        ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b := by
  apply integral_congr_ae
  filter_upwards [eta.valueLpCLM_apply_ae
    (BoxH1ZeroSigma I) 2 x] with t ht
  calc
    boxGradientDiffusion I (w t)
        ((eta.valueLpCLM (BoxH1ZeroSigma I) 2 x) t) =
        boxGradientDiffusion I (w t) (eta.value t • x) :=
      congrArg (boxGradientDiffusion I (w t)) ht
    _ = eta.value t • boxGradientDiffusion I (w t) x :=
      map_smul (boxGradientDiffusion I (w t)) (eta.value t) x
    _ = boxGradientDiffusion I (w t) x * eta.value t := by
      change eta.value t * boxGradientDiffusion I (w t) x = _
      exact mul_comm _ _

/-- Weak energy convergence and strong convergence of the spectral test
projection pass the diffusion term in the tested equation. -/
theorem zeroForcing_diffusionIntegral_tendsto
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I)
    (SW : (S.zeroForcingLeraySpectralCompactFamily2D hab u₀).StrongWeakSubsequence)
    (φ : BoxH1ZeroSigma I) (eta : LerayIntervalTimeTest a b) :
    Tendsto
      (fun k => ∫ t : Icc a b,
        boxGradientDiffusion I
          ((S.zeroForcingLeraySpectralCompactFamily2D hab u₀).energyLp
            (SW.subseq.idx k) t)
          (S.energyProjection (SW.subseq.idx k) φ) * eta.value t
        ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)
      atTop
      (nhds (∫ t : Icc a b,
        boxGradientDiffusion I (SW.energyLimit t) φ * eta.value t
        ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)) := by
  letI : CompleteSpace (BoxH1ZeroSigma I) :=
    boxH1ZeroSigma_completeSpace I
  let μ := SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b
  let testCLM : BoxH1ZeroSigma I →L[ℝ]
      Lp (BoxH1ZeroSigma I) (2 : ℝ≥0∞) μ :=
    eta.toIntervalTimeTest.valueLpCLM (BoxH1ZeroSigma I) 2
  let psi : ℕ → Lp (BoxH1ZeroSigma I) (2 : ℝ≥0∞) μ := fun k =>
    testCLM (S.energyProjection (SW.subseq.idx k) φ)
  let psiLimit : Lp (BoxH1ZeroSigma I) (2 : ℝ≥0∞) μ := testCLM φ
  have hproj : Tendsto
      (fun k => S.energyProjection (SW.subseq.idx k) φ) atTop (nhds φ) :=
    (GalerkinProjectorSequence.finitePartialProjection_tendsto
      S.energyBasis S.exhaustion φ).comp
      SW.subseq.strictMono_idx.tendsto_atTop
  have hpsi : Tendsto psi atTop (nhds psiLimit) := by
    exact (testCLM.continuous.tendsto φ).comp hproj
  have heq (w : Lp (BoxH1ZeroSigma I) (2 : ℝ≥0∞) μ)
      (x : BoxH1ZeroSigma I) :
      (∫ t, boxGradientDiffusion I (w t) ((testCLM x) t) ∂μ) =
        ∫ t : Icc a b,
          boxGradientDiffusion I (w t) x * eta.value t ∂μ := by
    exact diffusion_valueLp_integral_eq eta.toIntervalTimeTest w x
  have hbase :=
    @LeraySpectralCompactFamily.StrongWeakSubsequence.energyBilinearIntegral_tendsto_of_test_tendsto
      (Icc a b) (BoxH1ZeroSigma I) (BoxL2Sigma I)
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance (boxH1ZeroSigma_completeSpace I)
      inferInstance inferInstance μ inferInstance _ SW
      (boxGradientDiffusion I) psi psiLimit hpsi
  change Tendsto
    (fun k => ∫ t,
      boxGradientDiffusion I
        ((S.zeroForcingLeraySpectralCompactFamily2D hab u₀).energyLp
          (SW.subseq.idx k) t) (psi k t) ∂μ)
    atTop
    (nhds (∫ t, boxGradientDiffusion I (SW.energyLimit t)
      (psiLimit t) ∂μ)) at hbase
  have hseq :
      (fun k => ∫ t,
        boxGradientDiffusion I
          ((S.zeroForcingLeraySpectralCompactFamily2D hab u₀).energyLp
            (SW.subseq.idx k) t) (psi k t) ∂μ) =
      (fun k => ∫ t : Icc a b,
        boxGradientDiffusion I
          ((S.zeroForcingLeraySpectralCompactFamily2D hab u₀).energyLp
            (SW.subseq.idx k) t)
          (S.energyProjection (SW.subseq.idx k) φ) * eta.value t ∂μ) := by
    funext k
    exact heq _ _
  rw [hseq, heq SW.energyLimit φ] at hbase
  exact hbase

/-- The reconstructed spectral initial states pass to the prescribed initial
datum in every fixed energy test pairing. -/
theorem zeroForcing_initialPairing_tendsto
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I)
    (SW : (S.zeroForcingLeraySpectralCompactFamily2D hab u₀).StrongWeakSubsequence)
    (φ : BoxH1ZeroSigma I) (eta : IntervalTimeTest a b) :
    Tendsto
      (fun k =>
        ⟪S.stateSynthesis (SW.subseq.idx k)
            (S.stateInitialCoefficient (SW.subseq.idx k) u₀),
          boxEnergyToState I φ⟫_ℝ * eta.value a)
      atTop
      (nhds (⟪u₀, boxEnergyToState I φ⟫_ℝ * eta.value a)) := by
  have hinitial : Tendsto
      (fun k => S.stateSynthesis (SW.subseq.idx k)
        (S.stateInitialCoefficient (SW.subseq.idx k) u₀))
      atTop (nhds u₀) :=
    (S.stateInitialCoefficient_tendsto u₀).comp
      SW.subseq.strictMono_idx.tendsto_atTop
  have hinner :=
    ((innerSLFlip ℝ (boxEnergyToState I φ)).continuous.tendsto u₀).comp hinitial
  exact hinner.mul tendsto_const_nhds

/-- Skew symmetry places the spatial test in the gradient slot, while a
scalar time cutoff is absorbed into that gradient test. -/
theorem convection_mul_eq_neg_tested
    (L : BoxLadyzhenskayaRealization I)
    (u φ : BoxH1ZeroSigma I) (c : ℝ) :
    L.toBoxEnergyL4Realization.convectionForm I u u φ * c =
      -boxLpConvectionTested
        (L.toLp4 u) (L.toLp4 u) (c • boxEnergyGradient I φ) := by
  have hskew := BoxEnergyL4Realization.convectionForm_skew I
    L.toBoxEnergyL4Realization u u φ
  have hscale :
      boxLpConvection I (L.toLp4 u) (c • boxEnergyGradient I φ) (L.toLp4 u) =
        c * boxLpConvection I (L.toLp4 u) (boxEnergyGradient I φ) (L.toLp4 u) := by
    rw [map_smul]
    rfl
  calc
    L.toBoxEnergyL4Realization.convectionForm I u u φ * c =
        (-L.toBoxEnergyL4Realization.convectionForm I u φ u) * c :=
      congrArg (fun r : ℝ => r * c) hskew
    _ =
        (-boxLpConvection I (L.toLp4 u) (boxEnergyGradient I φ) (L.toLp4 u)) * c := by
      rw [BoxEnergyL4Realization.convectionForm_apply]
    _ =
        -boxLpConvection I (L.toLp4 u)
          (c • boxEnergyGradient I φ) (L.toLp4 u) := by
      rw [hscale]
      ring
    _ =
        -boxLpConvectionTested
          (L.toLp4 u) (L.toLp4 u) (c • boxEnergyGradient I φ) := rfl

/-- A bounded gradient test obtained by multiplying a fixed spatial gradient
by a scalar interval cutoff. -/
noncomputable def boxGradientCutoffCLM
    {a b : ℝ} (eta : IntervalTimeTest a b) :
    BoxH1ZeroSigma I →L[ℝ]
      Lp (BoxGradientL2 I) (∞ : ℝ≥0∞)
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) :=
  (eta.valueLpCLM (BoxGradientL2 I) ∞).comp (boxEnergyGradient I)

/-- Evaluation of the continuous cutoff-gradient map. -/
noncomputable def boxGradientCutoffLp
    {a b : ℝ} (eta : IntervalTimeTest a b) (φ : BoxH1ZeroSigma I) :
    Lp (BoxGradientL2 I) (∞ : ℝ≥0∞)
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) :=
  boxGradientCutoffCLM eta φ

/-- Almost-everywhere value of the bounded gradient test. -/
theorem boxGradientCutoffLp_apply_ae
    {a b : ℝ} (eta : IntervalTimeTest a b) (φ : BoxH1ZeroSigma I) :
    boxGradientCutoffLp eta φ =ᵐ[
      SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b]
        fun t => eta.value t • boxEnergyGradient I φ :=
  eta.valueLpCLM_apply_ae (BoxGradientL2 I) ∞ (boxEnergyGradient I φ)

/-- The quadratic `L4-L2-L4` convection integrand. -/
noncomputable def boxQuadraticConvectionIntegrand
    {Time : Type*} [MeasurableSpace Time] {μ : Measure Time}
    (u : Lp (BoxVelocityL4 I) (2 : ℝ≥0∞) μ)
    (psi : Lp (BoxGradientL2 I) (∞ : ℝ≥0∞) μ) : Time → ℝ :=
  fun t => boxLpConvectionTested (u t) (u t) (psi t)

/-- The quadratic `L4-L2-L4` convection integral. -/
noncomputable def boxQuadraticConvectionIntegral
    {Time : Type*} [MeasurableSpace Time] {μ : Measure Time}
    (u : Lp (BoxVelocityL4 I) (2 : ℝ≥0∞) μ)
    (psi : Lp (BoxGradientL2 I) (∞ : ℝ≥0∞) μ) : ℝ :=
  ∫ t, boxQuadraticConvectionIntegrand u psi t ∂μ

/-- The physical convection integrand before the skew conversion. -/
noncomputable def boxPhysicalConvectionIntegrand
    {a b : ℝ} (eta : IntervalTimeTest a b)
    (L : BoxLadyzhenskayaRealization I)
    (w : Lp (BoxH1ZeroSigma I) (2 : ℝ≥0∞)
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b))
    (φ : BoxH1ZeroSigma I) : Icc a b → ℝ :=
  fun t =>
    L.toBoxEnergyL4Realization.convectionForm I (w t) (w t) φ * eta.value t

/-- The physical convection integral in the time-tested weak equation. -/
noncomputable def boxPhysicalConvectionIntegral
    {a b : ℝ} (eta : IntervalTimeTest a b)
    (L : BoxLadyzhenskayaRealization I)
    (w : Lp (BoxH1ZeroSigma I) (2 : ℝ≥0∞)
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b))
    (φ : BoxH1ZeroSigma I) : ℝ :=
  ∫ t, boxPhysicalConvectionIntegrand eta L w φ t
    ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b

set_option maxHeartbeats 6000000 in
/-- Almost-everywhere form of the skew conversion for canonical `Lp`
representatives. -/
theorem convection_valueLp_integrand_ae
    {a b : ℝ} (eta : IntervalTimeTest a b)
    (L : BoxLadyzhenskayaRealization I)
    (w : Lp (BoxH1ZeroSigma I) (2 : ℝ≥0∞)
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b))
    (φ : BoxH1ZeroSigma I) :
    boxPhysicalConvectionIntegrand eta L w φ
      =ᵐ[SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b]
      -boxQuadraticConvectionIntegrand
        (boxLadyzhenskayaTimeMap L w) (boxGradientCutoffLp eta φ) := by
  filter_upwards [L.toLp4.coeFn_compLpL w,
    boxGradientCutoffLp_apply_ae eta φ] with t hL htest
  change
    L.toBoxEnergyL4Realization.convectionForm I (w t) (w t) φ * eta.value t =
      -boxLpConvectionTested
        ((boxLadyzhenskayaTimeMap L w) t)
        ((boxLadyzhenskayaTimeMap L w) t)
        ((boxGradientCutoffLp eta φ) t)
  change boxLadyzhenskayaTimeMap L w t = L.toLp4 (w t) at hL
  rw [hL, htest]
  exact convection_mul_eq_neg_tested L (w t) φ (eta.value t)

/-- Space-time form of the skew conversion used by the quadratic compactness
theorem. -/
theorem convection_valueLp_integral_eq
    {a b : ℝ} (eta : IntervalTimeTest a b)
    (L : BoxLadyzhenskayaRealization I)
    (w : Lp (BoxH1ZeroSigma I) (2 : ℝ≥0∞)
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b))
    (φ : BoxH1ZeroSigma I) :
    boxPhysicalConvectionIntegral eta L w φ =
      -boxQuadraticConvectionIntegral
        (boxLadyzhenskayaTimeMap L w) (boxGradientCutoffLp eta φ) := by
  change
    (∫ t, boxPhysicalConvectionIntegrand eta L w φ t
      ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) =
      -(∫ t, boxQuadraticConvectionIntegrand
        (boxLadyzhenskayaTimeMap L w) (boxGradientCutoffLp eta φ) t
        ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)
  calc
    (∫ t, boxPhysicalConvectionIntegrand eta L w φ t
        ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) =
        ∫ t, (-boxQuadraticConvectionIntegrand
          (boxLadyzhenskayaTimeMap L w) (boxGradientCutoffLp eta φ)) t
          ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b :=
      integral_congr_ae (convection_valueLp_integrand_ae eta L w φ)
    _ = _ := integral_neg _

set_option maxHeartbeats 8000000 in
/-- Ladyzhenskaya compactness and the projective tensor pairing pass the
quadratic `L4-L2-L4` integral with its converging projected gradient test. -/
theorem zeroForcing_quadraticConvectionIntegral_tendsto
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I)
    (SW : (S.zeroForcingLeraySpectralCompactFamily2D hab u₀).StrongWeakSubsequence)
    (φ : BoxH1ZeroSigma I) (eta : LerayIntervalTimeTest a b) :
    Tendsto
      (fun k => boxQuadraticConvectionIntegral
        (boxLadyzhenskayaTimeMap (boxLadyzhenskayaRealization I)
          ((S.zeroForcingLeraySpectralCompactFamily2D hab u₀).energyLp
            (SW.subseq.idx k)))
        (boxGradientCutoffLp eta.toIntervalTimeTest
          (S.energyProjection (SW.subseq.idx k) φ)))
      atTop
      (nhds (boxQuadraticConvectionIntegral
        (boxLadyzhenskayaTimeMap (boxLadyzhenskayaRealization I) SW.energyLimit)
        (boxGradientCutoffLp eta.toIntervalTimeTest φ))) := by
  letI : CompleteSpace (BoxH1ZeroSigma I) :=
    boxH1ZeroSigma_completeSpace I
  letI : CompleteSpace (BoxL2Sigma I) := boxL2Sigma_completeSpace I
  let G := S.zeroForcingLeraySpectralCompactFamily2D hab u₀
  let μ := SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b
  let L := boxLadyzhenskayaRealization I
  let L4S := SW.toInterpolatedStrongMetricSubsequence
    L.toLp4 L.constant L.constant_nonneg
      (S.zeroForcingLeraySpectralCompactFamily2D_ladyzhenskaya_pointwise
        hab u₀ L)
  let psi : ℕ → Lp (BoxGradientL2 I) (∞ : ℝ≥0∞) μ := fun k =>
    boxGradientCutoffLp eta.toIntervalTimeTest
      (S.energyProjection (SW.subseq.idx k) φ)
  let psiLimit : Lp (BoxGradientL2 I) (∞ : ℝ≥0∞) μ :=
    boxGradientCutoffLp eta.toIntervalTimeTest φ
  have hproj : Tendsto
      (fun k => S.energyProjection (SW.subseq.idx k) φ) atTop (nhds φ) :=
    (GalerkinProjectorSequence.finitePartialProjection_tendsto
      S.energyBasis S.exhaustion φ).comp
      SW.subseq.strictMono_idx.tendsto_atTop
  have hpsi : Tendsto psi atTop (nhds psiLimit) := by
    let testCLM : BoxH1ZeroSigma I →L[ℝ]
        Lp (BoxGradientL2 I) (∞ : ℝ≥0∞) μ :=
      boxGradientCutoffCLM (I := I) eta.toIntervalTimeTest
    exact (testCLM.continuous.tendsto φ).comp hproj
  have hbase := L4S.projectiveTrilinearIntegral_tendsto_of_test_tendsto
    (boxLpConvectionTested (I := I)) psi psiLimit hpsi
  change Tendsto
    (fun k => boxQuadraticConvectionIntegral
      (boxLadyzhenskayaTimeMap L (G.energyLp (SW.subseq.idx k))) (psi k))
    atTop
    (nhds (boxQuadraticConvectionIntegral
      (boxLadyzhenskayaTimeMap L SW.energyLimit) psiLimit)) at hbase
  exact hbase

set_option maxHeartbeats 4000000 in
/-- The quadratic convergence theorem, converted by skew symmetry to the
named physical convection integral. -/
theorem zeroForcing_physicalConvectionIntegral_tendsto
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I)
    (SW : (S.zeroForcingLeraySpectralCompactFamily2D hab u₀).StrongWeakSubsequence)
    (φ : BoxH1ZeroSigma I) (eta : LerayIntervalTimeTest a b) :
    Tendsto
      (fun k => boxPhysicalConvectionIntegral eta.toIntervalTimeTest
        (boxLadyzhenskayaRealization I)
        ((S.zeroForcingLeraySpectralCompactFamily2D hab u₀).energyLp
          (SW.subseq.idx k))
        (S.energyProjection (SW.subseq.idx k) φ))
      atTop
      (nhds (boxPhysicalConvectionIntegral eta.toIntervalTimeTest
        (boxLadyzhenskayaRealization I) SW.energyLimit φ)) := by
  have hquad := S.zeroForcing_quadraticConvectionIntegral_tendsto
    hab u₀ SW φ eta
  simpa only [convection_valueLp_integral_eq] using hquad.neg

set_option maxHeartbeats 4000000 in
/-- Expanded physical form of convection convergence used in the limiting
Galerkin identity. -/
theorem zeroForcing_convectionIntegral_tendsto
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I)
    (SW : (S.zeroForcingLeraySpectralCompactFamily2D hab u₀).StrongWeakSubsequence)
    (φ : BoxH1ZeroSigma I) (eta : LerayIntervalTimeTest a b) :
    Tendsto
      (fun k => ∫ t : Icc a b,
        (boxLadyzhenskayaRealization I).toBoxEnergyL4Realization.convectionForm I
          ((S.zeroForcingLeraySpectralCompactFamily2D hab u₀).energyLp
            (SW.subseq.idx k) t)
          ((S.zeroForcingLeraySpectralCompactFamily2D hab u₀).energyLp
            (SW.subseq.idx k) t)
          (S.energyProjection (SW.subseq.idx k) φ) * eta.value t
        ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)
      atTop
      (nhds (∫ t : Icc a b,
        (boxLadyzhenskayaRealization I).toBoxEnergyL4Realization.convectionForm I
          (SW.energyLimit t) (SW.energyLimit t) φ * eta.value t
        ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)) := by
  simpa only [boxPhysicalConvectionIntegral, boxPhysicalConvectionIntegrand] using
    S.zeroForcing_physicalConvectionIntegral_tendsto hab u₀ SW φ eta

set_option maxHeartbeats 5000000 in
/-- The simultaneous strong/weak limit satisfies the unforced box equation
against every spatial energy test and terminally vanishing Leray time test. -/
theorem zeroForcing_limit_timeTested_identity
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I)
    (SW : (S.zeroForcingLeraySpectralCompactFamily2D hab u₀).StrongWeakSubsequence)
    (φ : BoxH1ZeroSigma I) (eta : LerayIntervalTimeTest a b)
    (heta_terminal : eta.value b = 0) :
    -(∫ t : Icc a b,
        ⟪SW.stateLimit t, boxEnergyToState I φ⟫_ℝ * eta.deriv t
        ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) +
      (∫ t : Icc a b,
        boxGradientDiffusion I (SW.energyLimit t) φ * eta.value t
        ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) +
      (∫ t : Icc a b,
        (boxLadyzhenskayaRealization I).toBoxEnergyL4Realization.convectionForm I
          (SW.energyLimit t) (SW.energyLimit t) φ * eta.value t
        ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) =
      ⟪u₀, boxEnergyToState I φ⟫_ℝ * eta.value a := by
  let G := S.zeroForcingLeraySpectralCompactFamily2D hab u₀
  let μ := SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b
  let lhsSeq : ℕ → ℝ := fun k =>
    -(∫ t : Icc a b,
        ⟪G.stateLp (SW.subseq.idx k) t, boxEnergyToState I φ⟫_ℝ * eta.deriv t
        ∂μ) +
      (∫ t : Icc a b,
        boxGradientDiffusion I (G.energyLp (SW.subseq.idx k) t)
          (S.energyProjection (SW.subseq.idx k) φ) * eta.value t ∂μ) +
      (∫ t : Icc a b,
        (boxLadyzhenskayaRealization I).toBoxEnergyL4Realization.convectionForm I
          (G.energyLp (SW.subseq.idx k) t)
          (G.energyLp (SW.subseq.idx k) t)
          (S.energyProjection (SW.subseq.idx k) φ) * eta.value t ∂μ)
  let lhsLimit : ℝ :=
    -(∫ t : Icc a b,
        ⟪SW.stateLimit t, boxEnergyToState I φ⟫_ℝ * eta.deriv t ∂μ) +
      (∫ t : Icc a b,
        boxGradientDiffusion I (SW.energyLimit t) φ * eta.value t ∂μ) +
      (∫ t : Icc a b,
        (boxLadyzhenskayaRealization I).toBoxEnergyL4Realization.convectionForm I
          (SW.energyLimit t) (SW.energyLimit t) φ * eta.value t ∂μ)
  let rhsSeq : ℕ → ℝ := fun k =>
    ⟪S.stateSynthesis (SW.subseq.idx k)
        (S.stateInitialCoefficient (SW.subseq.idx k) u₀),
      boxEnergyToState I φ⟫_ℝ * eta.value a
  let rhsLimit : ℝ := ⟪u₀, boxEnergyToState I φ⟫_ℝ * eta.value a
  have hstate := S.zeroForcing_stateDerivativeIntegral_tendsto hab u₀ SW φ eta
  have hdiffusion := S.zeroForcing_diffusionIntegral_tendsto hab u₀ SW φ eta
  have hconvection := S.zeroForcing_convectionIntegral_tendsto hab u₀ SW φ eta
  have hleft : Tendsto lhsSeq atTop (nhds lhsLimit) := by
    dsimp only [lhsSeq, lhsLimit, G, μ]
    exact (hstate.neg.add hdiffusion).add hconvection
  have hright : Tendsto rhsSeq atTop (nhds rhsLimit) := by
    dsimp only [rhsSeq, rhsLimit]
    exact S.zeroForcing_initialPairing_tendsto
      hab u₀ SW φ eta.toIntervalTimeTest
  have hfinite (k : ℕ) : lhsSeq k = rhsSeq k := by
    dsimp only [lhsSeq, rhsSeq, G, μ]
    exact S.zeroForcing_timeTested_Lp_identity hab u₀
      (SW.subseq.idx k) φ eta.toIntervalTimeTest heta_terminal
  have hseq : lhsSeq = rhsSeq := funext hfinite
  have hleft' : Tendsto rhsSeq atTop (nhds lhsLimit) := by
    rw [← hseq]
    exact hleft
  have hlimit : lhsLimit = rhsLimit := tendsto_nhds_unique hleft' hright
  simpa only [lhsLimit, rhsLimit, μ] using hlimit

/-- Restricting the interval-subtype measure to times at most `t` recovers
the interval integral from the left endpoint to `t`. -/
theorem integral_Iic_intervalSubtypeMeasure
    {a b : ℝ} (hab : a ≤ b) (t : Icc a b) (f : ℝ → ℝ) :
    ∫ s : Icc a b in Set.Iic t, f s
        ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b =
      ∫ s in a..(t : ℝ), f s := by
  rw [← MeasureTheory.integral_indicator measurableSet_Iic]
  calc
    ∫ s : Icc a b,
        (Set.Iic t).indicator (fun r => f r) s
        ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b =
        ∫ s : Icc a b,
          ({r : ℝ | r ≤ (t : ℝ)}).indicator f s
          ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b := by
      apply integral_congr_ae
      filter_upwards with s
      by_cases hs : s ≤ t
      · have hs' : (s : ℝ) ≤ (t : ℝ) := hs
        rw [Set.indicator_of_mem (show s ∈ Set.Iic t from hs),
          Set.indicator_of_mem
            (show (s : ℝ) ∈ {r : ℝ | r ≤ (t : ℝ)} from hs')]
      · have hs' : ¬(s : ℝ) ≤ (t : ℝ) := by simpa using hs
        rw [Set.indicator_of_notMem (show s ∉ Set.Iic t from hs),
          Set.indicator_of_notMem
            (show (s : ℝ) ∉ {r : ℝ | r ≤ (t : ℝ)} from hs')]
    _ = ∫ s in a..b, ({r : ℝ | r ≤ (t : ℝ)}).indicator f s :=
      SmoothBoxVariationalGalerkinLevel.integral_intervalSubtypeMeasure hab _
    _ = ∫ s in a..(t : ℝ), f s :=
      intervalIntegral.integral_indicator t.property

/-- Squaring the `L2`-product norm of `(x, sqrt 2 • y)` gives the weighted
sum used in the energy inequality. -/
theorem norm_sqrtTwo_prodL2_sq
    {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (x : E) (y : F) :
    ‖WithLp.toLp 2 (x, Real.sqrt 2 • y)‖ ^ 2 =
      ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd, norm_smul, mul_pow]
  have hsqrt : ‖Real.sqrt 2‖ ^ 2 = 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2),
      Real.sq_sqrt (by norm_num)]
  rw [hsqrt]

/-- Space-time gradient followed by restriction to the initial time segment
ending at `t`. -/
noncomputable def restrictedGradientTimeMap
    {a b : ℝ} (t : Icc a b) :
    Lp (BoxH1ZeroSigma I) (2 : ℝ≥0∞)
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) →L[ℝ]
      Lp (BoxGradientL2 I) (2 : ℝ≥0∞)
        ((SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b).restrict
          (Set.Iic t)) :=
  (MeasureTheory.LpToLpRestrictCLM
      (Icc a b) (BoxGradientL2 I) ℝ
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)
      (2 : ℝ≥0∞) (Set.Iic t)).comp
    ((boxEnergyGradient I).compLpL 2
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b))

/-- The restricted gradient map is represented pointwise by the spatial
energy gradient. -/
theorem restrictedGradientTimeMap_ae
    {a b : ℝ} (t : Icc a b)
    (w : Lp (BoxH1ZeroSigma I) (2 : ℝ≥0∞)
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)) :
    restrictedGradientTimeMap (I := I) t w =ᵐ[
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b).restrict
          (Set.Iic t)]
      fun s => boxEnergyGradient I (w s) := by
  let μ := SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b
  filter_upwards [
    MeasureTheory.LpToLpRestrictCLM_coeFn ℝ (Set.Iic t)
      ((boxEnergyGradient I).compLpL 2 μ w),
    ae_restrict_of_ae ((boxEnergyGradient I).coeFn_compLpL w)] with s hs hgrad
  simpa only [restrictedGradientTimeMap,
    ContinuousLinearMap.comp_apply] using hs.trans hgrad

/-- The squared norm of the restricted gradient is its dissipation integral
over the initial time segment. -/
theorem restrictedGradientTimeMap_norm_sq_eq_setIntegral
    {a b : ℝ} (t : Icc a b)
    (w : Lp (BoxH1ZeroSigma I) (2 : ℝ≥0∞)
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)) :
    ‖restrictedGradientTimeMap (I := I) t w‖ ^ 2 =
      ∫ s : Icc a b in Set.Iic t,
        ‖boxEnergyGradient I (w s)‖ ^ 2
        ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b := by
  let μ := SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b
  let gradLp := restrictedGradientTimeMap (I := I) t w
  calc
    ‖restrictedGradientTimeMap (I := I) t w‖ ^ 2 =
        ∫ s, ‖gradLp s‖ ^ 2 ∂(μ.restrict (Set.Iic t)) := by
      simpa only [gradLp] using Lp.norm_two_sq_eq_integral_norm_sq gradLp
    _ = ∫ s : Icc a b in Set.Iic t,
        ‖boxEnergyGradient I (w s)‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [restrictedGradientTimeMap_ae (I := I) t w] with s hs
      rw [hs]

/-- At one finite spectral level, the restricted gradient norm is the
ordinary accumulated gradient integral from `a` to `t`. -/
theorem zeroForcing_restrictedGradientTimeMap_norm_sq
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I)
    (m : ℕ) (t : Icc a b) :
    ‖restrictedGradientTimeMap (I := I) t
        ((S.zeroForcingLeraySpectralCompactFamily2D hab u₀).energyLp m)‖ ^ 2 =
      ∫ s in a..(t : ℝ),
        ‖boxEnergyGradient I
          (S.zeroForcingEnergyTrajectory2D hab u₀ m s)‖ ^ 2 := by
  let G := S.zeroForcingLeraySpectralCompactFamily2D hab u₀
  let μ := SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b
  let gradLp := restrictedGradientTimeMap (I := I) t (G.energyLp m)
  have hgradAe : gradLp =ᵐ[μ.restrict (Set.Iic t)] fun s =>
      boxEnergyGradient I
        (S.zeroForcingEnergyTrajectory2D hab u₀ m s) := by
    filter_upwards [restrictedGradientTimeMap_ae (I := I) t (G.energyLp m),
      ae_restrict_of_ae
        (S.zeroForcing_energyLp_eq_trajectory_ae hab u₀ m)] with s hgrad henergy
    rw [hgrad, henergy]
  calc
    ‖restrictedGradientTimeMap (I := I) t (G.energyLp m)‖ ^ 2 =
        ∫ s, ‖gradLp s‖ ^ 2 ∂(μ.restrict (Set.Iic t)) := by
      simpa only [gradLp] using Lp.norm_two_sq_eq_integral_norm_sq gradLp
    _ = ∫ s : Icc a b in Set.Iic t,
        ‖boxEnergyGradient I
          (S.zeroForcingEnergyTrajectory2D hab u₀ m s)‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hgradAe] with s hs
      rw [hs]
    _ = ∫ s in a..(t : ℝ),
        ‖boxEnergyGradient I
          (S.zeroForcingEnergyTrajectory2D hab u₀ m s)‖ ^ 2 := by
      simpa only [μ] using integral_Iic_intervalSubtypeMeasure hab t
        (fun s => ‖boxEnergyGradient I
          (S.zeroForcingEnergyTrajectory2D hab u₀ m s)‖ ^ 2)

set_option maxHeartbeats 500000 in
/-- Diffusion energy of a finite unforced trajectory is integrable on every
initial subinterval. -/
theorem zeroForcing_diffusion_intervalIntegrable
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I)
    (m : ℕ) (t : Icc a b) :
    IntervalIntegrable
      (fun s => (S.zeroForcingProblem2D m u₀).system.diffusion
        (S.zeroForcingCoefficientTrajectory2D hab u₀ m s)
        (S.zeroForcingCoefficientTrajectory2D hab u₀ m s)) volume a (t : ℝ) := by
  simpa only [zeroForcingCoefficientTrajectory2D, canonicalSolutionToFun] using
    @VariationalGalerkinProblem.LocalSolutionOn.diffusion_intervalIntegrable
      (S.CoefficientSpace m)
      (S.coefficientSpaceNormedAddCommGroup m)
      (S.coefficientSpaceInnerProductSpace m)
      (S.coefficientSpaceCompleteSpace m)
      (S.zeroForcingProblem2D m u₀) a b
      (⟨a, le_rfl, hab⟩ : Icc a b)
      (S.zeroForcingSolution2D hab m u₀)
      a (t : ℝ) (⟨le_rfl, hab⟩ : a ∈ Icc a b) t.property t.property.1

set_option maxHeartbeats 500000 in
/-- Forcing work of a finite unforced trajectory is integrable on every
initial subinterval. -/
theorem zeroForcing_forcing_intervalIntegrable
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I)
    (m : ℕ) (t : Icc a b) :
    IntervalIntegrable
      (fun s => (S.zeroForcingProblem2D m u₀).forcing s
        (S.zeroForcingCoefficientTrajectory2D hab u₀ m s)) volume a (t : ℝ) := by
  simpa only [zeroForcingCoefficientTrajectory2D, canonicalSolutionToFun] using
    @VariationalGalerkinProblem.LocalSolutionOn.forcing_intervalIntegrable
      (S.CoefficientSpace m)
      (S.coefficientSpaceNormedAddCommGroup m)
      (S.coefficientSpaceInnerProductSpace m)
      (S.coefficientSpaceCompleteSpace m)
      (S.zeroForcingProblem2D m u₀) a b
      (⟨a, le_rfl, hab⟩ : Icc a b)
      (S.zeroForcingSolution2D hab m u₀)
      (S.zeroForcingProblem2D_forcing_continuous m u₀)
      a (t : ℝ) (⟨le_rfl, hab⟩ : a ∈ Icc a b) t.property t.property.1

set_option maxHeartbeats 1000000 in
/-- Exact coefficient-space energy balance on every initial subinterval. -/
theorem zeroForcing_coefficient_energy_balance
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I)
    (m : ℕ) (t : Icc a b) :
    ‖S.zeroForcingCoefficientTrajectory2D hab u₀ m t‖ ^ 2 +
        2 * ∫ s in a..(t : ℝ),
          (S.zeroForcingProblem2D m u₀).system.diffusion
            (S.zeroForcingCoefficientTrajectory2D hab u₀ m s)
            (S.zeroForcingCoefficientTrajectory2D hab u₀ m s) =
      ‖S.zeroForcingCoefficientTrajectory2D hab u₀ m a‖ ^ 2 +
        2 * ∫ s in a..(t : ℝ),
          (S.zeroForcingProblem2D m u₀).forcing s
            (S.zeroForcingCoefficientTrajectory2D hab u₀ m s) := by
  simpa only [zeroForcingCoefficientTrajectory2D, canonicalSolutionToFun] using
    @VariationalGalerkinProblem.LocalSolutionOn.energyIdentityOn
      (S.CoefficientSpace m)
      (S.coefficientSpaceNormedAddCommGroup m)
      (S.coefficientSpaceInnerProductSpace m)
      (S.coefficientSpaceCompleteSpace m)
      (S.zeroForcingProblem2D m u₀) a b
      (⟨a, le_rfl, hab⟩ : Icc a b)
      (S.zeroForcingSolution2D hab m u₀)
      a (t : ℝ) (⟨le_rfl, hab⟩ : a ∈ Icc a b) t.property t.property.1
      (S.zeroForcing_diffusion_intervalIntegrable hab u₀ m t)
      (S.zeroForcing_forcing_intervalIntegrable hab u₀ m t)

set_option maxHeartbeats 500000 in
/-- The unforced coefficient energy balance has no work term. -/
theorem zeroForcing_coefficient_energy_identity
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I)
    (m : ℕ) (t : Icc a b) :
    ‖S.zeroForcingCoefficientTrajectory2D hab u₀ m t‖ ^ 2 +
        2 * ∫ s in a..(t : ℝ),
          (S.zeroForcingProblem2D m u₀).system.diffusion
            (S.zeroForcingCoefficientTrajectory2D hab u₀ m s)
            (S.zeroForcingCoefficientTrajectory2D hab u₀ m s) =
      ‖S.stateInitialCoefficient m u₀‖ ^ 2 := by
  have hEnergy := S.zeroForcing_coefficient_energy_balance hab u₀ m t
  have huInitial := S.canonicalSolution_initial m hab
    (S.zeroForcingSolution2D hab m u₀)
  have huInitial' :
      S.zeroForcingCoefficientTrajectory2D hab u₀ m a =
        S.stateInitialCoefficient m u₀ := by
    simpa only [zeroForcingCoefficientTrajectory2D] using huInitial
  have huInitialSq := congrArg
    (fun x : S.CoefficientSpace m => ‖x‖ ^ 2) huInitial'
  calc
    _ = ‖S.zeroForcingCoefficientTrajectory2D hab u₀ m a‖ ^ 2 +
          2 * ∫ s in a..(t : ℝ),
            (S.zeroForcingProblem2D m u₀).forcing s
              (S.zeroForcingCoefficientTrajectory2D hab u₀ m s) := hEnergy
    _ = ‖S.stateInitialCoefficient m u₀‖ ^ 2 +
          2 * ∫ s in a..(t : ℝ),
            (S.zeroForcingProblem2D m u₀).forcing s
              (S.zeroForcingCoefficientTrajectory2D hab u₀ m s) :=
      congrArg (fun r : ℝ => r +
        2 * ∫ s in a..(t : ℝ),
          (S.zeroForcingProblem2D m u₀).forcing s
            (S.zeroForcingCoefficientTrajectory2D hab u₀ m s)) huInitialSq
    _ = ‖S.stateInitialCoefficient m u₀‖ ^ 2 := by
      simp only [S.zeroForcingProblem2D_forcing,
        ContinuousLinearMap.zero_apply, intervalIntegral.integral_zero,
        mul_zero, add_zero]

set_option maxHeartbeats 500000 in
/-- Physical gradient dissipation equals coefficient diffusion on every
initial subinterval. -/
theorem zeroForcing_gradient_integral_eq_diffusion
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I)
    (m : ℕ) (t : Icc a b) :
    (∫ s in a..(t : ℝ),
        ‖boxEnergyGradient I
          (S.zeroForcingEnergyTrajectory2D hab u₀ m s)‖ ^ 2) =
      ∫ s in a..(t : ℝ),
        (S.zeroForcingProblem2D m u₀).system.diffusion
          (S.zeroForcingCoefficientTrajectory2D hab u₀ m s)
          (S.zeroForcingCoefficientTrajectory2D hab u₀ m s) := by
  apply intervalIntegral.integral_congr
  intro s _hs
  change
    ‖boxEnergyGradient I
      (S.zeroForcingEnergyTrajectory2D hab u₀ m s)‖ ^ 2 = _
  calc
    ‖boxEnergyGradient I
        (S.zeroForcingEnergyTrajectory2D hab u₀ m s)‖ ^ 2 = _ :=
      (boxGradientDiffusion_self I _).symm
    _ = (S.zeroForcingProblem2D m u₀).system.diffusion
        (S.zeroForcingCoefficientTrajectory2D hab u₀ m s)
        (S.zeroForcingCoefficientTrajectory2D hab u₀ m s) :=
      (S.zeroForcingProblem2D_diffusion_apply m u₀
        (S.zeroForcingCoefficientTrajectory2D hab u₀ m s)
        (S.zeroForcingCoefficientTrajectory2D hab u₀ m s)).symm

/-- Exact physical energy identity for every finite unforced Galerkin
trajectory and every time in the interval. -/
theorem zeroForcing_finite_energy_identity
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I)
    (m : ℕ) (t : Icc a b) :
    ‖S.zeroForcingStateTrajectory2D hab u₀ m t‖ ^ 2 +
        2 * ∫ s in a..(t : ℝ),
          ‖boxEnergyGradient I
            (S.zeroForcingEnergyTrajectory2D hab u₀ m s)‖ ^ 2 =
      ‖S.stateSynthesis m (S.stateInitialCoefficient m u₀)‖ ^ 2 := by
  have hstate :
      ‖S.zeroForcingStateTrajectory2D hab u₀ m t‖ =
        ‖S.zeroForcingCoefficientTrajectory2D hab u₀ m t‖ := by
    exact S.norm_stateSynthesis m
      (S.zeroForcingCoefficientTrajectory2D hab u₀ m t)
  have hstateSq := congrArg (fun r : ℝ => r ^ 2) hstate
  have hdiff := S.zeroForcing_gradient_integral_eq_diffusion hab u₀ m t
  have hinitial := S.norm_stateSynthesis m (S.stateInitialCoefficient m u₀)
  have hinitialSq := congrArg (fun r : ℝ => r ^ 2) hinitial
  calc
    _ = ‖S.zeroForcingCoefficientTrajectory2D hab u₀ m t‖ ^ 2 +
        2 * ∫ s in a..(t : ℝ),
          ‖boxEnergyGradient I
            (S.zeroForcingEnergyTrajectory2D hab u₀ m s)‖ ^ 2 :=
      congrArg (fun r : ℝ => r +
        2 * ∫ s in a..(t : ℝ),
          ‖boxEnergyGradient I
            (S.zeroForcingEnergyTrajectory2D hab u₀ m s)‖ ^ 2) hstateSq
    _ = ‖S.zeroForcingCoefficientTrajectory2D hab u₀ m t‖ ^ 2 +
        2 * ∫ s in a..(t : ℝ),
          (S.zeroForcingProblem2D m u₀).system.diffusion
            (S.zeroForcingCoefficientTrajectory2D hab u₀ m s)
            (S.zeroForcingCoefficientTrajectory2D hab u₀ m s) :=
      congrArg
        (fun r : ℝ =>
          ‖S.zeroForcingCoefficientTrajectory2D hab u₀ m t‖ ^ 2 + 2 * r)
        hdiff
    _ = ‖S.stateInitialCoefficient m u₀‖ ^ 2 :=
      S.zeroForcing_coefficient_energy_identity hab u₀ m t
    _ = ‖S.stateSynthesis m (S.stateInitialCoefficient m u₀)‖ ^ 2 :=
      hinitialSq.symm

set_option maxHeartbeats 1000000 in
/-- The finite state and its restricted gradient form a uniformly bounded
vector in the weighted product Hilbert space. -/
theorem zeroForcing_finite_stateGradientPair_norm_le
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I)
    (m : ℕ) (t : Icc a b) :
    ‖WithLp.toLp 2
      (S.zeroForcingStateTrajectory2D hab u₀ m t,
        Real.sqrt 2 •
          restrictedGradientTimeMap (I := I) t
            ((S.zeroForcingLeraySpectralCompactFamily2D hab u₀).energyLp m))‖ ≤
      ‖u₀‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  calc
    ‖WithLp.toLp 2
        (S.zeroForcingStateTrajectory2D hab u₀ m t,
          Real.sqrt 2 •
            restrictedGradientTimeMap (I := I) t
              ((S.zeroForcingLeraySpectralCompactFamily2D hab u₀).energyLp m))‖ ^ 2 =
      ‖S.zeroForcingStateTrajectory2D hab u₀ m t‖ ^ 2 +
        2 * ‖restrictedGradientTimeMap (I := I) t
          ((S.zeroForcingLeraySpectralCompactFamily2D hab u₀).energyLp m)‖ ^ 2 :=
      norm_sqrtTwo_prodL2_sq _ _
    _ = ‖S.zeroForcingStateTrajectory2D hab u₀ m t‖ ^ 2 +
        2 * ∫ s in a..(t : ℝ),
          ‖boxEnergyGradient I
            (S.zeroForcingEnergyTrajectory2D hab u₀ m s)‖ ^ 2 :=
      congrArg
        (fun r : ℝ =>
          ‖S.zeroForcingStateTrajectory2D hab u₀ m t‖ ^ 2 + 2 * r)
        (S.zeroForcing_restrictedGradientTimeMap_norm_sq hab u₀ m t)
    _ = ‖S.stateSynthesis m (S.stateInitialCoefficient m u₀)‖ ^ 2 :=
      S.zeroForcing_finite_energy_identity hab u₀ m t
    _ = ‖S.stateInitialCoefficient m u₀‖ ^ 2 := by
      rw [S.norm_stateSynthesis]
    _ ≤ ‖u₀‖ ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
        (S.norm_stateInitialCoefficient_le m u₀)

/-- The concrete compact family state path is the physical pivot-space
trajectory at every time. -/
theorem zeroForcing_statePath_eq_trajectory
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I)
    (m : ℕ) (t : Icc a b) :
    (S.zeroForcingLeraySpectralCompactFamily2D hab u₀).statePath m t =
      S.zeroForcingStateTrajectory2D hab u₀ m t := by
  rw [LeraySpectralCompactFamily.statePath_apply,
    S.zeroForcingLeraySpectralCompactFamily2D_embed,
    S.zeroForcingLeraySpectralCompactFamily2D_lift_apply]
  change boxEnergyToState I
      (S.energySynthesis m
        (S.zeroForcingCoefficientTrajectory2D hab u₀ m t)) =
    S.stateSynthesis m
      (S.zeroForcingCoefficientTrajectory2D hab u₀ m t)
  exact S.boxEnergyToState_energySynthesis m _

set_option maxHeartbeats 5000000 in
/-- The synchronized weak limit satisfies the unforced energy inequality at
every time in the interval. -/
theorem zeroForcing_localEnergyInequality
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I)
    (SW : (S.zeroForcingLeraySpectralCompactFamily2D hab u₀).StrongWeakPathSubsequence)
    (t : Icc a b) :
    ‖(S.zeroForcingWeaklyContinuousStateRepresentative hab u₀ SW).path t‖ ^ 2 +
        2 * ∫ s : Icc a b in Set.Iic t,
          ‖boxEnergyGradient I (SW.energyLimit s)‖ ^ 2
          ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b ≤
      ‖u₀‖ ^ 2 := by
  let G := S.zeroForcingLeraySpectralCompactFamily2D hab u₀
  let base := SW.toStrongWeakSubsequence
  let A := restrictedGradientTimeMap (I := I) t
  let R := S.zeroForcingWeaklyContinuousStateRepresentative hab u₀ SW
  obtain ⟨rho, hrho, hstate⟩ := R.pointwise_weak_subsequence t
  let pairSeq : ℕ → WithLp 2
      (BoxL2Sigma I ×
        Lp (BoxGradientL2 I) (2 : ℝ≥0∞)
          ((SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b).restrict
            (Set.Iic t))) := fun j =>
    WithLp.toLp 2
      (G.statePath (SW.subseq.idx (rho j)) t,
        Real.sqrt 2 • A (G.energyLp (SW.subseq.idx (rho j))))
  let pairLimit : WithLp 2
      (BoxL2Sigma I ×
        Lp (BoxGradientL2 I) (2 : ℝ≥0∞)
          ((SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b).restrict
            (Set.Iic t))) :=
    WithLp.toLp 2
      (R.path t, Real.sqrt 2 • A base.energyLimit)
  have henergy (z : Lp (BoxGradientL2 I) (2 : ℝ≥0∞)
      ((SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b).restrict
        (Set.Iic t))) :
      Tendsto
        (fun j =>
          ⟪A (G.energyLp (SW.subseq.idx (rho j))), z⟫_ℝ)
        atTop (nhds ⟪A base.energyLimit, z⟫_ℝ) := by
    let ell : Lp (BoxH1ZeroSigma I) (2 : ℝ≥0∞)
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) →L[ℝ] ℝ :=
      (innerSLFlip ℝ z).comp A
    have hbase :=
      @LeraySpectralCompactFamily.StrongWeakSubsequence.energy_clm_tendsto
        (Icc a b) (BoxH1ZeroSigma I) (BoxL2Sigma I)
        inferInstance inferInstance inferInstance inferInstance
        inferInstance inferInstance (boxH1ZeroSigma_completeSpace I)
        inferInstance inferInstance
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)
        inferInstance G base ell
    have hsub := hbase.comp hrho.tendsto_atTop
    simpa only [ell, A, G, base, ContinuousLinearMap.comp_apply,
      innerSLFlip_apply_apply] using hsub
  have hpairWeak (z : WithLp 2
      (BoxL2Sigma I ×
        Lp (BoxGradientL2 I) (2 : ℝ≥0∞)
          ((SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b).restrict
            (Set.Iic t)))) :
      Tendsto (fun j => ⟪pairSeq j, z⟫_ℝ)
        atTop (nhds ⟪pairLimit, z⟫_ℝ) := by
    have hs := hstate z.fst
    have hg := henergy z.snd
    have hgScaled : Tendsto
        (fun j => Real.sqrt 2 *
          ⟪A (G.energyLp (SW.subseq.idx (rho j))), z.snd⟫_ℝ)
        atTop
        (nhds (Real.sqrt 2 * ⟪A base.energyLimit, z.snd⟫_ℝ)) := by
      exact tendsto_const_nhds.mul hg
    have hsum := hs.add hgScaled
    simpa only [pairSeq, pairLimit, WithLp.prod_inner_apply,
      WithLp.toLp_fst, WithLp.toLp_snd, real_inner_smul_left] using hsum
  let W : WeakHilbertSubsequence pairSeq := {
    subseq := ExtractedSubsequence.identity
    limit := pairLimit
    inner_tendsto := by
      intro z
      simpa only [ExtractedSubsequence.identity, id_eq] using hpairWeak z
  }
  have hbound (j : ℕ) : ‖pairSeq j‖ ≤ ‖u₀‖ := by
    simpa only [pairSeq, A, G,
      S.zeroForcing_statePath_eq_trajectory] using
        S.zeroForcing_finite_stateGradientPair_norm_le hab u₀
          (SW.subseq.idx (rho j)) t
  have hnorm : ‖pairLimit‖ ≤ ‖u₀‖ :=
    W.limit_norm_le ‖u₀‖ hbound
  have hsq : ‖pairLimit‖ ^ 2 ≤ ‖u₀‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hnorm
  calc
    ‖R.path t‖ ^ 2 +
        2 * ∫ s : Icc a b in Set.Iic t,
          ‖boxEnergyGradient I (SW.energyLimit s)‖ ^ 2
          ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b =
      ‖R.path t‖ ^ 2 + 2 * ‖A base.energyLimit‖ ^ 2 :=
      congrArg (fun r : ℝ => ‖R.path t‖ ^ 2 + 2 * r)
        (restrictedGradientTimeMap_norm_sq_eq_setIntegral
          (I := I) t base.energyLimit).symm
    _ = ‖pairLimit‖ ^ 2 := by
      exact (norm_sqrtTwo_prodL2_sq
        (R.path t) (A base.energyLimit)).symm
    _ ≤ ‖u₀‖ ^ 2 := hsq

/-- The gradient part of every canonical spectral lift satisfies the explicit
global dissipation bound inherited from the finite energy identity. -/
theorem zeroForcing_gradientTimeMap_norm_le
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I) (m : ℕ) :
    ‖(boxEnergyGradient I).compLpL 2
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)
        ((S.zeroForcingLeraySpectralCompactFamily2D hab u₀).energyLp m)‖ ≤
      ‖u₀‖ := by
  let G := S.zeroForcingLeraySpectralCompactFamily2D hab u₀
  let μ := SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b
  let gradLp : Lp (BoxGradientL2 I) (2 : ℝ≥0∞) μ :=
    (boxEnergyGradient I).compLpL 2 μ (G.energyLp m)
  have hgradAe : gradLp =ᵐ[μ] fun t =>
      boxEnergyGradient I (S.zeroForcingEnergyTrajectory2D hab u₀ m t) := by
    filter_upwards [(boxEnergyGradient I).coeFn_compLpL (G.energyLp m),
      S.zeroForcing_energyLp_eq_trajectory_ae hab u₀ m] with t hgrad henergy
    rw [hgrad, henergy]
    rfl
  have hsq : ‖gradLp‖ ^ 2 ≤ ‖u₀‖ ^ 2 := by
    calc
      ‖gradLp‖ ^ 2 = ∫ t, ‖gradLp t‖ ^ 2 ∂μ :=
        Lp.norm_two_sq_eq_integral_norm_sq gradLp
      _ = ∫ t : Icc a b,
          ‖boxEnergyGradient I
            (S.zeroForcingEnergyTrajectory2D hab u₀ m t)‖ ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [hgradAe] with t ht
        rw [ht]
      _ = ∫ t : Icc a b,
          boxGradientDiffusion I
            (S.zeroForcingEnergyTrajectory2D hab u₀ m t)
            (S.zeroForcingEnergyTrajectory2D hab u₀ m t) ∂μ := by
        apply integral_congr_ae
        filter_upwards with t
        exact (boxGradientDiffusion_self I _).symm
      _ = ∫ t in a..b,
          boxGradientDiffusion I
            (S.zeroForcingEnergyTrajectory2D hab u₀ m t)
            (S.zeroForcingEnergyTrajectory2D hab u₀ m t) :=
        by
          simpa only [μ] using
            SmoothBoxVariationalGalerkinLevel.integral_intervalSubtypeMeasure
              hab (fun t => boxGradientDiffusion I
                (S.zeroForcingEnergyTrajectory2D hab u₀ m t)
                (S.zeroForcingEnergyTrajectory2D hab u₀ m t))
      _ = ∫ t in a..b,
          (S.zeroForcingProblem2D m u₀).system.diffusion
            (S.zeroForcingCoefficientTrajectory2D hab u₀ m t)
            (S.zeroForcingCoefficientTrajectory2D hab u₀ m t) := by
        apply intervalIntegral.integral_congr
        intro t _ht
        exact (S.zeroForcingProblem2D_diffusion_apply m u₀
          (S.zeroForcingCoefficientTrajectory2D hab u₀ m t)
          (S.zeroForcingCoefficientTrajectory2D hab u₀ m t)).symm
      _ ≤ ‖u₀‖ ^ 2 :=
        S.zeroForcingSolution2D_diffusion_integral_le hab m u₀
          (S.zeroForcingSolution2D hab m u₀)
  exact (sq_le_sq₀ (norm_nonneg gradLp) (norm_nonneg u₀)).mp hsq

set_option maxHeartbeats 5000000 in
/-- The weak energy limit inherits the accumulated gradient bound. -/
theorem zeroForcing_gradientLimit_norm_le
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I)
    (SW : (S.zeroForcingLeraySpectralCompactFamily2D hab u₀).StrongWeakSubsequence) :
    ‖(boxEnergyGradient I).compLpL 2
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)
        SW.energyLimit‖ ≤ ‖u₀‖ := by
  letI : CompleteSpace (BoxH1ZeroSigma I) :=
    boxH1ZeroSigma_completeSpace I
  let G := S.zeroForcingLeraySpectralCompactFamily2D hab u₀
  let μ := SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b
  let A : Lp (BoxH1ZeroSigma I) (2 : ℝ≥0∞) μ →L[ℝ]
      Lp (BoxGradientL2 I) (2 : ℝ≥0∞) μ :=
    (boxEnergyGradient I).compLpL 2 μ
  let y : Lp (BoxGradientL2 I) (2 : ℝ≥0∞) μ := A SW.energyLimit
  let ell : Lp (BoxH1ZeroSigma I) (2 : ℝ≥0∞) μ →L[ℝ] ℝ :=
    (innerSLFlip ℝ y).comp A
  have hweak : Tendsto
      (fun k => ⟪A (G.energyLp (SW.subseq.idx k)), y⟫_ℝ)
      atTop (nhds ⟪y, y⟫_ℝ) := by
    have hbase :=
      @LeraySpectralCompactFamily.StrongWeakSubsequence.energy_clm_tendsto
        (Icc a b) (BoxH1ZeroSigma I) (BoxL2Sigma I)
        inferInstance inferInstance inferInstance inferInstance
        inferInstance inferInstance (boxH1ZeroSigma_completeSpace I)
        inferInstance inferInstance μ inferInstance G SW ell
    simpa only [ell, y, ContinuousLinearMap.comp_apply,
      innerSLFlip_apply_apply] using hbase
  have hsq : ‖y‖ ^ 2 ≤ ‖u₀‖ * ‖y‖ := by
    calc
      ‖y‖ ^ 2 = ⟪y, y⟫_ℝ := (real_inner_self_eq_norm_sq y).symm
      _ ≤ ‖u₀‖ * ‖y‖ := by
        apply le_of_tendsto hweak
        filter_upwards with k
        calc
          ⟪A (G.energyLp (SW.subseq.idx k)), y⟫_ℝ ≤
              ‖A (G.energyLp (SW.subseq.idx k))‖ * ‖y‖ :=
            real_inner_le_norm _ _
          _ ≤ ‖u₀‖ * ‖y‖ :=
            mul_le_mul_of_nonneg_right
              (S.zeroForcing_gradientTimeMap_norm_le hab u₀ (SW.subseq.idx k))
              (norm_nonneg _)
  change ‖y‖ ≤ ‖u₀‖
  by_cases hzero : ‖y‖ = 0
  · rw [hzero]
    exact norm_nonneg u₀
  · have hpos : 0 < ‖y‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    nlinarith [hsq]

/-- The weakly continuous representative selected from the synchronized
Galerkin subsequence attains the prescribed initial datum. -/
theorem zeroForcingWeaklyContinuousStateRepresentative_initial
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I)
    (SW : (S.zeroForcingLeraySpectralCompactFamily2D hab u₀).StrongWeakPathSubsequence) :
    (S.zeroForcingWeaklyContinuousStateRepresentative hab u₀ SW).path
      (⟨a, le_rfl, hab⟩ : Icc a b) = u₀ := by
  let t₀ : Icc a b := ⟨a, le_rfl, hab⟩
  apply (S.zeroForcingWeaklyContinuousStateRepresentative hab u₀ SW).eq_of_statePath_tendsto
    id tendsto_id t₀ u₀
  have hinitial := (S.stateInitialCoefficient_tendsto u₀).comp
    SW.subseq.strictMono_idx.tendsto_atTop
  have hinitial' : Tendsto
      (fun j => S.stateSynthesis (SW.subseq.idx j)
        (S.stateInitialCoefficient (SW.subseq.idx j) u₀))
      atTop (nhds u₀) := by
    simpa only [Function.comp_def] using hinitial
  convert hinitial' using 1
  funext j
  simpa only [t₀] using
    S.zeroForcing_statePath_initial hab u₀ (SW.subseq.idx j)

/-- An unforced Leray--Hopf weak solution on a two-dimensional box.  The
state has a bounded weakly continuous pivot-space representative attaining
the initial datum, the energy representative belongs to `L2` in the Sobolev
space, both representatives agree through the Gelfand-triple embedding, the
energy inequality holds at every time, and the time-tested equation carries
the same initial datum. -/
structure BoxLerayEnergyWeakSolutionOn
    (I : BoxIntegral.Box (Fin 2)) (a b : ℝ) (u₀ : BoxL2Sigma I) where
  interval_nonempty : a ≤ b
  state : Lp (BoxL2Sigma I) (2 : ℝ≥0∞)
    (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)
  energy : Lp (BoxH1ZeroSigma I) (2 : ℝ≥0∞)
    (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)
  weakState : Icc a b → BoxL2Sigma I
  weakState_norm_le : ∀ t, ‖weakState t‖ ≤ ‖u₀‖
  weakState_inner_continuous : ∀ y : BoxL2Sigma I,
    Continuous (fun t => ⟪weakState t, y⟫_ℝ)
  weakState_ae_eq_state :
    weakState =ᵐ[SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b]
      (state : Icc a b → BoxL2Sigma I)
  weakState_initial :
    weakState (⟨a, le_rfl, interval_nonempty⟩ : Icc a b) = u₀
  state_eq_energy :
    boxEnergyTimeStateMap energy = state
  state_memLp_top :
    MemLp (state : Icc a b → BoxL2Sigma I) ∞
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)
  state_eLpNorm_top_le :
    eLpNorm (state : Icc a b → BoxL2Sigma I) ∞
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) ≤
        ENNReal.ofReal ‖u₀‖
  energy_norm_le :
    ‖energy‖ ≤ zeroForcingEnergyRadius a b u₀
  gradient_norm_le :
    ‖(boxEnergyGradient I).compLpL 2
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) energy‖ ≤
      ‖u₀‖
  energy_inequality : ∀ t : Icc a b,
    ‖weakState t‖ ^ 2 +
        2 * ∫ s : Icc a b in Set.Iic t,
          ‖boxEnergyGradient I (energy s)‖ ^ 2
          ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b ≤
      ‖u₀‖ ^ 2
  weak_equation : ∀ (φ : BoxH1ZeroSigma I)
      (eta : LerayIntervalTimeTest a b), eta.value b = 0 →
    -(∫ t : Icc a b,
        ⟪state t, boxEnergyToState I φ⟫_ℝ * eta.deriv t
        ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) +
      (∫ t : Icc a b,
        boxGradientDiffusion I (energy t) φ * eta.value t
        ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) +
      (∫ t : Icc a b,
        (boxLadyzhenskayaRealization I).toBoxEnergyL4Realization.convectionForm I
          (energy t) (energy t) φ * eta.value t
        ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) =
      ⟪u₀, boxEnergyToState I φ⟫_ℝ * eta.value a

/-- The synchronized Galerkin limit determines a concrete unforced
Leray--Hopf weak solution. -/
noncomputable def zeroForcingEnergyWeakSolutionOfStrongWeakPath
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I)
    (SW : (S.zeroForcingLeraySpectralCompactFamily2D hab u₀).StrongWeakPathSubsequence) :
    BoxLerayEnergyWeakSolutionOn I a b u₀ := by
  let base := SW.toStrongWeakSubsequence
  let W := S.zeroForcingWeaklyContinuousStateRepresentative hab u₀ SW
  exact {
    interval_nonempty := hab
    state := base.stateLimit
    energy := base.energyLimit
    weakState := W.path
    weakState_norm_le := fun t => by
      simpa only [S.zeroForcingLeraySpectralCompactFamily2D_stateRadius] using
        W.norm_le t
    weakState_inner_continuous := W.inner_continuous
    weakState_ae_eq_state := W.path_ae_eq_stateLimit
    weakState_initial := by
      simpa only [W] using
        S.zeroForcingWeaklyContinuousStateRepresentative_initial hab u₀ SW
    state_eq_energy := by
      simpa only [boxEnergyTimeStateMap,
        S.zeroForcingLeraySpectralCompactFamily2D_embed] using
          base.embed_energyLimit
    state_memLp_top := base.stateLimit_memLp_top
    state_eLpNorm_top_le := by
      simpa only [S.zeroForcingLeraySpectralCompactFamily2D_stateRadius] using
        base.stateLimit_eLpNorm_top_le
    energy_norm_le := by
      simpa only [S.zeroForcingLeraySpectralCompactFamily2D_liftLpRadius] using
        base.energyLimit_norm_le
    gradient_norm_le := S.zeroForcing_gradientLimit_norm_le hab u₀ base
    energy_inequality := fun t => by
      simpa only [W, base] using
        S.zeroForcing_localEnergyInequality hab u₀ SW t
    weak_equation := fun φ eta heta =>
      S.zeroForcing_limit_timeTested_identity hab u₀ base φ eta heta
  }

/-- Existence of an unforced energy-class weak solution for every pivot-space
initial datum on every nonempty finite interval. -/
theorem exists_zeroForcing_twoDimensional_energyWeakSolution
    (S : BoxCompactSpectralRepresentation I)
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I) :
    Nonempty (BoxLerayEnergyWeakSolutionOn I a b u₀) := by
  obtain ⟨SW⟩ :=
    BoxCompactSpectralRepresentation.exists_zeroForcing_twoDimensional_strongWeakPath_subsequence
      S hab u₀
  exact ⟨S.zeroForcingEnergyWeakSolutionOfStrongWeakPath hab u₀ SW⟩

/-- Existence of an unforced Leray--Hopf weak solution for every pivot-space
initial datum on every nonempty finite interval. -/
theorem exists_zeroForcing_twoDimensional_lerayHopfSolution
    (S : BoxCompactSpectralRepresentation I)
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I) :
    Nonempty (BoxLerayEnergyWeakSolutionOn I a b u₀) :=
  S.exists_zeroForcing_twoDimensional_energyWeakSolution hab u₀

end BoxCompactSpectralRepresentation

/-- Unconditional existence of an unforced two-dimensional Leray--Hopf weak
solution on a rectangular box.  The spectral representation is constructed
canonically from the compact energy-to-state embedding. -/
theorem exists_zeroForcing_twoDimensional_lerayHopfSolution
    {I : BoxIntegral.Box (Fin 2)}
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I) :
    Nonempty
      (BoxCompactSpectralRepresentation.BoxLerayEnergyWeakSolutionOn
        I a b u₀) :=
  (boxCompactSpectralRepresentation I).exists_zeroForcing_twoDimensional_lerayHopfSolution
    hab u₀

end
