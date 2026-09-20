import PDEIdeas.BoxForcedSpectralGalerkin
import PDEIdeas.BoxLerayHopf

/-!
# Forced time-tested limit equation on a two-dimensional box

The forced spectral solutions satisfy an exact time-tested finite equation
carrying the pulled-back forcing.  The Riesz representative of the forcing is
a bounded continuous energy-space path, so testing it against a time--energy
class is an inner product; weak convergence therefore passes the forcing term
of the equation.  Together with the Ladyzhenskaya convection limit this gives
the forced weak equation satisfied by the synchronized Galerkin limit.
-/

open BoundedContinuousFunction Filter InnerProductSpace MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

noncomputable section

local instance box_forced_leray_fact_one_le_four : Fact (1 ≤ (4 : ℝ≥0∞)) :=
  ⟨by norm_num⟩

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 500000

/-- Weak limits obey the squared-norm bound of any convergent majorant
sequence. -/
theorem norm_sq_le_of_weak_tendsto
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x : ℕ → E} {ell : E}
    (hweak : ∀ z : E, Tendsto (fun j => ⟪x j, z⟫_ℝ) atTop (nhds ⟪ell, z⟫_ℝ))
    {c : ℕ → ℝ} {C : ℝ}
    (hc : ∀ j, ‖x j‖ ^ 2 ≤ c j)
    (hC : Tendsto c atTop (nhds C)) :
    ‖ell‖ ^ 2 ≤ C := by
  have hcnonneg : ∀ j, 0 ≤ c j := fun j => (sq_nonneg _).trans (hc j)
  have hCnonneg : 0 ≤ C := ge_of_tendsto' hC hcnonneg
  have hxnorm : ∀ j, ‖x j‖ ≤ Real.sqrt (c j) := by
    intro j
    have h := Real.sqrt_le_sqrt (hc j)
    rwa [Real.sqrt_sq (norm_nonneg _)] at h
  have hpair : ∀ j, ⟪x j, ell⟫_ℝ ≤ Real.sqrt (c j) * ‖ell‖ := by
    intro j
    calc
      ⟪x j, ell⟫_ℝ ≤ ‖x j‖ * ‖ell‖ := real_inner_le_norm _ _
      _ ≤ Real.sqrt (c j) * ‖ell‖ :=
        mul_le_mul_of_nonneg_right (hxnorm j) (norm_nonneg _)
  have hleft : Tendsto (fun j => ⟪x j, ell⟫_ℝ) atTop (nhds ⟪ell, ell⟫_ℝ) :=
    hweak ell
  have hright : Tendsto (fun j => Real.sqrt (c j) * ‖ell‖) atTop
      (nhds (Real.sqrt C * ‖ell‖)) :=
    ((Real.continuous_sqrt.tendsto C).comp hC).mul tendsto_const_nhds
  have hlim : ⟪ell, ell⟫_ℝ ≤ Real.sqrt C * ‖ell‖ :=
    le_of_tendsto_of_tendsto' hleft hright hpair
  rw [real_inner_self_eq_norm_sq] at hlim
  rcases eq_or_lt_of_le (norm_nonneg ell) with hzero | hpos
  · rw [← hzero]
    simpa using hCnonneg
  · have hmul : ‖ell‖ * ‖ell‖ ≤ Real.sqrt C * ‖ell‖ := by
      rw [← sq]
      exact hlim
    have hle : ‖ell‖ ≤ Real.sqrt C := le_of_mul_le_mul_right hmul hpos
    calc
      ‖ell‖ ^ 2 = ‖ell‖ * ‖ell‖ := sq _
      _ ≤ Real.sqrt C * Real.sqrt C :=
        mul_self_le_mul_self (norm_nonneg ell) hle
      _ = C := Real.mul_self_sqrt hCnonneg

namespace BoxDualForcing

variable {I : BoxIntegral.Box (Fin 2)} (Φ : BoxDualForcing I)

/-- The Riesz path of the forcing as a continuous map on the closed time
interval. -/
def repCM (a b : ℝ) : C(Icc a b, BoxH1ZeroSigma I) :=
  ⟨fun t => Φ.rep (t : ℝ), Φ.continuous_rep.comp continuous_subtype_val⟩

/-- The Riesz path of the forcing as a bounded continuous energy-space
path. -/
def repBCF (a b : ℝ) : (Icc a b) →ᵇ BoxH1ZeroSigma I :=
  BoundedContinuousFunction.mkOfCompact (Φ.repCM a b)

/-- The Riesz path of the forcing as a time--energy `L2` class. -/
def repLp (a b : ℝ) :
    Lp (BoxH1ZeroSigma I) (2 : ℝ≥0∞)
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) :=
  BoundedContinuousFunction.toLp (2 : ℝ≥0∞)
    (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) ℝ
    (Φ.repBCF a b)

theorem repLp_ae (a b : ℝ) :
    Φ.repLp a b =ᵐ[
      SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b]
        fun t : Icc a b => Φ.rep (t : ℝ) := by
  simpa only [repLp, repBCF, repCM,
    BoundedContinuousFunction.mkOfCompact_apply, ContinuousMap.coe_mk] using
    BoundedContinuousFunction.coeFn_toLp (2 : ℝ≥0∞)
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) ℝ
      (Φ.repBCF a b)

/-- Testing against the Riesz path is the time-integrated action of the
forcing. -/
theorem inner_repLp_eq_integral {a b : ℝ}
    (w : Lp (BoxH1ZeroSigma I) (2 : ℝ≥0∞)
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)) :
    ⟪Φ.repLp a b, w⟫_ℝ =
      ∫ t : Icc a b, Φ.value (t : ℝ) (w t)
        ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Φ.repLp_ae a b] with t ht
  rw [ht, Φ.value_apply]

/-- The time-tested action of the forcing on a fixed energy vector. -/
theorem inner_repLp_valueLp_eq {a b : ℝ}
    (eta : IntervalTimeTest a b) (x : BoxH1ZeroSigma I) :
    ⟪Φ.repLp a b,
        eta.valueLpCLM (BoxH1ZeroSigma I) (2 : ℝ≥0∞) x⟫_ℝ =
      ∫ t : Icc a b, Φ.value (t : ℝ) x * eta.value t
        ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b := by
  rw [Φ.inner_repLp_eq_integral]
  apply integral_congr_ae
  filter_upwards [eta.valueLpCLM_apply_ae (BoxH1ZeroSigma I) (2 : ℝ≥0∞) x]
    with t ht
  rw [ht, map_smul]
  change eta.value t * Φ.value (t : ℝ) x = _
  exact mul_comm _ _

/-- The time-tested forcing functional evaluated along a converging sequence
of energy tests. -/
theorem forcing_test_integral_tendsto {a b : ℝ}
    (eta : IntervalTimeTest a b) {x : ℕ → BoxH1ZeroSigma I}
    {xLimit : BoxH1ZeroSigma I} (hx : Tendsto x atTop (nhds xLimit)) :
    Tendsto
      (fun k => ∫ t : Icc a b, Φ.value (t : ℝ) (x k) * eta.value t
        ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)
      atTop
      (nhds (∫ t : Icc a b, Φ.value (t : ℝ) xLimit * eta.value t
        ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)) := by
  have hcont : Continuous fun y : BoxH1ZeroSigma I =>
      ⟪Φ.repLp a b,
        eta.valueLpCLM (BoxH1ZeroSigma I) (2 : ℝ≥0∞) y⟫_ℝ := by
    exact (innerSL ℝ (Φ.repLp a b)).continuous.comp
      (eta.valueLpCLM (BoxH1ZeroSigma I) (2 : ℝ≥0∞)).continuous
  have hbase := (hcont.tendsto xLimit).comp hx
  simpa only [Function.comp_def, Φ.inner_repLp_valueLp_eq eta] using hbase

end BoxDualForcing

namespace BoxCompactSpectralRepresentation

variable {I : BoxIntegral.Box (Fin 2)}
    (S : BoxCompactSpectralRepresentation I)

local instance box_forced_leray_h_complete : CompleteSpace (BoxL2Sigma I) :=
  boxL2Sigma_completeSpace I

local instance box_forced_leray_v_complete : CompleteSpace (BoxH1ZeroSigma I) :=
  boxH1ZeroSigma_completeSpace I

section GenericLimits

variable {a b : ℝ}
    (G : LeraySpectralCompactFamily
      (I := Icc a b) (V := BoxH1ZeroSigma I) (H := BoxL2Sigma I)
      (μ := SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b))

/-- Strong state convergence passes the time-derivative term for every
box compactness family. -/
theorem boxLeray_stateDerivativeIntegral_tendsto
    (SW : G.StrongWeakSubsequence)
    (φ : BoxH1ZeroSigma I) (eta : LerayIntervalTimeTest a b) :
    Tendsto
      (fun k => ∫ t : Icc a b,
        ⟪G.stateLp (SW.subseq.idx k) t, boxEnergyToState I φ⟫_ℝ * eta.deriv t
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
      (w t) (boxEnergyToState I φ) (eta.deriv t)).trans (mul_comm _ _)
  have hbase := SW.stateBilinearIntegral_tendsto A psi
  change Tendsto
    (fun k => ∫ t, A (G.stateLp (SW.subseq.idx k) t) (psi t) ∂μ)
    atTop (nhds (∫ t, A (SW.stateLimit t) (psi t) ∂μ)) at hbase
  have hseq :
      (fun k => ∫ t, A (G.stateLp (SW.subseq.idx k) t) (psi t) ∂μ) =
      (fun k => ∫ t : Icc a b,
        ⟪G.stateLp (SW.subseq.idx k) t, boxEnergyToState I φ⟫_ℝ *
          eta.deriv t ∂μ) := by
    funext k
    exact heq _
  rw [hseq, heq SW.stateLimit] at hbase
  exact hbase

/-- Weak energy convergence and strong convergence of the spectral test
projection pass the diffusion term for every box compactness family. -/
theorem boxLeray_diffusionIntegral_tendsto
    (SW : G.StrongWeakSubsequence)
    (φ : BoxH1ZeroSigma I) (eta : LerayIntervalTimeTest a b) :
    Tendsto
      (fun k => ∫ t : Icc a b,
        boxGradientDiffusion I (G.energyLp (SW.subseq.idx k) t)
          (S.energyProjection (SW.subseq.idx k) φ) * eta.value t
        ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)
      atTop
      (nhds (∫ t : Icc a b,
        boxGradientDiffusion I (SW.energyLimit t) φ * eta.value t
        ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)) := by
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
  have hpsi : Tendsto psi atTop (nhds psiLimit) :=
    (testCLM.continuous.tendsto φ).comp hproj
  have heq (w : Lp (BoxH1ZeroSigma I) (2 : ℝ≥0∞) μ)
      (x : BoxH1ZeroSigma I) :
      (∫ t, boxGradientDiffusion I (w t) ((testCLM x) t) ∂μ) =
        ∫ t : Icc a b,
          boxGradientDiffusion I (w t) x * eta.value t ∂μ :=
    diffusion_valueLp_integral_eq eta.toIntervalTimeTest w x
  have hbase :=
    @LeraySpectralCompactFamily.StrongWeakSubsequence.energyBilinearIntegral_tendsto_of_test_tendsto
      (Icc a b) (BoxH1ZeroSigma I) (BoxL2Sigma I)
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance (boxH1ZeroSigma_completeSpace I)
      inferInstance inferInstance μ inferInstance _ SW
      (boxGradientDiffusion I) psi psiLimit hpsi
  change Tendsto
    (fun k => ∫ t,
      boxGradientDiffusion I (G.energyLp (SW.subseq.idx k) t) (psi k t) ∂μ)
    atTop
    (nhds (∫ t, boxGradientDiffusion I (SW.energyLimit t)
      (psiLimit t) ∂μ)) at hbase
  have hseq :
      (fun k => ∫ t,
        boxGradientDiffusion I
          (G.energyLp (SW.subseq.idx k) t) (psi k t) ∂μ) =
      (fun k => ∫ t : Icc a b,
        boxGradientDiffusion I (G.energyLp (SW.subseq.idx k) t)
          (S.energyProjection (SW.subseq.idx k) φ) * eta.value t ∂μ) := by
    funext k
    exact heq _ _
  rw [hseq, heq SW.energyLimit φ] at hbase
  exact hbase

set_option maxHeartbeats 8000000 in
/-- Ladyzhenskaya compactness passes the quadratic convection integral for
every box compactness family whose embedding is the canonical one. -/
theorem boxLeray_quadraticConvectionIntegral_tendsto
    (hembed : G.embed = boxEnergyToState I)
    (SW : G.StrongWeakSubsequence)
    (φ : BoxH1ZeroSigma I) (eta : LerayIntervalTimeTest a b) :
    Tendsto
      (fun k => boxQuadraticConvectionIntegral
        (boxLadyzhenskayaTimeMap (boxLadyzhenskayaRealization I)
          (G.energyLp (SW.subseq.idx k)))
        (boxGradientCutoffLp eta.toIntervalTimeTest
          (S.energyProjection (SW.subseq.idx k) φ)))
      atTop
      (nhds (boxQuadraticConvectionIntegral
        (boxLadyzhenskayaTimeMap (boxLadyzhenskayaRealization I) SW.energyLimit)
        (boxGradientCutoffLp eta.toIntervalTimeTest φ))) := by
  let μ := SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b
  let L := boxLadyzhenskayaRealization I
  have hpointwise : ∀ v : BoxH1ZeroSigma I,
      ‖L.toLp4 v‖ ^ 2 ≤ L.constant * ‖G.embed v‖ * ‖v‖ := by
    intro v
    rw [hembed]
    exact (L.l4_sq_le v).trans
      (mul_le_mul_of_nonneg_left (norm_boxEnergyGradient_le I v)
        (mul_nonneg L.constant_nonneg (norm_nonneg _)))
  let L4S := SW.toInterpolatedStrongMetricSubsequence
    L.toLp4 L.constant L.constant_nonneg hpointwise
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

set_option maxHeartbeats 6000000 in
/-- The quadratic convergence theorem, converted by skew symmetry to the
named physical convection integral. -/
theorem boxLeray_physicalConvectionIntegral_tendsto
    (hembed : G.embed = boxEnergyToState I)
    (SW : G.StrongWeakSubsequence)
    (φ : BoxH1ZeroSigma I) (eta : LerayIntervalTimeTest a b) :
    Tendsto
      (fun k => boxPhysicalConvectionIntegral eta.toIntervalTimeTest
        (boxLadyzhenskayaRealization I)
        (G.energyLp (SW.subseq.idx k))
        (S.energyProjection (SW.subseq.idx k) φ))
      atTop
      (nhds (boxPhysicalConvectionIntegral eta.toIntervalTimeTest
        (boxLadyzhenskayaRealization I) SW.energyLimit φ)) := by
  have hquad :=
    S.boxLeray_quadraticConvectionIntegral_tendsto G hembed SW φ eta
  simpa only [convection_valueLp_integral_eq] using hquad.neg

set_option maxHeartbeats 6000000 in
/-- Expanded physical form of convection convergence for every box
compactness family with the canonical embedding. -/
theorem boxLeray_convectionIntegral_tendsto
    (hembed : G.embed = boxEnergyToState I)
    (SW : G.StrongWeakSubsequence)
    (φ : BoxH1ZeroSigma I) (eta : LerayIntervalTimeTest a b) :
    Tendsto
      (fun k => ∫ t : Icc a b,
        (boxLadyzhenskayaRealization I).toBoxEnergyL4Realization.convectionForm I
          (G.energyLp (SW.subseq.idx k) t)
          (G.energyLp (SW.subseq.idx k) t)
          (S.energyProjection (SW.subseq.idx k) φ) * eta.value t
        ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)
      atTop
      (nhds (∫ t : Icc a b,
        (boxLadyzhenskayaRealization I).toBoxEnergyL4Realization.convectionForm I
          (SW.energyLimit t) (SW.energyLimit t) φ * eta.value t
        ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)) := by
  have hphys :=
    S.boxLeray_physicalConvectionIntegral_tendsto G hembed SW φ eta
  simpa only [boxPhysicalConvectionIntegral,
    boxPhysicalConvectionIntegrand] using hphys

end GenericLimits

end BoxCompactSpectralRepresentation

namespace VariationalGalerkinProblem

variable {W Test : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    [NormedAddCommGroup Test] [NormedSpace ℝ Test]

/-- The finite-level distributional weak identity with the forcing term
displayed, for a continuous dual forcing. -/
theorem LocalSolutionOn.timeTested_forced_identity
    {P : VariationalGalerkinProblem W}
    {a b : ℝ} (hab : a ≤ b)
    (u : P.LocalSolutionOn (⟨a, le_rfl, hab⟩ : Icc a b))
    (Q : Test →L[ℝ] W) (phi : Test)
    (eta : IntervalTimeTest a b)
    (heta_terminal : eta.value b = 0)
    (hFcont : Continuous P.forcing) :
    -(∫ t in a..b, ⟪u.toFun t, Q phi⟫_ℝ * eta.deriv t) +
        (∫ t in a..b,
          P.system.diffusion (u.toFun t) (Q phi) * eta.value t) +
        (∫ t in a..b,
          P.system.convection (u.toFun t) (u.toFun t) (Q phi) * eta.value t) =
      ⟪P.initial, Q phi⟫_ℝ * eta.value a +
        ∫ t in a..b, P.forcing t (Q phi) * eta.value t := by
  let Y : ℝ → ℝ := fun t => ⟪u.toFun t, Q phi⟫_ℝ
  let A : ℝ → ℝ := fun t => P.system.diffusion (u.toFun t) (Q phi)
  let B : ℝ → ℝ := fun t => P.system.convection (u.toFun t) (u.toFun t) (Q phi)
  let F : ℝ → ℝ := fun t => P.forcing t (Q phi)
  let fA : ℝ → ℝ := fun t => A t * eta.value t
  let fB : ℝ → ℝ := fun t => B t * eta.value t
  let fF : ℝ → ℝ := fun t => F t * eta.value t
  let fY : ℝ → ℝ := fun t => Y t * eta.deriv t
  have hU : ContinuousOn u.toFun (Icc a b) := u.continuousOn
  have hY : ContinuousOn Y (Icc a b) :=
    (innerSLFlip ℝ (Q phi)).continuous.comp_continuousOn hU
  have hAcont : ContinuousOn A (Icc a b) :=
    (P.system.diffusion.continuous.comp_continuousOn hU).clm_apply
      continuousOn_const
  have hBcont : ContinuousOn B (Icc a b) :=
    (P.system.convection.continuous₂.comp_continuousOn
      (hU.prodMk hU)).clm_apply continuousOn_const
  have hFcont' : ContinuousOn F (Icc a b) :=
    hFcont.continuousOn.clm_apply continuousOn_const
  have hA : IntervalIntegrable fA volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab (hAcont.mul eta.continuousOn)
  have hB : IntervalIntegrable fB volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab (hBcont.mul eta.continuousOn)
  have hF : IntervalIntegrable fF volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab (hFcont'.mul eta.continuousOn)
  have hY_uIcc : ContinuousOn Y (uIcc a b) := by
    simpa only [uIcc_of_le hab] using hY
  have hYd : IntervalIntegrable fY volume a b :=
    eta.deriv_intervalIntegrable.continuousOn_mul hY_uIcc
  have hdual_cont : ContinuousOn
      (fun t => P.dualRHS Q t (u.toFun t) phi) (Icc a b) := by
    simpa only [dualRHS_apply, sub_eq_add_neg, A, B, F] using
      (hAcont.neg.sub hBcont).add hFcont'
  have hdual : IntervalIntegrable
      (fun t => P.dualRHS Q t (u.toFun t) phi) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab hdual_cont
  have hraw := u.timeTested_dualRHS_identity hab Q phi eta hdual
  have hsplit :
      (∫ t in a..b,
          P.dualRHS Q t (u.toFun t) phi * eta.value t + Y t * eta.deriv t) =
        (-(∫ t in a..b, fA t) - (∫ t in a..b, fB t) +
            ∫ t in a..b, fF t) +
          ∫ t in a..b, fY t := by
    calc
      (∫ t in a..b,
          P.dualRHS Q t (u.toFun t) phi * eta.value t + Y t * eta.deriv t) =
          ∫ t in a..b, (((-fA t) - fB t) + fF t) + fY t := by
            apply intervalIntegral.integral_congr
            intro t _ht
            simp only [dualRHS_apply, A, B, F, fA, fB, fF, fY, Y]
            ring
      _ = (∫ t in a..b, ((-fA t) - fB t) + fF t) + ∫ t in a..b, fY t :=
            intervalIntegral.integral_add
              (f := fun t => ((-fA t) - fB t) + fF t) (g := fY)
              ((hA.neg.sub hB).add hF) hYd
      _ = ((∫ t in a..b, (-fA t) - fB t) + ∫ t in a..b, fF t) +
            ∫ t in a..b, fY t := by
            rw [intervalIntegral.integral_add
              (f := fun t => (-fA t) - fB t) (g := fF) (hA.neg.sub hB) hF]
      _ = (((∫ t in a..b, -fA t) - ∫ t in a..b, fB t) +
            ∫ t in a..b, fF t) + ∫ t in a..b, fY t := by
            rw [intervalIntegral.integral_sub
              (f := fun t => -fA t) (g := fB) hA.neg hB]
      _ = (-(∫ t in a..b, fA t) - (∫ t in a..b, fB t) +
            ∫ t in a..b, fF t) + ∫ t in a..b, fY t := by
            rw [intervalIntegral.integral_neg (f := fA)]
  rw [show u.toFun a = P.initial from u.initial, heta_terminal,
    mul_zero, zero_sub] at hraw
  rw [hsplit] at hraw
  have hfinal : -(∫ t in a..b, fY t) +
      (∫ t in a..b, fA t) + (∫ t in a..b, fB t) =
        ⟪P.initial, Q phi⟫_ℝ * eta.value a + ∫ t in a..b, fF t := by
    linarith
  simpa only [fY, fA, fB, fF, Y, A, B, F] using hfinal

end VariationalGalerkinProblem

namespace BoxCompactSpectralRepresentation

variable {I : BoxIntegral.Box (Fin 2)}
    (S : BoxCompactSpectralRepresentation I)

local instance box_forced_leray_h_complete' : CompleteSpace (BoxL2Sigma I) :=
  boxL2Sigma_completeSpace I

local instance box_forced_leray_v_complete' : CompleteSpace (BoxH1ZeroSigma I) :=
  boxH1ZeroSigma_completeSpace I

section ForcedTrajectories

variable {a b : ℝ} (hab : a ≤ b) (Φ : BoxDualForcing I) (u₀ : BoxL2Sigma I)

/-- Coefficient trajectory selected at one forced spectral level. -/
def forcedCoefficientTrajectory2D (m : ℕ) : ℝ → S.CoefficientSpace m :=
  S.canonicalSolutionToFun m hab (S.forcedSolution2D hab m Φ u₀)

/-- Energy-space reconstruction of one forced spectral trajectory. -/
def forcedEnergyTrajectory2D (m : ℕ) : ℝ → BoxH1ZeroSigma I :=
  fun t => S.energySynthesis m (S.forcedCoefficientTrajectory2D hab Φ u₀ m t)

/-- Pivot-space reconstruction of one forced spectral trajectory. -/
def forcedStateTrajectory2D (m : ℕ) : ℝ → BoxL2Sigma I :=
  fun t => S.stateSynthesis m (S.forcedCoefficientTrajectory2D hab Φ u₀ m t)

@[simp]
theorem forcedFamily_embed :
    (S.forcedLeraySpectralCompactFamily2D hab Φ u₀).embed =
      boxEnergyToState I :=
  rfl

@[simp]
theorem forcedFamily_stateRadius :
    (S.forcedLeraySpectralCompactFamily2D hab Φ u₀).stateRadius =
      Φ.stateRadius a b u₀ :=
  rfl

@[simp]
theorem forcedFamily_liftLpRadius :
    (S.forcedLeraySpectralCompactFamily2D hab Φ u₀).liftLpRadius =
      Φ.energyRadius a b u₀ :=
  rfl

@[simp]
theorem forcedFamily_lift_apply (m : ℕ) (t : Icc a b) :
    (S.forcedLeraySpectralCompactFamily2D hab Φ u₀).lift m t =
      S.forcedEnergyTrajectory2D hab Φ u₀ m t :=
  rfl

/-- The forced energy `Lp` representative agrees almost everywhere with the
physical reconstructed trajectory. -/
theorem forced_energyLp_eq_trajectory_ae (m : ℕ) :
    (S.forcedLeraySpectralCompactFamily2D hab Φ u₀).energyLp m =ᵐ[
      SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b]
        fun t => S.forcedEnergyTrajectory2D hab Φ u₀ m t := by
  let G := S.forcedLeraySpectralCompactFamily2D hab Φ u₀
  change BoundedContinuousFunction.toLp (2 : ℝ≥0∞)
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) ℝ
      (G.lift m) =ᵐ[
        SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b] _
  filter_upwards [BoundedContinuousFunction.coeFn_toLp (2 : ℝ≥0∞)
    (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) ℝ
    (G.lift m)] with t ht
  rw [ht]
  rfl

/-- The forced state `Lp` representative agrees almost everywhere with the
physical reconstructed trajectory. -/
theorem forced_stateLp_eq_trajectory_ae (m : ℕ) :
    (S.forcedLeraySpectralCompactFamily2D hab Φ u₀).stateLp m =ᵐ[
      SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b]
        fun t => S.forcedStateTrajectory2D hab Φ u₀ m t := by
  let G := S.forcedLeraySpectralCompactFamily2D hab Φ u₀
  change BoundedContinuousFunction.toLp (2 : ℝ≥0∞)
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) ℝ
      (LeraySpectralCompactFamily.statePath G m) =ᵐ[
        SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b] _
  filter_upwards [BoundedContinuousFunction.coeFn_toLp (2 : ℝ≥0∞)
    (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) ℝ
    (LeraySpectralCompactFamily.statePath G m)] with t ht
  rw [ht]
  change boxEnergyToState I (G.lift m t) = _
  rw [S.forcedFamily_lift_apply hab Φ u₀ m t]
  exact S.boxEnergyToState_energySynthesis m _

/-- The pulled-back forcing tested by the spectral test projection is the
forcing tested by the reconstructed energy projection. -/
theorem forcedProblem2D_forcing_testProjection (m : ℕ) (φ : BoxH1ZeroSigma I)
    (t : ℝ) :
    (S.forcedProblem2D m Φ u₀).forcing t (S.testProjection m φ) =
      Φ.value t (S.energyProjection m φ) := by
  rw [S.forcedProblem2D_forcing_apply m Φ u₀ t (S.testProjection m φ),
    S.energySynthesis_testProjection_eq_partialProjection m φ]

@[simp]
theorem variationalProblem2D_forcing_apply (m : ℕ)
    (forcing : ℝ → BoxH1ZeroSigma I →L[ℝ] ℝ)
    (initial : S.CoefficientSpace m) (t : ℝ) (x : S.CoefficientSpace m) :
    (S.variationalProblem2D m forcing initial).forcing t x =
      forcing t (S.energySynthesis m x) :=
  rfl

@[simp]
theorem forcedProblem2D_convection_apply (m : ℕ)
    (Ψ : BoxDualForcing I) (v₀ : BoxL2Sigma I)
    (x y z : S.CoefficientSpace m) :
    (S.forcedProblem2D m Ψ v₀).system.convection x y z =
      (boxLadyzhenskayaRealization I).toBoxEnergyL4Realization.convectionForm I
        (S.energySynthesis m x) (S.energySynthesis m y)
        (S.energySynthesis m z) :=
  rfl

set_option maxHeartbeats 4000000 in
/-- Physical form of the finite forced spectral equation after testing in
time and reconstructing the common-space test projection. -/
theorem forcedSolution2D_timeTested_physical_identity
    (m : ℕ) (φ : BoxH1ZeroSigma I)
    (eta : IntervalTimeTest a b)
    (heta_terminal : eta.value b = 0) :
    -(∫ t in a..b,
        ⟪S.forcedStateTrajectory2D hab Φ u₀ m t, boxEnergyToState I φ⟫_ℝ *
          eta.deriv t) +
      (∫ t in a..b,
        boxGradientDiffusion I (S.forcedEnergyTrajectory2D hab Φ u₀ m t)
          (S.energyProjection m φ) * eta.value t) +
      (∫ t in a..b,
        (boxLadyzhenskayaRealization I).toBoxEnergyL4Realization.convectionForm I
          (S.forcedEnergyTrajectory2D hab Φ u₀ m t)
          (S.forcedEnergyTrajectory2D hab Φ u₀ m t)
          (S.energyProjection m φ) * eta.value t) =
      ⟪S.stateSynthesis m (S.stateInitialCoefficient m u₀),
          boxEnergyToState I φ⟫_ℝ * eta.value a +
        ∫ t in a..b, Φ.value t (S.energyProjection m φ) * eta.value t := by
  letI : NormedAddCommGroup (S.CoefficientSpace m) :=
    S.coefficientSpaceNormedAddCommGroup m
  letI : InnerProductSpace ℝ (S.CoefficientSpace m) :=
    S.coefficientSpaceInnerProductSpace m
  letI : CompleteSpace (S.CoefficientSpace m) :=
    S.coefficientSpaceCompleteSpace m
  let P := S.forcedProblem2D m Φ u₀
  let u := S.forcedSolution2D hab m Φ u₀
  have h :=
    @VariationalGalerkinProblem.LocalSolutionOn.timeTested_forced_identity
      (S.CoefficientSpace m) (BoxH1ZeroSigma I)
      (S.coefficientSpaceNormedAddCommGroup m)
      (S.coefficientSpaceInnerProductSpace m)
      (S.coefficientSpaceCompleteSpace m)
      inferInstance inferInstance P a b hab u
      (S.testProjection m) φ eta heta_terminal
      (S.forcedProblem2D_forcing_continuous m Φ u₀)
  have hcoeff :
      (-(∫ t in a..b,
          ⟪S.forcedCoefficientTrajectory2D hab Φ u₀ m t,
            S.testProjection m φ⟫_ℝ * eta.deriv t) +
        (∫ t in a..b,
          (S.forcedProblem2D m Φ u₀).system.diffusion
            (S.forcedCoefficientTrajectory2D hab Φ u₀ m t)
            (S.testProjection m φ) * eta.value t) +
        (∫ t in a..b,
          (S.forcedProblem2D m Φ u₀).system.convection
            (S.forcedCoefficientTrajectory2D hab Φ u₀ m t)
            (S.forcedCoefficientTrajectory2D hab Φ u₀ m t)
            (S.testProjection m φ) * eta.value t) =
        ⟪(S.forcedProblem2D m Φ u₀).initial,
            S.testProjection m φ⟫_ℝ * eta.value a +
          ∫ t in a..b,
            (S.forcedProblem2D m Φ u₀).forcing t
              (S.testProjection m φ) * eta.value t) := h
  have hstate : (∫ t in a..b,
      ⟪S.forcedCoefficientTrajectory2D hab Φ u₀ m t,
        S.testProjection m φ⟫_ℝ * eta.deriv t) =
      ∫ t in a..b,
        ⟪S.forcedStateTrajectory2D hab Φ u₀ m t,
          boxEnergyToState I φ⟫_ℝ * eta.deriv t := by
    apply intervalIntegral.integral_congr
    intro t _ht
    dsimp only
    exact congrArg (fun r : ℝ => r * eta.deriv t)
      (S.inner_testProjection_eq_state_inner m
        (S.forcedCoefficientTrajectory2D hab Φ u₀ m t) φ)
  have hdiffusion : (∫ t in a..b,
      (S.forcedProblem2D m Φ u₀).system.diffusion
        (S.forcedCoefficientTrajectory2D hab Φ u₀ m t)
        (S.testProjection m φ) * eta.value t) =
      ∫ t in a..b,
        boxGradientDiffusion I (S.forcedEnergyTrajectory2D hab Φ u₀ m t)
          (S.energyProjection m φ) * eta.value t := by
    apply intervalIntegral.integral_congr
    intro t _ht
    dsimp only
    apply congrArg (fun r : ℝ => r * eta.value t)
    calc
      (S.forcedProblem2D m Φ u₀).system.diffusion
          (S.forcedCoefficientTrajectory2D hab Φ u₀ m t)
          (S.testProjection m φ) =
          boxGradientDiffusion I (S.forcedEnergyTrajectory2D hab Φ u₀ m t)
            (S.energySynthesis m (S.testProjection m φ)) :=
        S.forcedProblem2D_diffusion_apply m Φ u₀
          (S.forcedCoefficientTrajectory2D hab Φ u₀ m t)
          (S.testProjection m φ)
      _ = boxGradientDiffusion I (S.forcedEnergyTrajectory2D hab Φ u₀ m t)
            (S.energyProjection m φ) :=
        congrArg
          (boxGradientDiffusion I (S.forcedEnergyTrajectory2D hab Φ u₀ m t))
          (S.energySynthesis_testProjection_eq_partialProjection m φ)
  have hconvection : (∫ t in a..b,
      (S.forcedProblem2D m Φ u₀).system.convection
        (S.forcedCoefficientTrajectory2D hab Φ u₀ m t)
        (S.forcedCoefficientTrajectory2D hab Φ u₀ m t)
        (S.testProjection m φ) * eta.value t) =
      ∫ t in a..b,
        (boxLadyzhenskayaRealization I).toBoxEnergyL4Realization.convectionForm I
          (S.forcedEnergyTrajectory2D hab Φ u₀ m t)
          (S.forcedEnergyTrajectory2D hab Φ u₀ m t)
          (S.energyProjection m φ) * eta.value t := by
    apply intervalIntegral.integral_congr
    intro t _ht
    dsimp only
    apply congrArg (fun r : ℝ => r * eta.value t)
    calc
      (S.forcedProblem2D m Φ u₀).system.convection
          (S.forcedCoefficientTrajectory2D hab Φ u₀ m t)
          (S.forcedCoefficientTrajectory2D hab Φ u₀ m t)
          (S.testProjection m φ) =
          (boxLadyzhenskayaRealization I).toBoxEnergyL4Realization.convectionForm I
            (S.forcedEnergyTrajectory2D hab Φ u₀ m t)
            (S.forcedEnergyTrajectory2D hab Φ u₀ m t)
            (S.energySynthesis m (S.testProjection m φ)) :=
        S.forcedProblem2D_convection_apply m Φ u₀
          (S.forcedCoefficientTrajectory2D hab Φ u₀ m t)
          (S.forcedCoefficientTrajectory2D hab Φ u₀ m t)
          (S.testProjection m φ)
      _ =
          (boxLadyzhenskayaRealization I).toBoxEnergyL4Realization.convectionForm I
            (S.forcedEnergyTrajectory2D hab Φ u₀ m t)
            (S.forcedEnergyTrajectory2D hab Φ u₀ m t)
            (S.energyProjection m φ) :=
        congrArg
          (fun z =>
            (boxLadyzhenskayaRealization I).toBoxEnergyL4Realization.convectionForm I
              (S.forcedEnergyTrajectory2D hab Φ u₀ m t)
              (S.forcedEnergyTrajectory2D hab Φ u₀ m t) z)
          (S.energySynthesis_testProjection_eq_partialProjection m φ)
  have hforcing : (∫ t in a..b,
      (S.forcedProblem2D m Φ u₀).forcing t (S.testProjection m φ) *
        eta.value t) =
      ∫ t in a..b, Φ.value t (S.energyProjection m φ) * eta.value t := by
    apply intervalIntegral.integral_congr
    intro t _ht
    dsimp only
    exact congrArg (fun r : ℝ => r * eta.value t)
      (S.forcedProblem2D_forcing_testProjection Φ u₀ m φ t)
  have hinitial :
      ⟪(S.forcedProblem2D m Φ u₀).initial, S.testProjection m φ⟫_ℝ =
        ⟪S.stateSynthesis m (S.stateInitialCoefficient m u₀),
          boxEnergyToState I φ⟫_ℝ := by
    change ⟪S.stateInitialCoefficient m u₀, S.testProjection m φ⟫_ℝ = _
    exact S.inner_testProjection_eq_state_inner m
      (S.stateInitialCoefficient m u₀) φ
  have hinitialMul := congrArg (fun r : ℝ => r * eta.value a) hinitial
  linarith only [hcoeff, hstate, hdiffusion, hconvection, hforcing,
    hinitialMul]

end ForcedTrajectories

section ForcedLimit

variable {a b : ℝ} (hab : a ≤ b) (Φ : BoxDualForcing I) (u₀ : BoxL2Sigma I)

@[simp]
theorem forcedFamily_projector :
    (S.forcedLeraySpectralCompactFamily2D hab Φ u₀).projector =
      S.stateProjection :=
  rfl

/-- The finite projectors of the forced box family are self-adjoint in the
pivot inner product. -/
theorem forced_projector_inner_eq (m : ℕ) (x y : BoxL2Sigma I) :
    ⟪(S.forcedLeraySpectralCompactFamily2D hab Φ u₀).projector m x, y⟫_ℝ =
      ⟪x, (S.forcedLeraySpectralCompactFamily2D hab Φ u₀).projector m y⟫_ℝ := by
  rw [S.forcedFamily_projector hab Φ u₀]
  exact
    GalerkinProjectorSequence.inner_finitePartialProjection_left_eq_right
      S.stateBasis (S.exhaustion.head m) x y

/-- The synchronized forced extraction determines a bounded weakly continuous
pivot-space representative of its strong state limit. -/
noncomputable def forcedWeaklyContinuousStateRepresentative
    (SW : (S.forcedLeraySpectralCompactFamily2D hab Φ u₀).StrongWeakPathSubsequence) :
    LeraySpectralCompactFamily.WeaklyContinuousStateRepresentative SW := by
  exact
    @LeraySpectralCompactFamily.StrongWeakPathSubsequence.weaklyContinuousStateRepresentative
      (Icc a b) (BoxH1ZeroSigma I) (BoxL2Sigma I)
      inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance
      inferInstance inferInstance (boxL2Sigma_completeSpace I)
      (boxL2Sigma_separableSpace I)
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)
      inferInstance
      (S.forcedLeraySpectralCompactFamily2D hab Φ u₀)
      SW (S.forced_projector_inner_eq hab Φ u₀)

set_option maxHeartbeats 3000000 in
/-- Every forced finite Galerkin state path starts from the canonical
orthogonal projection of the prescribed pivot-space datum. -/
theorem forced_statePath_initial (m : ℕ) :
    (S.forcedLeraySpectralCompactFamily2D hab Φ u₀).statePath m
      (⟨a, le_rfl, hab⟩ : Icc a b) =
        S.stateSynthesis m (S.stateInitialCoefficient m u₀) := by
  let G := S.forcedLeraySpectralCompactFamily2D hab Φ u₀
  change boxEnergyToState I (G.lift m (⟨a, le_rfl, hab⟩ : Icc a b)) = _
  rw [S.forcedFamily_lift_apply hab Φ u₀]
  change boxEnergyToState I
      (S.energySynthesis m (S.forcedCoefficientTrajectory2D hab Φ u₀ m a)) = _
  rw [show S.forcedCoefficientTrajectory2D hab Φ u₀ m a =
      S.stateInitialCoefficient m u₀ from
    S.canonicalSolution_initial m hab (S.forcedSolution2D hab m Φ u₀),
    S.boxEnergyToState_energySynthesis]

theorem forcedWeaklyContinuousStateRepresentative_initial
    (SW : (S.forcedLeraySpectralCompactFamily2D hab Φ u₀).StrongWeakPathSubsequence) :
    (S.forcedWeaklyContinuousStateRepresentative hab Φ u₀ SW).path
      (⟨a, le_rfl, hab⟩ : Icc a b) = u₀ := by
  let t₀ : Icc a b := ⟨a, le_rfl, hab⟩
  apply (S.forcedWeaklyContinuousStateRepresentative hab Φ u₀ SW).eq_of_statePath_tendsto
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
    S.forced_statePath_initial hab Φ u₀ (SW.subseq.idx j)

/-- State integral expressed with the forced state `Lp` representative. -/
theorem forced_stateLp_time_integral_eq
    (m : ℕ) (φ : BoxH1ZeroSigma I) (eta : IntervalTimeTest a b) :
    (∫ t : Icc a b,
      ⟪(S.forcedLeraySpectralCompactFamily2D hab Φ u₀).stateLp m t,
        boxEnergyToState I φ⟫_ℝ * eta.deriv t
      ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) =
      ∫ t in a..b,
        ⟪S.forcedStateTrajectory2D hab Φ u₀ m t,
          boxEnergyToState I φ⟫_ℝ * eta.deriv t := by
  let μ := SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b
  calc
    (∫ t : Icc a b,
        ⟪(S.forcedLeraySpectralCompactFamily2D hab Φ u₀).stateLp m t,
          boxEnergyToState I φ⟫_ℝ * eta.deriv t ∂μ) =
        ∫ t : Icc a b,
          ⟪S.forcedStateTrajectory2D hab Φ u₀ m t,
            boxEnergyToState I φ⟫_ℝ * eta.deriv t ∂μ := by
      apply integral_congr_ae
      filter_upwards [S.forced_stateLp_eq_trajectory_ae hab Φ u₀ m] with t ht
      rw [ht]
    _ = _ :=
      SmoothBoxVariationalGalerkinLevel.integral_intervalSubtypeMeasure hab
        (fun t =>
          ⟪S.forcedStateTrajectory2D hab Φ u₀ m t,
            boxEnergyToState I φ⟫_ℝ * eta.deriv t)

/-- Diffusion integral expressed with the forced energy `Lp`
representative. -/
theorem forced_energyLp_diffusion_time_integral_eq
    (m : ℕ) (φ : BoxH1ZeroSigma I) (eta : IntervalTimeTest a b) :
    (∫ t : Icc a b,
      boxGradientDiffusion I
        ((S.forcedLeraySpectralCompactFamily2D hab Φ u₀).energyLp m t)
        (S.energyProjection m φ) * eta.value t
      ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) =
      ∫ t in a..b,
        boxGradientDiffusion I (S.forcedEnergyTrajectory2D hab Φ u₀ m t)
          (S.energyProjection m φ) * eta.value t := by
  let μ := SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b
  calc
    (∫ t : Icc a b,
        boxGradientDiffusion I
          ((S.forcedLeraySpectralCompactFamily2D hab Φ u₀).energyLp m t)
          (S.energyProjection m φ) * eta.value t ∂μ) =
        ∫ t : Icc a b,
          boxGradientDiffusion I (S.forcedEnergyTrajectory2D hab Φ u₀ m t)
            (S.energyProjection m φ) * eta.value t ∂μ := by
      apply integral_congr_ae
      filter_upwards [S.forced_energyLp_eq_trajectory_ae hab Φ u₀ m] with t ht
      rw [ht]
    _ = _ :=
      SmoothBoxVariationalGalerkinLevel.integral_intervalSubtypeMeasure hab
        (fun t =>
          boxGradientDiffusion I (S.forcedEnergyTrajectory2D hab Φ u₀ m t)
            (S.energyProjection m φ) * eta.value t)

/-- Convection integral expressed with the forced energy `Lp`
representative. -/
theorem forced_energyLp_convection_time_integral_eq
    (m : ℕ) (φ : BoxH1ZeroSigma I) (eta : IntervalTimeTest a b) :
    (∫ t : Icc a b,
      (boxLadyzhenskayaRealization I).toBoxEnergyL4Realization.convectionForm I
        ((S.forcedLeraySpectralCompactFamily2D hab Φ u₀).energyLp m t)
        ((S.forcedLeraySpectralCompactFamily2D hab Φ u₀).energyLp m t)
        (S.energyProjection m φ) * eta.value t
      ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) =
      ∫ t in a..b,
        (boxLadyzhenskayaRealization I).toBoxEnergyL4Realization.convectionForm I
          (S.forcedEnergyTrajectory2D hab Φ u₀ m t)
          (S.forcedEnergyTrajectory2D hab Φ u₀ m t)
          (S.energyProjection m φ) * eta.value t := by
  let μ := SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b
  calc
    (∫ t : Icc a b,
        (boxLadyzhenskayaRealization I).toBoxEnergyL4Realization.convectionForm I
          ((S.forcedLeraySpectralCompactFamily2D hab Φ u₀).energyLp m t)
          ((S.forcedLeraySpectralCompactFamily2D hab Φ u₀).energyLp m t)
          (S.energyProjection m φ) * eta.value t ∂μ) =
        ∫ t : Icc a b,
          (boxLadyzhenskayaRealization I).toBoxEnergyL4Realization.convectionForm I
            (S.forcedEnergyTrajectory2D hab Φ u₀ m t)
            (S.forcedEnergyTrajectory2D hab Φ u₀ m t)
            (S.energyProjection m φ) * eta.value t ∂μ := by
      apply integral_congr_ae
      filter_upwards [S.forced_energyLp_eq_trajectory_ae hab Φ u₀ m] with t ht
      rw [ht]
    _ = _ :=
      SmoothBoxVariationalGalerkinLevel.integral_intervalSubtypeMeasure hab
        (fun t =>
          (boxLadyzhenskayaRealization I).toBoxEnergyL4Realization.convectionForm I
            (S.forcedEnergyTrajectory2D hab Φ u₀ m t)
            (S.forcedEnergyTrajectory2D hab Φ u₀ m t)
            (S.energyProjection m φ) * eta.value t)

set_option maxHeartbeats 4000000 in
/-- The finite forced physical equation written with the canonical `Lp`
representatives on the interval subtype. -/
theorem forced_timeTested_Lp_identity
    (m : ℕ) (φ : BoxH1ZeroSigma I) (eta : IntervalTimeTest a b)
    (heta_terminal : eta.value b = 0) :
    -(∫ t : Icc a b,
        ⟪(S.forcedLeraySpectralCompactFamily2D hab Φ u₀).stateLp m t,
          boxEnergyToState I φ⟫_ℝ * eta.deriv t
        ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) +
      (∫ t : Icc a b,
        boxGradientDiffusion I
          ((S.forcedLeraySpectralCompactFamily2D hab Φ u₀).energyLp m t)
          (S.energyProjection m φ) * eta.value t
        ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) +
      (∫ t : Icc a b,
        (boxLadyzhenskayaRealization I).toBoxEnergyL4Realization.convectionForm I
          ((S.forcedLeraySpectralCompactFamily2D hab Φ u₀).energyLp m t)
          ((S.forcedLeraySpectralCompactFamily2D hab Φ u₀).energyLp m t)
          (S.energyProjection m φ) * eta.value t
        ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) =
      ⟪S.stateSynthesis m (S.stateInitialCoefficient m u₀),
          boxEnergyToState I φ⟫_ℝ * eta.value a +
        ∫ t : Icc a b, Φ.value (t : ℝ) (S.energyProjection m φ) * eta.value t
          ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b := by
  have hstate := S.forced_stateLp_time_integral_eq hab Φ u₀ m φ eta
  have hdiffusion :=
    S.forced_energyLp_diffusion_time_integral_eq hab Φ u₀ m φ eta
  have hconvection :=
    S.forced_energyLp_convection_time_integral_eq hab Φ u₀ m φ eta
  have hforcing :=
    SmoothBoxVariationalGalerkinLevel.integral_intervalSubtypeMeasure hab
      (fun t => Φ.value t (S.energyProjection m φ) * eta.value t)
  have hphysical :=
    S.forcedSolution2D_timeTested_physical_identity hab Φ u₀ m φ eta
      heta_terminal
  linarith only [hphysical, hstate, hdiffusion, hconvection, hforcing]

/-- The reconstructed forced initial states pass to the prescribed initial
datum in every fixed energy test pairing. -/
theorem forced_initialPairing_tendsto
    (SW : (S.forcedLeraySpectralCompactFamily2D hab Φ u₀).StrongWeakSubsequence)
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

set_option maxHeartbeats 6000000 in
/-- The synchronized forced limit satisfies the forced box equation against
every spatial energy test and terminally vanishing Leray time test. -/
theorem forced_limit_timeTested_identity
    (SW : (S.forcedLeraySpectralCompactFamily2D hab Φ u₀).StrongWeakSubsequence)
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
      ⟪u₀, boxEnergyToState I φ⟫_ℝ * eta.value a +
        ∫ t : Icc a b, Φ.value (t : ℝ) φ * eta.value t
          ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b := by
  let G := S.forcedLeraySpectralCompactFamily2D hab Φ u₀
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
      boxEnergyToState I φ⟫_ℝ * eta.value a +
      ∫ t : Icc a b,
        Φ.value (t : ℝ) (S.energyProjection (SW.subseq.idx k) φ) *
          eta.value t ∂μ
  let rhsLimit : ℝ :=
    ⟪u₀, boxEnergyToState I φ⟫_ℝ * eta.value a +
      ∫ t : Icc a b, Φ.value (t : ℝ) φ * eta.value t ∂μ
  have hstate := boxLeray_stateDerivativeIntegral_tendsto G SW φ eta
  have hdiffusion := S.boxLeray_diffusionIntegral_tendsto G SW φ eta
  have hconvection := S.boxLeray_convectionIntegral_tendsto G rfl SW φ eta
  have hleft : Tendsto lhsSeq atTop (nhds lhsLimit) := by
    dsimp only [lhsSeq, lhsLimit, G, μ]
    exact (hstate.neg.add hdiffusion).add hconvection
  have hproj : Tendsto
      (fun k => S.energyProjection (SW.subseq.idx k) φ) atTop (nhds φ) :=
    (GalerkinProjectorSequence.finitePartialProjection_tendsto
      S.energyBasis S.exhaustion φ).comp
      SW.subseq.strictMono_idx.tendsto_atTop
  have hforce := Φ.forcing_test_integral_tendsto eta.toIntervalTimeTest hproj
  have hinit := S.forced_initialPairing_tendsto hab Φ u₀ SW φ
    eta.toIntervalTimeTest
  have hright : Tendsto rhsSeq atTop (nhds rhsLimit) := by
    dsimp only [rhsSeq, rhsLimit, μ]
    exact hinit.add hforce
  have hfinite (k : ℕ) : lhsSeq k = rhsSeq k := by
    dsimp only [lhsSeq, rhsSeq, G, μ]
    exact S.forced_timeTested_Lp_identity hab Φ u₀
      (SW.subseq.idx k) φ eta.toIntervalTimeTest heta_terminal
  have hseq : lhsSeq = rhsSeq := funext hfinite
  have hleft' : Tendsto rhsSeq atTop (nhds lhsLimit) := by
    rw [← hseq]
    exact hleft
  have hlimit : lhsLimit = rhsLimit := tendsto_nhds_unique hleft' hright
  simpa only [lhsLimit, rhsLimit, μ] using hlimit

end ForcedLimit
end BoxCompactSpectralRepresentation

end
