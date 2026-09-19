import PDEIdeas.BoxLerayWeakCompactness
import PDEIdeas.QuadraticWeakFormLimit
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Ladyzhenskaya compactness at the box limit

The two-dimensional Ladyzhenskaya inequality upgrades simultaneous strong
`L2_t H` and bounded `L2_t V` control to strong `L2_t L4_x` convergence.
This is the nonlinear compactness channel for the concrete box convection
form.
-/

open Filter MeasureTheory
open scoped ENNReal

noncomputable section

local instance box_limit_fact_one_le_four : Fact (1 ≤ (4 : ℝ≥0∞)) :=
  ⟨by norm_num⟩

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 500000

namespace MeasureTheory.Lp

variable {Time E : Type*} [MeasurableSpace Time]
    [NormedAddCommGroup E] {μ : Measure Time}

/-- The square of an `L2` norm is the integral of the pointwise squared
norm, for arbitrary normed targets. -/
theorem norm_two_sq_eq_integral_norm_sq
    (f : Lp E (2 : ℝ≥0∞) μ) :
    ‖f‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂μ := by
  rw [Lp.norm_def, MeasureTheory.toReal_eLpNorm (Lp.aestronglyMeasurable f)]
  rw [MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
    (by norm_num) (by norm_num) (Lp.aestronglyMeasurable f)]
  norm_num
  rw [← Real.sqrt_eq_rpow]
  exact Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)

variable {F : Type*} [NormedAddCommGroup F]

/-- Cauchy--Schwarz written directly in terms of two `L2` norms. -/
theorem integral_norm_mul_norm_le
    (f : Lp E (2 : ℝ≥0∞) μ) (g : Lp F (2 : ℝ≥0∞) μ) :
    ∫ t, ‖f t‖ * ‖g t‖ ∂μ ≤ ‖f‖ * ‖g‖ := by
  have hf2 : MemLp (fun t => ‖f t‖) (ENNReal.ofReal 2) μ := by
    simpa using (Lp.memLp f).norm
  have hg2 : MemLp (fun t => ‖g t‖) (ENNReal.ofReal 2) μ := by
    simpa using (Lp.memLp g).norm
  have hCS := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
    (μ := μ) Real.HolderConjugate.two_two hf2 hg2
  have hCS0 :
      ∫ t, ‖f t‖ * ‖g t‖ ∂μ ≤
        (∫ t, ‖f t‖ ^ 2 ∂μ) ^ (1 / 2 : ℝ) *
          (∫ t, ‖g t‖ ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
    simpa only [norm_norm, Real.rpow_two] using hCS
  rw [← norm_two_sq_eq_integral_norm_sq f,
    ← norm_two_sq_eq_integral_norm_sq g] at hCS0
  norm_num at hCS0
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
    Real.sqrt_sq (norm_nonneg f), Real.sqrt_sq (norm_nonneg g)] at hCS0
  exact hCS0

end MeasureTheory.Lp

variable {Time : Type*} [MeasurableSpace Time]
    {μ : Measure Time}

variable {V H X : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A pointwise interpolation inequality integrates to the corresponding
space-time `L2` estimate. -/
theorem norm_compLpL_sq_le_of_pointwise_interpolation
    (A : V →L[ℝ] X) (J : V →L[ℝ] H)
    (C : ℝ) (hC : 0 ≤ C)
    (hpointwise : ∀ v, ‖A v‖ ^ 2 ≤ C * ‖J v‖ * ‖v‖)
    (w : Lp V (2 : ℝ≥0∞) μ) :
    ‖A.compLpL 2 μ w‖ ^ 2 ≤ C * ‖J.compLpL 2 μ w‖ * ‖w‖ := by
  let wX := A.compLpL 2 μ w
  let wH := J.compLpL 2 μ w
  have hleft : Integrable (fun t => ‖wX t‖ ^ 2) μ :=
    (Lp.memLp wX).norm.integrable_sq
  have hprod : Integrable (fun t => ‖wH t‖ * ‖w t‖) μ := by
    simpa only [Pi.mul_apply, norm_norm] using
      (Lp.memLp wH).norm.integrable_mul (Lp.memLp w).norm
  have hright : Integrable (fun t => C * ‖wH t‖ * ‖w t‖) μ := by
    refine (hprod.const_mul C).congr ?_
    filter_upwards with t
    ring
  have hpoint : ∀ᵐ t ∂μ, ‖wX t‖ ^ 2 ≤ C * ‖wH t‖ * ‖w t‖ := by
    filter_upwards [A.coeFn_compLpL w, J.coeFn_compLpL w] with t hA hJ
    rw [show wX t = A (w t) from hA, show wH t = J (w t) from hJ]
    exact hpointwise (w t)
  have hmono :
      ∫ t, ‖wX t‖ ^ 2 ∂μ ≤ ∫ t, C * ‖wH t‖ * ‖w t‖ ∂μ :=
    integral_mono_ae hleft hright hpoint
  have hCS : ∫ t, ‖wH t‖ * ‖w t‖ ∂μ ≤ ‖wH‖ * ‖w‖ :=
    Lp.integral_norm_mul_norm_le wH w
  rw [Lp.norm_two_sq_eq_integral_norm_sq]
  change ∫ t, ‖wX t‖ ^ 2 ∂μ ≤ C * ‖wH‖ * ‖w‖
  calc
    ∫ t, ‖wX t‖ ^ 2 ∂μ ≤ ∫ t, C * ‖wH t‖ * ‖w t‖ ∂μ := hmono
    _ = C * ∫ t, ‖wH t‖ * ‖w t‖ ∂μ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      ring
    _ ≤ C * (‖wH‖ * ‖w‖) := mul_le_mul_of_nonneg_left hCS hC
    _ = C * ‖wH‖ * ‖w‖ := by ring

variable {I : BoxIntegral.Box (Fin 2)}

/-- Pointwise two-dimensional Ladyzhenskaya realization lifted to the time
`L2` space. -/
noncomputable def boxLadyzhenskayaTimeMap
    (L : BoxLadyzhenskayaRealization I) :
    Lp (BoxH1ZeroSigma I) (2 : ℝ≥0∞) μ →L[ℝ]
      Lp (BoxVelocityL4 I) (2 : ℝ≥0∞) μ :=
  L.toLp4.compLpL 2 μ

/-- The box energy-to-state embedding lifted to the time `L2` space. -/
noncomputable def boxEnergyTimeStateMap :
    Lp (BoxH1ZeroSigma I) (2 : ℝ≥0∞) μ →L[ℝ]
      Lp (BoxL2Sigma I) (2 : ℝ≥0∞) μ :=
  (boxEnergyToState I).compLpL 2 μ

/-- Space-time Ladyzhenskaya interpolation. -/
theorem norm_boxLadyzhenskayaTimeMap_sq_le
    (L : BoxLadyzhenskayaRealization I)
    (w : Lp (BoxH1ZeroSigma I) (2 : ℝ≥0∞) μ) :
    ‖boxLadyzhenskayaTimeMap (I := I) (μ := μ) L w‖ ^ 2 ≤
      L.constant *
        ‖boxEnergyTimeStateMap (I := I) (μ := μ) w‖ * ‖w‖ := by
  apply norm_compLpL_sq_le_of_pointwise_interpolation
    L.toLp4 (boxEnergyToState I) L.constant L.constant_nonneg
  intro v
  exact (L.l4_sq_le v).trans
    (mul_le_mul_of_nonneg_left
      (norm_boxEnergyGradient_le I v)
      (mul_nonneg L.constant_nonneg (norm_nonneg _)))

/-- The spatial box convection form with its two velocity arguments adjacent
and the gradient test in the last slot. -/
noncomputable def boxLpConvectionTested :
    BoxVelocityL4 I →L[ℝ]
      BoxVelocityL4 I →L[ℝ] BoxGradientL2 I →L[ℝ] ℝ :=
  ((ContinuousLinearMap.flipₗᵢ ℝ
    (BoxGradientL2 I) (BoxVelocityL4 I) ℝ).toLinearIsometry.toContinuousLinearMap).comp
      (boxLpConvection I)

@[simp]
theorem boxLpConvectionTested_apply
    (u w : BoxVelocityL4 I) (G : BoxGradientL2 I) :
    boxLpConvectionTested (I := I) u w G = boxLpConvection I u G w :=
  rfl

section StrongInterpolation

variable {Time V H X : Type*}
    [PseudoMetricSpace Time] [CompactSpace Time]
    [MeasurableSpace Time] [BorelSpace Time] [SecondCountableTopology Time]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {μ : Measure Time} [IsFiniteMeasure μ]

namespace LeraySpectralCompactFamily.StrongWeakSubsequence

variable {G : LeraySpectralCompactFamily
  (I := Time) (V := V) (H := H) (μ := μ)}

omit [CompactSpace Time] [CompleteSpace V] [CompleteSpace H] in
/-- A pointwise interpolation estimate upgrades the simultaneous
strong-state/weak-energy extraction to strong convergence in the
interpolated space. -/
theorem interpolatedTimeMap_tendsto
    (S : G.StrongWeakSubsequence)
    (A : V →L[ℝ] X) (C : ℝ) (hC : 0 ≤ C)
    (hpointwise : ∀ v, ‖A v‖ ^ 2 ≤ C * ‖G.embed v‖ * ‖v‖) :
    Tendsto
      (fun k => A.compLpL 2 μ (G.energyLp (S.subseq.idx k)))
      atTop
      (nhds (A.compLpL 2 μ S.energyLimit)) := by
  let d : ℕ → Lp V (2 : ℝ≥0∞) μ :=
    fun k => G.energyLp (S.subseq.idx k) - S.energyLimit
  let J := G.embed.compLpL (2 : ℝ≥0∞) μ
  have hstateDiff (k : ℕ) :
      J (d k) = G.stateLp (S.subseq.idx k) - S.stateLimit := by
    calc
      J (d k) = J (G.energyLp (S.subseq.idx k)) - J S.energyLimit := by
        change J (G.energyLp (S.subseq.idx k) - S.energyLimit) = _
        rw [map_sub]
      _ = G.stateLp (S.subseq.idx k) - S.stateLimit :=
        congrArg₂ (· - ·)
          (G.stateLp_eq_embed_energyLp (S.subseq.idx k)).symm
          S.embed_energyLimit
  have hdBound (k : ℕ) :
      ‖d k‖ ≤ G.liftLpRadius + ‖S.energyLimit‖ := by
    calc
      ‖d k‖ ≤ ‖G.energyLp (S.subseq.idx k)‖ + ‖S.energyLimit‖ :=
        norm_sub_le _ _
      _ ≤ G.liftLpRadius + ‖S.energyLimit‖ := by
        apply add_le_add
        · simpa only [LeraySpectralCompactFamily.energyLp] using
            G.liftLp_bound (S.subseq.idx k)
        · exact le_rfl
  let upper : ℕ → ℝ := fun k =>
    C * ‖G.stateLp (S.subseq.idx k) - S.stateLimit‖ *
      (G.liftLpRadius + ‖S.energyLimit‖)
  have hupper_nonneg (k : ℕ) : 0 ≤ upper k := by
    dsimp only [upper]
    exact mul_nonneg
      (mul_nonneg hC (norm_nonneg _))
      (add_nonneg G.liftLpRadius_nonneg (norm_nonneg _))
  have hsquare (k : ℕ) :
      ‖A.compLpL 2 μ (d k)‖ ^ 2 ≤ upper k := by
    have hinterp := norm_compLpL_sq_le_of_pointwise_interpolation
      A G.embed C hC hpointwise (d k)
    rw [hstateDiff k] at hinterp
    exact hinterp.trans
      (mul_le_mul_of_nonneg_left (hdBound k)
        (mul_nonneg hC (norm_nonneg _)))
  have hnormBound (k : ℕ) :
      ‖A.compLpL 2 μ (d k)‖ ≤ Real.sqrt (upper k) := by
    rw [← sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _),
      Real.sq_sqrt (hupper_nonneg k)]
    exact hsquare k
  have hstateNorm : Tendsto
      (fun k => ‖G.stateLp (S.subseq.idx k) - S.stateLimit‖)
      atTop (nhds 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp S.state_strong
  have hupper : Tendsto upper atTop (nhds 0) := by
    dsimp only [upper]
    simpa using
      ((tendsto_const_nhds.mul hstateNorm).mul tendsto_const_nhds)
  have hsqrt : Tendsto (fun k => Real.sqrt (upper k)) atTop (nhds 0) := by
    have hsqrtAt : Tendsto Real.sqrt (nhds 0) (nhds (Real.sqrt 0)) :=
      Real.continuous_sqrt.continuousAt
    simpa using hsqrtAt.comp hupper
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have hnorm : Tendsto
      (fun k => ‖A.compLpL 2 μ (d k)‖)
      atTop (nhds 0) := by
    apply squeeze_zero (fun _ => norm_nonneg _) hnormBound hsqrt
  simpa only [d, map_sub] using hnorm

/-- The interpolated extraction as a standard strong metric subsequence. -/
noncomputable def toInterpolatedStrongMetricSubsequence
    (S : G.StrongWeakSubsequence)
    (A : V →L[ℝ] X) (C : ℝ) (hC : 0 ≤ C)
    (hpointwise : ∀ v, ‖A v‖ ^ 2 ≤ C * ‖G.embed v‖ * ‖v‖) :
    StrongMetricSubsequence
      (fun n => A.compLpL 2 μ (G.energyLp n)) where
  subseq := S.subseq
  limit := A.compLpL 2 μ S.energyLimit
  converges := S.interpolatedTimeMap_tendsto A C hC hpointwise

end LeraySpectralCompactFamily.StrongWeakSubsequence

end StrongInterpolation

namespace BoxCompactSpectralRepresentation

variable {I : BoxIntegral.Box (Fin 2)}
    (S : BoxCompactSpectralRepresentation I)

/-- The canonical box family satisfies the pointwise interpolation estimate
with its own compact embedding. -/
theorem zeroForcingLeraySpectralCompactFamily2D_ladyzhenskaya_pointwise
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I)
    (L : BoxLadyzhenskayaRealization I)
    (v : BoxH1ZeroSigma I) :
    ‖L.toLp4 v‖ ^ 2 ≤ L.constant *
      ‖(S.zeroForcingLeraySpectralCompactFamily2D hab u₀).embed v‖ * ‖v‖ := by
  rw [S.zeroForcingLeraySpectralCompactFamily2D_embed]
  exact (L.l4_sq_le v).trans
    (mul_le_mul_of_nonneg_left
      (norm_boxEnergyGradient_le I v)
      (mul_nonneg L.constant_nonneg (norm_nonneg _)))

end BoxCompactSpectralRepresentation

end
