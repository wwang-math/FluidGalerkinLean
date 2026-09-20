import PDEIdeas.BoxLadyzhenskayaInequality
import PDEIdeas.BoxWeakSobolev

/-!
# The Poincaré inequality on a two-dimensional box

Mathlib's Gagliardo--Nirenberg--Sobolev theorem applied to a compactly
supported `C¹` plane field bounds its `L²` norm by the `L¹` norm of its
Fréchet derivative.  On a box the derivative is supported in the compact
closure, so Hölder's inequality converts that `L¹` norm into an `L²` norm.
Transferring the resulting estimate along the smooth graph core and taking
closures gives

  `‖J_Q v‖ ≤ C_Q ‖G_Q v‖`

for every `v` in the closed energy space, hence the equivalence of the graph
norm with the gradient seminorm.  The consequence used by the Galerkin theory
is that an arbitrary energy-dual forcing functional is absorbed by the
diffusion form with a state-independent remainder.
-/

open MeasureTheory Set Real InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 400000

local instance boxPoincareFactOneLeTwo : Fact (1 ≤ (2 : ℝ≥0∞)) :=
  ⟨by norm_num⟩

/-- The Gagliardo--Nirenberg--Sobolev constant of the plane used below. -/
def planePoincareConstant : ℝ≥0 :=
  eLpNormLESNormFDerivOneConst (volume : Measure (Fin 2 → ℝ)) 2

/-- Gagliardo--Nirenberg--Sobolev in the plane: the `L²` norm of a compactly
supported `C¹` field is bounded by the `L¹` norm of its derivative. -/
theorem plane_poincare_ennreal
    (u : (Fin 2 → ℝ) → BoxVelocityValue 1)
    (hu : ContDiff ℝ 1 u)
    (huc : HasCompactSupport u) :
    eLpNorm u 2 volume ≤
      planePoincareConstant * eLpNorm (fderiv ℝ u) 1 volume := by
  have hfin : Module.finrank ℝ (Fin 2 → ℝ) = 2 := by
    simp
  have hconj : NNReal.HolderConjugate
      (Module.finrank ℝ (Fin 2 → ℝ)) (2 : ℝ≥0) := by
    rw [hfin]
    rw [NNReal.holderConjugate_iff]
    norm_num
  simpa only [planePoincareConstant] using
    eLpNorm_le_eLpNorm_fderiv_one (μ := (volume : Measure (Fin 2 → ℝ)))
      hu huc hconj

variable (I : BoxIntegral.Box (Fin 2))

private theorem boxPoincareMeasure_isFinite : IsFiniteMeasure (BoxMeasure I) := by
  rw [isFiniteMeasure_restrict]
  exact (I.measure_Icc_lt_top volume).ne

local instance boxPoincareFiniteMeasure : IsFiniteMeasure (BoxMeasure I) :=
  boxPoincareMeasure_isFinite I

/-- Extended-real Poincaré constant of the box. -/
def boxPoincareENNReal : ℝ≥0∞ :=
  (planePoincareConstant : ℝ≥0∞) *
    (volume (BoxIntegral.Box.Icc I)) ^ (1 / 2 : ℝ) *
    (‖planeGradientOperator‖₊ : ℝ≥0∞)

theorem boxPoincareENNReal_ne_top : boxPoincareENNReal I ≠ ∞ := by
  apply ENNReal.mul_ne_top
  · apply ENNReal.mul_ne_top ENNReal.coe_ne_top
    apply ENNReal.rpow_ne_top_of_nonneg (by norm_num)
    exact (I.measure_Icc_lt_top volume).ne
  · exact ENNReal.coe_ne_top

/-- Hölder's inequality on the compact box turns the `L¹` derivative bound
into an `L²` derivative bound. -/
theorem eLpNorm_fderiv_one_le_of_support_subset
    (v : (Fin 2 → ℝ) → BoxVelocityValue 1)
    (hsupp : Function.support (fderiv ℝ v) ⊆ BoxIntegral.Box.Icc I)
    (hmeas : AEStronglyMeasurable (fderiv ℝ v) (BoxMeasure I)) :
    eLpNorm (fderiv ℝ v) 1 volume ≤
      (volume (BoxIntegral.Box.Icc I)) ^ (1 / 2 : ℝ) *
        eLpNorm (fderiv ℝ v) 2 (BoxMeasure I) := by
  have hrestrict :
      eLpNorm (fderiv ℝ v) 1 volume =
        eLpNorm (fderiv ℝ v) 1 (BoxMeasure I) :=
    (eLpNorm_restrict_eq_of_support_subset
      (p := (1 : ℝ≥0∞)) (μ := volume)
      (s := BoxIntegral.Box.Icc I) (f := fderiv ℝ v) hsupp).symm
  have hholder :
      eLpNorm (fderiv ℝ v) 1 (BoxMeasure I) ≤
        eLpNorm (fderiv ℝ v) 2 (BoxMeasure I) *
          (BoxMeasure I) Set.univ ^
            (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) :=
    eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num) hmeas
  have huniv : (BoxMeasure I) Set.univ = volume (BoxIntegral.Box.Icc I) := by
    simp [BoxMeasure]
  rw [hrestrict]
  refine hholder.trans ?_
  rw [huniv]
  have hexp : (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) := by
    norm_num
  rw [hexp, mul_comm]

theorem box_smooth_poincare_ennreal (c : SmoothBoxCombination I) :
    eLpNorm (boxSmoothVelocityValueCombination I c) 2 (BoxMeasure I) ≤
      boxPoincareENNReal I *
        eLpNorm (boxSmoothGradientValueCombination I c) 2 (BoxMeasure I) := by
  set v := boxSmoothVelocityValueCombination I c with hv
  set G := boxSmoothGradientValueCombination I c with hG
  have hcontDiff : ContDiff ℝ 1 v :=
    boxSmoothVelocityValueCombination_contDiff I c
  have hcompact : HasCompactSupport v :=
    boxSmoothVelocityValueCombination_hasCompactSupport I c
  have h2 : eLpNorm v 2 (BoxMeasure I) = eLpNorm v 2 volume :=
    eLpNorm_restrict_eq_of_support_subset
      (p := (2 : ℝ≥0∞)) (μ := volume)
      (s := BoxIntegral.Box.Icc I) (f := v)
      (boxSmoothVelocityValueCombination_support I c)
  have hmeas : AEStronglyMeasurable (fderiv ℝ v) (BoxMeasure I) :=
    (hcontDiff.continuous_fderiv one_ne_zero).aestronglyMeasurable
  have hL1 := eLpNorm_fderiv_one_le_of_support_subset I v
    (boxSmoothVelocityValueCombination_fderiv_support I c) hmeas
  have hrestrict2 :
      eLpNorm (fderiv ℝ v) 2 (BoxMeasure I) = eLpNorm (fderiv ℝ v) 2 volume :=
    eLpNorm_restrict_eq_of_support_subset
      (p := (2 : ℝ≥0∞)) (μ := volume)
      (s := BoxIntegral.Box.Icc I) (f := fderiv ℝ v)
      (boxSmoothVelocityValueCombination_fderiv_support I c)
  have hL2 : eLpNorm (fderiv ℝ v) 2 (BoxMeasure I) ≤
      (‖planeGradientOperator‖₊ : ℝ≥0∞) * eLpNorm G 2 (BoxMeasure I) := by
    rw [hrestrict2]
    exact eLpNorm_fderiv_boxSmoothVelocityValueCombination_le I c
  calc
    eLpNorm v 2 (BoxMeasure I) = eLpNorm v 2 volume := h2
    _ ≤ planePoincareConstant * eLpNorm (fderiv ℝ v) 1 volume :=
      plane_poincare_ennreal v hcontDiff hcompact
    _ ≤ (planePoincareConstant : ℝ≥0∞) *
        ((volume (BoxIntegral.Box.Icc I)) ^ (1 / 2 : ℝ) *
          eLpNorm (fderiv ℝ v) 2 (BoxMeasure I)) := by
      gcongr
    _ ≤ (planePoincareConstant : ℝ≥0∞) *
        ((volume (BoxIntegral.Box.Icc I)) ^ (1 / 2 : ℝ) *
          ((‖planeGradientOperator‖₊ : ℝ≥0∞) *
            eLpNorm G 2 (BoxMeasure I))) := by
      gcongr
    _ = boxPoincareENNReal I * eLpNorm G 2 (BoxMeasure I) := by
      simp only [boxPoincareENNReal]
      ring

/-- Real-valued Poincaré constant of the box. -/
def boxPoincareConstant : ℝ := (boxPoincareENNReal I).toReal

theorem boxPoincareConstant_nonneg : 0 ≤ boxPoincareConstant I :=
  ENNReal.toReal_nonneg

theorem box_smooth_poincare_real (c : SmoothBoxCombination I) :
    ‖boxSmoothVelocityL2Combination I c‖ ≤
      boxPoincareConstant I * ‖boxSmoothGradientL2Combination I c‖ := by
  set v := boxSmoothVelocityValueCombination I c with hv
  set G := boxSmoothGradientValueCombination I c with hG
  have h := box_smooth_poincare_ennreal I c
  have hGtop : eLpNorm G 2 (BoxMeasure I) ≠ ∞ := by
    rw [hG, ← eLpNorm_congr_ae (coeFn_boxSmoothGradientL2Combination I c)]
    exact Lp.eLpNorm_ne_top (boxSmoothGradientL2Combination I c)
  have hRtop : boxPoincareENNReal I * eLpNorm G 2 (BoxMeasure I) ≠ ∞ :=
    ENNReal.mul_ne_top (boxPoincareENNReal_ne_top I) hGtop
  have hreal := ENNReal.toReal_mono hRtop h
  rw [ENNReal.toReal_mul] at hreal
  rw [← norm_boxSmoothVelocityL2Combination_eq I c,
    ← norm_boxSmoothGradientL2Combination_eq I c] at hreal
  exact hreal

/-- The Poincaré estimate for every point of the smooth graph core. -/
theorem boxPoincare_core
    (y : BoxEnergyAmbient I) (hy : y ∈ smoothBoxGraphCore I) :
    ‖boxEnergyVelocityProjection I y‖ ≤
      boxPoincareConstant I * ‖boxEnergyGradientProjection I y‖ := by
  have hrange : y ∈ LinearMap.range (boxSmoothGraphCombination I) := by
    rw [boxSmoothGraphCombination_range I]
    exact hy
  obtain ⟨c, hc⟩ := hrange
  subst hc
  exact box_smooth_poincare_real I c

/-- **Box Poincaré inequality.**  On the closed energy space the state norm
is controlled by the gradient norm. -/
theorem boxPoincare (v : BoxH1ZeroSigma I) :
    ‖boxEnergyToState I v‖ ≤
      boxPoincareConstant I * ‖boxEnergyGradient I v‖ := by
  have hclosed : IsClosed
      {y : BoxEnergyAmbient I |
        ‖boxEnergyVelocityProjection I y‖ ≤
          boxPoincareConstant I * ‖boxEnergyGradientProjection I y‖} := by
    apply isClosed_le
    · exact (boxEnergyVelocityProjection I).continuous.norm
    · exact continuous_const.mul (boxEnergyGradientProjection I).continuous.norm
  have hsubset :
      (closure (smoothBoxGraphCore I : Set (BoxEnergyAmbient I))) ⊆
        {y : BoxEnergyAmbient I |
          ‖boxEnergyVelocityProjection I y‖ ≤
            boxPoincareConstant I * ‖boxEnergyGradientProjection I y‖} := by
    apply closure_minimal _ hclosed
    intro y hy
    exact boxPoincare_core I y hy
  have hmem : (v : BoxEnergyAmbient I) ∈
      closure (smoothBoxGraphCore I : Set (BoxEnergyAmbient I)) := by
    simpa only [Submodule.topologicalClosure_coe] using v.property
  exact hsubset hmem

/-- The graph norm is controlled by the gradient norm alone. -/
theorem boxEnergy_norm_le_gradient (v : BoxH1ZeroSigma I) :
    ‖v‖ ≤
      Real.sqrt (1 + boxPoincareConstant I ^ 2) * ‖boxEnergyGradient I v‖ := by
  have hC := boxPoincareConstant_nonneg I
  have hgrad : (0 : ℝ) ≤ ‖boxEnergyGradient I v‖ := norm_nonneg _
  have hsq : ‖v‖ ^ 2 ≤
      (1 + boxPoincareConstant I ^ 2) * ‖boxEnergyGradient I v‖ ^ 2 := by
    rw [boxEnergy_norm_sq_eq_state_add_gradient I v]
    have hstate := boxPoincare I v
    have hstate_sq : ‖boxEnergyToState I v‖ ^ 2 ≤
        boxPoincareConstant I ^ 2 * ‖boxEnergyGradient I v‖ ^ 2 := by
      have := mul_self_le_mul_self (norm_nonneg (boxEnergyToState I v)) hstate
      calc
        ‖boxEnergyToState I v‖ ^ 2 =
            ‖boxEnergyToState I v‖ * ‖boxEnergyToState I v‖ := sq _
        _ ≤ (boxPoincareConstant I * ‖boxEnergyGradient I v‖) *
              (boxPoincareConstant I * ‖boxEnergyGradient I v‖) := this
        _ = boxPoincareConstant I ^ 2 * ‖boxEnergyGradient I v‖ ^ 2 := by ring
    nlinarith [hstate_sq]
  have hK : (0 : ℝ) ≤ 1 + boxPoincareConstant I ^ 2 := by positivity
  have hRHS : (0 : ℝ) ≤
      Real.sqrt (1 + boxPoincareConstant I ^ 2) * ‖boxEnergyGradient I v‖ :=
    mul_nonneg (Real.sqrt_nonneg _) hgrad
  have hRHS_sq :
      (Real.sqrt (1 + boxPoincareConstant I ^ 2) *
          ‖boxEnergyGradient I v‖) ^ 2 =
        (1 + boxPoincareConstant I ^ 2) * ‖boxEnergyGradient I v‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hK]
  exact (sq_le_sq₀ (norm_nonneg v) hRHS).mp (by rw [hRHS_sq]; exact hsq)

set_option maxHeartbeats 1000000 in
/-- **State-independent absorption of an energy-dual forcing functional.**
The forcing is measured by any real majorant of its dual norm.  This is the
hypothesis shape required by energy-driven continuation of the
finite-dimensional Galerkin systems. -/
theorem boxForcing_work_le
    (F : BoxH1ZeroSigma I →L[ℝ] ℝ) (f : ℝ) (hf : 0 ≤ f)
    (hbound : ∀ w : BoxH1ZeroSigma I, ‖F w‖ ≤ f * ‖w‖)
    (v : BoxH1ZeroSigma I) :
    2 * F v ≤
      (1 + boxPoincareConstant I ^ 2) * f ^ 2 +
        boxGradientDiffusion I v v := by
  have hKnonneg : (0 : ℝ) ≤ 1 + boxPoincareConstant I ^ 2 := by positivity
  have h1 : F v ≤ f * ‖v‖ := by
    have hnorm : |F v| ≤ f * ‖v‖ := by
      simpa only [Real.norm_eq_abs] using hbound v
    exact (le_abs_self _).trans hnorm
  have h2 : ‖v‖ ≤
      Real.sqrt (1 + boxPoincareConstant I ^ 2) *
        ‖boxEnergyGradient I v‖ :=
    boxEnergy_norm_le_gradient I v
  have hmul : f * ‖v‖ ≤
      f * (Real.sqrt (1 + boxPoincareConstant I ^ 2) *
        ‖boxEnergyGradient I v‖) :=
    mul_le_mul_of_nonneg_left h2 hf
  have hyoung := two_mul_le_add_sq
    (Real.sqrt (1 + boxPoincareConstant I ^ 2) * f)
    ‖boxEnergyGradient I v‖
  have hsq : (Real.sqrt (1 + boxPoincareConstant I ^ 2) * f) ^ 2 =
      (1 + boxPoincareConstant I ^ 2) * f ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hKnonneg]
  rw [boxGradientDiffusion_self I v, ← hsq]
  linarith

end
