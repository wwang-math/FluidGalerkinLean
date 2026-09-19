import PDEIdeas.BoxSpectralGalerkinTower
import PDEIdeas.BoxConvectionClosure
import PDEIdeas.BoxL4Convection
import PDEIdeas.EnergyConvectionForm

/-!
# Variational problems on the box spectral tower

A bounded skew trilinear form on an energy space pulls back along any
continuous finite-dimensional energy lift. The resulting coefficient system
inherits diffusion nonnegativity and convection cancellation. Specializing
the construction to `BoxSpectralGalerkinTower` gives one coherent variational
problem at every spectral level.
-/

open InnerProductSpace MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

noncomputable section

variable {n : ℕ}

namespace BoxCompactSpectralRepresentation

section Level

variable {I : BoxIntegral.Box (Fin (n + 1))}
variable (S : BoxCompactSpectralRepresentation I) (m : ℕ)

local instance coeffNormedAddCommGroup :
    NormedAddCommGroup (S.CoefficientSpace m) :=
  S.coefficientSpaceNormedAddCommGroup m

local instance coeffInnerProductSpace :
    InnerProductSpace ℝ (S.CoefficientSpace m) :=
  S.coefficientSpaceInnerProductSpace m

local instance coeffFiniteDimensional :
    FiniteDimensional ℝ (S.CoefficientSpace m) :=
  S.coefficientSpaceFiniteDimensional m

local instance coeffCompleteSpace : CompleteSpace (S.CoefficientSpace m) :=
  S.coefficientSpaceCompleteSpace m

def pullbackConvection
    (C : EnergyConvectionForm (BoxH1ZeroSigma I)) :
    S.CoefficientSpace m →L[ℝ]
      S.CoefficientSpace m →L[ℝ] S.CoefficientSpace m →L[ℝ] ℝ :=
  C.form.trilinearCompSame (S.energySynthesis m)

@[simp]
theorem pullbackConvection_apply
    (C : EnergyConvectionForm (BoxH1ZeroSigma I))
    (u v w : S.CoefficientSpace m) :
    S.pullbackConvection m C u v w =
      C.form (S.energySynthesis m u) (S.energySynthesis m v)
        (S.energySynthesis m w) :=
  rfl

def pullbackDiffusion
    : S.CoefficientSpace m →L[ℝ] S.CoefficientSpace m →L[ℝ] ℝ :=
  (boxGradientDiffusion I).bilinearCompSame (S.energySynthesis m)

@[simp]
theorem pullbackDiffusion_apply
    (u v : S.CoefficientSpace m) :
    S.pullbackDiffusion m u v =
      boxGradientDiffusion I (S.energySynthesis m u) (S.energySynthesis m v) :=
  rfl

noncomputable def variationalSystem
    (C : EnergyConvectionForm (BoxH1ZeroSigma I)) :
    VariationalGalerkinSystem (S.CoefficientSpace m) :=
  C.pullbackSystem (S.energySynthesis m) (boxGradientDiffusion I)
    (boxGradientDiffusion_nonneg I)

def forcingPullback
    (forcing : ℝ → BoxH1ZeroSigma I →L[ℝ] ℝ)
  (t : ℝ) : S.CoefficientSpace m →L[ℝ] ℝ :=
  (forcing t).comp (S.energySynthesis m)

theorem forcingPullback_aestronglyMeasurable
    (forcing : ℝ → BoxH1ZeroSigma I →L[ℝ] ℝ)
    (μ : Measure ℝ)
    (hforcing : AEStronglyMeasurable forcing μ) :
    AEStronglyMeasurable (S.forcingPullback m forcing) μ := by
  have hcomp : Continuous
      (fun F : BoxH1ZeroSigma I →L[ℝ] ℝ =>
        F.comp (S.energySynthesis m)) := by
    fun_prop
  exact hcomp.comp_aestronglyMeasurable hforcing

noncomputable def variationalProblem
    (C : EnergyConvectionForm (BoxH1ZeroSigma I))
    (forcing : ℝ → BoxH1ZeroSigma I →L[ℝ] ℝ)
    (initial : S.CoefficientSpace m) :
    VariationalGalerkinProblem (S.CoefficientSpace m) where
  system := S.variationalSystem m C
  forcing := S.forcingPullback m forcing
  initial := initial

/-- Spectral variational system obtained directly from a bounded skew
convection form on the dense smooth graph core. -/
noncomputable def variationalSystemOfCoreConvection
    (B : smoothBoxGraphCore I →L[ℝ]
      smoothBoxGraphCore I →L[ℝ] smoothBoxGraphCore I →L[ℝ] ℝ)
    (hskew : ∀ u v w, B u v w = -B u w v) :
    VariationalGalerkinSystem (S.CoefficientSpace m) :=
  S.variationalSystem m (boxCoreEnergyConvectionForm I B hskew)

/-- Spectral variational problem with convection supplied on the dense smooth
graph core and forcing supplied in the common energy dual. -/
noncomputable def variationalProblemOfCoreConvection
    (B : smoothBoxGraphCore I →L[ℝ]
      smoothBoxGraphCore I →L[ℝ] smoothBoxGraphCore I →L[ℝ] ℝ)
    (hskew : ∀ u v w, B u v w = -B u w v)
    (forcing : ℝ → BoxH1ZeroSigma I →L[ℝ] ℝ)
    (initial : S.CoefficientSpace m) :
    VariationalGalerkinProblem (S.CoefficientSpace m) :=
  S.variationalProblem m (boxCoreEnergyConvectionForm I B hskew)
    forcing initial

/-- The spectral variational problem driven by the concrete `L4-L2-L4` box
transport form and a two-dimensional Ladyzhenskaya estimate. -/
noncomputable def variationalProblemOfLadyzhenskaya
    (L : BoxLadyzhenskayaRealization I)
    (forcing : ℝ → BoxH1ZeroSigma I →L[ℝ] ℝ)
    (initial : S.CoefficientSpace m) :
    VariationalGalerkinProblem (S.CoefficientSpace m) :=
  S.variationalProblem m L.toBoxEnergyL4Realization.energyConvectionForm
    forcing initial

theorem dualRHS_ladyzhenskaya_norm_le_with_one
    (L : BoxLadyzhenskayaRealization I)
    (forcing : ℝ → BoxH1ZeroSigma I →L[ℝ] ℝ)
    (initial : S.CoefficientSpace m)
    (t : ℝ) (u : S.CoefficientSpace m)
    (f : ℝ) (hf : 0 ≤ f)
    (hforcing : ∀ φ, ‖forcing t φ‖ ≤ f * ‖φ‖) :
    ‖(S.variationalProblemOfLadyzhenskaya m L forcing initial).dualRHS
        (S.testProjection m) t u‖ ≤
      1 * ‖S.energySynthesis m u‖ +
        (boxLpConvectionBound I * L.constant) *
          ‖boxEnergyToState I (S.energySynthesis m u)‖ *
          ‖S.energySynthesis m u‖ + f := by
  let P := S.variationalProblemOfLadyzhenskaya m L forcing initial
  let Eu := S.energySynthesis m u
  let cB := boxLpConvectionBound I * L.constant
  change ‖P.dualRHS (S.testProjection m) t u‖ ≤
    1 * ‖Eu‖ + cB * ‖boxEnergyToState I Eu‖ * ‖Eu‖ + f
  apply P.dualRHS_nse_norm_le (S.testProjection m) t u
    1 cB ‖boxEnergyToState I Eu‖ ‖Eu‖ f
  · norm_num
  · exact mul_nonneg (boxLpConvectionBound_pos I).le L.constant_nonneg
  · exact norm_nonneg _
  · exact norm_nonneg _
  · exact hf
  · intro φ
    change ‖boxGradientDiffusion I Eu
      (S.energySynthesis m (S.testProjection m φ))‖ ≤
        1 * ‖Eu‖ * ‖φ‖
    calc
      ‖boxGradientDiffusion I Eu
          (S.energySynthesis m (S.testProjection m φ))‖ ≤
          ‖Eu‖ * ‖S.energySynthesis m (S.testProjection m φ)‖ :=
        norm_boxGradientDiffusion_apply_le I Eu _
      _ ≤ ‖Eu‖ * ‖φ‖ := mul_le_mul_of_nonneg_left
        (S.norm_energySynthesis_testProjection_le m φ) (norm_nonneg Eu)
      _ = 1 * ‖Eu‖ * ‖φ‖ := by ring
  · intro φ
    change ‖L.toBoxEnergyL4Realization.convectionForm I Eu Eu
      (S.energySynthesis m (S.testProjection m φ))‖ ≤
        cB * ‖boxEnergyToState I Eu‖ * ‖Eu‖ * ‖φ‖
    calc
      ‖L.toBoxEnergyL4Realization.convectionForm I Eu Eu
          (S.energySynthesis m (S.testProjection m φ))‖ ≤
          cB * ‖boxEnergyToState I Eu‖ * ‖Eu‖ *
            ‖S.energySynthesis m (S.testProjection m φ)‖ :=
        L.convectionForm_diagonal_norm_le I Eu _
      _ ≤ cB * ‖boxEnergyToState I Eu‖ * ‖Eu‖ * ‖φ‖ :=
        mul_le_mul_of_nonneg_left
          (S.norm_energySynthesis_testProjection_le m φ)
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (boxLpConvectionBound_pos I).le L.constant_nonneg)
              (norm_nonneg _)) (norm_nonneg _))
  · intro φ
    change ‖forcing t (S.energySynthesis m (S.testProjection m φ))‖ ≤
      f * ‖φ‖
    calc
      ‖forcing t (S.energySynthesis m (S.testProjection m φ))‖ ≤
          f * ‖S.energySynthesis m (S.testProjection m φ)‖ :=
        hforcing _
      _ ≤ f * ‖φ‖ := mul_le_mul_of_nonneg_left
        (S.norm_energySynthesis_testProjection_le m φ) hf

/-- Uniform common-dual estimate for the Ladyzhenskaya spectral problem. -/
theorem dualRHS_ladyzhenskaya_norm_le
    (L : BoxLadyzhenskayaRealization I)
    (forcing : ℝ → BoxH1ZeroSigma I →L[ℝ] ℝ)
    (initial : S.CoefficientSpace m)
    (t : ℝ) (u : S.CoefficientSpace m)
    (f : ℝ) (hf : 0 ≤ f)
    (hforcing : ∀ φ, ‖forcing t φ‖ ≤ f * ‖φ‖) :
    ‖(S.variationalProblemOfLadyzhenskaya m L forcing initial).dualRHS
        (S.testProjection m) t u‖ ≤
      ‖S.energySynthesis m u‖ +
        (boxLpConvectionBound I * L.constant) *
          ‖boxEnergyToState I (S.energySynthesis m u)‖ *
          ‖S.energySynthesis m u‖ + f := by
  simpa only [one_mul] using
    S.dualRHS_ladyzhenskaya_norm_le_with_one m L forcing initial t u
      f hf hforcing

set_option synthInstance.maxHeartbeats 100000 in
/-- Squared common-dual estimate, ready for integration against the spectral
energy bound. -/
theorem dualRHS_ladyzhenskaya_norm_sq_le
    (L : BoxLadyzhenskayaRealization I)
    (forcing : ℝ → BoxH1ZeroSigma I →L[ℝ] ℝ)
    (initial : S.CoefficientSpace m)
    (t : ℝ) (u : S.CoefficientSpace m)
    (f H : ℝ) (hf : 0 ≤ f) (hH : 0 ≤ H)
    (hforcing : ∀ φ, ‖forcing t φ‖ ≤ f * ‖φ‖)
    (hstate : ‖boxEnergyToState I (S.energySynthesis m u)‖ ≤ H) :
    ‖(S.variationalProblemOfLadyzhenskaya m L forcing initial).dualRHS
        (S.testProjection m) t u‖ ^ 2 ≤
      2 * (1 + (boxLpConvectionBound I * L.constant) * H) ^ 2 *
          ‖S.energySynthesis m u‖ ^ 2 + 2 * f ^ 2 := by
  let cB := boxLpConvectionBound I * L.constant
  let h := ‖boxEnergyToState I (S.energySynthesis m u)‖
  let d := ‖S.energySynthesis m u‖
  have hcB : 0 ≤ cB :=
    mul_nonneg (boxLpConvectionBound_pos I).le L.constant_nonneg
  have hh : 0 ≤ h := norm_nonneg _
  have hd : 0 ≤ d := norm_nonneg _
  have hbase := S.dualRHS_ladyzhenskaya_norm_le m L forcing initial t u
    f hf hforcing
  have hconv : cB * h * d ≤ cB * H * d :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hstate hcB) hd
  have hlinear :
      ‖(S.variationalProblemOfLadyzhenskaya m L forcing initial).dualRHS
          (S.testProjection m) t u‖ ≤ (1 + cB * H) * d + f := by
    calc
      ‖(S.variationalProblemOfLadyzhenskaya m L forcing initial).dualRHS
          (S.testProjection m) t u‖ ≤ d + cB * h * d + f := hbase
      _ ≤ d + cB * H * d + f := by linarith
      _ = (1 + cB * H) * d + f := by ring
  have hcoef : 0 ≤ (1 + cB * H) * d :=
    mul_nonneg (add_nonneg zero_le_one (mul_nonneg hcB hH)) hd
  have hdual_nonneg :
      0 ≤ ‖(S.variationalProblemOfLadyzhenskaya m L forcing initial).dualRHS
        (S.testProjection m) t u‖ :=
    ContinuousLinearMap.opNorm_nonneg
      ((S.variationalProblemOfLadyzhenskaya m L forcing initial).dualRHS
        (S.testProjection m) t u)
  have hsq :
      ‖(S.variationalProblemOfLadyzhenskaya m L forcing initial).dualRHS
          (S.testProjection m) t u‖ ^ 2 ≤
        ((1 + cB * H) * d + f) ^ 2 :=
    (sq_le_sq₀ hdual_nonneg (add_nonneg hcoef hf)).2 hlinear
  calc
    ‖(S.variationalProblemOfLadyzhenskaya m L forcing initial).dualRHS
        (S.testProjection m) t u‖ ^ 2 ≤
        ((1 + cB * H) * d + f) ^ 2 := hsq
    _ ≤ 2 * ((1 + cB * H) * d) ^ 2 + 2 * f ^ 2 := by
      nlinarith [sq_nonneg (((1 + cB * H) * d) - f)]
    _ = 2 * (1 + cB * H) ^ 2 * d ^ 2 + 2 * f ^ 2 := by ring

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The energy-path and forcing-envelope bounds produce both the common-dual
`L2` property and its explicit uniform square-integral estimate. -/
theorem ladyzhenskaya_dual_memLp_and_integral_le
    {a b : ℝ} (hab : a ≤ b)
    (L : BoxLadyzhenskayaRealization I)
    (forcing : ℝ → BoxH1ZeroSigma I →L[ℝ] ℝ)
    (initial : S.CoefficientSpace m)
    (U : ℝ → S.CoefficientSpace m)
    (f : ℝ → ℝ) (H R F : ℝ)
    (hH : 0 ≤ H)
    (hf_nonneg : ∀ t ∈ Icc a b, 0 ≤ f t)
    (hforcing : ∀ t ∈ Icc a b, ∀ φ, ‖forcing t φ‖ ≤ f t * ‖φ‖)
    (hstate : ∀ t ∈ Icc a b,
      ‖boxEnergyToState I (S.energySynthesis m (U t))‖ ≤ H)
    (henergy : MemLp
      (fun t => S.energySynthesis m (U t)) 2
      (volume.restrict (Icc a b)))
    (henergy_sq :
      ∫ t in a..b, ‖S.energySynthesis m (U t)‖ ^ 2 ≤ R ^ 2)
    (hforce : MemLp f 2 (volume.restrict (Icc a b)))
    (hforce_sq : ∫ t in a..b, ‖f t‖ ^ 2 ≤ F ^ 2)
    (hdual_meas : AEStronglyMeasurable
      (fun t => (S.variationalProblemOfLadyzhenskaya m L forcing initial).dualRHS
        (S.testProjection m) t (U t))
      (volume.restrict (Icc a b))) :
    MemLp
        (fun t => (S.variationalProblemOfLadyzhenskaya m L forcing initial).dualRHS
          (S.testProjection m) t (U t))
        2 (volume.restrict (Icc a b)) ∧
      ∫ t in a..b,
          ‖(S.variationalProblemOfLadyzhenskaya m L forcing initial).dualRHS
            (S.testProjection m) t (U t)‖ ^ 2 ≤
        2 * (1 + (boxLpConvectionBound I * L.constant) * H) ^ 2 * R ^ 2 +
          2 * F ^ 2 := by
  let P := S.variationalProblemOfLadyzhenskaya m L forcing initial
  let Epath := fun t => S.energySynthesis m (U t)
  let D := fun t => P.dualRHS (S.testProjection m) t (U t)
  let cB := boxLpConvectionBound I * L.constant
  let A := 1 + cB * H
  have hcB : 0 ≤ cB :=
    mul_nonneg (boxLpConvectionBound_pos I).le L.constant_nonneg
  have hA : 0 ≤ A := add_nonneg zero_le_one (mul_nonneg hcB hH)
  have hmajor : MemLp (fun t => A * ‖Epath t‖ + f t) 2
      (volume.restrict (Icc a b)) :=
    (henergy.norm.const_mul A).add hforce
  have hDmeas : AEStronglyMeasurable D
      (volume.restrict (Icc a b)) := by
    simpa only [D, P] using hdual_meas
  have hdual : MemLp D 2 (volume.restrict (Icc a b)) := by
    apply MemLp.of_le (f := D) (g := fun t => A * ‖Epath t‖ + f t)
      hmajor hDmeas
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hbase := S.dualRHS_ladyzhenskaya_norm_le m L forcing initial t
      (U t) (f t) (hf_nonneg t ht) (hforcing t ht)
    have hconv :
        cB * ‖boxEnergyToState I (Epath t)‖ * ‖Epath t‖ ≤
          cB * H * ‖Epath t‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hstate t ht) hcB) (norm_nonneg _)
    have hbound : ‖D t‖ ≤ A * ‖Epath t‖ + f t := by
      calc
        ‖D t‖ ≤ ‖Epath t‖ +
            cB * ‖boxEnergyToState I (Epath t)‖ * ‖Epath t‖ + f t := hbase
        _ ≤ ‖Epath t‖ + cB * H * ‖Epath t‖ + f t := by linarith
        _ = A * ‖Epath t‖ + f t := by ring
    have hmajor_nonneg : 0 ≤ A * ‖Epath t‖ + f t :=
      add_nonneg (mul_nonneg hA (norm_nonneg _)) (hf_nonneg t ht)
    simpa only [Real.norm_eq_abs, abs_of_nonneg hmajor_nonneg] using hbound
  refine ⟨hdual, ?_⟩
  have hdual_norm : MemLp (fun t => ‖D t‖) 2
      (volume.restrict (Icc a b)) := MemLp.norm (f := D) hdual
  have hdual_sq_int : IntervalIntegrable (fun t => ‖D t‖ ^ 2) volume a b := by
    rw [intervalIntegrable_iff, uIoc_of_le hab]
    exact (hdual_norm.mono_measure
      (Measure.restrict_mono_set volume Ioc_subset_Icc_self)).integrable_sq
  have henergy_sq_int : IntervalIntegrable
      (fun t => ‖Epath t‖ ^ 2) volume a b := by
    rw [intervalIntegrable_iff, uIoc_of_le hab]
    exact (henergy.norm.mono_measure
      (Measure.restrict_mono_set volume Ioc_subset_Icc_self)).integrable_sq
  have hforce_sq_int : IntervalIntegrable (fun t => ‖f t‖ ^ 2) volume a b := by
    rw [intervalIntegrable_iff, uIoc_of_le hab]
    exact (hforce.norm.mono_measure
      (Measure.restrict_mono_set volume Ioc_subset_Icc_self)).integrable_sq
  have hrhs_int : IntervalIntegrable
      (fun t => 2 * A ^ 2 * ‖Epath t‖ ^ 2 + 2 * ‖f t‖ ^ 2)
      volume a b :=
    (henergy_sq_int.const_mul (2 * A ^ 2)).add
      (hforce_sq_int.const_mul 2)
  calc
    ∫ t in a..b, ‖D t‖ ^ 2 ≤
        ∫ t in a..b, 2 * A ^ 2 * ‖Epath t‖ ^ 2 + 2 * ‖f t‖ ^ 2 := by
      apply intervalIntegral.integral_mono_on hab hdual_sq_int hrhs_int
      intro t ht
      have hsquare := S.dualRHS_ladyzhenskaya_norm_sq_le m L forcing initial
        t (U t) (f t) H (hf_nonneg t ht) hH
        (hforcing t ht) (hstate t ht)
      simpa only [P, D, Epath, cB, A, Real.norm_eq_abs,
        abs_of_nonneg (hf_nonneg t ht)] using hsquare
    _ = 2 * A ^ 2 * (∫ t in a..b, ‖Epath t‖ ^ 2) +
          2 * (∫ t in a..b, ‖f t‖ ^ 2) := by
      rw [intervalIntegral.integral_add
        (henergy_sq_int.const_mul (2 * A ^ 2))
        (hforce_sq_int.const_mul 2),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
    _ ≤ 2 * A ^ 2 * R ^ 2 + 2 * F ^ 2 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left henergy_sq
          (mul_nonneg (by norm_num) (sq_nonneg A)))
        (mul_le_mul_of_nonneg_left hforce_sq (by norm_num))
    _ = 2 * (1 + (boxLpConvectionBound I * L.constant) * H) ^ 2 * R ^ 2 +
          2 * F ^ 2 := rfl

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- A measurable common forcing path supplies the Bochner measurability needed
by the integrated Ladyzhenskaya dual estimate. -/
theorem ladyzhenskaya_dual_memLp_and_integral_le_of_forcing_measurable
    {a b : ℝ} (hab : a ≤ b)
    (L : BoxLadyzhenskayaRealization I)
    (forcing : ℝ → BoxH1ZeroSigma I →L[ℝ] ℝ)
    (initial : S.CoefficientSpace m)
    (U : ℝ → S.CoefficientSpace m)
    (f : ℝ → ℝ) (H R F : ℝ)
    (hH : 0 ≤ H)
    (hf_nonneg : ∀ t ∈ Icc a b, 0 ≤ f t)
    (hforcing : ∀ t ∈ Icc a b, ∀ φ, ‖forcing t φ‖ ≤ f t * ‖φ‖)
    (hforcing_meas : AEStronglyMeasurable forcing
      (volume.restrict (Icc a b)))
    (hstate : ∀ t ∈ Icc a b,
      ‖boxEnergyToState I (S.energySynthesis m (U t))‖ ≤ H)
    (henergy : MemLp
      (fun t => S.energySynthesis m (U t)) 2
      (volume.restrict (Icc a b)))
    (henergy_sq :
      ∫ t in a..b, ‖S.energySynthesis m (U t)‖ ^ 2 ≤ R ^ 2)
    (hforce : MemLp f 2 (volume.restrict (Icc a b)))
    (hforce_sq : ∫ t in a..b, ‖f t‖ ^ 2 ≤ F ^ 2) :
    MemLp
        (fun t => (S.variationalProblemOfLadyzhenskaya m L forcing initial).dualRHS
          (S.testProjection m) t (U t))
        2 (volume.restrict (Icc a b)) ∧
      ∫ t in a..b,
          ‖(S.variationalProblemOfLadyzhenskaya m L forcing initial).dualRHS
            (S.testProjection m) t (U t)‖ ^ 2 ≤
        2 * (1 + (boxLpConvectionBound I * L.constant) * H) ^ 2 * R ^ 2 +
          2 * F ^ 2 := by
  let μ := volume.restrict (Icc a b)
  let P := S.variationalProblemOfLadyzhenskaya m L forcing initial
  have hforcing_pullback : AEStronglyMeasurable P.forcing μ := by
    change AEStronglyMeasurable (S.forcingPullback m forcing) μ
    exact S.forcingPullback_aestronglyMeasurable m forcing μ hforcing_meas
  have hU : AEStronglyMeasurable U μ := by
    have henergy_meas := henergy.1
    have hemb : Topology.IsEmbedding (S.energySynthesis m) :=
      (LinearMap.isClosedEmbedding_of_injective
        (LinearMap.ker_eq_bot.mpr (S.energySynthesis_injective m))).isEmbedding
    exact hemb.aestronglyMeasurable_comp_iff.mp henergy_meas
  have hdual_meas : AEStronglyMeasurable
      (fun t => P.dualRHS (S.testProjection m) t (U t)) μ :=
    P.dualRHS_aestronglyMeasurable (S.testProjection m) μ U hU
      hforcing_pullback
  exact S.ladyzhenskaya_dual_memLp_and_integral_le m hab L forcing initial
    U f H R F hH hf_nonneg hforcing hstate henergy henergy_sq hforce
    hforce_sq hdual_meas

end Level

end BoxCompactSpectralRepresentation

end
