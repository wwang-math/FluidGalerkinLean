import PDEIdeas.BoxSmoothLadyzhenskaya
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The two-dimensional box Ladyzhenskaya inequality

Mathlib's Gagliardo--Nirenberg--Sobolev theorem applied to `‖u‖²` gives the
mixed `L4-L2-H1` estimate for compactly supported `C¹` plane fields.  This
file identifies the Fréchet derivative with the stored Euclidean gradient,
transfers the estimate to finite combinations of the smooth box core, and
constructs the closed `BoxLadyzhenskayaRealization`.
-/

open MeasureTheory Set Real InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 400000

local instance compactLadyBoxFactOneLeTwo : Fact (1 ≤ (2 : ℝ≥0∞)) :=
  ⟨by norm_num⟩

local instance compactLadyBoxFactOneLeFour : Fact (1 ≤ (4 : ℝ≥0∞)) :=
  ⟨by norm_num⟩

def planeLadyConstant : ℝ≥0 :=
  2 * eLpNormLESNormFDerivOneConst
    (volume : Measure (Fin 2 → ℝ)) 2

theorem plane_lady_ennreal
    (u : (Fin 2 → ℝ) → BoxVelocityValue 1)
    (hu : ContDiff ℝ 1 u)
    (huc : HasCompactSupport u) :
    eLpNorm u 4 volume ^ (2 : ℝ) ≤
      planeLadyConstant * eLpNorm u 2 volume *
        eLpNorm (fderiv ℝ u) 2 volume := by
  let q : (Fin 2 → ℝ) → ℝ := fun x => ‖u x‖ ^ 2
  have hq : ContDiff ℝ 1 q := hu.norm_sq ℝ
  have hqc : HasCompactSupport q := by
    simpa [q, pow_two] using
      (huc.norm.mul_left (f := fun x => ‖u x‖))
  have hgns : eLpNorm q 2 volume ≤
      eLpNormLESNormFDerivOneConst
          (volume : Measure (Fin 2 → ℝ)) 2 *
        eLpNorm (fderiv ℝ q) 1 volume := by
    exact eLpNorm_le_eLpNorm_fderiv_one volume hq hqc
      (by rw [NNReal.holderConjugate_iff]; norm_num)
  have hfderiv : fderiv ℝ q = fun x =>
      (2 : ℝ) • (innerSL ℝ (u x)).comp (fderiv ℝ u x) := by
    funext x
    simpa [q, two_smul] using
      (hu.differentiable one_ne_zero x).hasFDerivAt.norm_sq.fderiv
  have hproduct : eLpNorm (fderiv ℝ q) 1 volume ≤
      2 * eLpNorm u 2 volume * eLpNorm (fderiv ℝ u) 2 volume := by
    rw [hfderiv]
    apply eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm
      hu.continuous.aestronglyMeasurable
      (hu.continuous_fderiv one_ne_zero).aestronglyMeasurable
      (fun x L => (2 : ℝ) • (innerSL ℝ x).comp L) 2
    filter_upwards with x
    calc
      ‖(2 : ℝ) • (innerSL ℝ (u x)).comp (fderiv ℝ u x)‖ =
          2 * ‖(innerSL ℝ (u x)).comp (fderiv ℝ u x)‖ := by
            rw [norm_smul,
              Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ 2 * (‖innerSL ℝ (u x)‖ * ‖fderiv ℝ u x‖) := by
        gcongr
        exact ContinuousLinearMap.opNorm_comp_le _ _
      _ = 2 * ‖u x‖ * ‖fderiv ℝ u x‖ := by
        rw [innerSL_apply_norm]
        ring
  calc
    eLpNorm u 4 volume ^ (2 : ℝ) = eLpNorm q 2 volume := by
      rw [show q = fun x => ‖u x‖ ^ (2 : ℝ) by simp [q],
        eLpNorm_norm_rpow u (by norm_num : (0 : ℝ) < 2)]
      norm_num
    _ ≤ eLpNormLESNormFDerivOneConst
          (volume : Measure (Fin 2 → ℝ)) 2 *
        eLpNorm (fderiv ℝ q) 1 volume := hgns
    _ ≤ eLpNormLESNormFDerivOneConst
          (volume : Measure (Fin 2 → ℝ)) 2 *
        (2 * eLpNorm u 2 volume * eLpNorm (fderiv ℝ u) 2 volume) := by
      gcongr
    _ = planeLadyConstant * eLpNorm u 2 volume *
        eLpNorm (fderiv ℝ u) 2 volume := by
      simp only [planeLadyConstant]
      push_cast
      ring

variable (I : BoxIntegral.Box (Fin 2))

def boxSmoothFieldCombination :
    SmoothBoxCombination I →ₗ[ℝ] ((Fin 2 → ℝ) → Fin 2 → ℝ) :=
  Finsupp.linearCombination ℝ (fun u : SmoothBoxEnergyField I => u.field)

def boxSmoothDerivativeCombination :
    SmoothBoxCombination I →ₗ[ℝ]
      ((Fin 2 → ℝ) → (Fin 2 → ℝ) →L[ℝ] Fin 2 → ℝ) :=
  Finsupp.linearCombination ℝ (fun u : SmoothBoxEnergyField I => u.derivative)

theorem boxSmoothFieldCombination_contDiff
    (c : SmoothBoxCombination I) :
    ContDiff ℝ 1 (boxSmoothFieldCombination I c) := by
  induction c using Finsupp.induction_linear with
  | zero => simpa using (contDiff_const : ContDiff ℝ 1 (0 : (Fin 2 → ℝ) → Fin 2 → ℝ))
  | add c d hc hd => simpa using hc.add hd
  | single u a =>
      simpa [boxSmoothFieldCombination] using
        u.contDiff_field.const_smul a

theorem boxSmoothFieldCombination_eq_zero_of_not_mem
    (c : SmoothBoxCombination I) {x : Fin 2 → ℝ}
    (hx : x ∉ BoxIntegral.Box.Icc I) :
    boxSmoothFieldCombination I c x = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [hc, hd]
  | single u a =>
      have hu : u.field x = 0 := by
        by_contra hux
        exact hx (u.support_field hux)
      simp [boxSmoothFieldCombination, hu]

theorem boxSmoothFieldCombination_support
    (c : SmoothBoxCombination I) :
    Function.support (boxSmoothFieldCombination I c) ⊆
      BoxIntegral.Box.Icc I := by
  intro x hx
  by_contra hnot
  exact hx (boxSmoothFieldCombination_eq_zero_of_not_mem I c hnot)

theorem boxSmoothFieldCombination_hasFDerivAt
    (c : SmoothBoxCombination I) {x : Fin 2 → ℝ}
    (hx : x ∈ interior (BoxIntegral.Box.Icc I)) :
    HasFDerivAt (boxSmoothFieldCombination I c)
      (boxSmoothDerivativeCombination I c x) x := by
  induction c using Finsupp.induction_linear with
  | zero =>
      simpa [boxSmoothFieldCombination, boxSmoothDerivativeCombination] using
        (hasFDerivAt_const (𝕜 := ℝ) (0 : Fin 2 → ℝ) x)
  | add c d hc hd =>
      simpa [boxSmoothFieldCombination, boxSmoothDerivativeCombination] using hc.add hd
  | single u a =>
      simpa [boxSmoothFieldCombination, boxSmoothDerivativeCombination] using
        (u.hasFDerivAt_field x hx).const_smul a

/-- The Euclidean realization of a coordinate vector. -/
def planeVelocityCLM :
    (Fin 2 → ℝ) →L[ℝ] BoxVelocityValue 1 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm

@[simp]
theorem planeVelocityCLM_apply (v : Fin 2 → ℝ) :
    planeVelocityCLM v = WithLp.toLp 2 v :=
  rfl

def planeGradientOperatorLinear :
    BoxGradientValue 1 →ₗ[ℝ]
      ((Fin 2 → ℝ) →L[ℝ] BoxVelocityValue 1) where
  toFun G := LinearMap.toContinuousLinearMap {
    toFun := fun h => WithLp.toLp 2 fun i => ∑ j, h j * G (i, j)
    map_add' := by
      intro h k
      ext i
      simp [add_mul, Finset.sum_add_distrib]
    map_smul' := by
      intro a h
      ext i
      simp
      ring }
  map_add' := by
    intro G H
    ext h i
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro a G
    ext h i
    simp
    ring

noncomputable def planeGradientOperator :
    BoxGradientValue 1 →L[ℝ]
      ((Fin 2 → ℝ) →L[ℝ] BoxVelocityValue 1) :=
  LinearMap.toContinuousLinearMap planeGradientOperatorLinear

def planeGradientValue
    (D : (Fin 2 → ℝ) →L[ℝ] Fin 2 → ℝ) :
    BoxGradientValue 1 :=
  WithLp.toLp 2 fun ij => D (Pi.single ij.2 1) ij.1

theorem planeGradientOperator_boxGradientValue
    (D : (Fin 2 → ℝ) →L[ℝ] Fin 2 → ℝ) :
    planeGradientOperator (planeGradientValue D) =
      planeVelocityCLM.comp D := by
  ext h i
  simp only [planeGradientOperator, planeGradientOperatorLinear,
    planeGradientValue, WithLp.ofLp_toLp, ContinuousLinearMap.comp_apply,
    planeVelocityCLM_apply]
  exact (continuousLinearMap_apply_eq_sum_basis D h i).symm

def boxSmoothVelocityValueCombination
    (c : SmoothBoxCombination I) :
    (Fin 2 → ℝ) → BoxVelocityValue 1 :=
  fun x => boxVelocityValue (boxSmoothFieldCombination I c) x

def boxSmoothGradientValueCombination
    (c : SmoothBoxCombination I) :
    (Fin 2 → ℝ) → BoxGradientValue 1 :=
  fun x => boxGradientValue (boxSmoothDerivativeCombination I c) x

theorem boxSmoothVelocityValueCombination_contDiff
    (c : SmoothBoxCombination I) :
    ContDiff ℝ 1 (boxSmoothVelocityValueCombination I c) := by
  exact planeVelocityCLM.contDiff.comp
    (boxSmoothFieldCombination_contDiff I c)

theorem boxSmoothVelocityValueCombination_support
    (c : SmoothBoxCombination I) :
    Function.support (boxSmoothVelocityValueCombination I c) ⊆
      BoxIntegral.Box.Icc I := by
  intro x hx
  by_contra hnot
  apply hx
  simp [boxSmoothVelocityValueCombination,
    boxSmoothFieldCombination_eq_zero_of_not_mem I c hnot,
    boxVelocityValue]

theorem boxSmoothVelocityValueCombination_hasCompactSupport
    (c : SmoothBoxCombination I) :
    HasCompactSupport (boxSmoothVelocityValueCombination I c) := by
  exact HasCompactSupport.of_support_subset_isCompact I.isCompact_Icc
    (boxSmoothVelocityValueCombination_support I c)

theorem fderiv_support_subset_of_support_subset_closed
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : E → F) {s : Set E} (hs : IsClosed s)
    (hu : Function.support u ⊆ s) :
    Function.support (fderiv ℝ u) ⊆ s := by
  intro x hx
  by_contra hxs
  have hzero : u =ᶠ[nhds x] (0 : E → F) := by
    filter_upwards [hs.isOpen_compl.mem_nhds hxs] with y hy
    simp only [Pi.zero_apply]
    by_contra huy
    exact hy (hu huy)
  have hfd := hzero.fderiv_eq (𝕜 := ℝ)
  simp only [fderiv_zero] at hfd
  exact hx hfd

theorem boxSmoothVelocityValueCombination_fderiv_support
    (c : SmoothBoxCombination I) :
    Function.support (fderiv ℝ (boxSmoothVelocityValueCombination I c)) ⊆
      BoxIntegral.Box.Icc I :=
  fderiv_support_subset_of_support_subset_closed
    (boxSmoothVelocityValueCombination I c) isClosed_Icc
    (boxSmoothVelocityValueCombination_support I c)

theorem fderiv_boxSmoothVelocityValueCombination_of_mem_interior
    (c : SmoothBoxCombination I) {x : Fin 2 → ℝ}
    (hx : x ∈ interior (BoxIntegral.Box.Icc I)) :
    fderiv ℝ (boxSmoothVelocityValueCombination I c) x =
      planeGradientOperator (boxSmoothGradientValueCombination I c x) := by
  have hraw := boxSmoothFieldCombination_hasFDerivAt I c hx
  have hvelocity : HasFDerivAt (boxSmoothVelocityValueCombination I c)
      (planeVelocityCLM.comp (boxSmoothDerivativeCombination I c x)) x := by
    exact planeVelocityCLM.hasFDerivAt.comp x hraw
  rw [hvelocity.fderiv]
  exact (planeGradientOperator_boxGradientValue
    (boxSmoothDerivativeCombination I c x)).symm

theorem coeFn_boxSmoothVelocityL4Combination
    (c : SmoothBoxCombination I) :
    (boxSmoothVelocityL4Combination I c :
        (Fin 2 → ℝ) → BoxVelocityValue 1) =ᵐ[BoxMeasure I]
      boxSmoothVelocityValueCombination I c := by
  induction c using Finsupp.induction_linear with
  | zero =>
      filter_upwards [Lp.coeFn_zero (BoxVelocityValue 1) 4 (BoxMeasure I)] with x hx
      change (boxSmoothVelocityL4Combination I 0) x = _
      rw [map_zero]
      rw [hx]
      simp [boxSmoothVelocityValueCombination, boxSmoothFieldCombination,
        boxVelocityValue]
  | add c d hc hd =>
      filter_upwards [Lp.coeFn_add
        (boxSmoothVelocityL4Combination I c)
        (boxSmoothVelocityL4Combination I d), hc, hd] with x hadd hc hd
      rw [map_add, hadd]
      change (boxSmoothVelocityL4Combination I c) x +
        (boxSmoothVelocityL4Combination I d) x = _
      rw [hc, hd]
      simp [boxSmoothVelocityValueCombination, boxSmoothFieldCombination,
        boxVelocityValue]
  | single u a =>
      filter_upwards [Lp.coeFn_smul a (u.velocityLp4 I),
        u.coeFn_velocityLp4 I] with x hsmul hu
      change (boxSmoothVelocityL4Combination I (Finsupp.single u a)) x = _
      rw [show boxSmoothVelocityL4Combination I (Finsupp.single u a) =
        a • u.velocityLp4 I by simp [boxSmoothVelocityL4Combination], hsmul]
      change a • u.velocityLp4 I x = _
      rw [hu]
      simp [boxSmoothVelocityValueCombination, boxSmoothFieldCombination,
        boxVelocityValue]

def boxSmoothVelocityL2Combination :
    SmoothBoxCombination I →ₗ[ℝ] BoxVelocityL2 I :=
  (boxEnergyVelocityProjection I).toLinearMap.comp
    (boxSmoothGraphCombination I)

def boxSmoothGradientL2Combination :
    SmoothBoxCombination I →ₗ[ℝ] BoxGradientL2 I :=
  (boxEnergyGradientProjection I).toLinearMap.comp
    (boxSmoothGraphCombination I)

theorem coeFn_boxSmoothVelocityL2Combination
    (c : SmoothBoxCombination I) :
    (boxSmoothVelocityL2Combination I c :
        (Fin 2 → ℝ) → BoxVelocityValue 1) =ᵐ[BoxMeasure I]
      boxSmoothVelocityValueCombination I c := by
  induction c using Finsupp.induction_linear with
  | zero =>
      filter_upwards [Lp.coeFn_zero (BoxVelocityValue 1) 2 (BoxMeasure I)] with x hx
      change (boxSmoothVelocityL2Combination I 0) x = _
      rw [map_zero, hx]
      simp [boxSmoothVelocityValueCombination, boxSmoothFieldCombination,
        boxVelocityValue]
  | add c d hc hd =>
      filter_upwards [Lp.coeFn_add
        (boxSmoothVelocityL2Combination I c)
        (boxSmoothVelocityL2Combination I d), hc, hd] with x hadd hc hd
      rw [map_add, hadd]
      change (boxSmoothVelocityL2Combination I c) x +
        (boxSmoothVelocityL2Combination I d) x = _
      rw [hc, hd]
      simp [boxSmoothVelocityValueCombination, boxSmoothFieldCombination,
        boxVelocityValue]
  | single u a =>
      filter_upwards [Lp.coeFn_smul a u.velocityLp,
        u.velocity_memLp.coeFn_toLp] with x hsmul hu
      rw [show boxSmoothVelocityL2Combination I (Finsupp.single u a) =
        a • u.velocityLp by
          simp [boxSmoothVelocityL2Combination, boxSmoothGraphCombination], hsmul]
      change a • u.velocityLp x = _
      change u.velocityLp x = boxVelocityValue u.field x at hu
      rw [hu]
      simp [boxSmoothVelocityValueCombination, boxSmoothFieldCombination,
        boxVelocityValue]

theorem coeFn_boxSmoothGradientL2Combination
    (c : SmoothBoxCombination I) :
    (boxSmoothGradientL2Combination I c :
        (Fin 2 → ℝ) → BoxGradientValue 1) =ᵐ[BoxMeasure I]
      boxSmoothGradientValueCombination I c := by
  induction c using Finsupp.induction_linear with
  | zero =>
      filter_upwards [Lp.coeFn_zero (BoxGradientValue 1) 2 (BoxMeasure I)] with x hx
      change (boxSmoothGradientL2Combination I 0) x = _
      rw [map_zero, hx]
      ext ij
      simp [boxSmoothGradientValueCombination, boxSmoothDerivativeCombination,
        boxGradientValue]
  | add c d hc hd =>
      filter_upwards [Lp.coeFn_add
        (boxSmoothGradientL2Combination I c)
        (boxSmoothGradientL2Combination I d), hc, hd] with x hadd hc hd
      rw [map_add, hadd]
      change (boxSmoothGradientL2Combination I c) x +
        (boxSmoothGradientL2Combination I d) x = _
      rw [hc, hd]
      ext ij
      simp [boxSmoothGradientValueCombination, boxSmoothDerivativeCombination,
        boxGradientValue]
  | single u a =>
      filter_upwards [Lp.coeFn_smul a u.gradientLp,
        u.gradient_memLp.coeFn_toLp] with x hsmul hu
      rw [show boxSmoothGradientL2Combination I (Finsupp.single u a) =
        a • u.gradientLp by
          simp [boxSmoothGradientL2Combination, boxSmoothGraphCombination], hsmul]
      change a • u.gradientLp x = _
      change u.gradientLp x = boxGradientValue u.derivative x at hu
      rw [hu]
      ext ij
      simp [boxSmoothGradientValueCombination, boxSmoothDerivativeCombination,
        boxGradientValue]

theorem ae_mem_interior_box :
    ∀ᵐ x ∂BoxMeasure I, x ∈ interior (BoxIntegral.Box.Icc I) := by
  have hset :
      interior (BoxIntegral.Box.Icc I) =
        Set.pi Set.univ fun i => Set.Ioo (I.lower i) (I.upper i) := by
    rw [BoxIntegral.Box.Icc_eq_pi,
      interior_pi_set (@Set.finite_univ (Fin 2) _)]
    simp
  have hae :
      interior (BoxIntegral.Box.Icc I) =ᵐ[volume]
        BoxIntegral.Box.Icc I := by
    rw [hset, BoxIntegral.Box.Icc_eq_pi]
    exact MeasureTheory.Measure.pi_Ioo_ae_eq_pi_Icc
  filter_upwards [ae_restrict_of_ae hae,
    ae_restrict_mem (by exact measurableSet_Icc)] with x hx hbox
  exact hx.mpr hbox

theorem fderiv_boxSmoothVelocityValueCombination_ae
    (c : SmoothBoxCombination I) :
    fderiv ℝ (boxSmoothVelocityValueCombination I c) =ᵐ[BoxMeasure I]
      fun x => planeGradientOperator
        (boxSmoothGradientValueCombination I c x) := by
  filter_upwards [ae_mem_interior_box I] with x hx
  exact fderiv_boxSmoothVelocityValueCombination_of_mem_interior I c hx

theorem norm_boxSmoothVelocityL4Combination_eq
    (c : SmoothBoxCombination I) :
    ‖boxSmoothVelocityL4Combination I c‖ =
      (eLpNorm (boxSmoothVelocityValueCombination I c) 4
        (BoxMeasure I)).toReal := by
  change (eLpNorm (boxSmoothVelocityL4Combination I c :
      (Fin 2 → ℝ) → BoxVelocityValue 1) 4 (BoxMeasure I)).toReal = _
  rw [eLpNorm_congr_ae (coeFn_boxSmoothVelocityL4Combination I c)]

theorem norm_boxSmoothVelocityL2Combination_eq
    (c : SmoothBoxCombination I) :
    ‖boxSmoothVelocityL2Combination I c‖ =
      (eLpNorm (boxSmoothVelocityValueCombination I c) 2
        (BoxMeasure I)).toReal := by
  change (eLpNorm (boxSmoothVelocityL2Combination I c :
      (Fin 2 → ℝ) → BoxVelocityValue 1) 2 (BoxMeasure I)).toReal = _
  rw [eLpNorm_congr_ae (coeFn_boxSmoothVelocityL2Combination I c)]

theorem norm_boxSmoothGradientL2Combination_eq
    (c : SmoothBoxCombination I) :
    ‖boxSmoothGradientL2Combination I c‖ =
      (eLpNorm (boxSmoothGradientValueCombination I c) 2
        (BoxMeasure I)).toReal := by
  change (eLpNorm (boxSmoothGradientL2Combination I c :
      (Fin 2 → ℝ) → BoxGradientValue 1) 2 (BoxMeasure I)).toReal = _
  rw [eLpNorm_congr_ae (coeFn_boxSmoothGradientL2Combination I c)]

theorem eLpNorm_fderiv_boxSmoothVelocityValueCombination_le
    (c : SmoothBoxCombination I) :
    eLpNorm (fderiv ℝ (boxSmoothVelocityValueCombination I c)) 2 volume ≤
      ‖planeGradientOperator‖₊ *
        eLpNorm (boxSmoothGradientValueCombination I c) 2 (BoxMeasure I) := by
  calc
    eLpNorm (fderiv ℝ (boxSmoothVelocityValueCombination I c)) 2 volume =
        eLpNorm (fderiv ℝ (boxSmoothVelocityValueCombination I c)) 2
          (BoxMeasure I) :=
      (eLpNorm_restrict_eq_of_support_subset
        (p := (2 : ℝ≥0∞)) (μ := volume)
        (s := BoxIntegral.Box.Icc I)
        (f := fderiv ℝ (boxSmoothVelocityValueCombination I c))
        (boxSmoothVelocityValueCombination_fderiv_support I c)).symm
    _ = eLpNorm (fun x => planeGradientOperator
          (boxSmoothGradientValueCombination I c x)) 2 (BoxMeasure I) :=
      eLpNorm_congr_ae
        (fderiv_boxSmoothVelocityValueCombination_ae I c)
    _ ≤ ‖planeGradientOperator‖₊ *
        eLpNorm (boxSmoothGradientValueCombination I c) 2 (BoxMeasure I) :=
      eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
        (Filter.Eventually.of_forall fun x => planeGradientOperator.le_opNNNorm
          (boxSmoothGradientValueCombination I c x)) 2

def boxSmoothLadyConstantNNReal : ℝ≥0 :=
  planeLadyConstant * ‖planeGradientOperator‖₊

theorem box_smooth_lady_ennreal
    (c : SmoothBoxCombination I) :
    eLpNorm (boxSmoothVelocityValueCombination I c) 4 (BoxMeasure I) ^
        (2 : ℝ) ≤
      boxSmoothLadyConstantNNReal *
        eLpNorm (boxSmoothVelocityValueCombination I c) 2 (BoxMeasure I) *
        eLpNorm (boxSmoothGradientValueCombination I c) 2 (BoxMeasure I) := by
  let v := boxSmoothVelocityValueCombination I c
  let G := boxSmoothGradientValueCombination I c
  have h4 : eLpNorm v 4 (BoxMeasure I) = eLpNorm v 4 volume :=
    eLpNorm_restrict_eq_of_support_subset
      (p := (4 : ℝ≥0∞)) (μ := volume)
      (s := BoxIntegral.Box.Icc I) (f := v)
      (boxSmoothVelocityValueCombination_support I c)
  have h2 : eLpNorm v 2 (BoxMeasure I) = eLpNorm v 2 volume :=
    eLpNorm_restrict_eq_of_support_subset
      (p := (2 : ℝ≥0∞)) (μ := volume)
      (s := BoxIntegral.Box.Icc I) (f := v)
      (boxSmoothVelocityValueCombination_support I c)
  have hbase := plane_lady_ennreal v
    (boxSmoothVelocityValueCombination_contDiff I c)
    (boxSmoothVelocityValueCombination_hasCompactSupport I c)
  have hderiv :=
    eLpNorm_fderiv_boxSmoothVelocityValueCombination_le I c
  change eLpNorm v 4 (BoxMeasure I) ^ (2 : ℝ) ≤
    boxSmoothLadyConstantNNReal * eLpNorm v 2 (BoxMeasure I) *
      eLpNorm G 2 (BoxMeasure I)
  calc
    eLpNorm v 4 (BoxMeasure I) ^ (2 : ℝ) =
        eLpNorm v 4 volume ^ (2 : ℝ) := by rw [h4]
    _ ≤ planeLadyConstant * eLpNorm v 2 volume *
        eLpNorm (fderiv ℝ v) 2 volume := hbase
    _ ≤ planeLadyConstant * eLpNorm v 2 volume *
        (‖planeGradientOperator‖₊ * eLpNorm G 2 (BoxMeasure I)) := by
      gcongr
    _ = boxSmoothLadyConstantNNReal * eLpNorm v 2 (BoxMeasure I) *
        eLpNorm G 2 (BoxMeasure I) := by
      rw [h2]
      simp only [boxSmoothLadyConstantNNReal]
      push_cast
      ring

def boxSmoothLadyConstant : ℝ := boxSmoothLadyConstantNNReal

theorem boxSmoothLadyConstant_nonneg : 0 ≤ boxSmoothLadyConstant :=
  NNReal.zero_le_coe

theorem box_smooth_lady_real
    (c : SmoothBoxCombination I) :
    ‖boxSmoothVelocityL4Combination I c‖ ^ 2 ≤
      boxSmoothLadyConstant * ‖boxSmoothVelocityL2Combination I c‖ *
        ‖boxSmoothGradientL2Combination I c‖ := by
  let v := boxSmoothVelocityValueCombination I c
  let G := boxSmoothGradientValueCombination I c
  have h := box_smooth_lady_ennreal I c
  have h2top : eLpNorm v 2 (BoxMeasure I) ≠ ∞ := by
    rw [← eLpNorm_congr_ae
      (coeFn_boxSmoothVelocityL2Combination I c)]
    exact Lp.eLpNorm_ne_top (boxSmoothVelocityL2Combination I c)
  have hGtop : eLpNorm G 2 (BoxMeasure I) ≠ ∞ := by
    rw [← eLpNorm_congr_ae
      (coeFn_boxSmoothGradientL2Combination I c)]
    exact Lp.eLpNorm_ne_top (boxSmoothGradientL2Combination I c)
  have hRtop :
      (boxSmoothLadyConstantNNReal : ℝ≥0∞) *
          eLpNorm v 2 (BoxMeasure I) * eLpNorm G 2 (BoxMeasure I) ≠ ∞ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.coe_ne_top h2top) hGtop
  have hreal := ENNReal.toReal_mono hRtop h
  rw [← ENNReal.toReal_rpow, ENNReal.toReal_mul,
    ENNReal.toReal_mul, Real.rpow_two] at hreal
  simp only [ENNReal.coe_toReal] at hreal
  rw [← norm_boxSmoothVelocityL4Combination_eq I c,
    ← norm_boxSmoothVelocityL2Combination_eq I c,
    ← norm_boxSmoothGradientL2Combination_eq I c] at hreal
  exact hreal

noncomputable def boxSmoothLadyzhenskayaEstimate :
    BoxSmoothLadyzhenskayaEstimate I where
  constant := boxSmoothLadyConstant
  constant_nonneg := boxSmoothLadyConstant_nonneg
  bound c := by
    change ‖boxSmoothVelocityL4Combination I c‖ ^ 2 ≤
      boxSmoothLadyConstant * ‖boxSmoothVelocityL2Combination I c‖ *
        ‖boxSmoothGradientL2Combination I c‖
    exact box_smooth_lady_real I c

noncomputable def boxLadyzhenskayaRealization :
    BoxLadyzhenskayaRealization I :=
  (boxSmoothLadyzhenskayaEstimate I).toBoxLadyzhenskayaRealization I

end
