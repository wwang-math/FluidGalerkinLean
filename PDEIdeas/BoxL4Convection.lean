import PDEIdeas.BoxConvectionClosure
import Mathlib.MeasureTheory.Function.Holder

/-!
# The box convection form from the `L4-L2-L4` estimate

A continuous realization of the box energy space in `L4` combines with the
closed `L2` gradient to define the transport integral on the entire energy
space. Holder's inequality gives continuity. Transport integration by parts
gives skew symmetry on smooth graph generators; linear span and density then
give skew symmetry on the closed energy space.
-/

open MeasureTheory InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

local instance holder_4_4_2 :
    ENNReal.HolderTriple (4 : ℝ≥0∞) 4 2 where
  inv_add_inv_eq_inv := by
    have h4 : (4 : ℝ≥0∞) = 2 * 2 := by norm_num
    rw [h4, ENNReal.mul_inv (by norm_num) (by norm_num)]
    calc
      (2 : ℝ≥0∞)⁻¹ * 2⁻¹ + 2⁻¹ * 2⁻¹ =
          (2 * 2⁻¹) * 2⁻¹ := by ring
      _ = 2⁻¹ := by rw [ENNReal.mul_inv_cancel] <;> norm_num

local instance fact_one_le_four : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

variable {n : ℕ}

/-- Pointwise tensor product `w ⊗ u`, represented as a Euclidean matrix. -/
noncomputable def boxVelocityOuter :
    BoxVelocityValue n →L[ℝ] BoxVelocityValue n →L[ℝ] BoxGradientValue n :=
  LinearMap.toContinuousLinearMap {
    toFun := fun u => LinearMap.toContinuousLinearMap {
      toFun := fun w => WithLp.toLp 2 fun ij => w ij.1 * u ij.2
      map_add' := by
        intro w z
        ext ij
        simp [add_mul]
      map_smul' := by
        intro c w
        ext ij
        simp [mul_assoc] }
    map_add' := by
      intro u v
      ext w ij
      simp [mul_add]
    map_smul' := by
      intro c u
      ext w ij
      simp [mul_left_comm] }

theorem continuousLinearMap_apply_eq_sum_basis
    (D : (Fin (n + 1) → ℝ) →L[ℝ] Fin (n + 1) → ℝ)
    (u : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    D u i = ∑ j, u j * D (Pi.single j 1) i := by
  have h := LinearMap.pi_apply_eq_sum_univ D.toLinearMap u
  have hi := congrArg (fun z => z i) h
  have hb : ∀ j : Fin (n + 1),
      (fun k => if j = k then (1 : ℝ) else 0) = Pi.single j 1 := by
    intro j
    ext k
    simp [Pi.single_apply, eq_comm]
  simpa only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, hb] using hi

theorem inner_boxVelocityOuter_gradient
    (u w : Fin (n + 1) → ℝ)
    (D : (Fin (n + 1) → ℝ) →L[ℝ] Fin (n + 1) → ℝ) :
    ⟪boxVelocityOuter (WithLp.toLp 2 u) (WithLp.toLp 2 w),
        WithLp.toLp 2 (fun ij => D (Pi.single ij.2 1) ij.1)⟫_ℝ =
      ∑ i, D u i * w i := by
  simp_rw [continuousLinearMap_apply_eq_sum_basis D u]
  change (∑ ij : Fin (n + 1) × Fin (n + 1),
      D (Pi.single ij.2 1) ij.1 * (w ij.1 * u ij.2)) =
    ∑ i, (∑ j, u j * D (Pi.single j 1) i) * w i
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

variable (I : BoxIntegral.Box (Fin (n + 1)))

/-- Vector-valued `L4` on the box. -/
abbrev BoxVelocityL4 :=
  Lp (BoxVelocityValue n) (4 : ℝ≥0∞) (BoxMeasure I)

/-- Holder multiplication from two velocity `L4` factors to a matrix `L2`
factor. -/
noncomputable def boxVelocityOuterLp :
    BoxVelocityL4 I →L[ℝ] BoxVelocityL4 I →L[ℝ] BoxGradientL2 I :=
  (boxVelocityOuter (n := n)).holderL (BoxMeasure I) 4 4 2

/-- The integral pairing of two matrix-valued `L2` functions. -/
noncomputable def boxGradientLpPairing :
    BoxGradientL2 I →L[ℝ] BoxGradientL2 I →L[ℝ] ℝ :=
  (isBoundedBilinearMap_inner (𝕜 := ℝ)).toContinuousLinearMap.lpPairing
    (BoxMeasure I) 2 2

/-- The continuous `L4-L2-L4` transport form. -/
noncomputable def boxLpConvection :
    BoxVelocityL4 I →L[ℝ] BoxGradientL2 I →L[ℝ] BoxVelocityL4 I →L[ℝ] ℝ := by
  let post : (BoxVelocityL4 I →L[ℝ] BoxGradientL2 I) →L[ℝ]
      BoxVelocityL4 I →L[ℝ] BoxGradientL2 I →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ (BoxVelocityL4 I)
      (BoxGradientL2 I) (BoxGradientL2 I →L[ℝ] ℝ))
        (boxGradientLpPairing I)
  let Cuwg : BoxVelocityL4 I →L[ℝ]
      BoxVelocityL4 I →L[ℝ] BoxGradientL2 I →L[ℝ] ℝ :=
    post.comp (boxVelocityOuterLp I)
  exact (ContinuousLinearMap.flipₗᵢ ℝ (BoxVelocityL4 I)
    (BoxGradientL2 I) ℝ).toContinuousLinearEquiv.toContinuousLinearMap.comp Cuwg

@[simp]
theorem boxLpConvection_apply
    (u w : BoxVelocityL4 I) (G : BoxGradientL2 I) :
    boxLpConvection I u G w =
      boxGradientLpPairing I (boxVelocityOuterLp I u w) G :=
  rfl

theorem boxLpConvection_eq_integral_inner
    (u w : BoxVelocityL4 I) (G : BoxGradientL2 I) :
    boxLpConvection I u G w =
      ∫ x, ⟪boxVelocityOuter (u x) (w x), G x⟫_ℝ ∂BoxMeasure I := by
  rw [boxLpConvection_apply, boxGradientLpPairing,
    ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [
    (boxVelocityOuter (n := n)).coeFn_holder (r := (2 : ℝ≥0∞)) u w] with x hx
  change ⟪(boxVelocityOuterLp I u w) x, G x⟫_ℝ = _
  rw [show (boxVelocityOuterLp I u w) x =
    boxVelocityOuter (u x) (w x) from hx]

/-- A continuous `L4` representative of every box energy state. -/
structure BoxEnergyL4Realization where
  toLp4 : BoxH1ZeroSigma I →L[ℝ] BoxVelocityL4 I
  coeFn_toLp4_eq_state : ∀ u : BoxH1ZeroSigma I,
    (toLp4 u : (Fin (n + 1) → ℝ) → BoxVelocityValue n) =ᵐ[BoxMeasure I]
      (boxEnergyToState I u : (Fin (n + 1) → ℝ) → BoxVelocityValue n)

namespace BoxEnergyL4Realization

variable (E : BoxEnergyL4Realization I)

theorem coeFn_toLp4_toEnergy
    (u : SmoothBoxEnergyField I) :
    (E.toLp4 u.toEnergy : (Fin (n + 1) → ℝ) → BoxVelocityValue n)
      =ᵐ[BoxMeasure I] boxVelocityValue u.field := by
  filter_upwards [E.coeFn_toLp4_eq_state u.toEnergy,
    u.velocity_memLp.coeFn_toLp] with x hstate hvelocity
  change E.toLp4 u.toEnergy x = u.velocityLp x at hstate
  exact hstate.trans hvelocity

/-- The transport integral on the closed energy space obtained from the `L4`
velocity representative and the closed `L2` gradient. -/
noncomputable def convectionForm :
    BoxH1ZeroSigma I →L[ℝ]
      BoxH1ZeroSigma I →L[ℝ] BoxH1ZeroSigma I →L[ℝ] ℝ :=
  (boxLpConvection I).trilinearComp E.toLp4 (boxEnergyGradient I) E.toLp4

@[simp]
theorem convectionForm_apply (u v w : BoxH1ZeroSigma I) :
    convectionForm I E u v w =
      boxLpConvection I (E.toLp4 u) (boxEnergyGradient I v) (E.toLp4 w) :=
  rfl

theorem convectionForm_eq_integral_inner (u v w : BoxH1ZeroSigma I) :
    convectionForm I E u v w =
      ∫ x, ⟪boxVelocityOuter (E.toLp4 u x) (E.toLp4 w x),
        boxEnergyGradient I v x⟫_ℝ ∂BoxMeasure I := by
  rw [convectionForm_apply I E]
  exact boxLpConvection_eq_integral_inner I _ _ _

theorem convectionForm_toEnergy_eq_integral
    (u v w : SmoothBoxEnergyField I) :
    convectionForm I E u.toEnergy v.toEnergy w.toEnergy =
      ∫ x, ∑ i, v.derivative x (u.field x) i * w.field x i
        ∂BoxMeasure I := by
  rw [convectionForm_eq_integral_inner I E]
  apply integral_congr_ae
  filter_upwards [coeFn_toLp4_toEnergy I E u,
    coeFn_toLp4_toEnergy I E w,
    v.gradient_memLp.coeFn_toLp] with x hu hw hv
  change ⟪boxVelocityOuter (E.toLp4 u.toEnergy x) (E.toLp4 w.toEnergy x),
      v.gradientLp x⟫_ℝ = _
  rw [hu, hw, show v.gradientLp x = boxGradientValue v.derivative x from hv]
  exact inner_boxVelocityOuter_gradient (u.field x) (w.field x) (v.derivative x)

theorem transportIntegrable
    (E : BoxEnergyL4Realization I) (u v w : SmoothBoxEnergyField I) :
    Integrable
      (fun x => ∑ i, v.derivative x (u.field x) i * w.field x i)
      (BoxMeasure I) := by
  let inner : BoxGradientValue n →L[ℝ] BoxGradientValue n →L[ℝ] ℝ :=
    (isBoundedBilinearMap_inner (𝕜 := ℝ)).toContinuousLinearMap
  have houter : MemLp
      (fun x => boxVelocityOuter (E.toLp4 u.toEnergy x)
        (E.toLp4 w.toEnergy x)) 2 (BoxMeasure I) :=
    (boxVelocityOuter (n := n)).memLp_of_bilin 2
      (Lp.memLp (E.toLp4 u.toEnergy)) (Lp.memLp (E.toLp4 w.toEnergy))
  have hinner : MemLp
      (fun x => inner
        (boxVelocityOuter (E.toLp4 u.toEnergy x) (E.toLp4 w.toEnergy x))
        (boxEnergyGradient I v.toEnergy x)) 1 (BoxMeasure I) :=
    inner.memLp_of_bilin 1 houter (Lp.memLp (boxEnergyGradient I v.toEnergy))
  have hint : Integrable
      (fun x => inner
        (boxVelocityOuter (E.toLp4 u.toEnergy x) (E.toLp4 w.toEnergy x))
        (boxEnergyGradient I v.toEnergy x)) (BoxMeasure I) :=
    memLp_one_iff_integrable.mp hinner
  apply hint.congr
  filter_upwards [coeFn_toLp4_toEnergy I E u,
    coeFn_toLp4_toEnergy I E w,
    v.gradient_memLp.coeFn_toLp] with x hu hw hv
  change ⟪boxVelocityOuter (E.toLp4 u.toEnergy x) (E.toLp4 w.toEnergy x),
      v.gradientLp x⟫_ℝ = _
  rw [hu, hw, show v.gradientLp x = boxGradientValue v.derivative x from hv]
  exact inner_boxVelocityOuter_gradient (u.field x) (w.field x) (v.derivative x)

theorem convectionForm_toEnergy_skew
    (u v w : SmoothBoxEnergyField I) :
    convectionForm I E u.toEnergy v.toEnergy w.toEnergy =
      -convectionForm I E u.toEnergy w.toEnergy v.toEnergy := by
  have hint₂ : IntegrableOn
      (fun x => ∑ i, v.field x i * w.derivative x (u.field x) i)
      (BoxIntegral.Box.Icc I) := by
    apply (transportIntegrable I E u w v).congr
    filter_upwards with x
    apply Finset.sum_congr rfl
    intro i _hi
    exact mul_comm _ _
  have hskew :
      (∫ x in BoxIntegral.Box.Icc I,
          ∑ i, v.derivative x (u.field x) i * w.field x i) +
        ∫ x in BoxIntegral.Box.Icc I,
          ∑ i, w.derivative x (u.field x) i * v.field x i = 0 :=
    trilinear_skew I
      u.field v.field w.field u.derivative v.derivative w.derivative
      u.hasFDerivAt_field u.continuousOn_field
      v.hasFDerivAt_field v.continuousOn_field
      w.hasFDerivAt_field w.continuousOn_field
      v.zeroDirichlet_field w.zeroDirichlet_field u.divergence_field
      (transportIntegrable I E u v w) hint₂
  calc
    convectionForm I E u.toEnergy v.toEnergy w.toEnergy =
        ∫ x in BoxIntegral.Box.Icc I,
          ∑ i, v.derivative x (u.field x) i * w.field x i :=
      convectionForm_toEnergy_eq_integral I E u v w
    _ = -∫ x in BoxIntegral.Box.Icc I,
          ∑ i, w.derivative x (u.field x) i * v.field x i := by
      linarith only [hskew]
    _ = -convectionForm I E u.toEnergy w.toEnergy v.toEnergy := by
      rw [convectionForm_toEnergy_eq_integral I E u w v]

/-- Restriction of the `L4-L2-L4` transport integral to the dense smooth graph
core. -/
noncomputable def coreConvectionForm :
    smoothBoxGraphCore I →L[ℝ]
      smoothBoxGraphCore I →L[ℝ] smoothBoxGraphCore I →L[ℝ] ℝ :=
  (convectionForm I E).trilinearCompSame (boxSmoothGraphCoreInclusion I)

theorem coreConvectionForm_skew :
    ∀ u v w, coreConvectionForm I E u v w =
      -coreConvectionForm I E u w v := by
  apply ContinuousLinearMap.trilinear_skew_of_span
    (smoothBoxGraphSet I) (coreConvectionForm I E)
  intro x hx y hy z hz
  rcases hx with ⟨u, rfl⟩
  rcases hy with ⟨v, rfl⟩
  rcases hz with ⟨w, rfl⟩
  change convectionForm I E u.toEnergy v.toEnergy w.toEnergy =
    -convectionForm I E u.toEnergy w.toEnergy v.toEnergy
  exact convectionForm_toEnergy_skew I E u v w

theorem coreConvectionExtension_eq_convectionForm :
    boxCoreConvectionExtension I (coreConvectionForm I E) =
      convectionForm I E := by
  apply boxCoreConvectionExtension_unique
  intro u v w
  rfl

theorem convectionForm_skew :
    ∀ u v w, convectionForm I E u v w =
      -convectionForm I E u w v := by
  intro u v w
  let C := boxCoreConvectionExtension I (coreConvectionForm I E)
  have heq : C = convectionForm I E :=
    coreConvectionExtension_eq_convectionForm I E
  have huv : C u v w = convectionForm I E u v w :=
    congrArg (fun B => B u v w) heq
  have huw : C u w v = convectionForm I E u w v :=
    congrArg (fun B => B u w v) heq
  calc
    convectionForm I E u v w = C u v w := huv.symm
    _ = -C u w v :=
      boxCoreConvectionExtension_skew I (coreConvectionForm I E)
        (coreConvectionForm_skew I E) u v w
    _ = -convectionForm I E u w v := congrArg Neg.neg huw

/-- The actual `L4-L2-L4` box transport integral as a bounded skew energy
convection form. -/
noncomputable def energyConvectionForm :
    EnergyConvectionForm (BoxH1ZeroSigma I) :=
  EnergyConvectionForm.ofContinuousSkew
    (convectionForm I E) (convectionForm_skew I E)

@[simp]
theorem energyConvectionForm_form :
    (energyConvectionForm I E).form = convectionForm I E :=
  rfl

end BoxEnergyL4Realization

/-- A selected positive continuity constant in the first `L4` variable of the
box transport map. -/
noncomputable def boxLpConvectionBoundData :
    { C : ℝ // 0 < C ∧ ∀ u : BoxVelocityL4 I,
      ‖boxLpConvection I u‖ ≤ C * ‖u‖ } :=
  Classical.choice (by
    apply Exists.elim (ContinuousLinearMap.bound
      (𝕜 := ℝ) (𝕜₂ := ℝ) (σ₁₂ := RingHom.id ℝ)
      (E := BoxVelocityL4 I)
      (F := BoxGradientL2 I →L[ℝ] BoxVelocityL4 I →L[ℝ] ℝ)
      (boxLpConvection I))
    intro C hC
    exact ⟨⟨C, hC⟩⟩)

noncomputable def boxLpConvectionBound : ℝ :=
  (boxLpConvectionBoundData I).1

theorem boxLpConvectionBound_pos : 0 < boxLpConvectionBound I :=
  (boxLpConvectionBoundData I).property.1

theorem norm_boxLpConvection_apply_le (u : BoxVelocityL4 I) :
    ‖boxLpConvection I u‖ ≤ boxLpConvectionBound I * ‖u‖ :=
  (boxLpConvectionBoundData I).property.2 u

theorem norm_boxLpConvection_le
    (u w : BoxVelocityL4 I) (G : BoxGradientL2 I) :
    ‖boxLpConvection I u G w‖ ≤
      boxLpConvectionBound I * ‖u‖ * ‖G‖ * ‖w‖ := by
  calc
    ‖boxLpConvection I u G w‖ ≤ ‖boxLpConvection I u G‖ * ‖w‖ :=
      (boxLpConvection I u G).le_opNorm w
    _ ≤ (‖boxLpConvection I u‖ * ‖G‖) * ‖w‖ :=
      mul_le_mul_of_nonneg_right
        ((boxLpConvection I u).le_opNorm G) (norm_nonneg w)
    _ ≤ ((boxLpConvectionBound I * ‖u‖) * ‖G‖) * ‖w‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (norm_boxLpConvection_apply_le I u) (norm_nonneg G))
        (norm_nonneg w)

namespace BoxEnergyL4Realization

theorem norm_convectionForm_le
    (E : BoxEnergyL4Realization I) (u v w : BoxH1ZeroSigma I) :
    ‖E.convectionForm I u v w‖ ≤
      boxLpConvectionBound I * ‖E.toLp4 u‖ * ‖boxEnergyGradient I v‖ *
        ‖E.toLp4 w‖ := by
  rw [convectionForm_apply I E]
  exact norm_boxLpConvection_le I _ _ _

end BoxEnergyL4Realization

/-- A box `L4` realization satisfying the two-dimensional Ladyzhenskaya
estimate. -/
structure BoxLadyzhenskayaRealization extends BoxEnergyL4Realization I where
  constant : ℝ
  constant_nonneg : 0 ≤ constant
  l4_sq_le : ∀ u : BoxH1ZeroSigma I,
    ‖toLp4 u‖ ^ 2 ≤
      constant * ‖boxEnergyToState I u‖ * ‖boxEnergyGradient I u‖

namespace BoxLadyzhenskayaRealization

variable (L : BoxLadyzhenskayaRealization I)

theorem ladyzhenskaya_product_bound
    (c C l h gu gp vu vp : ℝ)
    (hc : 0 ≤ c) (hC : 0 ≤ C) (hh : 0 ≤ h)
    (hgp0 : 0 ≤ gp) (hvu0 : 0 ≤ vu)
    (hsq : l ^ 2 ≤ C * h * gu) (hgu : gu ≤ vu) (hgp : gp ≤ vp) :
    c * l * gp * l ≤ (c * C) * h * vu * vp := by
  have hpref : 0 ≤ c * C * h := mul_nonneg (mul_nonneg hc hC) hh
  calc
    c * l * gp * l = c * (l ^ 2) * gp := by ring
    _ ≤ c * (C * h * gu) * gp :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsq hc) hgp0
    _ = (c * C * h) * gu * gp := by ring
    _ ≤ (c * C * h) * vu * gp :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hgu hpref) hgp0
    _ ≤ (c * C * h) * vu * vp :=
      mul_le_mul_of_nonneg_left hgp (mul_nonneg hpref hvu0)
    _ = (c * C) * h * vu * vp := by ring

/-- The diagonal convection term has the mixed `H-V-V` bound needed for the
two-dimensional common-dual estimate. -/
theorem convectionForm_diagonal_norm_le
    (u φ : BoxH1ZeroSigma I) :
    ‖L.toBoxEnergyL4Realization.convectionForm I u u φ‖ ≤
      (boxLpConvectionBound I * L.constant) *
        ‖boxEnergyToState I u‖ * ‖u‖ * ‖φ‖ := by
  have hskew := BoxEnergyL4Realization.convectionForm_skew I
    L.toBoxEnergyL4Realization u u φ
  have hnorm :
      ‖L.toBoxEnergyL4Realization.convectionForm I u u φ‖ =
        ‖L.toBoxEnergyL4Realization.convectionForm I u φ u‖ := by
    calc
      ‖L.toBoxEnergyL4Realization.convectionForm I u u φ‖ =
          ‖-L.toBoxEnergyL4Realization.convectionForm I u φ u‖ :=
        congrArg norm hskew
      _ = ‖L.toBoxEnergyL4Realization.convectionForm I u φ u‖ := norm_neg _
  calc
    ‖L.toBoxEnergyL4Realization.convectionForm I u u φ‖ =
        ‖L.toBoxEnergyL4Realization.convectionForm I u φ u‖ := hnorm
    _ ≤ boxLpConvectionBound I * ‖L.toLp4 u‖ *
          ‖boxEnergyGradient I φ‖ * ‖L.toLp4 u‖ :=
      BoxEnergyL4Realization.norm_convectionForm_le I
        L.toBoxEnergyL4Realization u φ u
    _ ≤ (boxLpConvectionBound I * L.constant) *
          ‖boxEnergyToState I u‖ * ‖u‖ * ‖φ‖ :=
      ladyzhenskaya_product_bound
        (boxLpConvectionBound I) L.constant ‖L.toLp4 u‖
        ‖boxEnergyToState I u‖ ‖boxEnergyGradient I u‖
        ‖boxEnergyGradient I φ‖ ‖u‖ ‖φ‖
        (boxLpConvectionBound_pos I).le L.constant_nonneg
        (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (L.l4_sq_le u)
        (norm_boxEnergyGradient_le I u) (norm_boxEnergyGradient_le I φ)

end BoxLadyzhenskayaRealization

end
