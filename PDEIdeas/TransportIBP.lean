import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Transport Integration by Parts on Boxes

The divergence theorem yields scalar and vector transport identities for
continuously differentiable fields on closed boxes with zero boundary data.
-/

open MeasureTheory MeasureTheory.Measure Real InnerProductSpace
open scoped NNReal ENNReal

noncomputable section

variable {n : ℕ}

/-- Concrete box-domain vector-field type. -/
abbrev Domain (n : ℕ) := Fin n → ℝ

/-- The transport operator `(u · ∇)v` at `x`, represented with the Fréchet
derivative. -/
def transport (u : Domain n → Domain n) (v : Domain n → Domain n)
    (x : Domain n) : Domain n :=
  fderiv ℝ v x (u x)

/-- Divergence of a vector field, written as the trace of its derivative in the
coordinate basis. -/
def divergence (u : Domain n → Domain n) (x : Domain n) : ℝ :=
  ∑ i : Fin n, fderiv ℝ (fun y => u y i) x (Pi.single i 1)

/-- `u` is divergence-free at `x`. -/
def DivFreeAt (u : Domain n → Domain n) (x : Domain n) : Prop :=
  divergence u x = 0

/-- `u` is divergence-free on a set. -/
def DivFreeOn (u : Domain n → Domain n) (s : Set (Domain n)) : Prop :=
  ∀ x ∈ s, DivFreeAt u x

/-- The integral of the divergence vanishes when every normal component of the
field vanishes on the corresponding pair of faces. -/
theorem integral_divergence_zero_bc
    (I : BoxIntegral.Box (Fin (n + 1)))
    (F : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (F' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] Fin (n + 1) → ℝ)
    (hFc : ContinuousOn F (BoxIntegral.Box.Icc I))
    (hFd : ∀ x ∈ interior (BoxIntegral.Box.Icc I), HasFDerivAt F (F' x) x)
    (hFi : IntegrableOn (fun x => ∑ i, F' x (Pi.single i 1) i)
        (BoxIntegral.Box.Icc I))
    (hFbc : ∀ i : Fin (n + 1), ∀ x : Fin n → ℝ,
        F (i.insertNth (I.upper i) x) i = 0 ∧
        F (i.insertNth (I.lower i) x) i = 0) :
    ∫ x in BoxIntegral.Box.Icc I, ∑ i, F' x (Pi.single i 1) i = 0 := by
  change ∫ x in Set.Icc I.lower I.upper,
    ∑ i, F' x (Pi.single i 1) i = 0
  rw [MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable
    I.lower I.upper I.lower_le_upper F F' ∅ Set.countable_empty hFc]
  · simp [hFbc]
  · intro x hx
    apply hFd x
    rw [BoxIntegral.Box.Icc_def, ← Set.pi_univ_Icc,
      interior_pi_set (@Set.finite_univ (Fin (n + 1)) _)]
    simpa only [Set.mem_pi, Set.mem_univ, true_implies, interior_Icc]
      using hx.1
  · exact hFi

private theorem continuousLinearMap_apply_eq_sum_standardBasis
    (L : (Fin (n + 1) → ℝ) →L[ℝ] ℝ)
    (x : Fin (n + 1) → ℝ) :
    L x = ∑ i, L (Pi.single i 1) * x i := by
  conv_lhs => rw [← Finset.univ_sum_single x]
  rw [_root_.map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [show Pi.single i (x i) =
      x i • (Pi.single i 1 : Fin (n + 1) → ℝ) by
    simpa using (Pi.single_smul' i (x i) (1 : ℝ))]
  simp [mul_comm]

/-- Scalar transport integration by parts on a box. -/
theorem scalar_ibp
    (I : BoxIntegral.Box (Fin (n + 1)))
    (u : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (f : (Fin (n + 1) → ℝ) → ℝ)
    (u' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] Fin (n + 1) → ℝ)
    (f' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] ℝ)
    (hu : ∀ x ∈ interior (BoxIntegral.Box.Icc I), HasFDerivAt u (u' x) x)
    (huc : ContinuousOn u (BoxIntegral.Box.Icc I))
    (hf : ∀ x ∈ interior (BoxIntegral.Box.Icc I), HasFDerivAt f (f' x) x)
    (hfc : ContinuousOn f (BoxIntegral.Box.Icc I))
    (hfbc : ∀ i : Fin (n + 1), ∀ x : Fin n → ℝ,
        f (i.insertNth (I.upper i) x) = 0 ∧
        f (i.insertNth (I.lower i) x) = 0)
    (hint_transport : IntegrableOn (fun x => f' x (u x))
        (BoxIntegral.Box.Icc I))
    (hint_div : IntegrableOn
        (fun x => f x * ∑ i, u' x (Pi.single i 1) i)
        (BoxIntegral.Box.Icc I)) :
    ∫ x in BoxIntegral.Box.Icc I, f' x (u x) =
      -∫ x in BoxIntegral.Box.Icc I,
        f x * ∑ i, u' x (Pi.single i 1) i := by
  let flux : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ :=
    fun x => f x • u x
  let flux' :
      (Fin (n + 1) → ℝ) →
        (Fin (n + 1) → ℝ) →L[ℝ] Fin (n + 1) → ℝ :=
    fun x => f x • u' x + (f' x).smulRight (u x)
  have hflux_deriv :
      ∀ x ∈ interior (BoxIntegral.Box.Icc I),
        HasFDerivAt flux (flux' x) x := by
    intro x hx
    simpa [flux, flux'] using (hf x hx).smul (hu x hx)
  have hflux_cont : ContinuousOn flux (BoxIntegral.Box.Icc I) := by
    exact hfc.smul huc
  have hflux_bc : ∀ i : Fin (n + 1), ∀ x : Fin n → ℝ,
      flux (i.insertNth (I.upper i) x) i = 0 ∧
      flux (i.insertNth (I.lower i) x) i = 0 := by
    intro i x
    constructor
    · simp [flux, (hfbc i x).1]
    · simp [flux, (hfbc i x).2]
  have hflux_div : ∀ x,
      ∑ i, flux' x (Pi.single i 1) i =
        f' x (u x) + f x * ∑ i, u' x (Pi.single i 1) i := by
    intro x
    rw [continuousLinearMap_apply_eq_sum_standardBasis (f' x) (u x)]
    simp only [flux', ContinuousLinearMap.add_apply, Pi.add_apply,
      ContinuousLinearMap.smul_apply, Pi.smul_apply,
      ContinuousLinearMap.smulRight_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    ring
  have hflux_int : IntegrableOn
      (fun x => ∑ i, flux' x (Pi.single i 1) i)
      (BoxIntegral.Box.Icc I) := by
    apply (hint_transport.add hint_div).congr
    exact Filter.Eventually.of_forall fun x => (hflux_div x).symm
  have hzero := integral_divergence_zero_bc I flux flux'
    hflux_cont hflux_deriv hflux_int hflux_bc
  have hsum :
      ∫ x in BoxIntegral.Box.Icc I,
          (f' x (u x) + f x * ∑ i, u' x (Pi.single i 1) i) = 0 := by
    calc
      _ = ∫ x in BoxIntegral.Box.Icc I,
          ∑ i, flux' x (Pi.single i 1) i := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => (hflux_div x).symm
      _ = 0 := hzero
  rw [integral_add hint_transport hint_div] at hsum
  linarith

/-- Coordinate integration by parts for a scalar field that vanishes on every
face of a box. -/
theorem scalar_coordinate_ibp
    (I : BoxIntegral.Box (Fin (n + 1)))
    (j : Fin (n + 1))
    (f g : (Fin (n + 1) → ℝ) → ℝ)
    (f' g' : (Fin (n + 1) → ℝ) →
      (Fin (n + 1) → ℝ) →L[ℝ] ℝ)
    (hf : ∀ x ∈ interior (BoxIntegral.Box.Icc I),
      HasFDerivAt f (f' x) x)
    (hfc : ContinuousOn f (BoxIntegral.Box.Icc I))
    (hg : ∀ x ∈ interior (BoxIntegral.Box.Icc I),
      HasFDerivAt g (g' x) x)
    (hgc : ContinuousOn g (BoxIntegral.Box.Icc I))
    (hfbc : ∀ i : Fin (n + 1), ∀ x : Fin n → ℝ,
      f (i.insertNth (I.upper i) x) = 0 ∧
      f (i.insertNth (I.lower i) x) = 0)
    (hint_left : IntegrableOn
      (fun x => f' x (Pi.single j 1) * g x)
      (BoxIntegral.Box.Icc I))
    (hint_right : IntegrableOn
      (fun x => f x * g' x (Pi.single j 1))
      (BoxIntegral.Box.Icc I)) :
    ∫ x in BoxIntegral.Box.Icc I, f' x (Pi.single j 1) * g x =
      -∫ x in BoxIntegral.Box.Icc I,
        f x * g' x (Pi.single j 1) := by
  let e : Fin (n + 1) → ℝ := Pi.single j 1
  let product : (Fin (n + 1) → ℝ) → ℝ := fun x => f x * g x
  let product' : (Fin (n + 1) → ℝ) →
      (Fin (n + 1) → ℝ) →L[ℝ] ℝ :=
    fun x => g x • f' x + f x • g' x
  have hproduct_deriv :
      ∀ x ∈ interior (BoxIntegral.Box.Icc I),
        HasFDerivAt product (product' x) x := by
    intro x hx
    simpa only [product, product', add_comm] using (hf x hx).mul (hg x hx)
  have hproduct_cont :
      ContinuousOn product (BoxIntegral.Box.Icc I) :=
    hfc.mul hgc
  have hproduct_bc :
      ∀ i : Fin (n + 1), ∀ x : Fin n → ℝ,
        product (i.insertNth (I.upper i) x) = 0 ∧
        product (i.insertNth (I.lower i) x) = 0 := by
    intro i x
    simp [product, (hfbc i x).1, (hfbc i x).2]
  have hproduct_int :
      IntegrableOn (fun x => product' x e)
        (BoxIntegral.Box.Icc I) := by
    apply (hint_left.add hint_right).congr
    exact Filter.Eventually.of_forall fun x => by
      simp only [Pi.add_apply, product', e, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
  have hibp := scalar_ibp I (fun _ => e) product (fun _ => 0) product'
    (fun x _ => hasFDerivAt_const e x) continuousOn_const
    hproduct_deriv hproduct_cont hproduct_bc hproduct_int (by simp)
  have hsum :
      ∫ x in BoxIntegral.Box.Icc I,
          (f' x (Pi.single j 1) * g x +
            f x * g' x (Pi.single j 1)) = 0 := by
    calc
      _ = ∫ x in BoxIntegral.Box.Icc I, product' x e := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          simp only [product', e, ContinuousLinearMap.add_apply,
            ContinuousLinearMap.smul_apply, smul_eq_mul]
          ring
      _ = 0 := by simpa using hibp
  rw [integral_add hint_left hint_right] at hsum
  linarith

/-- Scalar transport cancellation for divergence-free fields. -/
theorem scalar_transport_cancel
    (I : BoxIntegral.Box (Fin (n + 1)))
    (u : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (f : (Fin (n + 1) → ℝ) → ℝ)
    (u' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] Fin (n + 1) → ℝ)
    (f' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] ℝ)
    (hu : ∀ x ∈ interior (BoxIntegral.Box.Icc I), HasFDerivAt u (u' x) x)
    (huc : ContinuousOn u (BoxIntegral.Box.Icc I))
    (hf : ∀ x ∈ interior (BoxIntegral.Box.Icc I), HasFDerivAt f (f' x) x)
    (hfc : ContinuousOn f (BoxIntegral.Box.Icc I))
    (hfbc : ∀ i : Fin (n + 1), ∀ x : Fin n → ℝ,
        f (i.insertNth (I.upper i) x) = 0 ∧
        f (i.insertNth (I.lower i) x) = 0)
    (hdiv : ∀ x ∈ BoxIntegral.Box.Icc I,
        ∑ i : Fin (n + 1), u' x (Pi.single i 1) i = 0)
    (hint : IntegrableOn (fun x => f' x (u x)) (BoxIntegral.Box.Icc I)) :
    ∫ x in BoxIntegral.Box.Icc I, f' x (u x) = 0 := by
  have hbox : MeasurableSet (BoxIntegral.Box.Icc I) := by
    rw [BoxIntegral.Box.Icc_def]
    exact measurableSet_Icc
  have hint_div : IntegrableOn
      (fun x => f x * ∑ i, u' x (Pi.single i 1) i)
      (BoxIntegral.Box.Icc I) := by
    apply integrableOn_zero.congr_fun
    · intro x hx
      simp [hdiv x hx]
    · exact hbox
  have hibp := scalar_ibp I u f u' f' hu huc hf hfc hfbc hint hint_div
  have hdiv_integral :
      ∫ x in BoxIntegral.Box.Icc I,
          f x * ∑ i, u' x (Pi.single i 1) i = 0 := by
    calc
      _ = ∫ _x in BoxIntegral.Box.Icc I, (0 : ℝ) := by
        apply setIntegral_congr_fun hbox
        intro x hx
        simp [hdiv x hx]
      _ = 0 := by simp
  rw [hdiv_integral, neg_zero] at hibp
  exact hibp

/-- Vector transport integration by parts on a box. -/
theorem vector_transport_ibp
    (I : BoxIntegral.Box (Fin (n + 1)))
    (u v w : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (u' v' w' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] Fin (n + 1) → ℝ)
    (hu : ∀ x ∈ interior (BoxIntegral.Box.Icc I), HasFDerivAt u (u' x) x)
    (huc : ContinuousOn u (BoxIntegral.Box.Icc I))
    (hv : ∀ x ∈ interior (BoxIntegral.Box.Icc I), HasFDerivAt v (v' x) x)
    (hvc : ContinuousOn v (BoxIntegral.Box.Icc I))
    (hw : ∀ x ∈ interior (BoxIntegral.Box.Icc I), HasFDerivAt w (w' x) x)
    (hwc : ContinuousOn w (BoxIntegral.Box.Icc I))
    (hvbc : ∀ i : Fin (n + 1), ∀ x : Fin n → ℝ,
        v (i.insertNth (I.upper i) x) = 0 ∧
        v (i.insertNth (I.lower i) x) = 0)
    (hwbc : ∀ i : Fin (n + 1), ∀ x : Fin n → ℝ,
        w (i.insertNth (I.upper i) x) = 0 ∧
        w (i.insertNth (I.lower i) x) = 0)
    (hdiv : ∀ x ∈ BoxIntegral.Box.Icc I,
        ∑ i : Fin (n + 1), u' x (Pi.single i 1) i = 0)
    (hint_tuv : IntegrableOn
        (fun x => ∑ i, v' x (u x) i * w x i) (BoxIntegral.Box.Icc I))
    (hint_tuw : IntegrableOn
        (fun x => ∑ i, v x i * w' x (u x) i) (BoxIntegral.Box.Icc I)) :
    ∫ x in BoxIntegral.Box.Icc I, ∑ i, v' x (u x) i * w x i =
      -∫ x in BoxIntegral.Box.Icc I, ∑ i, v x i * w' x (u x) i := by
  let dot : (Fin (n + 1) → ℝ) → ℝ :=
    fun x => ∑ i, v x i * w x i
  let dot' : (Fin (n + 1) → ℝ) →
      (Fin (n + 1) → ℝ) →L[ℝ] ℝ :=
    fun x => ∑ i, (
      w x i • ((ContinuousLinearMap.proj i :
        (Fin (n + 1) → ℝ) →L[ℝ] ℝ).comp (v' x)) +
      v x i • ((ContinuousLinearMap.proj i :
        (Fin (n + 1) → ℝ) →L[ℝ] ℝ).comp (w' x)))
  have hdot_deriv : ∀ x ∈ interior (BoxIntegral.Box.Icc I),
      HasFDerivAt dot (dot' x) x := by
    intro x hx
    dsimp only [dot, dot']
    apply HasFDerivAt.fun_sum
    intro i _hi
    have hvi : HasFDerivAt (fun y => v y i)
        ((ContinuousLinearMap.proj i :
          (Fin (n + 1) → ℝ) →L[ℝ] ℝ).comp (v' x)) x :=
      (ContinuousLinearMap.proj i :
        (Fin (n + 1) → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp x (hv x hx)
    have hwi : HasFDerivAt (fun y => w y i)
        ((ContinuousLinearMap.proj i :
          (Fin (n + 1) → ℝ) →L[ℝ] ℝ).comp (w' x)) x :=
      (ContinuousLinearMap.proj i :
        (Fin (n + 1) → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp x (hw x hx)
    simpa only [add_comm] using hvi.mul hwi
  have hdot_cont : ContinuousOn dot (BoxIntegral.Box.Icc I) := by
    dsimp only [dot]
    apply continuousOn_finset_sum Finset.univ
    intro i _hi
    have hvi : ContinuousOn (fun x => v x i) (BoxIntegral.Box.Icc I) := by
      simpa using (ContinuousLinearMap.proj i :
        (Fin (n + 1) → ℝ) →L[ℝ] ℝ).continuous.comp_continuousOn hvc
    have hwi : ContinuousOn (fun x => w x i) (BoxIntegral.Box.Icc I) := by
      simpa using (ContinuousLinearMap.proj i :
        (Fin (n + 1) → ℝ) →L[ℝ] ℝ).continuous.comp_continuousOn hwc
    exact hvi.mul hwi
  have hdot_bc : ∀ i : Fin (n + 1), ∀ x : Fin n → ℝ,
      dot (i.insertNth (I.upper i) x) = 0 ∧
      dot (i.insertNth (I.lower i) x) = 0 := by
    intro i x
    constructor
    · simp [dot, (hvbc i x).1, (hwbc i x).1]
    · simp [dot, (hvbc i x).2, (hwbc i x).2]
  have hdot_apply : ∀ x,
      dot' x (u x) =
        (∑ i, v' x (u x) i * w x i) +
        ∑ i, v x i * w' x (u x) i := by
    intro x
    simp only [dot', ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      smul_eq_mul, Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _hi
    rw [mul_comm]
  have hbox : MeasurableSet (BoxIntegral.Box.Icc I) := by
    rw [BoxIntegral.Box.Icc_def]
    exact measurableSet_Icc
  have hdot_int : IntegrableOn (fun x => dot' x (u x))
      (BoxIntegral.Box.Icc I) := by
    apply (hint_tuv.add hint_tuw).congr_fun
    · intro x _hx
      exact (hdot_apply x).symm
    · exact hbox
  have hdot_div_int : IntegrableOn
      (fun x => dot x * ∑ i, u' x (Pi.single i 1) i)
      (BoxIntegral.Box.Icc I) := by
    apply integrableOn_zero.congr_fun
    · intro x hx
      simp [hdiv x hx]
    · exact hbox
  have hibp_dot := scalar_ibp I u dot u' dot' hu huc hdot_deriv
    hdot_cont hdot_bc hdot_int hdot_div_int
  have hdot_div_integral :
      ∫ x in BoxIntegral.Box.Icc I,
          dot x * ∑ i, u' x (Pi.single i 1) i = 0 := by
    calc
      _ = ∫ _x in BoxIntegral.Box.Icc I, (0 : ℝ) := by
        apply setIntegral_congr_fun hbox
        intro x hx
        simp [hdiv x hx]
      _ = 0 := by simp
  rw [hdot_div_integral, neg_zero] at hibp_dot
  have hsum :
      ∫ x in BoxIntegral.Box.Icc I,
          ((∑ i, v' x (u x) i * w x i) +
            ∑ i, v x i * w' x (u x) i) = 0 := by
    calc
      _ = ∫ x in BoxIntegral.Box.Icc I, dot' x (u x) := by
        apply setIntegral_congr_fun hbox
        intro x _hx
        exact (hdot_apply x).symm
      _ = 0 := hibp_dot
  rw [integral_add hint_tuv hint_tuw] at hsum
  linarith

/-- Skew-symmetry of the trilinear transport form. -/
theorem trilinear_skew
    (I : BoxIntegral.Box (Fin (n + 1)))
    (u v w : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (u' v' w' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] Fin (n + 1) → ℝ)
    (hu : ∀ x ∈ interior (BoxIntegral.Box.Icc I), HasFDerivAt u (u' x) x)
    (huc : ContinuousOn u (BoxIntegral.Box.Icc I))
    (hv : ∀ x ∈ interior (BoxIntegral.Box.Icc I), HasFDerivAt v (v' x) x)
    (hvc : ContinuousOn v (BoxIntegral.Box.Icc I))
    (hw : ∀ x ∈ interior (BoxIntegral.Box.Icc I), HasFDerivAt w (w' x) x)
    (hwc : ContinuousOn w (BoxIntegral.Box.Icc I))
    (hvbc : ∀ i : Fin (n + 1), ∀ x : Fin n → ℝ,
        v (i.insertNth (I.upper i) x) = 0 ∧
        v (i.insertNth (I.lower i) x) = 0)
    (hwbc : ∀ i : Fin (n + 1), ∀ x : Fin n → ℝ,
        w (i.insertNth (I.upper i) x) = 0 ∧
        w (i.insertNth (I.lower i) x) = 0)
    (hdiv : ∀ x ∈ BoxIntegral.Box.Icc I,
        ∑ i : Fin (n + 1), u' x (Pi.single i 1) i = 0)
    (hint₁ : IntegrableOn (fun x => ∑ i, v' x (u x) i * w x i)
        (BoxIntegral.Box.Icc I))
    (hint₂ : IntegrableOn (fun x => ∑ i, v x i * w' x (u x) i)
        (BoxIntegral.Box.Icc I)) :
    (∫ x in BoxIntegral.Box.Icc I, ∑ i, v' x (u x) i * w x i) +
      ∫ x in BoxIntegral.Box.Icc I, ∑ i, w' x (u x) i * v x i = 0 := by
  have hibp := vector_transport_ibp I u v w u' v' w' hu huc hv hvc hw hwc
    hvbc hwbc hdiv hint₁ hint₂
  have hbox : MeasurableSet (BoxIntegral.Box.Icc I) := by
    rw [BoxIntegral.Box.Icc_def]
    exact measurableSet_Icc
  have hsecond :
      ∫ x in BoxIntegral.Box.Icc I, ∑ i, w' x (u x) i * v x i =
        ∫ x in BoxIntegral.Box.Icc I, ∑ i, v x i * w' x (u x) i := by
    apply setIntegral_congr_fun hbox
    intro x _hx
    apply Finset.sum_congr rfl
    intro i _hi
    exact mul_comm _ _
  rw [hsecond]
  calc
    (∫ x in BoxIntegral.Box.Icc I, ∑ i, v' x (u x) i * w x i) +
        ∫ x in BoxIntegral.Box.Icc I, ∑ i, v x i * w' x (u x) i =
      -(∫ x in BoxIntegral.Box.Icc I, ∑ i, v x i * w' x (u x) i) +
        ∫ x in BoxIntegral.Box.Icc I, ∑ i, v x i * w' x (u x) i := by
          rw [hibp]
    _ = 0 := neg_add_cancel _

/-- Diagonal transport cancellation, the concrete counterpart of the abstract
Galerkin cubic cancellation. -/
theorem trilinear_self_cancel
    (I : BoxIntegral.Box (Fin (n + 1)))
    (u : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (u' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] Fin (n + 1) → ℝ)
    (hu : ∀ x ∈ interior (BoxIntegral.Box.Icc I), HasFDerivAt u (u' x) x)
    (huc : ContinuousOn u (BoxIntegral.Box.Icc I))
    (hubc : ∀ i : Fin (n + 1), ∀ x : Fin n → ℝ,
        u (i.insertNth (I.upper i) x) = 0 ∧
        u (i.insertNth (I.lower i) x) = 0)
    (hdiv : ∀ x ∈ BoxIntegral.Box.Icc I,
        ∑ i : Fin (n + 1), u' x (Pi.single i 1) i = 0)
    (hint : IntegrableOn (fun x => ∑ i, u' x (u x) i * u x i)
        (BoxIntegral.Box.Icc I)) :
    ∫ x in BoxIntegral.Box.Icc I, ∑ i, u' x (u x) i * u x i = 0 := by
  have hbox : MeasurableSet (BoxIntegral.Box.Icc I) := by
    rw [BoxIntegral.Box.Icc_def]
    exact measurableSet_Icc
  have hint_comm : IntegrableOn
      (fun x => ∑ i, u x i * u' x (u x) i) (BoxIntegral.Box.Icc I) := by
    apply hint.congr_fun
    · intro x _hx
      apply Finset.sum_congr rfl
      intro i _hi
      exact mul_comm _ _
    · exact hbox
  have hibp := vector_transport_ibp I u u u u' u' u' hu huc hu huc hu huc
    hubc hubc hdiv hint hint_comm
  have hsame :
      ∫ x in BoxIntegral.Box.Icc I, ∑ i, u x i * u' x (u x) i =
        ∫ x in BoxIntegral.Box.Icc I, ∑ i, u' x (u x) i * u x i := by
    apply setIntegral_congr_fun hbox
    intro x _hx
    apply Finset.sum_congr rfl
    intro i _hi
    exact mul_comm _ _
  rw [hsame] at hibp
  have hsum :
      (∫ x in BoxIntegral.Box.Icc I, ∑ i, u' x (u x) i * u x i) +
        ∫ x in BoxIntegral.Box.Icc I, ∑ i, u' x (u x) i * u x i = 0 := by
    calc
      _ = -(∫ x in BoxIntegral.Box.Icc I, ∑ i, u' x (u x) i * u x i) +
          ∫ x in BoxIntegral.Box.Icc I, ∑ i, u' x (u x) i * u x i := by
            nth_rewrite 1 [hibp]
            rfl
      _ = 0 := neg_add_cancel _
  calc
    ∫ x in BoxIntegral.Box.Icc I, ∑ i, u' x (u x) i * u x i =
        (2 : ℝ)⁻¹ *
          ((∫ x in BoxIntegral.Box.Icc I, ∑ i, u' x (u x) i * u x i) +
            ∫ x in BoxIntegral.Box.Icc I, ∑ i, u' x (u x) i * u x i) := by
              ring
    _ = 0 := by rw [hsum]; simp

end
