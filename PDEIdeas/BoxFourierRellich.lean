import PDEIdeas.BoxScalarRellichReduction
import PDEIdeas.GalerkinStrongCompactness
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# Fourier coordinates for scalar Rellich compactness on boxes

The unit cube is identified, up to its null boundary, with the standard
fundamental cell of the unit torus.  This file develops the measure and L2
transport used to express zero-trace box fields in the torus Fourier basis.
-/

open Filter Function InnerProductSpace MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace Topology

noncomputable section

local instance : Fact (1 <= (2 : ENNReal)) := ⟨by norm_num⟩

/-- Fourier analysis uses Haar probability measure on the unit circle. -/
local instance : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance instLpIsScalarTowerRealComplex
    {α : Type*} [MeasurableSpace α] {μ : Measure α} :
    IsScalarTower ℝ ℂ (Lp ℂ 2 μ) :=
  IsScalarTower.of_algebraMap_smul fun r f => by
    change (r : ℂ) • f = r • f
    apply Lp.ext
    filter_upwards [Lp.coeFn_smul (r : ℂ) f, Lp.coeFn_smul r f] with x hc hr
    rw [hc, hr]
    exact IsScalarTower.algebraMap_smul ℂ r (f x : ℂ)

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

variable {n : ℕ}

/-- The closed unit box in `Fin (n + 1) -> R`. -/
def unitGalerkinBox (n : ℕ) : BoxIntegral.Box (Fin (n + 1)) where
  lower := 0
  upper := 1
  lower_lt_upper := fun _ => zero_lt_one

/-- The half-open fundamental cell used by the torus parametrization. -/
def unitCubeIoc (n : ℕ) : Set (Fin (n + 1) -> ℝ) :=
  {x | forall i, x i ∈ Ioc 0 ((0 : ℝ) + 1)}

theorem measurableSet_unitCubeIoc (n : ℕ) :
    MeasurableSet (unitCubeIoc n) := by
  rw [unitCubeIoc, show
      {x : Fin (n + 1) -> ℝ |
        forall i, x i ∈ Ioc 0 ((0 : ℝ) + 1)} =
      Set.pi Set.univ (fun _ => Ioc 0 ((0 : ℝ) + 1)) by
        ext x
        simp]
  exact MeasurableSet.univ_pi (δ := Fin (n + 1)) fun _ =>
    measurableSet_Ioc

/-- The half-open unit cell and the closed unit box differ only on a null
set. -/
theorem unitCubeIoc_ae_eq_unitGalerkinBox (n : ℕ) :
    unitCubeIoc n =ᵐ[volume]
      BoxIntegral.Box.Icc (unitGalerkinBox n) := by
  have hcell : unitCubeIoc n =
      Set.pi Set.univ (fun _ : Fin (n + 1) => Ioc (0 : ℝ) 1) := by
    ext x
    simp [unitCubeIoc]
  rw [hcell, volume_pi]
  change
    (Set.pi Set.univ (fun _ : Fin (n + 1) => Ioc (0 : ℝ) 1))
      =ᵐ[Measure.pi fun _ : Fin (n + 1) => (volume : Measure ℝ)]
    Set.Icc (fun _ : Fin (n + 1) => (0 : ℝ))
      (fun _ : Fin (n + 1) => (1 : ℝ))
  exact Measure.univ_pi_Ioc_ae_eq_Icc

theorem restrict_unitCubeIoc_eq_unitGalerkinBoxMeasure (n : ℕ) :
    volume.restrict (unitCubeIoc n) =
      BoxMeasure (unitGalerkinBox n) := by
  exact Measure.restrict_congr_set
    (unitCubeIoc_ae_eq_unitGalerkinBox n)

/-- Inclusion of the half-open unit cell into the ambient Euclidean space,
with the target measure written as the closed-box measure. -/
def unitCubeSubtypeCoeMeasurePreserving (n : ℕ) :
    MeasurePreserving
      ((↑) : unitCubeIoc n -> (Fin (n + 1) -> ℝ))
      (Measure.comap
        ((↑) : unitCubeIoc n -> (Fin (n + 1) -> ℝ)) volume)
      (BoxMeasure (unitGalerkinBox n)) := by
  rw [← restrict_unitCubeIoc_eq_unitGalerkinBoxMeasure n]
  exact measurePreserving_subtype_coe (measurableSet_unitCubeIoc n)

/-- The standard representative of a torus point in the half-open unit
cell, viewed in the ambient Euclidean space. -/
def unitTorusToCube (n : ℕ) :
    UnitAddTorus (Fin (n + 1)) -> (Fin (n + 1) -> ℝ) :=
  ((↑) : unitCubeIoc n -> (Fin (n + 1) -> ℝ)) ∘
    UnitAddTorus.measurableEquivPiIoc
      (fun _ : Fin (n + 1) => (0 : ℝ))

/-- The torus parametrization preserves Haar measure and the restricted
Lebesgue measure on the unit box. -/
theorem unitTorusToCube_measurePreserving (n : ℕ) :
    MeasurePreserving (unitTorusToCube n) volume
      (BoxMeasure (unitGalerkinBox n)) := by
  exact (unitCubeSubtypeCoeMeasurePreserving n).comp
    (UnitAddTorus.measurePreserving_equivPiIoc
      (fun _ : Fin (n + 1) => (0 : ℝ)))

/-- Pullback from real L2 on the unit box to real L2 on the unit torus. -/
def unitCubeLpToRealTorus (n : ℕ) :
    BoxScalarL2 (unitGalerkinBox n) →ₗᵢ[ℝ]
      Lp ℝ 2 (volume : Measure (UnitAddTorus (Fin (n + 1)))) :=
  Lp.compMeasurePreservingₗᵢ ℝ (unitTorusToCube n)
    (unitTorusToCube_measurePreserving n)

/-- Pointwise complexification is an isometry on every real L2 space. -/
def lpOfRealLinearIsometry
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) :
    Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℂ 2 μ where
  toLinearMap := Complex.ofRealCLM.compLpL 2 μ
  norm_map' f := by
    rw [Lp.norm_def, Lp.norm_def]
    congr 1
    apply eLpNorm_congr_norm_ae
    filter_upwards [Complex.ofRealCLM.coeFn_compLpL f] with x hx
    change
      ‖((Complex.ofRealCLM.compLpL 2 μ f : Lp ℂ 2 μ) x : ℂ)‖ =
        ‖(f x : ℝ)‖
    rw [hx]
    exact Complex.norm_real (f x)

/-- Isometric realization of real unit-cube L2 inside complex torus L2. -/
def unitCubeLpToComplexTorus (n : ℕ) :
    BoxScalarL2 (unitGalerkinBox n) →ₗᵢ[ℝ]
      Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin (n + 1)))) :=
  let C := lpOfRealLinearIsometry
    (volume : Measure (UnitAddTorus (Fin (n + 1))))
  { toLinearMap := C.toLinearMap.comp
      (unitCubeLpToRealTorus n).toLinearMap
    norm_map' := fun f => by simp [C] }

/-- A torus Fourier monomial evaluated on Euclidean representatives. -/
def unitCubeFourierTest
    (k : Fin (n + 1) -> ℤ)
    (x : Fin (n + 1) -> ℝ) : ℂ :=
  UnitAddTorus.mFourier (-k) (fun i => (x i : UnitAddCircle))

theorem unitCubeLpToComplexTorus_coeFn
    (f : BoxScalarL2 (unitGalerkinBox n)) :
    unitCubeLpToComplexTorus n f =ᵐ[volume]
      fun t => (f (unitTorusToCube n t) : ℂ) := by
  let R := unitCubeLpToRealTorus n
  filter_upwards [
    Complex.ofRealCLM.coeFn_compLpL (R f),
    Lp.coeFn_compMeasurePreserving f
      (unitTorusToCube_measurePreserving n)] with t hC hR
  rw [show (unitCubeLpToComplexTorus n f :
      Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin (n + 1))))) =
        Complex.ofRealCLM.compLpL 2 volume (R f) by rfl]
  rw [hC]
  change ((R f : Lp ℝ 2 volume) t : ℂ) = _
  rw [show R f = Lp.compMeasurePreserving (unitTorusToCube n)
      (unitTorusToCube_measurePreserving n) f by rfl]
  simpa only [Function.comp_apply] using
    congrArg (fun r : ℝ => (r : ℂ)) hR

theorem unitCubeLpToComplexTorus_coeFn_on_cell
    (f : BoxScalarL2 (unitGalerkinBox n)) :
    (fun x : Fin (n + 1) -> ℝ =>
        ((unitCubeLpToComplexTorus n f :
          Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin (n + 1)))))
            (fun i => (x i : UnitAddCircle)) : ℂ))
      =ᵐ[volume.restrict (unitCubeIoc n)]
    fun x => (f x : ℂ) := by
  let e := UnitAddTorus.measurableEquivPiIoc
    (fun _ : Fin (n + 1) => (0 : ℝ))
  have heq :=
    ((UnitAddTorus.measurePreserving_equivPiIoc
      (fun _ : Fin (n + 1) => (0 : ℝ))).symm.quasiMeasurePreserving).ae_eq_comp
        (unitCubeLpToComplexTorus_coeFn f)
  apply (ae_restrict_iff_subtype (measurableSet_unitCubeIoc n)).2
  filter_upwards [heq] with x hx
  change
    ((unitCubeLpToComplexTorus n f)
        ((UnitAddTorus.measurableEquivPiIoc
          (fun _ : Fin (n + 1) => (0 : ℝ))).symm x) : ℂ) =
      (f ((UnitAddTorus.measurableEquivPiIoc
        (fun _ : Fin (n + 1) => (0 : ℝ)))
          ((UnitAddTorus.measurableEquivPiIoc
            (fun _ : Fin (n + 1) => (0 : ℝ))).symm x)) : ℂ) at hx
  rw [e.apply_symm_apply] at hx
  exact hx

/-- Fourier coefficients of the transported L2 function are the usual
box integrals against the Euclidean Fourier monomials. -/
theorem unitCube_mFourierCoeff_eq_integral
    (f : BoxScalarL2 (unitGalerkinBox n))
    (k : Fin (n + 1) -> ℤ) :
    UnitAddTorus.mFourierCoeff (unitCubeLpToComplexTorus n f) k =
      ∫ x, unitCubeFourierTest k x * (f x : ℂ)
        ∂BoxMeasure (unitGalerkinBox n) := by
  rw [UnitAddTorus.mFourierCoeff_eq_integral
    (unitCubeLpToComplexTorus n f) k
    (fun _ : Fin (n + 1) => (0 : ℝ))]
  calc
    (∫ (x : Fin (n + 1) → ℝ) in unitCubeIoc n,
        UnitAddTorus.mFourier (-k) (fun i => (x i : UnitAddCircle)) •
          (unitCubeLpToComplexTorus n f)
            (fun i => (x i : UnitAddCircle))) =
        ∫ x, unitCubeFourierTest k x * (f x : ℂ)
          ∂volume.restrict (unitCubeIoc n) := by
            apply integral_congr_ae
            filter_upwards [unitCubeLpToComplexTorus_coeFn_on_cell f] with x hx
            simp only [unitCubeFourierTest, smul_eq_mul]
            rw [hx]
    _ = _ := by rw [restrict_unitCubeIoc_eq_unitGalerkinBoxMeasure]

/-! ## Smooth Fourier tests on the unit cube -/

/-- Derivative of one factor in a multivariable Fourier monomial. -/
def unitCubeFourierFactorDerivative
    (k : Fin (n + 1) -> ℤ)
    (i : Fin (n + 1))
    (x : Fin (n + 1) -> ℝ) :
    (Fin (n + 1) -> ℝ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj i).smulRight
    (-2 * (Real.pi : ℂ) * Complex.I * (k i : ℂ) *
      fourier (-(k i)) (x i : UnitAddCircle))

/-- Fréchet derivative of a multivariable Fourier monomial, written by the
finite product rule. -/
def unitCubeFourierTestDerivative
    (k : Fin (n + 1) -> ℤ)
    (x : Fin (n + 1) -> ℝ) :
    (Fin (n + 1) -> ℝ) →L[ℝ] ℂ :=
  ∑ i : Fin (n + 1),
    (∏ j ∈ (Finset.univ.erase i),
      fourier (-(k j)) (x j : UnitAddCircle)) •
        unitCubeFourierFactorDerivative k i x

theorem hasFDerivAt_unitCubeFourierFactor
    (k : Fin (n + 1) -> ℤ)
    (i : Fin (n + 1))
    (x : Fin (n + 1) -> ℝ) :
    HasFDerivAt
      (fun y : Fin (n + 1) -> ℝ =>
        fourier (-(k i)) (y i : UnitAddCircle))
      (unitCubeFourierFactorDerivative k i x) x := by
  have h :=
    (hasDerivAt_fourier_neg (1 : ℝ) (k i) (x i)).hasFDerivAt.comp
      x (hasFDerivAt_apply (𝕜 := ℝ) i x)
  convert h using 1
  ext y
  simp [unitCubeFourierFactorDerivative]

theorem hasFDerivAt_unitCubeFourierTest
    (k : Fin (n + 1) -> ℤ)
    (x : Fin (n + 1) -> ℝ) :
    HasFDerivAt (unitCubeFourierTest k)
      (unitCubeFourierTestDerivative k x) x := by
  simpa only [unitCubeFourierTest, UnitAddTorus.mFourier,
    ContinuousMap.coe_mk, Pi.neg_apply,
    unitCubeFourierTestDerivative] using
    (HasFDerivAt.finset_prod
      (u := Finset.univ)
      (g := fun i (y : Fin (n + 1) -> ℝ) =>
        fourier (-(k i)) (y i : UnitAddCircle))
      (g' := fun i => unitCubeFourierFactorDerivative k i x)
      (x := x)
      (fun i _ => hasFDerivAt_unitCubeFourierFactor k i x))

theorem unitCubeFourierTestDerivative_single
    (k : Fin (n + 1) -> ℤ)
    (x : Fin (n + 1) -> ℝ)
    (j : Fin (n + 1)) :
    unitCubeFourierTestDerivative k x (Pi.single j 1) =
      -2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ) *
        unitCubeFourierTest k x := by
  classical
  simp only [unitCubeFourierTestDerivative,
    ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, unitCubeFourierFactorDerivative,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply]
  rw [Finset.sum_eq_single j]
  · simp only [Pi.single_eq_same, one_smul]
    change
      (∏ i ∈ Finset.univ.erase j,
        fourier (-(k i)) (x i : UnitAddCircle)) *
          (-2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ) *
            fourier (-(k j)) (x j : UnitAddCircle)) =
        -2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ) *
          unitCubeFourierTest k x
    have hprod : (∏ i ∈ Finset.univ.erase j,
        fourier (-(k i)) (x i : UnitAddCircle)) *
          fourier (-(k j)) (x j : UnitAddCircle) =
        unitCubeFourierTest k x := by
      rw [unitCubeFourierTest, UnitAddTorus.mFourier]
      simp only [ContinuousMap.coe_mk, Pi.neg_apply]
      exact Finset.prod_erase_mul Finset.univ
        (fun i => fourier (-(k i)) (x i : UnitAddCircle))
        (Finset.mem_univ j)
    calc
      _ = (-2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ)) *
          ((∏ i ∈ Finset.univ.erase j,
            fourier (-(k i)) (x i : UnitAddCircle)) *
              fourier (-(k j)) (x j : UnitAddCircle)) := by ring
      _ = _ := by rw [hprod]
  · intro i _hi hij
    simp [hij]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

theorem norm_unitCubeFourierTest
    (k : Fin (n + 1) -> ℤ)
    (x : Fin (n + 1) -> ℝ) :
    ‖unitCubeFourierTest k x‖ = 1 := by
  simp only [unitCubeFourierTest, UnitAddTorus.mFourier,
    ContinuousMap.coe_mk, Pi.neg_apply, fourier_apply,
    norm_prod, Circle.norm_coe, Finset.prod_const_one]

theorem continuous_unitCubeFourierTest
    (k : Fin (n + 1) -> ℤ) :
    Continuous (unitCubeFourierTest k) :=
  continuous_iff_continuousAt.2 fun x =>
    (hasFDerivAt_unitCubeFourierTest k x).continuousAt

def unitCubeFourierTestReDerivative
    (k : Fin (n + 1) -> ℤ)
    (x : Fin (n + 1) -> ℝ) :
    (Fin (n + 1) -> ℝ) →L[ℝ] ℝ :=
  Complex.reCLM.comp (unitCubeFourierTestDerivative k x)

def unitCubeFourierTestImDerivative
    (k : Fin (n + 1) -> ℤ)
    (x : Fin (n + 1) -> ℝ) :
    (Fin (n + 1) -> ℝ) →L[ℝ] ℝ :=
  Complex.imCLM.comp (unitCubeFourierTestDerivative k x)

theorem hasFDerivAt_unitCubeFourierTest_re
    (k : Fin (n + 1) -> ℤ)
    (x : Fin (n + 1) -> ℝ) :
    HasFDerivAt (fun y => (unitCubeFourierTest k y).re)
      (unitCubeFourierTestReDerivative k x) x := by
  exact Complex.reCLM.hasFDerivAt.comp x
    (hasFDerivAt_unitCubeFourierTest k x)

theorem hasFDerivAt_unitCubeFourierTest_im
    (k : Fin (n + 1) -> ℤ)
    (x : Fin (n + 1) -> ℝ) :
    HasFDerivAt (fun y => (unitCubeFourierTest k y).im)
      (unitCubeFourierTestImDerivative k x) x := by
  exact Complex.imCLM.hasFDerivAt.comp x
    (hasFDerivAt_unitCubeFourierTest k x)

theorem unitCubeFourierTestReDerivative_single
    (k : Fin (n + 1) -> ℤ)
    (x : Fin (n + 1) -> ℝ)
    (j : Fin (n + 1)) :
    unitCubeFourierTestReDerivative k x (Pi.single j 1) =
      (-2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ) *
        unitCubeFourierTest k x).re := by
  simp [unitCubeFourierTestReDerivative,
    unitCubeFourierTestDerivative_single]

theorem unitCubeFourierTestImDerivative_single
    (k : Fin (n + 1) -> ℤ)
    (x : Fin (n + 1) -> ℝ)
    (j : Fin (n + 1)) :
    unitCubeFourierTestImDerivative k x (Pi.single j 1) =
      (-2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ) *
        unitCubeFourierTest k x).im := by
  simp [unitCubeFourierTestImDerivative,
    unitCubeFourierTestDerivative_single]

private theorem unitGalerkinBox_isFiniteMeasure (n : ℕ) :
    IsFiniteMeasure (BoxMeasure (unitGalerkinBox n)) := by
  rw [isFiniteMeasure_restrict]
  rw [BoxIntegral.Box.Icc_def, Real.volume_Icc_pi]
  simp [unitGalerkinBox]

theorem unitCubeFourierTest_memLp
    (k : Fin (n + 1) -> ℤ) :
    MemLp (unitCubeFourierTest k) 2
      (BoxMeasure (unitGalerkinBox n)) := by
  letI := unitGalerkinBox_isFiniteMeasure n
  apply MemLp.of_bound
    (continuous_unitCubeFourierTest k).aestronglyMeasurable 1
  filter_upwards with x
  exact (norm_unitCubeFourierTest k x).le

theorem unitCubeFourierTest_re_memLp
    (k : Fin (n + 1) -> ℤ) :
    MemLp (fun x => (unitCubeFourierTest k x).re) 2
      (BoxMeasure (unitGalerkinBox n)) := by
  letI := unitGalerkinBox_isFiniteMeasure n
  apply MemLp.of_bound
    ((Complex.continuous_re.comp
      (continuous_unitCubeFourierTest k)).aestronglyMeasurable) 1
  filter_upwards with x
  exact (Complex.abs_re_le_norm _).trans_eq
    (norm_unitCubeFourierTest k x)

theorem unitCubeFourierTest_im_memLp
    (k : Fin (n + 1) -> ℤ) :
    MemLp (fun x => (unitCubeFourierTest k x).im) 2
      (BoxMeasure (unitGalerkinBox n)) := by
  letI := unitGalerkinBox_isFiniteMeasure n
  apply MemLp.of_bound
    ((Complex.continuous_im.comp
      (continuous_unitCubeFourierTest k)).aestronglyMeasurable) 1
  filter_upwards with x
  exact (Complex.abs_im_le_norm _).trans_eq
    (norm_unitCubeFourierTest k x)

theorem unitCubeFourierTestReDerivative_single_memLp
    (k : Fin (n + 1) -> ℤ)
    (j : Fin (n + 1)) :
    MemLp
      (fun x => unitCubeFourierTestReDerivative k x (Pi.single j 1)) 2
      (BoxMeasure (unitGalerkinBox n)) := by
  letI := unitGalerkinBox_isFiniteMeasure n
  have hcont : Continuous
      (fun x => unitCubeFourierTestReDerivative k x (Pi.single j 1)) := by
    simpa only [unitCubeFourierTestReDerivative_single] using
      Complex.continuous_re.comp
        (continuous_const.mul (continuous_unitCubeFourierTest k))
  apply MemLp.of_bound hcont.aestronglyMeasurable
    ‖-2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ)‖
  filter_upwards with x
  rw [unitCubeFourierTestReDerivative_single]
  calc
    ‖(-2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ) *
        unitCubeFourierTest k x).re‖
        <= ‖-2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ) *
          unitCubeFourierTest k x‖ := Complex.abs_re_le_norm _
    _ = ‖-2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ)‖ := by
      rw [norm_mul, norm_unitCubeFourierTest, mul_one]

theorem unitCubeFourierTestImDerivative_single_memLp
    (k : Fin (n + 1) -> ℤ)
    (j : Fin (n + 1)) :
    MemLp
      (fun x => unitCubeFourierTestImDerivative k x (Pi.single j 1)) 2
      (BoxMeasure (unitGalerkinBox n)) := by
  letI := unitGalerkinBox_isFiniteMeasure n
  have hcont : Continuous
      (fun x => unitCubeFourierTestImDerivative k x (Pi.single j 1)) := by
    simpa only [unitCubeFourierTestImDerivative_single] using
      Complex.continuous_im.comp
        (continuous_const.mul (continuous_unitCubeFourierTest k))
  apply MemLp.of_bound hcont.aestronglyMeasurable
    ‖-2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ)‖
  filter_upwards with x
  rw [unitCubeFourierTestImDerivative_single]
  calc
    ‖(-2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ) *
        unitCubeFourierTest k x).im‖
        <= ‖-2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ) *
          unitCubeFourierTest k x‖ := Complex.abs_im_le_norm _
    _ = ‖-2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ)‖ := by
      rw [norm_mul, norm_unitCubeFourierTest, mul_one]

theorem unitCubeFourierTestDerivative_single_memLp
    (k : Fin (n + 1) -> ℤ)
    (j : Fin (n + 1)) :
    MemLp
      (fun x => unitCubeFourierTestDerivative k x (Pi.single j 1)) 2
      (BoxMeasure (unitGalerkinBox n)) := by
  letI := unitGalerkinBox_isFiniteMeasure n
  have hcont : Continuous
      (fun x => unitCubeFourierTestDerivative k x (Pi.single j 1)) := by
    simpa only [unitCubeFourierTestDerivative_single] using
      continuous_const.mul (continuous_unitCubeFourierTest k)
  apply MemLp.of_bound hcont.aestronglyMeasurable
    ‖-2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ)‖
  filter_upwards with x
  rw [unitCubeFourierTestDerivative_single, norm_mul,
    norm_unitCubeFourierTest, mul_one]

theorem SmoothBoxScalarH1ZeroField.gradientCoordinate_memLp
    (u : SmoothBoxScalarH1ZeroField (unitGalerkinBox n))
    (j : Fin (n + 1)) :
    MemLp (fun x => u.derivative x (Pi.single j 1)) 2
      (BoxMeasure (unitGalerkinBox n)) := by
  simpa [boxVelocityCoordinateValue, boxScalarGradientValue] using
    u.gradient_memLp.continuousLinearMap_comp
      (boxVelocityCoordinateValue j)

/-- Complex integration by parts against a Fourier monomial, obtained by
combining the real and imaginary coordinate identities. -/
theorem SmoothBoxScalarH1ZeroField.integral_gradient_mul_fourier
    (u : SmoothBoxScalarH1ZeroField (unitGalerkinBox n))
    (k : Fin (n + 1) -> ℤ)
    (j : Fin (n + 1)) :
    ∫ x, (u.derivative x (Pi.single j 1) : ℂ) *
        unitCubeFourierTest k x ∂BoxMeasure (unitGalerkinBox n) =
      -∫ x, (u.field x : ℂ) *
        unitCubeFourierTestDerivative k x (Pi.single j 1)
        ∂BoxMeasure (unitGalerkinBox n) := by
  have hleftRe := (u.gradientCoordinate_memLp j).integrable_mul
    (unitCubeFourierTest_re_memLp k)
  have hrightRe := u.field_memLp.integrable_mul
    (unitCubeFourierTestReDerivative_single_memLp k j)
  have hibpRe := scalar_coordinate_ibp (unitGalerkinBox n) j
    u.field (fun x => (unitCubeFourierTest k x).re)
    u.derivative (unitCubeFourierTestReDerivative k)
    u.hasFDerivAt_field u.continuousOn_field
    (fun x _ => hasFDerivAt_unitCubeFourierTest_re k x)
    ((Complex.continuous_re.comp
      (continuous_unitCubeFourierTest k)).continuousOn)
    u.zeroDirichlet_field hleftRe hrightRe
  have hleftIm := (u.gradientCoordinate_memLp j).integrable_mul
    (unitCubeFourierTest_im_memLp k)
  have hrightIm := u.field_memLp.integrable_mul
    (unitCubeFourierTestImDerivative_single_memLp k j)
  have hibpIm := scalar_coordinate_ibp (unitGalerkinBox n) j
    u.field (fun x => (unitCubeFourierTest k x).im)
    u.derivative (unitCubeFourierTestImDerivative k)
    u.hasFDerivAt_field u.continuousOn_field
    (fun x _ => hasFDerivAt_unitCubeFourierTest_im k x)
    ((Complex.continuous_im.comp
      (continuous_unitCubeFourierTest k)).continuousOn)
    u.zeroDirichlet_field hleftIm hrightIm
  have hleft : Integrable
      (fun x => (u.derivative x (Pi.single j 1) : ℂ) *
        unitCubeFourierTest k x) (BoxMeasure (unitGalerkinBox n)) := by
    exact (u.gradientCoordinate_memLp j).ofReal.integrable_mul
      (unitCubeFourierTest_memLp k)
  have hright : Integrable
      (fun x => (u.field x : ℂ) *
        unitCubeFourierTestDerivative k x (Pi.single j 1))
      (BoxMeasure (unitGalerkinBox n)) := by
    exact u.field_memLp.ofReal.integrable_mul
      (unitCubeFourierTestDerivative_single_memLp k j)
  apply Complex.ext
  · have hleftIntegral :
        (∫ x, (u.derivative x (Pi.single j 1) : ℂ) *
            unitCubeFourierTest k x
            ∂BoxMeasure (unitGalerkinBox n)).re =
          ∫ x, u.derivative x (Pi.single j 1) *
            (unitCubeFourierTest k x).re
            ∂BoxMeasure (unitGalerkinBox n) := by
          calc
            _ = ∫ x, RCLike.re
                ((u.derivative x (Pi.single j 1) : ℂ) *
                  unitCubeFourierTest k x)
                ∂BoxMeasure (unitGalerkinBox n) :=
              (integral_re hleft).symm
            _ = _ := by
              apply integral_congr_ae
              filter_upwards with x
              simp
    have hrightIntegral :
        (∫ x, (u.field x : ℂ) *
            unitCubeFourierTestDerivative k x (Pi.single j 1)
            ∂BoxMeasure (unitGalerkinBox n)).re =
          ∫ x, u.field x *
            unitCubeFourierTestReDerivative k x (Pi.single j 1)
            ∂BoxMeasure (unitGalerkinBox n) := by
          calc
            _ = ∫ x, RCLike.re
                ((u.field x : ℂ) *
                  unitCubeFourierTestDerivative k x (Pi.single j 1))
                ∂BoxMeasure (unitGalerkinBox n) :=
              (integral_re hright).symm
            _ = _ := by
              apply integral_congr_ae
              filter_upwards with x
              simp [unitCubeFourierTestReDerivative]
    calc
      _ = ∫ x, u.derivative x (Pi.single j 1) *
            (unitCubeFourierTest k x).re
            ∂BoxMeasure (unitGalerkinBox n) := hleftIntegral
      _ = -∫ x, u.field x *
            unitCubeFourierTestReDerivative k x (Pi.single j 1)
            ∂BoxMeasure (unitGalerkinBox n) := hibpRe
      _ = -(∫ x, (u.field x : ℂ) *
            unitCubeFourierTestDerivative k x (Pi.single j 1)
            ∂BoxMeasure (unitGalerkinBox n)).re :=
        congrArg Neg.neg hrightIntegral.symm
      _ = (-∫ x, (u.field x : ℂ) *
            unitCubeFourierTestDerivative k x (Pi.single j 1)
            ∂BoxMeasure (unitGalerkinBox n)).re := by simp
  · have hleftIntegral :
        (∫ x, (u.derivative x (Pi.single j 1) : ℂ) *
            unitCubeFourierTest k x
            ∂BoxMeasure (unitGalerkinBox n)).im =
          ∫ x, u.derivative x (Pi.single j 1) *
            (unitCubeFourierTest k x).im
            ∂BoxMeasure (unitGalerkinBox n) := by
          calc
            _ = ∫ x, RCLike.im
                ((u.derivative x (Pi.single j 1) : ℂ) *
                  unitCubeFourierTest k x)
                ∂BoxMeasure (unitGalerkinBox n) :=
              (integral_im hleft).symm
            _ = _ := by
              apply integral_congr_ae
              filter_upwards with x
              simp
    have hrightIntegral :
        (∫ x, (u.field x : ℂ) *
            unitCubeFourierTestDerivative k x (Pi.single j 1)
            ∂BoxMeasure (unitGalerkinBox n)).im =
          ∫ x, u.field x *
            unitCubeFourierTestImDerivative k x (Pi.single j 1)
            ∂BoxMeasure (unitGalerkinBox n) := by
          calc
            _ = ∫ x, RCLike.im
                ((u.field x : ℂ) *
                  unitCubeFourierTestDerivative k x (Pi.single j 1))
                ∂BoxMeasure (unitGalerkinBox n) :=
              (integral_im hright).symm
            _ = _ := by
              apply integral_congr_ae
              filter_upwards with x
              simp [unitCubeFourierTestImDerivative]
    calc
      _ = ∫ x, u.derivative x (Pi.single j 1) *
            (unitCubeFourierTest k x).im
            ∂BoxMeasure (unitGalerkinBox n) := hleftIntegral
      _ = -∫ x, u.field x *
            unitCubeFourierTestImDerivative k x (Pi.single j 1)
            ∂BoxMeasure (unitGalerkinBox n) := hibpIm
      _ = -(∫ x, (u.field x : ℂ) *
            unitCubeFourierTestDerivative k x (Pi.single j 1)
            ∂BoxMeasure (unitGalerkinBox n)).im :=
        congrArg Neg.neg hrightIntegral.symm
      _ = (-∫ x, (u.field x : ℂ) *
            unitCubeFourierTestDerivative k x (Pi.single j 1)
            ∂BoxMeasure (unitGalerkinBox n)).im := by simp

def SmoothBoxScalarH1ZeroField.gradientCoordinateLp
    (u : SmoothBoxScalarH1ZeroField (unitGalerkinBox n))
    (j : Fin (n + 1)) :
    BoxScalarL2 (unitGalerkinBox n) :=
  boxVelocityCoordinateLp (unitGalerkinBox n) j u.gradientLp

@[simp]
theorem SmoothBoxScalarH1ZeroField.gradientCoordinateLp_eq_toLp
    (u : SmoothBoxScalarH1ZeroField (unitGalerkinBox n))
    (j : Fin (n + 1)) :
    u.gradientCoordinateLp j =
      (u.gradientCoordinate_memLp j).toLp
        (fun x => u.derivative x (Pi.single j 1)) := by
  apply Lp.ext
  filter_upwards [
    (boxVelocityCoordinateValue j).coeFn_compLpL u.gradientLp,
    u.gradient_memLp.coeFn_toLp,
    (u.gradientCoordinate_memLp j).coeFn_toLp] with x hcoord hgrad hrhs
  change
    ((boxVelocityCoordinateLp (unitGalerkinBox n) j u.gradientLp) x : ℝ) = _
  simp only [boxVelocityCoordinateLp]
  rw [hcoord, hrhs]
  simpa [SmoothBoxScalarH1ZeroField.gradientCoordinateLp,
    SmoothBoxScalarH1ZeroField.gradientLp, boxVelocityCoordinateValue,
    boxScalarGradientValue] using
    congrArg (boxVelocityCoordinateValue j) hgrad

theorem SmoothBoxScalarH1ZeroField.mFourierCoeff_velocityLp
    (u : SmoothBoxScalarH1ZeroField (unitGalerkinBox n))
    (k : Fin (n + 1) -> ℤ) :
    UnitAddTorus.mFourierCoeff
        (unitCubeLpToComplexTorus n u.velocityLp) k =
      ∫ x, unitCubeFourierTest k x * (u.field x : ℂ)
        ∂BoxMeasure (unitGalerkinBox n) := by
  rw [unitCube_mFourierCoeff_eq_integral]
  apply integral_congr_ae
  filter_upwards [u.field_memLp.coeFn_toLp] with x hx
  simp only [SmoothBoxScalarH1ZeroField.velocityLp]
  rw [hx]

theorem SmoothBoxScalarH1ZeroField.mFourierCoeff_gradientCoordinateLp
    (u : SmoothBoxScalarH1ZeroField (unitGalerkinBox n))
    (j : Fin (n + 1))
    (k : Fin (n + 1) -> ℤ) :
    UnitAddTorus.mFourierCoeff
        (unitCubeLpToComplexTorus n (u.gradientCoordinateLp j)) k =
      ∫ x, unitCubeFourierTest k x *
        (u.derivative x (Pi.single j 1) : ℂ)
        ∂BoxMeasure (unitGalerkinBox n) := by
  rw [unitCube_mFourierCoeff_eq_integral,
    u.gradientCoordinateLp_eq_toLp j]
  apply integral_congr_ae
  filter_upwards [(u.gradientCoordinate_memLp j).coeFn_toLp] with x hx
  rw [hx]

/-- On the smooth zero-face core, differentiation multiplies the `k`th
Fourier coefficient by `2 pi i k_j`. -/
theorem SmoothBoxScalarH1ZeroField.mFourierCoeff_gradientCoordinateLp_eq
    (u : SmoothBoxScalarH1ZeroField (unitGalerkinBox n))
    (j : Fin (n + 1))
    (k : Fin (n + 1) -> ℤ) :
    UnitAddTorus.mFourierCoeff
        (unitCubeLpToComplexTorus n (u.gradientCoordinateLp j)) k =
      2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ) *
        UnitAddTorus.mFourierCoeff
          (unitCubeLpToComplexTorus n u.velocityLp) k := by
  rw [u.mFourierCoeff_gradientCoordinateLp,
    u.mFourierCoeff_velocityLp]
  calc
    (∫ x, unitCubeFourierTest k x *
        (u.derivative x (Pi.single j 1) : ℂ)
        ∂BoxMeasure (unitGalerkinBox n)) =
        ∫ x, (u.derivative x (Pi.single j 1) : ℂ) *
          unitCubeFourierTest k x
          ∂BoxMeasure (unitGalerkinBox n) := by
            apply integral_congr_ae
            filter_upwards with x
            ring
    _ = -∫ x, (u.field x : ℂ) *
        unitCubeFourierTestDerivative k x (Pi.single j 1)
        ∂BoxMeasure (unitGalerkinBox n) :=
      u.integral_gradient_mul_fourier k j
    _ = -∫ x,
        (-2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ)) *
          (unitCubeFourierTest k x * (u.field x : ℂ))
        ∂BoxMeasure (unitGalerkinBox n) := by
          apply congrArg Neg.neg
          apply integral_congr_ae
          filter_upwards with x
          rw [unitCubeFourierTestDerivative_single]
          ring
    _ = -( (-2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ)) *
        ∫ x, unitCubeFourierTest k x * (u.field x : ℂ)
          ∂BoxMeasure (unitGalerkinBox n)) := by
            congr 1
            exact integral_const_mul
              (-2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ))
              (fun x => unitCubeFourierTest k x * (u.field x : ℂ))
    _ = 2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ) *
        ∫ x, unitCubeFourierTest k x * (u.field x : ℂ)
          ∂BoxMeasure (unitGalerkinBox n) := by ring

/-- The `k`th Fourier coefficient as a real continuous linear functional on
real L2 of the unit cube. -/
def unitCubeFourierCoeffCLM
    (k : Fin (n + 1) -> ℤ) :
    BoxScalarL2 (unitGalerkinBox n) →L[ℝ] ℂ :=
  let T : Lp ℂ 2
        (volume : Measure (UnitAddTorus (Fin (n + 1)))) →L[ℂ] ℂ :=
    (lp.evalCLM ℂ (fun _ : Fin (n + 1) -> ℤ => ℂ) 2 k).comp
      UnitAddTorus.mFourierBasis.repr.toContinuousLinearEquiv.toContinuousLinearMap
  let TR : Lp ℂ 2
        (volume : Measure (UnitAddTorus (Fin (n + 1)))) →L[ℝ] ℂ :=
    { toLinearMap :=
        { toFun := T
          map_add' := T.map_add
          map_smul' := fun r f => by
            simp only [RingHom.id_apply]
            rw [← IsScalarTower.algebraMap_smul ℂ r f, T.map_smul]
            exact Complex.real_smul.symm }
      cont := T.continuous }
  TR.comp (unitCubeLpToComplexTorus n).toContinuousLinearMap

@[simp]
theorem unitCubeFourierCoeffCLM_apply
    (k : Fin (n + 1) -> ℤ)
    (f : BoxScalarL2 (unitGalerkinBox n)) :
    unitCubeFourierCoeffCLM k f =
      UnitAddTorus.mFourierCoeff
        (unitCubeLpToComplexTorus n f) k := by
  change UnitAddTorus.mFourierBasis.repr
    (unitCubeLpToComplexTorus n f) k = _
  exact UnitAddTorus.mFourierBasis_repr _ _

/-- Projection onto the scalar-gradient component of the graph ambient
space. -/
def boxScalarEnergyGradientProjection
    (I : BoxIntegral.Box (Fin (n + 1))) :
    BoxScalarEnergyAmbient I →L[ℝ] BoxScalarGradientL2 I :=
  WithLp.sndL 2 ℝ (BoxScalarL2 I) (BoxScalarGradientL2 I)

/-- The closed coefficient relation on the scalar graph ambient space. -/
def unitCubeFourierDerivativeRelation
    (j : Fin (n + 1))
    (k : Fin (n + 1) -> ℤ) :
    BoxScalarEnergyAmbient (unitGalerkinBox n) →L[ℝ] ℂ :=
  (unitCubeFourierCoeffCLM k).comp
      ((boxVelocityCoordinateLp (unitGalerkinBox n) j).comp
        (boxScalarEnergyGradientProjection (unitGalerkinBox n))) -
    (2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ)) •
      ((unitCubeFourierCoeffCLM k).comp
        (boxScalarEnergyVelocityProjection (unitGalerkinBox n)))

theorem unitCubeFourierDerivativeRelation_graphPoint
    (u : SmoothBoxScalarH1ZeroField (unitGalerkinBox n))
    (j : Fin (n + 1))
    (k : Fin (n + 1) -> ℤ) :
    unitCubeFourierDerivativeRelation j k u.graphPoint = 0 := by
  change
    unitCubeFourierCoeffCLM k (u.gradientCoordinateLp j) -
      (2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ)) *
        unitCubeFourierCoeffCLM k u.velocityLp = 0
  rw [unitCubeFourierCoeffCLM_apply,
    unitCubeFourierCoeffCLM_apply,
    u.mFourierCoeff_gradientCoordinateLp_eq j k]
  ring

theorem smoothBoxScalarFullGraphCore_le_fourierDerivativeRelation_ker
    (j : Fin (n + 1))
    (k : Fin (n + 1) -> ℤ) :
    smoothBoxScalarFullGraphCore (unitGalerkinBox n) ≤
      (unitCubeFourierDerivativeRelation j k).ker := by
  apply Submodule.span_le.mpr
  rintro _ ⟨u, rfl⟩
  exact unitCubeFourierDerivativeRelation_graphPoint u j k

/-- The Fourier derivative identity persists on the completed scalar graph. -/
theorem unitCubeFourierCoeff_gradient_eq
    (u : BoxH1ZeroScalarFull (unitGalerkinBox n))
    (j : Fin (n + 1))
    (k : Fin (n + 1) -> ℤ) :
    unitCubeFourierCoeffCLM k
        (boxVelocityCoordinateLp (unitGalerkinBox n) j
          (boxScalarEnergyGradientProjection (unitGalerkinBox n)
            (u : BoxScalarEnergyAmbient (unitGalerkinBox n)))) =
      2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ) *
        unitCubeFourierCoeffCLM k
          (boxScalarEnergyVelocityProjection (unitGalerkinBox n)
            (u : BoxScalarEnergyAmbient (unitGalerkinBox n))) := by
  have hu : (u : BoxScalarEnergyAmbient (unitGalerkinBox n)) ∈
      (unitCubeFourierDerivativeRelation j k).ker :=
    (smoothBoxScalarFullGraphCore (unitGalerkinBox n)).topologicalClosure_minimal
      (smoothBoxScalarFullGraphCore_le_fourierDerivativeRelation_ker j k)
      (unitCubeFourierDerivativeRelation j k).isClosed_ker u.property
  change unitCubeFourierDerivativeRelation j k
    (u : BoxScalarEnergyAmbient (unitGalerkinBox n)) = 0 at hu
  change _ - (2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ)) * _ = 0 at hu
  exact sub_eq_zero.mp hu

theorem tsum_sq_mFourierCoeff_eq_norm_sq
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin (n + 1))))) :
    ∑' k : Fin (n + 1) -> ℤ,
        ‖UnitAddTorus.mFourierCoeff f k‖ ^ 2 = ‖f‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := (2 : ENNReal))
    (by norm_num) (UnitAddTorus.mFourierBasis.repr f)
  calc
    (∑' k : Fin (n + 1) -> ℤ,
        ‖UnitAddTorus.mFourierCoeff f k‖ ^ (2 : ℕ)) =
      ∑' k : Fin (n + 1) -> ℤ,
        ‖UnitAddTorus.mFourierCoeff f k‖ ^ (2 : ENNReal).toReal := by
          norm_cast
    _ = ‖UnitAddTorus.mFourierBasis.repr f‖ ^
        (2 : ENNReal).toReal := by
          simpa only [UnitAddTorus.mFourierBasis_repr] using h.symm
    _ = ‖f‖ ^ (2 : ℕ) := by
      rw [LinearIsometryEquiv.norm_map]
      norm_cast

/-- Frequencies whose every coordinate lies between `-N` and `N`. -/
def unitCubeFrequencyBox
    (n N : ℕ) : Finset (Fin (n + 1) -> ℤ) :=
  Fintype.piFinset fun _ : Fin (n + 1) =>
    Finset.Icc (-(N : ℤ)) (N : ℤ)

theorem exists_large_coordinate_of_not_mem_frequencyBox
    {N : ℕ}
    (k : Fin (n + 1) -> ℤ)
    (hk : k ∉ unitCubeFrequencyBox n N) :
    ∃ j : Fin (n + 1), (N : ℝ) <= |(k j : ℝ)| := by
  classical
  by_contra h
  push Not at h
  apply hk
  rw [unitCubeFrequencyBox, Fintype.mem_piFinset]
  intro j
  rw [Finset.mem_Icc]
  have habs : |(k j : ℝ)| < (N : ℝ) := h j
  have hbounds := (abs_lt.mp habs)
  constructor
  · exact_mod_cast (le_of_lt hbounds.1)
  · exact_mod_cast (le_of_lt hbounds.2)

theorem unitCube_fourierCoeff_sq_le_gradient_sum
    (u : BoxH1ZeroScalarFull (unitGalerkinBox n))
    {N : ℕ}
    (hN : 0 < N)
    (k : Fin (n + 1) -> ℤ)
    (hk : k ∉ unitCubeFrequencyBox n N) :
    ‖unitCubeFourierCoeffCLM k
        (boxScalarEnergyVelocityProjection (unitGalerkinBox n)
          (u : BoxScalarEnergyAmbient (unitGalerkinBox n)))‖ ^ 2 <=
      (1 / (N : ℝ) ^ 2) *
        ∑ j : Fin (n + 1),
          ‖unitCubeFourierCoeffCLM k
            (boxVelocityCoordinateLp (unitGalerkinBox n) j
              (boxScalarEnergyGradientProjection (unitGalerkinBox n)
                (u : BoxScalarEnergyAmbient (unitGalerkinBox n))))‖ ^ 2 := by
  obtain ⟨j, hj⟩ :=
    exists_large_coordinate_of_not_mem_frequencyBox k hk
  let c := unitCubeFourierCoeffCLM k
    (boxScalarEnergyVelocityProjection (unitGalerkinBox n)
      (u : BoxScalarEnergyAmbient (unitGalerkinBox n)))
  let g := unitCubeFourierCoeffCLM k
    (boxVelocityCoordinateLp (unitGalerkinBox n) j
      (boxScalarEnergyGradientProjection (unitGalerkinBox n)
        (u : BoxScalarEnergyAmbient (unitGalerkinBox n))))
  have hg : g =
      2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ) * c := by
    exact unitCubeFourierCoeff_gradient_eq u j k
  have hfactor : (N : ℝ) <= 2 * Real.pi * |(k j : ℝ)| := by
    calc
      (N : ℝ) <= |(k j : ℝ)| := hj
      _ <= 2 * Real.pi * |(k j : ℝ)| := by
        apply le_mul_of_one_le_left (abs_nonneg _)
        nlinarith [Real.two_le_pi]
  have hnorm : (N : ℝ) * ‖c‖ <= ‖g‖ := by
    rw [hg]
    calc
      (N : ℝ) * ‖c‖ <=
          (2 * Real.pi * |(k j : ℝ)|) * ‖c‖ :=
        mul_le_mul_of_nonneg_right hfactor (norm_nonneg c)
      _ = ‖2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ) * c‖ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos Real.pi_pos, Complex.norm_I,
          Complex.norm_intCast, mul_one]
        norm_num
  have hsq : (N : ℝ) ^ 2 * ‖c‖ ^ 2 <= ‖g‖ ^ 2 := by
    have hmul := mul_self_le_mul_self
      (mul_nonneg (by positivity) (norm_nonneg c)) hnorm
    calc
      (N : ℝ) ^ 2 * ‖c‖ ^ 2 =
          ((N : ℝ) * ‖c‖) * ((N : ℝ) * ‖c‖) := by ring
      _ <= ‖g‖ * ‖g‖ := hmul
      _ = ‖g‖ ^ 2 := by ring
  have hsum : ‖g‖ ^ 2 <=
      ∑ i : Fin (n + 1),
        ‖unitCubeFourierCoeffCLM k
          (boxVelocityCoordinateLp (unitGalerkinBox n) i
            (boxScalarEnergyGradientProjection (unitGalerkinBox n)
              (u : BoxScalarEnergyAmbient (unitGalerkinBox n))))‖ ^ 2 := by
    exact Finset.single_le_sum (fun i _ => sq_nonneg
      ‖unitCubeFourierCoeffCLM k
        (boxVelocityCoordinateLp (unitGalerkinBox n) i
          (boxScalarEnergyGradientProjection (unitGalerkinBox n)
            (u : BoxScalarEnergyAmbient (unitGalerkinBox n))))‖)
      (Finset.mem_univ j)
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  change ‖c‖ ^ 2 <= _
  calc
    ‖c‖ ^ 2 =
        (1 / (N : ℝ) ^ 2) * ((N : ℝ) ^ 2 * ‖c‖ ^ 2) := by
      field_simp [hNreal.ne']
    _ <= (1 / (N : ℝ) ^ 2) * ‖g‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ <= (1 / (N : ℝ) ^ 2) * _ :=
      mul_le_mul_of_nonneg_left hsum (by positivity)

theorem unitCube_fourierTail_tsum_le
    (u : BoxH1ZeroScalarFull (unitGalerkinBox n))
    {N : ℕ}
    (hN : 0 < N) :
    (∑' k : Fin (n + 1) -> ℤ,
      if k ∈ unitCubeFrequencyBox n N then 0 else
        ‖unitCubeFourierCoeffCLM k
          (boxScalarEnergyVelocityProjection (unitGalerkinBox n)
            (u : BoxScalarEnergyAmbient (unitGalerkinBox n)))‖ ^ 2) <=
      (1 / (N : ℝ) ^ 2) *
        ∑ j : Fin (n + 1),
          ‖unitCubeLpToComplexTorus n
            (boxVelocityCoordinateLp (unitGalerkinBox n) j
              (boxScalarEnergyGradientProjection (unitGalerkinBox n)
                (u : BoxScalarEnergyAmbient (unitGalerkinBox n))))‖ ^ 2 := by
  classical
  let v := boxScalarEnergyVelocityProjection (unitGalerkinBox n)
    (u : BoxScalarEnergyAmbient (unitGalerkinBox n))
  let g : Fin (n + 1) -> BoxScalarL2 (unitGalerkinBox n) := fun j =>
    boxVelocityCoordinateLp (unitGalerkinBox n) j
      (boxScalarEnergyGradientProjection (unitGalerkinBox n)
        (u : BoxScalarEnergyAmbient (unitGalerkinBox n)))
  have hvSummable : Summable (fun k : Fin (n + 1) -> ℤ =>
      ‖unitCubeFourierCoeffCLM k v‖ ^ 2) := by
    simpa only [unitCubeFourierCoeffCLM_apply] using
      (UnitAddTorus.hasSum_sq_mFourierCoeff
        (unitCubeLpToComplexTorus n v)).summable
  have htailSummable : Summable (fun k : Fin (n + 1) -> ℤ =>
      if k ∈ unitCubeFrequencyBox n N then 0 else
        ‖unitCubeFourierCoeffCLM k v‖ ^ 2) := by
    apply hvSummable.of_nonneg_of_le
    · intro k
      by_cases hk : k ∈ unitCubeFrequencyBox n N <;>
        simp [hk]
    · intro k
      by_cases hk : k ∈ unitCubeFrequencyBox n N <;>
        simp [hk]
  have hgSummable (j : Fin (n + 1)) :
      Summable (fun k : Fin (n + 1) -> ℤ =>
        ‖unitCubeFourierCoeffCLM k (g j)‖ ^ 2) := by
    simpa only [unitCubeFourierCoeffCLM_apply] using
      (UnitAddTorus.hasSum_sq_mFourierCoeff
        (unitCubeLpToComplexTorus n (g j))).summable
  have hsumSummable : Summable (fun k : Fin (n + 1) -> ℤ =>
      ∑ j : Fin (n + 1),
        ‖unitCubeFourierCoeffCLM k (g j)‖ ^ 2) := by
    exact summable_sum (s := Finset.univ) fun j _ => hgSummable j
  have hrhsSummable : Summable (fun k : Fin (n + 1) -> ℤ =>
      (1 / (N : ℝ) ^ 2) *
        ∑ j : Fin (n + 1),
          ‖unitCubeFourierCoeffCLM k (g j)‖ ^ 2) :=
    hsumSummable.mul_left _
  change (∑' k, if k ∈ unitCubeFrequencyBox n N then 0 else
      ‖unitCubeFourierCoeffCLM k v‖ ^ 2) <= _
  calc
    (∑' k, if k ∈ unitCubeFrequencyBox n N then 0 else
        ‖unitCubeFourierCoeffCLM k v‖ ^ 2) <=
        ∑' k, (1 / (N : ℝ) ^ 2) *
          ∑ j : Fin (n + 1),
            ‖unitCubeFourierCoeffCLM k (g j)‖ ^ 2 := by
      apply htailSummable.tsum_le_tsum
      · intro k
        by_cases hk : k ∈ unitCubeFrequencyBox n N
        · simp only [if_pos hk]
          apply mul_nonneg (by positivity)
          exact Finset.sum_nonneg fun _ _ => sq_nonneg _
        · simpa only [if_false, hk, v, g] using
            unitCube_fourierCoeff_sq_le_gradient_sum u hN k hk
      · exact hrhsSummable
    _ = (1 / (N : ℝ) ^ 2) *
        ∑' k, ∑ j : Fin (n + 1),
          ‖unitCubeFourierCoeffCLM k (g j)‖ ^ 2 := by
      rw [tsum_mul_left]
    _ = (1 / (N : ℝ) ^ 2) *
        ∑ j : Fin (n + 1), ∑' k,
          ‖unitCubeFourierCoeffCLM k (g j)‖ ^ 2 := by
      rw [Summable.tsum_finsetSum fun j _ => hgSummable j]
    _ = (1 / (N : ℝ) ^ 2) *
        ∑ j : Fin (n + 1),
          ‖unitCubeLpToComplexTorus n (g j)‖ ^ 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _hj
      simpa only [unitCubeFourierCoeffCLM_apply] using
        tsum_sq_mFourierCoeff_eq_norm_sq
          (unitCubeLpToComplexTorus n (g j))
    _ = _ := rfl

theorem norm_boxVelocityCoordinateLp_le
    (I : BoxIntegral.Box (Fin (n + 1)))
    (j : Fin (n + 1))
    (f : BoxScalarGradientL2 I) :
    ‖boxVelocityCoordinateLp I j f‖ <= ‖f‖ := by
  have hcoord : ‖boxVelocityCoordinateValue j‖ <= 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simpa [boxVelocityCoordinateValue] using PiLp.norm_apply_le x j
  calc
    ‖boxVelocityCoordinateLp I j f‖ <=
        ‖boxVelocityCoordinateValue j‖ * ‖f‖ := by
      exact ContinuousLinearMap.norm_compLp_le
        (boxVelocityCoordinateValue j) f
    _ <= 1 * ‖f‖ :=
      mul_le_mul_of_nonneg_right hcoord (norm_nonneg f)
    _ = ‖f‖ := one_mul _

theorem unitCube_gradientCoordinateTorus_norm_le
    (u : BoxH1ZeroScalarFull (unitGalerkinBox n))
    (j : Fin (n + 1)) :
    ‖unitCubeLpToComplexTorus n
      (boxVelocityCoordinateLp (unitGalerkinBox n) j
        (boxScalarEnergyGradientProjection (unitGalerkinBox n)
          (u : BoxScalarEnergyAmbient (unitGalerkinBox n))))‖ <= ‖u‖ := by
  rw [(unitCubeLpToComplexTorus n).norm_map]
  calc
    ‖boxVelocityCoordinateLp (unitGalerkinBox n) j
        (boxScalarEnergyGradientProjection (unitGalerkinBox n)
          (u : BoxScalarEnergyAmbient (unitGalerkinBox n)))‖ <=
        ‖boxScalarEnergyGradientProjection (unitGalerkinBox n)
          (u : BoxScalarEnergyAmbient (unitGalerkinBox n))‖ :=
      norm_boxVelocityCoordinateLp_le (unitGalerkinBox n) j _
    _ <= ‖u‖ := by
      exact WithLp.norm_snd_le
        (x := (u : BoxScalarEnergyAmbient (unitGalerkinBox n)))

theorem unitCube_gradientCoordinateTorus_sum_sq_le
    (u : BoxH1ZeroScalarFull (unitGalerkinBox n)) :
    (∑ j : Fin (n + 1),
      ‖unitCubeLpToComplexTorus n
        (boxVelocityCoordinateLp (unitGalerkinBox n) j
          (boxScalarEnergyGradientProjection (unitGalerkinBox n)
            (u : BoxScalarEnergyAmbient (unitGalerkinBox n))))‖ ^ 2) <=
      (n + 1 : ℝ) * ‖u‖ ^ 2 := by
  calc
    _ <= ∑ _j : Fin (n + 1), ‖u‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _hj
      have h := unitCube_gradientCoordinateTorus_norm_le u j
      have hmul := mul_self_le_mul_self (norm_nonneg _) h
      simpa [pow_two] using hmul
    _ = (n + 1 : ℝ) * ‖u‖ ^ 2 := by simp

theorem unitCube_fourierTail_tsum_le_norm
    (u : BoxH1ZeroScalarFull (unitGalerkinBox n))
    {N : ℕ}
    (hN : 0 < N) :
    (∑' k : Fin (n + 1) -> ℤ,
      if k ∈ unitCubeFrequencyBox n N then 0 else
        ‖unitCubeFourierCoeffCLM k
          (boxScalarEnergyVelocityProjection (unitGalerkinBox n)
            (u : BoxScalarEnergyAmbient (unitGalerkinBox n)))‖ ^ 2) <=
      ((n + 1 : ℝ) / (N : ℝ) ^ 2) * ‖u‖ ^ 2 := by
  calc
    _ <= (1 / (N : ℝ) ^ 2) *
        ∑ j : Fin (n + 1),
          ‖unitCubeLpToComplexTorus n
            (boxVelocityCoordinateLp (unitGalerkinBox n) j
              (boxScalarEnergyGradientProjection (unitGalerkinBox n)
                (u : BoxScalarEnergyAmbient (unitGalerkinBox n))))‖ ^ 2 :=
      unitCube_fourierTail_tsum_le u hN
    _ <= (1 / (N : ℝ) ^ 2) * ((n + 1 : ℝ) * ‖u‖ ^ 2) :=
      mul_le_mul_of_nonneg_left
        (unitCube_gradientCoordinateTorus_sum_sq_le u) (by positivity)
    _ = ((n + 1 : ℝ) / (N : ℝ) ^ 2) * ‖u‖ ^ 2 := by ring

/-- Orthogonal reconstruction from a finite set of torus Fourier modes. -/
def unitTorusFourierProjection
    (s : Finset (Fin (n + 1) -> ℤ)) :
    Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin (n + 1)))) →L[ℂ]
      Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin (n + 1)))) :=
  ∑ k ∈ s,
    (LinearIsometry.toSpanSingleton ℂ _
      (UnitAddTorus.orthonormal_mFourier.norm_eq_one k)
      ).toContinuousLinearMap.comp
        (innerSL ℂ (UnitAddTorus.mFourierLp 2 k))

@[simp]
theorem unitTorusFourierProjection_apply
    (s : Finset (Fin (n + 1) -> ℤ))
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin (n + 1))))) :
    unitTorusFourierProjection s f =
      ∑ k ∈ s, UnitAddTorus.mFourierCoeff f k •
        UnitAddTorus.mFourierLp 2 k := by
  classical
  rw [unitTorusFourierProjection]
  simp only [ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro k _hk
  change ⟪UnitAddTorus.mFourierLp 2 k, f⟫_ℂ •
      UnitAddTorus.mFourierLp 2 k = _
  congr 1
  rw [← UnitAddTorus.coe_mFourierBasis,
    ← HilbertBasis.repr_apply_apply,
    UnitAddTorus.mFourierBasis_repr]

theorem unitTorusFourierProjection_isCompactOperator
    (s : Finset (Fin (n + 1) -> ℤ)) :
    IsCompactOperator (unitTorusFourierProjection s) := by
  classical
  rw [unitTorusFourierProjection]
  induction s using Finset.induction_on with
  | empty => simpa using (isCompactOperator_zero :
      IsCompactOperator
        (0 : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin (n + 1)))) ->
          Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin (n + 1))))))
  | @insert k s hk ih =>
      rw [Finset.sum_insert hk]
      have hterm : IsCompactOperator
          ((LinearIsometry.toSpanSingleton ℂ _
            (UnitAddTorus.orthonormal_mFourier.norm_eq_one k)
            ).toContinuousLinearMap.comp
              (innerSL ℂ (UnitAddTorus.mFourierLp 2 k))) := by
        let A : ℂ →L[ℂ]
            Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin (n + 1)))) :=
          (LinearIsometry.toSpanSingleton ℂ _
            (UnitAddTorus.orthonormal_mFourier.norm_eq_one k)
            ).toContinuousLinearMap
        let B : Lp ℂ 2
              (volume : Measure (UnitAddTorus (Fin (n + 1)))) →L[ℂ] ℂ :=
          innerSL ℂ (UnitAddTorus.mFourierLp 2 k)
        have hA : IsCompactOperator A :=
          isCompactOperator_of_locallyCompactSpace_rng A
        have hcomp := hA.comp_clm B
        simpa [A, B, Function.comp_def] using hcomp
      simpa only [ContinuousLinearMap.add_apply] using hterm.add ih

/-- The finite Fourier projector viewed as a real continuous linear map. -/
def unitTorusFourierProjectionReal
    (s : Finset (Fin (n + 1) -> ℤ)) :
    Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin (n + 1)))) →L[ℝ]
      Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin (n + 1)))) :=
  let T := unitTorusFourierProjection s
  { toLinearMap :=
      { toFun := T
        map_add' := T.map_add
        map_smul' := fun r f => by
          simp only [RingHom.id_apply]
          rw [← IsScalarTower.algebraMap_smul ℂ r f, T.map_smul,
            IsScalarTower.algebraMap_smul ℂ r (T f)] }
    cont := T.continuous }

@[simp]
theorem unitTorusFourierProjectionReal_apply
    (s : Finset (Fin (n + 1) -> ℤ))
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin (n + 1))))) :
    unitTorusFourierProjectionReal s f = unitTorusFourierProjection s f :=
  rfl

theorem unitTorusFourierProjectionReal_isCompactOperator
    (s : Finset (Fin (n + 1) -> ℤ)) :
    IsCompactOperator (unitTorusFourierProjectionReal s) := by
  change IsCompactOperator (unitTorusFourierProjection s)
  exact unitTorusFourierProjection_isCompactOperator s

theorem unitTorusFourierProjection_error_norm_sq
    (s : Finset (Fin (n + 1) -> ℤ))
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin (n + 1))))) :
    ‖f - unitTorusFourierProjection s f‖ ^ 2 =
      ∑' k : Fin (n + 1) -> ℤ,
        if k ∈ s then 0 else
          ‖UnitAddTorus.mFourierCoeff f k‖ ^ 2 := by
  classical
  let b := UnitAddTorus.mFourierBasis (d := Fin (n + 1))
  have hrepr : b.repr (unitTorusFourierProjection s f) =
      ∑ k ∈ s, lp.single 2 k (b.repr f k) := by
    rw [unitTorusFourierProjection_apply]
    simp only [b, ← UnitAddTorus.mFourierBasis_repr]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _hk
    rw [map_smul]
    rw [← UnitAddTorus.coe_mFourierBasis]
    rw [HilbertBasis.repr_self]
    simpa using
      (lp.single_smul
        (E := fun _ : Fin (n + 1) -> ℤ => ℂ)
        2 k (b.repr f k) (1 : ℂ)).symm
  have hsum_apply (k : Fin (n + 1) -> ℤ) :
      (∑ i ∈ s, lp.single 2 i (b.repr f i)) k =
        if k ∈ s then b.repr f k else 0 := by
    simp only [lp.coeFn_sum, Finset.sum_apply, lp.single_apply,
      Finset.sum_pi_single]
  calc
    ‖f - unitTorusFourierProjection s f‖ ^ 2 =
        ‖b.repr (f - unitTorusFourierProjection s f)‖ ^ 2 := by
      rw [b.repr.norm_map]
    _ = ‖b.repr f - ∑ k ∈ s, lp.single 2 k (b.repr f k)‖ ^ 2 := by
      rw [map_sub, hrepr]
    _ = ∑' k : Fin (n + 1) -> ℤ,
        ‖(b.repr f - ∑ i ∈ s, lp.single 2 i (b.repr f i)) k‖ ^ 2 := by
      simpa using lp.norm_rpow_eq_tsum (p := (2 : ENNReal))
        (by norm_num)
        (b.repr f - ∑ k ∈ s, lp.single 2 k (b.repr f k))
    _ = ∑' k : Fin (n + 1) -> ℤ,
        if k ∈ s then 0 else ‖b.repr f k‖ ^ 2 := by
      apply tsum_congr
      intro k
      change ‖b.repr f k -
          (∑ i ∈ s, lp.single 2 i (b.repr f i)) k‖ ^ 2 = _
      by_cases hk : k ∈ s
      · rw [hsum_apply k, if_pos hk]
        simp [hk]
      · rw [hsum_apply k, if_neg hk]
        simp [hk]
    _ = _ := by
      apply tsum_congr
      intro k
      rw [UnitAddTorus.mFourierBasis_repr]

/-- The scalar graph embedding followed by the isometric torus
realization. -/
def unitCubeScalarEnergyToComplexTorus :
    BoxH1ZeroScalarFull (unitGalerkinBox n) →L[ℝ]
      Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin (n + 1)))) :=
  (unitCubeLpToComplexTorus n).toContinuousLinearMap.comp
    (boxScalarFullEnergyToVelocity (unitGalerkinBox n))

/-- Finite Fourier reconstruction of the scalar unit-cube embedding. -/
def unitCubeScalarFourierApproximation (N : ℕ) :
    BoxH1ZeroScalarFull (unitGalerkinBox n) →L[ℝ]
      Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin (n + 1)))) :=
  (unitTorusFourierProjectionReal (unitCubeFrequencyBox n N)).comp
    (unitCubeScalarEnergyToComplexTorus (n := n))

local instance unitCubeScalarOperatorNorm
    [Nontrivial (BoxH1ZeroScalarFull (unitGalerkinBox n))] :
    Norm (BoxH1ZeroScalarFull (unitGalerkinBox n) →L[ℝ]
      Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin (n + 1))))) :=
  ContinuousLinearMap.hasOpNorm

local instance unitCubeScalarOperatorPseudoMetric
    [Nontrivial (BoxH1ZeroScalarFull (unitGalerkinBox n))] :
    PseudoMetricSpace (BoxH1ZeroScalarFull (unitGalerkinBox n) →L[ℝ]
      Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin (n + 1))))) :=
  ContinuousLinearMap.toPseudoMetricSpace

local instance unitCubeScalarOperatorSeminormed
    [Nontrivial (BoxH1ZeroScalarFull (unitGalerkinBox n))] :
    SeminormedAddCommGroup
      (BoxH1ZeroScalarFull (unitGalerkinBox n) →L[ℝ]
        Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin (n + 1))))) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

theorem unitCubeScalarFourierApproximation_isCompactOperator (N : ℕ) :
    IsCompactOperator (unitCubeScalarFourierApproximation (n := n) N) :=
  (unitTorusFourierProjectionReal_isCompactOperator
    (unitCubeFrequencyBox n N)).comp_clm
      (unitCubeScalarEnergyToComplexTorus (n := n))

theorem unitCubeScalarFourierApproximation_error_sq_le
    (u : BoxH1ZeroScalarFull (unitGalerkinBox n))
    {N : ℕ}
    (hN : 0 < N) :
    ‖unitCubeScalarEnergyToComplexTorus u -
        unitCubeScalarFourierApproximation N u‖ ^ 2 <=
      ((n + 1 : ℝ) / (N : ℝ) ^ 2) * ‖u‖ ^ 2 := by
  rw [show unitCubeScalarFourierApproximation N u =
      unitTorusFourierProjection (unitCubeFrequencyBox n N)
        (unitCubeScalarEnergyToComplexTorus u) by rfl]
  rw [unitTorusFourierProjection_error_norm_sq]
  simpa only [unitCubeScalarEnergyToComplexTorus,
    ContinuousLinearMap.comp_apply,
    unitCubeFourierCoeffCLM_apply] using
    unitCube_fourierTail_tsum_le_norm u hN

theorem unitCubeScalarFourierApproximation_opNorm_error_le
    [Nontrivial (BoxH1ZeroScalarFull (unitGalerkinBox n))]
    {N : ℕ}
    (hN : 0 < N) :
    ‖unitCubeScalarEnergyToComplexTorus (n := n) -
        unitCubeScalarFourierApproximation (n := n) N‖ <=
      Real.sqrt (n + 1 : ℝ) / (N : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  change
    ‖unitCubeScalarEnergyToComplexTorus u -
      unitCubeScalarFourierApproximation N u‖ <=
        (Real.sqrt (n + 1 : ℝ) / (N : ℝ)) * ‖u‖
  have hsquare := unitCubeScalarFourierApproximation_error_sq_le u hN
  have hsqrt : (Real.sqrt (n + 1 : ℝ)) ^ 2 = (n + 1 : ℝ) := by
    rw [Real.sq_sqrt]
    positivity
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have htargetSq :
      ((Real.sqrt (n + 1 : ℝ) / (N : ℝ)) * ‖u‖) ^ 2 =
        ((n + 1 : ℝ) / (N : ℝ) ^ 2) * ‖u‖ ^ 2 := by
    rw [mul_pow, div_pow, hsqrt]
  rw [← htargetSq] at hsquare
  exact (sq_le_sq₀
    (norm_nonneg
      (unitCubeScalarEnergyToComplexTorus u -
        unitCubeScalarFourierApproximation N u))
    (mul_nonneg
      (div_nonneg (Real.sqrt_nonneg _) hNreal.le)
      (norm_nonneg u))).mp hsquare

theorem unitCubeScalarFourierApproximation_tendsto
    [Nontrivial (BoxH1ZeroScalarFull (unitGalerkinBox n))] :
    Tendsto
      (fun m => unitCubeScalarFourierApproximation (n := n) (m + 1))
      atTop (𝓝 (unitCubeScalarEnergyToComplexTorus (n := n))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have hbound : Tendsto
      (fun m : ℕ => Real.sqrt (n + 1 : ℝ) / ((m + 1 : ℕ) : ℝ))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_const_div_atTop_nhds_zero_nat
        (𝕜 := ℝ) (Real.sqrt (n + 1 : ℝ))).comp
          (tendsto_add_atTop_nat 1)
  apply squeeze_zero
    (fun _ => norm_nonneg _)
    (fun m => by
      rw [norm_sub_rev]
      exact unitCubeScalarFourierApproximation_opNorm_error_le
        (n := n) (Nat.succ_pos m))
    hbound

/-- Compactness of the isometrically realized scalar unit-cube embedding. -/
theorem unitCubeScalarEnergyToComplexTorus_isCompactOperator :
    IsCompactOperator (unitCubeScalarEnergyToComplexTorus (n := n)) := by
  let V := BoxH1ZeroScalarFull (unitGalerkinBox n)
  by_cases hV : Nontrivial V
  · letI : Nontrivial V := hV
    exact isCompactOperator_of_tendsto
      unitCubeScalarFourierApproximation_tendsto
      (Filter.Eventually.of_forall fun m =>
        unitCubeScalarFourierApproximation_isCompactOperator (n := n) (m + 1))
  · haveI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
    have hzero : unitCubeScalarEnergyToComplexTorus (n := n) = 0 := by
      apply ContinuousLinearMap.ext
      intro u
      change unitCubeScalarEnergyToComplexTorus (n := n) u = 0
      rw [Subsingleton.elim u 0, map_zero]
    rw [hzero]
    exact isCompactOperator_zero

private theorem isCompactOperator_of_isometry_comp_real
    {V H K : Type*}
    [Zero V] [TopologicalSpace V]
    [MetricSpace H] [CompleteSpace H]
    [MetricSpace K]
    (R : H -> K)
    (hR : Isometry R)
    (T : V -> H)
    (hcompact : IsCompactOperator (R ∘ T)) :
    IsCompactOperator T := by
  rcases hcompact with ⟨C, hC, hpreimage⟩
  have hclosed : Topology.IsClosedEmbedding R := hR.isClosedEmbedding
  refine ⟨R ⁻¹' C, hclosed.isCompact_preimage hC, ?_⟩
  simpa only [preimage_preimage] using hpreimage

/-- Scalar Rellich compactness for the completed zero-trace graph on the
unit cube in every positive finite dimension. -/
theorem unitCube_boxScalarFullEnergyToVelocity_isCompactOperator :
    IsCompactOperator
      (boxScalarFullEnergyToVelocity (unitGalerkinBox n)) := by
  apply isCompactOperator_of_isometry_comp_real
    (unitCubeLpToComplexTorus n)
    (unitCubeLpToComplexTorus n).isometry
    (boxScalarFullEnergyToVelocity (unitGalerkinBox n))
  change IsCompactOperator
    (unitCubeScalarEnergyToComplexTorus (n := n) :
      BoxH1ZeroScalarFull (unitGalerkinBox n) ->
        Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin (n + 1)))))
  exact unitCubeScalarEnergyToComplexTorus_isCompactOperator

/-- Rellich compactness for the canonical divergence-free graph embedding
on the unit cube. -/
theorem unitCube_boxEnergyToState_isCompactOperator :
    IsCompactOperator (boxEnergyToState (unitGalerkinBox n)) :=
  boxEnergyToState_isCompactOperator_of_scalarFullRellich
    (unitGalerkinBox n)
    unitCube_boxScalarFullEnergyToVelocity_isCompactOperator

/-! ## Affine transport from a rectangular box -/

section MeasureScale

variable {α E : Type*} [MeasurableSpace α]
variable [NormedAddCommGroup E]

private theorem Lp.memLp_base_of_smulMeasure
    (μ : Measure α)
    (c : ℝ≥0)
    (hc : c ≠ 0)
    (f : Lp E 2 ((c : ENNReal) • μ)) :
    MemLp f 2 μ := by
  apply (Lp.memLp f).of_measure_le_smul
    (c := ((c : ENNReal)⁻¹))
    (ENNReal.inv_ne_top.2 (ENNReal.coe_ne_zero.2 hc))
  have hmul : (c : ENNReal)⁻¹ * (c : ENNReal) = 1 :=
    ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.2 hc) ENNReal.coe_ne_top
  rw [smul_smul, hmul, one_smul]

variable [NormedSpace ℝ E]

/-- Multiplication by `sqrt c` identifies L2 for `c μ` isometrically with
L2 for `μ`. -/
def lpSqrtMeasureScale
    (μ : Measure α)
    (c : ℝ≥0)
    (hc : c ≠ 0) :
    Lp E 2 ((c : ENNReal) • μ) →ₗᵢ[ℝ] Lp E 2 μ where
  toFun f :=
    ((Lp.memLp_base_of_smulMeasure μ c hc f).const_smul
      (NNReal.sqrt c : ℝ)).toLp
        ((NNReal.sqrt c : ℝ) • (f : α → E))
  map_add' f g := by
    have hadd := (Measure.ae_ennreal_smul_measure_iff
      (ENNReal.coe_ne_zero.2 hc)).1 (Lp.coeFn_add f g)
    apply Lp.ext
    filter_upwards [
      (Lp.memLp_base_of_smulMeasure μ c hc (f + g)).const_smul
        (NNReal.sqrt c : ℝ) |>.coeFn_toLp,
      (Lp.memLp_base_of_smulMeasure μ c hc f).const_smul
        (NNReal.sqrt c : ℝ) |>.coeFn_toLp,
      (Lp.memLp_base_of_smulMeasure μ c hc g).const_smul
        (NNReal.sqrt c : ℝ) |>.coeFn_toLp,
      hadd,
      Lp.coeFn_add
        (((Lp.memLp_base_of_smulMeasure μ c hc f).const_smul
          (NNReal.sqrt c : ℝ)).toLp
            ((NNReal.sqrt c : ℝ) • (f : α → E)))
        (((Lp.memLp_base_of_smulMeasure μ c hc g).const_smul
          (NNReal.sqrt c : ℝ)).toLp
            ((NNReal.sqrt c : ℝ) • (g : α → E)))] with x hfg hf hg hadd haddOut
    simp only [Pi.smul_apply, Pi.add_apply] at hfg hf hg hadd haddOut
    rw [hfg, haddOut, hf, hg, hadd]
    exact smul_add _ _ _
  map_smul' r f := by
    have hsmul := (Measure.ae_ennreal_smul_measure_iff
      (ENNReal.coe_ne_zero.2 hc)).1 (Lp.coeFn_smul r f)
    apply Lp.ext
    filter_upwards [
      (Lp.memLp_base_of_smulMeasure μ c hc (r • f)).const_smul
        (NNReal.sqrt c : ℝ) |>.coeFn_toLp,
      (Lp.memLp_base_of_smulMeasure μ c hc f).const_smul
        (NNReal.sqrt c : ℝ) |>.coeFn_toLp,
      hsmul,
      Lp.coeFn_smul r
        (((Lp.memLp_base_of_smulMeasure μ c hc f).const_smul
          (NNReal.sqrt c : ℝ)).toLp
            ((NNReal.sqrt c : ℝ) • (f : α → E)))] with x hrf hf hsmul hsmulOut
    simp only [RingHom.id_apply, Pi.smul_apply] at hrf hf hsmul hsmulOut ⊢
    rw [hrf, hsmulOut, hf, hsmul]
    exact smul_comm _ _ _
  norm_map' f := by
    change ‖((Lp.memLp_base_of_smulMeasure μ c hc f).const_smul
        (NNReal.sqrt c : ℝ)).toLp
          ((NNReal.sqrt c : ℝ) • (f : α → E))‖ = ‖f‖
    rw [Lp.norm_toLp, Lp.norm_def]
    rw [eLpNorm_const_smul]
    rw [eLpNorm_smul_measure_of_ne_zero
      (ENNReal.coe_ne_zero.2 hc) (f : α -> E) 2 μ]
    rw [show (1 / (2 : ENNReal)).toReal = (1 : ℝ) / 2 by norm_num]
    rw [← ENNReal.coe_rpow_of_nonneg c (by positivity)]
    rw [← NNReal.sqrt_eq_rpow]
    rw [NNReal.enorm_eq]
    rfl

theorem lpSqrtMeasureScale_coeFn
    (μ : Measure α)
    (c : ℝ≥0)
    (hc : c ≠ 0)
    (f : Lp E 2 ((c : ENNReal) • μ)) :
    lpSqrtMeasureScale μ c hc f =ᵐ[μ]
      fun x => (NNReal.sqrt c : ℝ) • f x :=
  ((Lp.memLp_base_of_smulMeasure μ c hc f).const_smul
    (NNReal.sqrt c : ℝ)).coeFn_toLp

end MeasureScale

section BoxAffine

open Matrix

/-- Positive side length of a rectangular box. -/
def boxSideLength
    (I : BoxIntegral.Box (Fin (n + 1)))
    (i : Fin (n + 1)) : ℝ :=
  I.upper i - I.lower i

theorem boxSideLength_pos
    (I : BoxIntegral.Box (Fin (n + 1)))
    (i : Fin (n + 1)) :
    0 < boxSideLength I i :=
  sub_pos.2 (I.lower_lt_upper i)

/-- Jacobian determinant of the coordinatewise affine map from the unit
cube to the box. -/
def boxJacobian
    (I : BoxIntegral.Box (Fin (n + 1))) : ℝ≥0 :=
  ∏ i : Fin (n + 1),
    ⟨boxSideLength I i, (boxSideLength_pos I i).le⟩

theorem boxJacobian_pos
    (I : BoxIntegral.Box (Fin (n + 1))) :
    0 < boxJacobian I := by
  apply Finset.prod_pos
  intro i _hi
  exact boxSideLength_pos I i

@[simp]
theorem boxJacobian_coe
    (I : BoxIntegral.Box (Fin (n + 1))) :
    (boxJacobian I : ℝ) =
      ∏ i : Fin (n + 1), boxSideLength I i := by
  rw [boxJacobian, NNReal.coe_prod]
  rfl

/-- Diagonal linear part of the affine unit-cube parametrization. -/
def boxDiagonalLinear
    (I : BoxIntegral.Box (Fin (n + 1))) :
    (Fin (n + 1) -> ℝ) →ₗ[ℝ] (Fin (n + 1) -> ℝ) :=
  Matrix.toLin' (Matrix.diagonal (boxSideLength I))

@[simp]
theorem boxDiagonalLinear_apply
    (I : BoxIntegral.Box (Fin (n + 1)))
    (x : Fin (n + 1) -> ℝ)
    (i : Fin (n + 1)) :
    boxDiagonalLinear I x i = boxSideLength I i * x i := by
  simp [boxDiagonalLinear, Matrix.diagonal_toLin']

/-- Coordinatewise affine map from the unit cube onto `I`. -/
def boxFromUnit
    (I : BoxIntegral.Box (Fin (n + 1)))
    (x : Fin (n + 1) -> ℝ) : Fin (n + 1) -> ℝ :=
  I.lower + boxDiagonalLinear I x

@[simp]
theorem boxFromUnit_apply
    (I : BoxIntegral.Box (Fin (n + 1)))
    (x : Fin (n + 1) -> ℝ)
    (i : Fin (n + 1)) :
    boxFromUnit I x i =
      I.lower i + boxSideLength I i * x i := by
  simp [boxFromUnit]

theorem continuous_boxFromUnit
    (I : BoxIntegral.Box (Fin (n + 1))) :
    Continuous (boxFromUnit I) :=
  continuous_const.add
    (LinearMap.toContinuousLinearMap (boxDiagonalLinear I)).continuous

theorem boxFromUnit_mapsTo_Icc
    (I : BoxIntegral.Box (Fin (n + 1))) :
    MapsTo (boxFromUnit I)
      (BoxIntegral.Box.Icc (unitGalerkinBox n))
      (BoxIntegral.Box.Icc I) := by
  intro x hx
  rw [BoxIntegral.Box.Icc_def] at hx ⊢
  constructor
  · intro i
    have hxi := hx.1 i
    have hlen := boxSideLength_pos I i
    simp only [boxSideLength] at hlen
    simp only [unitGalerkinBox, Pi.zero_apply] at hxi
    simp only [boxFromUnit_apply, boxSideLength]
    nlinarith
  · intro i
    have hxi := hx.2 i
    have hlen := boxSideLength_pos I i
    simp only [boxSideLength] at hlen
    simp only [unitGalerkinBox, Pi.one_apply] at hxi
    simp only [boxFromUnit_apply, boxSideLength]
    nlinarith

theorem boxFromUnit_mapsTo_interior
    (I : BoxIntegral.Box (Fin (n + 1))) :
    MapsTo (boxFromUnit I)
      (interior (BoxIntegral.Box.Icc (unitGalerkinBox n)))
      (interior (BoxIntegral.Box.Icc I)) := by
  intro x hx
  rw [BoxIntegral.Box.Icc_def, ← Set.pi_univ_Icc,
    interior_pi_set (@Set.finite_univ (Fin (n + 1)) _)] at hx ⊢
  simp only [Set.mem_pi, Set.mem_univ, true_implies, interior_Icc] at hx ⊢
  intro i
  have hxi := hx i
  have hlen := boxSideLength_pos I i
  simp only [boxSideLength] at hlen
  simp only [unitGalerkinBox, Pi.zero_apply, Pi.one_apply] at hxi
  simp only [boxFromUnit_apply, boxSideLength]
  constructor <;> nlinarith [hxi.1, hxi.2]

theorem boxFromUnit_injective
    (I : BoxIntegral.Box (Fin (n + 1))) :
    Function.Injective (boxFromUnit I) := by
  intro x y hxy
  funext i
  have hi := congrFun hxy i
  simp only [boxFromUnit_apply] at hi
  exact mul_left_cancel₀ (boxSideLength_pos I i).ne' (add_left_cancel hi)

theorem boxFromUnit_preimage_Icc
    (I : BoxIntegral.Box (Fin (n + 1))) :
    boxFromUnit I ⁻¹' BoxIntegral.Box.Icc I =
      BoxIntegral.Box.Icc (unitGalerkinBox n) := by
  ext x
  simp only [Set.mem_preimage, BoxIntegral.Box.Icc_def, Set.mem_Icc,
    Pi.le_def, unitGalerkinBox, Pi.zero_apply, Pi.one_apply]
  constructor
  · intro hx
    constructor
    · intro i
      have hlen := boxSideLength_pos I i
      have hlo := hx.1 i
      simp only [boxSideLength] at hlen
      simp only [boxFromUnit_apply, boxSideLength] at hlo
      nlinarith
    · intro i
      have hlen := boxSideLength_pos I i
      have hup := hx.2 i
      simp only [boxSideLength] at hlen
      simp only [boxFromUnit_apply, boxSideLength] at hup
      nlinarith
  · intro hx
    constructor
    · intro i
      have hlen := boxSideLength_pos I i
      have hi := hx.1 i
      simp only [boxSideLength] at hlen
      simp only [boxFromUnit_apply, boxSideLength]
      nlinarith
    · intro i
      have hlen := boxSideLength_pos I i
      have hi := hx.2 i
      simp only [boxSideLength] at hlen
      simp only [boxFromUnit_apply, boxSideLength]
      nlinarith

theorem boxDiagonalLinear_det
    (I : BoxIntegral.Box (Fin (n + 1))) :
    LinearMap.det (boxDiagonalLinear I) =
      (boxJacobian I : ℝ) := by
  simp [boxDiagonalLinear, Matrix.det_diagonal]

theorem boxDiagonalLinear_map_volume
    (I : BoxIntegral.Box (Fin (n + 1))) :
    Measure.map (boxDiagonalLinear I) volume =
      ((boxJacobian I : ENNReal)⁻¹) • volume := by
  rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi]
  · rw [boxDiagonalLinear_det]
    have hJ : 0 < (boxJacobian I : ℝ) := by
      exact_mod_cast boxJacobian_pos I
    rw [abs_of_pos (inv_pos.mpr hJ), ENNReal.ofReal_inv_of_pos hJ]
    change (ENNReal.ofReal (boxJacobian I : ℝ))⁻¹ • volume = _
    rw [ENNReal.ofReal_coe_nnreal]
  · rw [boxDiagonalLinear_det]
    exact_mod_cast (boxJacobian_pos I).ne'

theorem boxFromUnit_map_volume
    (I : BoxIntegral.Box (Fin (n + 1))) :
    Measure.map (boxFromUnit I) volume =
      ((boxJacobian I : ENNReal)⁻¹) • volume := by
  calc
    Measure.map (boxFromUnit I) volume =
        Measure.map (fun x => I.lower + x)
          (Measure.map (boxDiagonalLinear I) volume) := by
      rw [show boxFromUnit I =
          (fun x => I.lower + x) ∘ boxDiagonalLinear I by rfl]
      exact (Measure.map_map
        (continuous_const.add continuous_id).measurable
        (LinearMap.toContinuousLinearMap
          (boxDiagonalLinear I)).continuous.measurable).symm
    _ = ((boxJacobian I : ENNReal)⁻¹) • volume := by
      rw [boxDiagonalLinear_map_volume, Measure.map_smul,
        map_add_left_eq_self]

theorem boxFromUnit_map_unitBoxMeasure
    (I : BoxIntegral.Box (Fin (n + 1))) :
    Measure.map (boxFromUnit I) (BoxMeasure (unitGalerkinBox n)) =
      ((boxJacobian I : ENNReal)⁻¹) • BoxMeasure I := by
  change Measure.map (boxFromUnit I)
      (volume.restrict (BoxIntegral.Box.Icc (unitGalerkinBox n))) =
    ((boxJacobian I : ENNReal)⁻¹) •
      volume.restrict (BoxIntegral.Box.Icc I)
  rw [← boxFromUnit_preimage_Icc I]
  rw [← Measure.restrict_map
    (continuous_boxFromUnit I).measurable
    (BoxIntegral.Box.measurableSet_Icc I)]
  rw [boxFromUnit_map_volume]
  simp

/-- The affine map preserves the Jacobian-weighted unit-box measure and
Lebesgue measure on `I`. -/
theorem boxFromUnit_measurePreserving
    (I : BoxIntegral.Box (Fin (n + 1))) :
    MeasurePreserving (boxFromUnit I)
      ((boxJacobian I : ENNReal) • BoxMeasure (unitGalerkinBox n))
      (BoxMeasure I) := by
  refine ⟨(continuous_boxFromUnit I).measurable, ?_⟩
  rw [Measure.map_smul, boxFromUnit_map_unitBoxMeasure, smul_smul]
  rw [ENNReal.mul_inv_cancel]
  · simp
  · exact ENNReal.coe_ne_zero.2 (boxJacobian_pos I).ne'
  · exact ENNReal.coe_ne_top

/-- Jacobian-normalized pullback from L2 on a box to L2 on the unit cube. -/
def boxLpToUnitCube
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : BoxIntegral.Box (Fin (n + 1))) :
    Lp E 2 (BoxMeasure I) →ₗᵢ[ℝ]
      Lp E 2 (BoxMeasure (unitGalerkinBox n)) :=
  let P : Lp E 2 (BoxMeasure I) →ₗᵢ[ℝ]
      Lp E 2
        ((boxJacobian I : ENNReal) •
          BoxMeasure (unitGalerkinBox n)) :=
    Lp.compMeasurePreservingₗᵢ ℝ (boxFromUnit I)
      (boxFromUnit_measurePreserving I)
  let S := lpSqrtMeasureScale (E := E)
    (BoxMeasure (unitGalerkinBox n)) (boxJacobian I)
    (boxJacobian_pos I).ne'
  { toLinearMap := S.toLinearMap.comp P.toLinearMap
    norm_map' := fun f => by
      change ‖S (P f)‖ = ‖f‖
      rw [S.norm_map, P.norm_map] }

theorem boxLpToUnitCube_coeFn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : BoxIntegral.Box (Fin (n + 1)))
    (f : Lp E 2 (BoxMeasure I)) :
    boxLpToUnitCube I f =ᵐ[BoxMeasure (unitGalerkinBox n)]
      fun x => (NNReal.sqrt (boxJacobian I) : ℝ) •
        f (boxFromUnit I x) := by
  let P : Lp E 2 (BoxMeasure I) →ₗᵢ[ℝ]
      Lp E 2
        ((boxJacobian I : ENNReal) •
          BoxMeasure (unitGalerkinBox n)) :=
    Lp.compMeasurePreservingₗᵢ ℝ (boxFromUnit I)
      (boxFromUnit_measurePreserving I)
  have hPscaled := Lp.coeFn_compMeasurePreserving (p := (2 : ENNReal)) f
    (boxFromUnit_measurePreserving I)
  have hP : P f =ᵐ[BoxMeasure (unitGalerkinBox n)]
      fun x => f (boxFromUnit I x) := by
    exact (Measure.ae_ennreal_smul_measure_iff
      (ENNReal.coe_ne_zero.2 (boxJacobian_pos I).ne')).1 hPscaled
  filter_upwards [
    lpSqrtMeasureScale_coeFn
      (BoxMeasure (unitGalerkinBox n)) (boxJacobian I)
      (boxJacobian_pos I).ne' (P f), hP] with x hS hPx
  rw [show boxLpToUnitCube I f =
      lpSqrtMeasureScale (BoxMeasure (unitGalerkinBox n))
        (boxJacobian I) (boxJacobian_pos I).ne' (P f) by rfl]
  rw [hS, hPx]

/-- Coordinatewise side-length scaling on Euclidean gradient values. -/
def boxGradientScaleValue
    (I : BoxIntegral.Box (Fin (n + 1))) :
    BoxScalarGradientValue n →L[ℝ] BoxScalarGradientValue n :=
  (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm.toContinuousLinearMap.comp
    ((LinearMap.toContinuousLinearMap (boxDiagonalLinear I)).comp
      (EuclideanSpace.equiv (Fin (n + 1)) ℝ).toContinuousLinearMap)

@[simp]
theorem boxGradientScaleValue_apply
    (I : BoxIntegral.Box (Fin (n + 1)))
    (v : BoxScalarGradientValue n)
    (j : Fin (n + 1)) :
    boxGradientScaleValue I v j = boxSideLength I j * v j := by
  simp [boxGradientScaleValue, boxDiagonalLinear_apply]

/-- Pull back an L2 gradient and apply the chain-rule side-length factors. -/
def boxGradientLpToUnitCube
    (I : BoxIntegral.Box (Fin (n + 1))) :
    BoxScalarGradientL2 I →L[ℝ]
      BoxScalarGradientL2 (unitGalerkinBox n) :=
  (boxGradientScaleValue I).compLpL 2
      (BoxMeasure (unitGalerkinBox n)) |>.comp
    (boxLpToUnitCube I).toContinuousLinearMap

theorem boxGradientLpToUnitCube_coeFn
    (I : BoxIntegral.Box (Fin (n + 1)))
    (g : BoxScalarGradientL2 I) :
    boxGradientLpToUnitCube I g =ᵐ[BoxMeasure (unitGalerkinBox n)]
      fun x => (NNReal.sqrt (boxJacobian I) : ℝ) •
        boxGradientScaleValue I (g (boxFromUnit I x)) := by
  filter_upwards [
    (boxGradientScaleValue I).coeFn_compLpL (boxLpToUnitCube I g),
    boxLpToUnitCube_coeFn I g] with x hscale hpull
  change
    ((boxGradientScaleValue I).compLpL 2
        (BoxMeasure (unitGalerkinBox n)) (boxLpToUnitCube I g) x) = _
  rw [hscale, hpull, map_smul]

private theorem MemLp.comp_boxFromUnit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : BoxIntegral.Box (Fin (n + 1)))
    {f : (Fin (n + 1) → ℝ) → E}
    (hf : MemLp f 2 (BoxMeasure I)) :
    MemLp (f ∘ boxFromUnit I) 2
      (BoxMeasure (unitGalerkinBox n)) := by
  have hscaled := hf.comp_measurePreserving
    (boxFromUnit_measurePreserving I)
  apply hscaled.of_measure_le_smul
    (c := ((boxJacobian I : ENNReal)⁻¹))
    (ENNReal.inv_ne_top.2
      (ENNReal.coe_ne_zero.2 (boxJacobian_pos I).ne'))
  have hmul : (boxJacobian I : ENNReal)⁻¹ *
      (boxJacobian I : ENNReal) = 1 :=
    ENNReal.inv_mul_cancel
      (ENNReal.coe_ne_zero.2 (boxJacobian_pos I).ne') ENNReal.coe_ne_top
  rw [smul_smul, hmul, one_smul]

private theorem ae_comp_boxFromUnit
    {E : Type*} [NormedAddCommGroup E]
    (I : BoxIntegral.Box (Fin (n + 1)))
    {f g : (Fin (n + 1) → ℝ) → E}
    (hfg : f =ᵐ[BoxMeasure I] g) :
    (f ∘ boxFromUnit I) =ᵐ[BoxMeasure (unitGalerkinBox n)]
      (g ∘ boxFromUnit I) := by
  have hscaled :=
    (boxFromUnit_measurePreserving I).quasiMeasurePreserving.ae_eq_comp hfg
  exact (Measure.ae_ennreal_smul_measure_iff
    (ENNReal.coe_ne_zero.2 (boxJacobian_pos I).ne')).1 hscaled

namespace SmoothBoxScalarH1ZeroField

/-- Jacobian-normalized affine pullback of a smooth scalar field. -/
def affineToUnitField
    {I : BoxIntegral.Box (Fin (n + 1))}
    (u : SmoothBoxScalarH1ZeroField I)
    (x : Fin (n + 1) → ℝ) : ℝ :=
  (NNReal.sqrt (boxJacobian I) : ℝ) * u.field (boxFromUnit I x)

/-- Chain-rule derivative of the normalized affine pullback. -/
def affineToUnitDerivative
    {I : BoxIntegral.Box (Fin (n + 1))}
    (u : SmoothBoxScalarH1ZeroField I)
    (x : Fin (n + 1) → ℝ) :
    (Fin (n + 1) → ℝ) →L[ℝ] ℝ :=
  (NNReal.sqrt (boxJacobian I) : ℝ) •
    (u.derivative (boxFromUnit I x)).comp
      (LinearMap.toContinuousLinearMap (boxDiagonalLinear I))

theorem affineToUnit_gradient
    {I : BoxIntegral.Box (Fin (n + 1))}
    (u : SmoothBoxScalarH1ZeroField I)
    (x : Fin (n + 1) → ℝ) :
    boxScalarGradientValue u.affineToUnitDerivative x =
      (NNReal.sqrt (boxJacobian I) : ℝ) •
        boxGradientScaleValue I
          (boxScalarGradientValue u.derivative (boxFromUnit I x)) := by
  apply WithLp.ofLp_injective 2
  funext j
  have hdiag : boxDiagonalLinear I (Pi.single j 1) =
      boxSideLength I j •
        (Pi.single j 1 : Fin (n + 1) → ℝ) := by
    ext q
    by_cases hq : q = j
    · subst q
      simp [boxDiagonalLinear_apply]
    · simp [boxDiagonalLinear_apply, Pi.single_eq_of_ne hq]
  simp only [boxScalarGradientValue, WithLp.ofLp_toLp,
    WithLp.ofLp_smul, Pi.smul_apply]
  rw [boxGradientScaleValue_apply]
  change (NNReal.sqrt (boxJacobian I) : ℝ) *
      u.derivative (boxFromUnit I x)
        (boxDiagonalLinear I
          (Pi.single j 1 : Fin (n + 1) → ℝ)) =
    (NNReal.sqrt (boxJacobian I) : ℝ) *
      (boxSideLength I j *
        u.derivative (boxFromUnit I x)
          (Pi.single j 1 : Fin (n + 1) → ℝ))
  rw [hdiag, map_smul]
  ring

/-- A normalized affine pullback carries the smooth zero-face scalar graph
on an arbitrary rectangular box into the corresponding unit-cube graph. -/
def affineToUnit
    {I : BoxIntegral.Box (Fin (n + 1))}
    (u : SmoothBoxScalarH1ZeroField I) :
    SmoothBoxScalarH1ZeroField (unitGalerkinBox n) where
  field := u.affineToUnitField
  derivative := u.affineToUnitDerivative
  hasFDerivAt_field := by
    intro x hx
    have hA : HasFDerivAt (boxFromUnit I)
        (LinearMap.toContinuousLinearMap (boxDiagonalLinear I)) x := by
      simpa [boxFromUnit] using
        (hasFDerivAt_const I.lower x).add
          (LinearMap.toContinuousLinearMap
            (boxDiagonalLinear I)).hasFDerivAt
    have hu := u.hasFDerivAt_field (boxFromUnit I x)
      (boxFromUnit_mapsTo_interior I hx)
    simpa only [affineToUnitField, affineToUnitDerivative,
      Pi.smul_apply, smul_eq_mul] using
      (hu.comp x hA).const_mul
        (NNReal.sqrt (boxJacobian I) : ℝ)
  continuousOn_field := by
    have hcomp := u.continuousOn_field.comp
      (continuous_boxFromUnit I).continuousOn
      (boxFromUnit_mapsTo_Icc I)
    simpa only [affineToUnitField, Function.comp_apply, smul_eq_mul] using
      hcomp.const_smul (NNReal.sqrt (boxJacobian I) : ℝ)
  zeroDirichlet_field := by
    intro i x
    let yUpper : Fin (n + 1) → ℝ := i.insertNth 1 x
    let yLower : Fin (n + 1) → ℝ := i.insertNth 0 x
    have hUpperCoord : boxFromUnit I yUpper i = I.upper i := by
      simp [yUpper, boxFromUnit_apply, boxSideLength]
    have hLowerCoord : boxFromUnit I yLower i = I.lower i := by
      simp [yLower, boxFromUnit_apply]
    have hUpperFace : boxFromUnit I yUpper =
        i.insertNth (I.upper i)
          (i.removeNth (boxFromUnit I yUpper)) := by
      exact Fin.eq_insertNth_iff.2 ⟨hUpperCoord, rfl⟩
    have hLowerFace : boxFromUnit I yLower =
        i.insertNth (I.lower i)
          (i.removeNth (boxFromUnit I yLower)) := by
      exact Fin.eq_insertNth_iff.2 ⟨hLowerCoord, rfl⟩
    constructor
    · change (NNReal.sqrt (boxJacobian I) : ℝ) *
          u.field (boxFromUnit I yUpper) = 0
      rw [hUpperFace,
        (u.zeroDirichlet_field i
          (i.removeNth (boxFromUnit I yUpper))).1, mul_zero]
    · change (NNReal.sqrt (boxJacobian I) : ℝ) *
          u.field (boxFromUnit I yLower) = 0
      rw [hLowerFace,
        (u.zeroDirichlet_field i
          (i.removeNth (boxFromUnit I yLower))).2, mul_zero]
  field_memLp := by
    have hpull := MemLp.comp_boxFromUnit I u.field_memLp
    simpa only [affineToUnitField, Function.comp_apply, smul_eq_mul] using
      hpull.const_smul (NNReal.sqrt (boxJacobian I) : ℝ)
  gradient_memLp := by
    have hpull := MemLp.comp_boxFromUnit I u.gradient_memLp
    have hscale := hpull.continuousLinearMap_comp
      (boxGradientScaleValue I)
    have hsmul := hscale.const_smul
      (NNReal.sqrt (boxJacobian I) : ℝ)
    apply hsmul.ae_eq
    exact Filter.Eventually.of_forall fun x => by
      rw [affineToUnit_gradient]
      rfl

@[simp]
theorem affineToUnit_velocityLp
    {I : BoxIntegral.Box (Fin (n + 1))}
    (u : SmoothBoxScalarH1ZeroField I) :
    u.affineToUnit.velocityLp =
      boxLpToUnitCube I u.velocityLp := by
  have hu := ae_comp_boxFromUnit I u.field_memLp.coeFn_toLp
  apply Lp.ext
  filter_upwards [u.affineToUnit.field_memLp.coeFn_toLp,
    boxLpToUnitCube_coeFn I u.velocityLp, hu] with x hnew hpull hu
  change
    ((u.affineToUnit.field_memLp.toLp u.affineToUnit.field) x : ℝ) =
      ((boxLpToUnitCube I u.velocityLp) x : ℝ)
  rw [hnew, hpull]
  change (NNReal.sqrt (boxJacobian I) : ℝ) *
      u.field (boxFromUnit I x) =
    (NNReal.sqrt (boxJacobian I) : ℝ) *
      u.velocityLp (boxFromUnit I x)
  have hux : u.velocityLp (boxFromUnit I x) =
      u.field (boxFromUnit I x) := by
    simpa only [Function.comp_apply,
      SmoothBoxScalarH1ZeroField.velocityLp] using hu
  rw [hux]

@[simp]
theorem affineToUnit_gradientLp
    {I : BoxIntegral.Box (Fin (n + 1))}
    (u : SmoothBoxScalarH1ZeroField I) :
    u.affineToUnit.gradientLp =
      boxGradientLpToUnitCube I u.gradientLp := by
  have hu := ae_comp_boxFromUnit I u.gradient_memLp.coeFn_toLp
  apply Lp.ext
  filter_upwards [u.affineToUnit.gradient_memLp.coeFn_toLp,
    boxGradientLpToUnitCube_coeFn I u.gradientLp, hu] with x hnew hpull hu
  change
    ((u.affineToUnit.gradient_memLp.toLp
        (boxScalarGradientValue u.affineToUnit.derivative)) x :
      BoxScalarGradientValue n) =
      ((boxGradientLpToUnitCube I u.gradientLp) x :
        BoxScalarGradientValue n)
  rw [hnew, hpull]
  change boxScalarGradientValue u.affineToUnitDerivative x = _
  rw [affineToUnit_gradient]
  have hux : u.gradientLp (boxFromUnit I x) =
      boxScalarGradientValue u.derivative (boxFromUnit I x) := by
    simpa only [Function.comp_apply,
      SmoothBoxScalarH1ZeroField.gradientLp] using hu
  rw [hux]

end SmoothBoxScalarH1ZeroField

/-- Componentwise affine pullback on the scalar graph ambient spaces. -/
def boxScalarAmbientToUnitCube
    (I : BoxIntegral.Box (Fin (n + 1))) :
    BoxScalarEnergyAmbient I →L[ℝ]
      BoxScalarEnergyAmbient (unitGalerkinBox n) :=
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ
    (BoxScalarL2 (unitGalerkinBox n))
    (BoxScalarGradientL2 (unitGalerkinBox n))
  (e.symm :
      (BoxScalarL2 (unitGalerkinBox n) ×
        BoxScalarGradientL2 (unitGalerkinBox n)) →L[ℝ]
        BoxScalarEnergyAmbient (unitGalerkinBox n)) ∘L
    (((boxLpToUnitCube I).toContinuousLinearMap.comp
        (WithLp.fstL 2 ℝ (BoxScalarL2 I) (BoxScalarGradientL2 I))).prod
      ((boxGradientLpToUnitCube I).comp
        (WithLp.sndL 2 ℝ (BoxScalarL2 I) (BoxScalarGradientL2 I))))

@[simp]
theorem boxScalarAmbientToUnitCube_velocity
    (I : BoxIntegral.Box (Fin (n + 1)))
    (z : BoxScalarEnergyAmbient I) :
    boxScalarEnergyVelocityProjection (unitGalerkinBox n)
        (boxScalarAmbientToUnitCube I z) =
      boxLpToUnitCube I (boxScalarEnergyVelocityProjection I z) := by
  rfl

@[simp]
theorem boxScalarAmbientToUnitCube_gradient
    (I : BoxIntegral.Box (Fin (n + 1)))
    (z : BoxScalarEnergyAmbient I) :
    WithLp.sndL 2 ℝ
        (BoxScalarL2 (unitGalerkinBox n))
        (BoxScalarGradientL2 (unitGalerkinBox n))
        (boxScalarAmbientToUnitCube I z) =
      boxGradientLpToUnitCube I
        (WithLp.sndL 2 ℝ (BoxScalarL2 I) (BoxScalarGradientL2 I) z) := by
  rfl

@[simp]
theorem boxScalarAmbientToUnitCube_graphPoint
    (I : BoxIntegral.Box (Fin (n + 1)))
    (u : SmoothBoxScalarH1ZeroField I) :
    boxScalarAmbientToUnitCube I u.graphPoint =
      u.affineToUnit.graphPoint := by
  change WithLp.toLp 2
      (boxLpToUnitCube I u.velocityLp,
        boxGradientLpToUnitCube I u.gradientLp) =
    WithLp.toLp 2
      (u.affineToUnit.velocityLp, u.affineToUnit.gradientLp)
  rw [u.affineToUnit_velocityLp, u.affineToUnit_gradientLp]

theorem smoothBoxScalarFullGraphCore_map_toUnitCube_le
    (I : BoxIntegral.Box (Fin (n + 1))) :
    (smoothBoxScalarFullGraphCore I).map
        (boxScalarAmbientToUnitCube I).toLinearMap ≤
      smoothBoxScalarFullGraphCore (unitGalerkinBox n) := by
  rw [smoothBoxScalarFullGraphCore, smoothBoxScalarFullGraphCore]
  apply (Submodule.map_span_le
    (boxScalarAmbientToUnitCube I).toLinearMap
    (smoothBoxScalarFullGraphSet I)
    (Submodule.span ℝ
      (smoothBoxScalarFullGraphSet (unitGalerkinBox n)))).2
  rintro _ ⟨u, rfl⟩
  exact Submodule.subset_span
    ⟨u.affineToUnit, (boxScalarAmbientToUnitCube_graphPoint I u).symm⟩

/-- Affine pullback on the completed scalar zero-trace graph. -/
def boxScalarFullEnergyToUnitCube
    (I : BoxIntegral.Box (Fin (n + 1))) :
    BoxH1ZeroScalarFull I →L[ℝ]
      BoxH1ZeroScalarFull (unitGalerkinBox n) :=
  ((boxScalarAmbientToUnitCube I).comp
      (smoothBoxScalarFullGraphCore I).topologicalClosure.subtypeL).codRestrict
    (smoothBoxScalarFullGraphCore
      (unitGalerkinBox n)).topologicalClosure fun u => by
      have huMap :
          boxScalarAmbientToUnitCube I
              (u : BoxScalarEnergyAmbient I) ∈
            (smoothBoxScalarFullGraphCore I).topologicalClosure.map
              (boxScalarAmbientToUnitCube I).toLinearMap :=
        ⟨u, u.property, rfl⟩
      have huClosure :
          boxScalarAmbientToUnitCube I
              (u : BoxScalarEnergyAmbient I) ∈
            ((smoothBoxScalarFullGraphCore I).map
              (boxScalarAmbientToUnitCube I).toLinearMap
            ).topologicalClosure :=
        (smoothBoxScalarFullGraphCore I).topologicalClosure_map
          (boxScalarAmbientToUnitCube I) huMap
      exact Submodule.topologicalClosure_mono
        (smoothBoxScalarFullGraphCore_map_toUnitCube_le I) huClosure

@[simp]
theorem boxScalarFullEnergyToVelocity_toUnitCube
    (I : BoxIntegral.Box (Fin (n + 1)))
    (u : BoxH1ZeroScalarFull I) :
    boxScalarFullEnergyToVelocity (unitGalerkinBox n)
        (boxScalarFullEnergyToUnitCube I u) =
      boxLpToUnitCube I (boxScalarFullEnergyToVelocity I u) := by
  rfl

/-- Scalar Rellich compactness for the completed zero-trace graph on every
nondegenerate rectangular box. -/
theorem boxScalarFullEnergyToVelocity_isCompactOperator_fourier
    (I : BoxIntegral.Box (Fin (n + 1))) :
    IsCompactOperator (boxScalarFullEnergyToVelocity I) := by
  apply isCompactOperator_of_isometry_comp_real
    (boxLpToUnitCube I)
    (boxLpToUnitCube I).isometry
    (boxScalarFullEnergyToVelocity I)
  have hcomp :=
    unitCube_boxScalarFullEnergyToVelocity_isCompactOperator.comp_clm
      (boxScalarFullEnergyToUnitCube I)
  simpa only [Function.comp_apply,
    boxScalarFullEnergyToVelocity_toUnitCube] using hcomp

/-- Compactness of the canonical divergence-free graph embedding on every
nondegenerate rectangular box. -/
theorem boxEnergyToState_isCompactOperator_fourier
    (I : BoxIntegral.Box (Fin (n + 1))) :
    IsCompactOperator (boxEnergyToState I) :=
  boxEnergyToState_isCompactOperator_of_scalarFullRellich I
    (boxScalarFullEnergyToVelocity_isCompactOperator_fourier I)

end BoxAffine

end
