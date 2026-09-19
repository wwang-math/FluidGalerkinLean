import PDEIdeas.BoxSobolevClosure
import Mathlib.Analysis.Normed.Lp.SmoothApprox

open MeasureTheory Real InnerProductSpace Set
open scoped ContDiff ENNReal NNReal RealInnerProductSpace

noncomputable section

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

variable {n : ℕ}

/-- Scalar L2 space on a rectangular box. -/
abbrev BoxScalarL2 (I : BoxIntegral.Box (Fin (n + 1))) :=
  Lp ℝ (2 : ℝ≥0∞) (BoxMeasure I)

/-- One velocity coordinate as a continuous linear map. -/
def boxVelocityCoordinateValue
    (i : Fin (n + 1)) :
    BoxVelocityValue n →L[ℝ] ℝ :=
  PiLp.proj (p := 2) (β := fun _ : Fin (n + 1) => ℝ) i

/-- One full-derivative coordinate as a continuous linear map. -/
def boxGradientCoordinateValue
    (i j : Fin (n + 1)) :
    BoxGradientValue n →L[ℝ] ℝ :=
  PiLp.proj (p := 2)
    (β := fun _ : Fin (n + 1) × Fin (n + 1) => ℝ) (i, j)

/-- Coordinate projection on box velocity L2. -/
def boxVelocityCoordinateLp
    (I : BoxIntegral.Box (Fin (n + 1)))
    (i : Fin (n + 1)) :
    BoxVelocityL2 I →L[ℝ] BoxScalarL2 I :=
  (boxVelocityCoordinateValue i).compLpL 2 (BoxMeasure I)

/-- Coordinate projection on box derivative L2. -/
def boxGradientCoordinateLp
    (I : BoxIntegral.Box (Fin (n + 1)))
    (i j : Fin (n + 1)) :
    BoxGradientL2 I →L[ℝ] BoxScalarL2 I :=
  (boxGradientCoordinateValue i j).compLpL 2 (BoxMeasure I)

theorem SmoothBoxEnergyField.velocityCoordinate_memLp
    {I : BoxIntegral.Box (Fin (n + 1))}
    (u : SmoothBoxEnergyField I)
    (i : Fin (n + 1)) :
    MemLp (fun x => u.field x i) 2 (BoxMeasure I) := by
  simpa [boxVelocityCoordinateValue, boxVelocityValue] using
    u.velocity_memLp.continuousLinearMap_comp (boxVelocityCoordinateValue i)

theorem SmoothBoxEnergyField.gradientCoordinate_memLp
    {I : BoxIntegral.Box (Fin (n + 1))}
    (u : SmoothBoxEnergyField I)
    (i j : Fin (n + 1)) :
    MemLp (fun x => u.derivative x (Pi.single j 1) i)
      2 (BoxMeasure I) := by
  simpa [boxGradientCoordinateValue, boxGradientValue] using
    u.gradient_memLp.continuousLinearMap_comp
      (boxGradientCoordinateValue i j)

@[simp]
theorem boxVelocityCoordinateLp_velocityLp
    {I : BoxIntegral.Box (Fin (n + 1))}
    (u : SmoothBoxEnergyField I)
    (i : Fin (n + 1)) :
    boxVelocityCoordinateLp I i u.velocityLp =
      (u.velocityCoordinate_memLp i).toLp (fun x => u.field x i) := by
  change
    (boxVelocityCoordinateValue i).compLpL 2 (BoxMeasure I) u.velocityLp =
      (u.velocityCoordinate_memLp i).toLp (fun x => u.field x i)
  apply Lp.ext
  filter_upwards [
    (boxVelocityCoordinateValue i).coeFn_compLpL u.velocityLp,
    u.velocity_memLp.coeFn_toLp,
    (u.velocityCoordinate_memLp i).coeFn_toLp] with x hcomp hu hrhs
  rw [hcomp, hrhs]
  simpa [SmoothBoxEnergyField.velocityLp, boxVelocityCoordinateValue,
    boxVelocityValue] using congrArg (boxVelocityCoordinateValue i) hu

@[simp]
theorem boxGradientCoordinateLp_gradientLp
    {I : BoxIntegral.Box (Fin (n + 1))}
    (u : SmoothBoxEnergyField I)
    (i j : Fin (n + 1)) :
    boxGradientCoordinateLp I i j u.gradientLp =
      (u.gradientCoordinate_memLp i j).toLp
        (fun x => u.derivative x (Pi.single j 1) i) := by
  change
    (boxGradientCoordinateValue i j).compLpL 2 (BoxMeasure I) u.gradientLp =
      (u.gradientCoordinate_memLp i j).toLp
        (fun x => u.derivative x (Pi.single j 1) i)
  apply Lp.ext
  filter_upwards [
    (boxGradientCoordinateValue i j).coeFn_compLpL u.gradientLp,
    u.gradient_memLp.coeFn_toLp,
    (u.gradientCoordinate_memLp i j).coeFn_toLp] with x hcomp hu hrhs
  rw [hcomp, hrhs]
  simpa [SmoothBoxEnergyField.gradientLp, boxGradientCoordinateValue,
    boxGradientValue] using congrArg (boxGradientCoordinateValue i j) hu

theorem real_inner_toLp_toLp
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f g : α → ℝ)
    (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) :
    ⟪hf.toLp f, hg.toLp g⟫_ℝ = ∫ x, f x * g x ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  rw [hfx, hgx]
  change g x * f x = f x * g x
  exact mul_comm _ _

/-- A smooth compactly supported scalar test is square-integrable on the box. -/
def smoothBoxScalarTestMemLp
    (I : BoxIntegral.Box (Fin (n + 1)))
    (g : (Fin (n + 1) → ℝ) → ℝ)
    (hg : ContDiff ℝ (∞ : WithTop ℕ∞) g)
    (hgc : HasCompactSupport g) :
    MemLp g 2 (BoxMeasure I) :=
  hg.continuous.memLp_of_hasCompactSupport hgc

/-- One coordinate derivative of a smooth scalar test. -/
def smoothBoxScalarDirectionalDerivative
    (j : Fin (n + 1))
    (g : (Fin (n + 1) → ℝ) → ℝ) :
    (Fin (n + 1) → ℝ) → ℝ :=
  fun x => fderiv ℝ g x (Pi.single j 1)

/-- A directional derivative of a smooth compactly supported scalar test is
square-integrable on the box. -/
def smoothBoxScalarDerivativeTestMemLp
    (I : BoxIntegral.Box (Fin (n + 1)))
    (j : Fin (n + 1))
    (g : (Fin (n + 1) → ℝ) → ℝ)
    (hg : ContDiff ℝ (∞ : WithTop ℕ∞) g)
    (hgc : HasCompactSupport g) :
    MemLp (smoothBoxScalarDirectionalDerivative j g) 2 (BoxMeasure I) := by
  let dg := smoothBoxScalarDirectionalDerivative j g
  have hdg_cont : Continuous dg :=
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdg_compact : HasCompactSupport dg :=
    hgc.fderiv_apply ℝ (Pi.single j 1)
  exact hdg_cont.memLp_of_hasCompactSupport hdg_compact

/-- A smooth compactly supported scalar test represented in box L2. -/
def smoothBoxScalarTestLp
    (I : BoxIntegral.Box (Fin (n + 1)))
    (g : (Fin (n + 1) → ℝ) → ℝ)
    (hg : ContDiff ℝ (∞ : WithTop ℕ∞) g)
    (hgc : HasCompactSupport g) :
    BoxScalarL2 I :=
  (smoothBoxScalarTestMemLp I g hg hgc).toLp g

/-- One directional derivative of a smooth compactly supported scalar test in
box L2. -/
def smoothBoxScalarDerivativeTestLp
    (I : BoxIntegral.Box (Fin (n + 1)))
    (j : Fin (n + 1))
    (g : (Fin (n + 1) → ℝ) → ℝ)
    (hg : ContDiff ℝ (∞ : WithTop ℕ∞) g)
    (hgc : HasCompactSupport g) :
    BoxScalarL2 I :=
  (smoothBoxScalarDerivativeTestMemLp I j g hg hgc).toLp
    (smoothBoxScalarDirectionalDerivative j g)

/-- The closed weak-derivative relation for one velocity component and one
coordinate direction. -/
def boxWeakDerivativePairing
    (I : BoxIntegral.Box (Fin (n + 1)))
    (i j : Fin (n + 1))
    (g : (Fin (n + 1) → ℝ) → ℝ)
    (hg : ContDiff ℝ (∞ : WithTop ℕ∞) g)
    (hgc : HasCompactSupport g) :
    BoxEnergyAmbient I →L[ℝ] ℝ :=
  ((innerSL ℝ (smoothBoxScalarTestLp I g hg hgc)).comp
      ((boxGradientCoordinateLp I i j).comp
        (boxEnergyGradientProjection I))) +
    ((innerSL ℝ (smoothBoxScalarDerivativeTestLp I j g hg hgc)).comp
      ((boxVelocityCoordinateLp I i).comp
        (boxEnergyVelocityProjection I)))

theorem boxWeakDerivativePairing_graphPoint
    (I : BoxIntegral.Box (Fin (n + 1)))
    (i j : Fin (n + 1))
    (g : (Fin (n + 1) → ℝ) → ℝ)
    (hg : ContDiff ℝ (∞ : WithTop ℕ∞) g)
    (hgc : HasCompactSupport g)
    (u : SmoothBoxEnergyField I) :
    boxWeakDerivativePairing I i j g hg hgc u.graphPoint = 0 := by
  let velocityProj :
      (Fin (n + 1) → ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.proj i
  let velocityDerivative :
      (Fin (n + 1) → ℝ) →
        (Fin (n + 1) → ℝ) →L[ℝ] ℝ :=
    fun x => velocityProj.comp (u.derivative x)
  have hvelocity_deriv :
      ∀ x ∈ interior (BoxIntegral.Box.Icc I),
        HasFDerivAt (fun y => u.field y i) (velocityDerivative x) x := by
    intro x hx
    exact velocityProj.hasFDerivAt.comp x (u.hasFDerivAt_field x hx)
  have hvelocity_cont :
      ContinuousOn (fun y => u.field y i) (BoxIntegral.Box.Icc I) :=
    velocityProj.continuous.comp_continuousOn u.continuousOn_field
  have htest_deriv :
      ∀ x ∈ interior (BoxIntegral.Box.Icc I),
        HasFDerivAt g (fderiv ℝ g x) x := by
    intro x _hx
    exact (hg.differentiable (by simp) x).hasFDerivAt
  have htest : MemLp g 2 (BoxMeasure I) :=
    smoothBoxScalarTestMemLp I g hg hgc
  have hdtest :
      MemLp (smoothBoxScalarDirectionalDerivative j g) 2 (BoxMeasure I) :=
    smoothBoxScalarDerivativeTestMemLp I j g hg hgc
  have hleft :
      IntegrableOn
        (fun x => u.derivative x (Pi.single j 1) i * g x)
        (BoxIntegral.Box.Icc I) :=
    (u.gradientCoordinate_memLp i j).integrable_mul htest
  have hright :
      IntegrableOn
        (fun x => u.field x i *
          smoothBoxScalarDirectionalDerivative j g x)
        (BoxIntegral.Box.Icc I) :=
    (u.velocityCoordinate_memLp i).integrable_mul hdtest
  have hibp := scalar_coordinate_ibp I j
    (fun x => u.field x i) g velocityDerivative (fun x => fderiv ℝ g x)
    hvelocity_deriv hvelocity_cont htest_deriv hg.continuous.continuousOn
    (ZeroDirichletVectorOnBox.component I u.field
      u.zeroDirichlet_field i)
    (by simpa [velocityDerivative, velocityProj] using hleft)
    (by simpa [smoothBoxScalarDirectionalDerivative] using hright)
  have hibp' :
      ∫ x, g x * u.derivative x (Pi.single j 1) i ∂BoxMeasure I =
        -∫ x, smoothBoxScalarDirectionalDerivative j g x *
          u.field x i ∂BoxMeasure I := by
    simpa [BoxMeasure, velocityDerivative, velocityProj,
      smoothBoxScalarDirectionalDerivative, mul_comm] using hibp
  change
    ⟪smoothBoxScalarTestLp I g hg hgc,
      boxGradientCoordinateLp I i j u.gradientLp⟫_ℝ +
      ⟪smoothBoxScalarDerivativeTestLp I j g hg hgc,
        boxVelocityCoordinateLp I i u.velocityLp⟫_ℝ = 0
  rw [boxGradientCoordinateLp_gradientLp,
    boxVelocityCoordinateLp_velocityLp]
  change
    ⟪htest.toLp g,
      (u.gradientCoordinate_memLp i j).toLp
        (fun x => u.derivative x (Pi.single j 1) i)⟫_ℝ +
      ⟪hdtest.toLp (smoothBoxScalarDirectionalDerivative j g),
        (u.velocityCoordinate_memLp i).toLp
          (fun x => u.field x i)⟫_ℝ = 0
  rw [real_inner_toLp_toLp, real_inner_toLp_toLp]
  linarith [hibp']

theorem smoothBoxGraphCore_le_boxWeakDerivativePairing_ker
    (I : BoxIntegral.Box (Fin (n + 1)))
    (i j : Fin (n + 1))
    (g : (Fin (n + 1) → ℝ) → ℝ)
    (hg : ContDiff ℝ (∞ : WithTop ℕ∞) g)
    (hgc : HasCompactSupport g) :
    smoothBoxGraphCore I ≤
      (boxWeakDerivativePairing I i j g hg hgc).ker := by
  apply Submodule.span_le.mpr
  rintro _ ⟨u, rfl⟩
  exact boxWeakDerivativePairing_graphPoint I i j g hg hgc u

theorem boxWeakDerivativePairing_eq_zero
    (I : BoxIntegral.Box (Fin (n + 1)))
    (i j : Fin (n + 1))
    (g : (Fin (n + 1) → ℝ) → ℝ)
    (hg : ContDiff ℝ (∞ : WithTop ℕ∞) g)
    (hgc : HasCompactSupport g)
    (u : BoxH1ZeroSigma I) :
    boxWeakDerivativePairing I i j g hg hgc
      (u : BoxEnergyAmbient I) = 0 := by
  have hu :
      (u : BoxEnergyAmbient I) ∈
        (boxWeakDerivativePairing I i j g hg hgc).ker :=
    (smoothBoxGraphCore I).topologicalClosure_minimal
      (smoothBoxGraphCore_le_boxWeakDerivativePairing_ker
        I i j g hg hgc)
      (boxWeakDerivativePairing I i j g hg hgc).isClosed_ker
      u.property
  exact hu

theorem boxEnergyGradientCoordinate_inner_smoothTest_eq_zero
    (I : BoxIntegral.Box (Fin (n + 1)))
    (u : BoxH1ZeroSigma I)
    (hu : boxEnergyToState I u = 0)
    (i j : Fin (n + 1))
    (g : (Fin (n + 1) → ℝ) → ℝ)
    (hg : ContDiff ℝ (∞ : WithTop ℕ∞) g)
    (hgc : HasCompactSupport g) :
    ⟪smoothBoxScalarTestLp I g hg hgc,
      boxGradientCoordinateLp I i j (boxEnergyGradient I u)⟫_ℝ = 0 := by
  have hvelocity :
      boxEnergyVelocityProjection I (u : BoxEnergyAmbient I) = 0 := by
    exact congrArg Subtype.val hu
  have hp :=
    boxWeakDerivativePairing_eq_zero I i j g hg hgc u
  change
    ⟪smoothBoxScalarTestLp I g hg hgc,
      boxGradientCoordinateLp I i j
        (boxEnergyGradientProjection I (u : BoxEnergyAmbient I))⟫_ℝ +
      ⟪smoothBoxScalarDerivativeTestLp I j g hg hgc,
        boxVelocityCoordinateLp I i
          (boxEnergyVelocityProjection I (u : BoxEnergyAmbient I))⟫_ℝ = 0 at hp
  rw [hvelocity, map_zero] at hp
  simpa [boxEnergyGradient] using hp

theorem boxEnergyGradientCoordinate_eq_zero
    (I : BoxIntegral.Box (Fin (n + 1)))
    (u : BoxH1ZeroSigma I)
    (hu : boxEnergyToState I u = 0)
    (i j : Fin (n + 1)) :
    boxGradientCoordinateLp I i j (boxEnergyGradient I u) = 0 := by
  let G : BoxScalarL2 I :=
    boxGradientCoordinateLp I i j (boxEnergyGradient I u)
  have hdense :
      Dense {φ : BoxScalarL2 I |
        ∃ g : (Fin (n + 1) → ℝ) → ℝ,
          φ =ᵐ[BoxMeasure I] g ∧
          HasCompactSupport g ∧
          ContDiff ℝ (∞ : WithTop ℕ∞) g} :=
    MeasureTheory.Lp.dense_hasCompactSupport_contDiff
      (μ := BoxMeasure I) (p := (2 : ℝ≥0∞)) (by norm_num)
  apply hdense.eq_zero_of_inner_right ℝ
  intro φ hφ
  rcases hφ with ⟨g, hφg, hgc, hg⟩
  have hφ_eq : φ = smoothBoxScalarTestLp I g hg hgc := by
    apply Lp.ext
    exact hφg.trans
      (smoothBoxScalarTestMemLp I g hg hgc).coeFn_toLp.symm
  rw [hφ_eq]
  exact boxEnergyGradientCoordinate_inner_smoothTest_eq_zero
    I u hu i j g hg hgc

theorem boxEnergyGradient_eq_zero_of_state_eq_zero
    (I : BoxIntegral.Box (Fin (n + 1)))
    (u : BoxH1ZeroSigma I)
    (hu : boxEnergyToState I u = 0) :
    boxEnergyGradient I u = 0 := by
  let G : BoxGradientL2 I := boxEnergyGradient I u
  have hcoordinate :
      ∀ i j : Fin (n + 1), boxGradientCoordinateLp I i j G = 0 := by
    intro i j
    exact boxEnergyGradientCoordinate_eq_zero I u hu i j
  have hcoordinate_ae :
      ∀ ij : Fin (n + 1) × Fin (n + 1),
        ∀ᵐ x ∂BoxMeasure I, G x ij = 0 := by
    intro ij
    have hzero :
        (boxGradientCoordinateValue ij.1 ij.2).compLpL
          2 (BoxMeasure I) G = 0 := by
      simpa [boxGradientCoordinateLp] using
        hcoordinate ij.1 ij.2
    have hcomp :=
      (boxGradientCoordinateValue ij.1 ij.2).coeFn_compLpL G
    rw [hzero] at hcomp
    filter_upwards [hcomp, Lp.coeFn_zero ℝ 2 (BoxMeasure I)] with x hx hzero_x
    rw [hzero_x] at hx
    simpa [boxGradientCoordinateValue] using hx.symm
  have hall :
      ∀ᵐ x ∂BoxMeasure I,
        ∀ ij : Fin (n + 1) × Fin (n + 1), G x ij = 0 :=
    Filter.eventually_all.mpr hcoordinate_ae
  apply Lp.ext
  filter_upwards [hall,
    Lp.coeFn_zero (BoxGradientValue n) 2 (BoxMeasure I)] with x hx hzero_x
  rw [hzero_x]
  ext ij
  exact hx ij

theorem boxEnergyToState_injective
    (I : BoxIntegral.Box (Fin (n + 1))) :
    Function.Injective (boxEnergyToState I) := by
  intro u v huv
  have hstate :
      boxEnergyToState I (u - v) = 0 := by
    rw [map_sub, huv, sub_self]
  have hvelocity :
      boxEnergyVelocityProjection I
        ((u - v : BoxH1ZeroSigma I) : BoxEnergyAmbient I) = 0 :=
    congrArg Subtype.val hstate
  have hgradient :
      boxEnergyGradientProjection I
        ((u - v : BoxH1ZeroSigma I) : BoxEnergyAmbient I) = 0 :=
    boxEnergyGradient_eq_zero_of_state_eq_zero I (u - v) hstate
  have hambient :
      ((u - v : BoxH1ZeroSigma I) : BoxEnergyAmbient I) = 0 := by
    apply (WithLp.equiv 2
      (BoxVelocityL2 I × BoxGradientL2 I)).injective
    apply Prod.ext
    · exact hvelocity
    · exact hgradient
  apply sub_eq_zero.mp
  apply Subtype.ext
  exact hambient

end
