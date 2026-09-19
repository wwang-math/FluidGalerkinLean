import PDEIdeas.BoxLerayBounds
import PDEIdeas.BoxVariationalGalerkin
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Physical energy bounds for finite box Galerkin solutions

A finite coefficient space must carry the physical `L²` mass norm.  The
state-lift isometry records this compatibility.  The resulting coefficient
energy estimate then controls the lifted state, gradient, and full box energy
path with constants independent of coordinates.
-/

open BoundedContinuousFunction InnerProductSpace MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

variable {n : ℕ}

/-- A finite smooth box Galerkin level whose coefficient norm is exactly the
physical `L²` norm of the synthesized velocity. -/
structure SmoothBoxVariationalGalerkinLevel
    (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] where
  transport : SmoothBoxGalerkinTransport (n := n) W
  energyData : transport.EnergyData
  stateLift_isometry : Isometry energyData.stateLift

namespace SmoothBoxVariationalGalerkinLevel

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
variable [FiniteDimensional ℝ W]

/-- The finite variational problem with physical gradient diffusion and the
box transport form. -/
def problem
    (L : SmoothBoxVariationalGalerkinLevel (n := n) W)
    (forcing : ℝ → W →L[ℝ] ℝ) (initial : W) :
    VariationalGalerkinProblem W where
  system := L.energyData.toBoxVariationalGalerkinSystem
  forcing := forcing
  initial := initial

@[simp]
theorem problem_system
    (L : SmoothBoxVariationalGalerkinLevel (n := n) W)
    (forcing : ℝ → W →L[ℝ] ℝ) (initial : W) :
    (L.problem forcing initial).system =
      L.energyData.toBoxVariationalGalerkinSystem :=
  rfl

@[simp]
theorem problem_diffusion_apply
    (L : SmoothBoxVariationalGalerkinLevel (n := n) W)
    (forcing : ℝ → W →L[ℝ] ℝ) (initial u v : W) :
    (L.problem forcing initial).system.diffusion u v =
      ⟪L.energyData.gradientLift u, L.energyData.gradientLift v⟫_ℝ :=
  rfl

/-- The physical state lift preserves the coefficient norm. -/
theorem norm_stateLift
    (L : SmoothBoxVariationalGalerkinLevel (n := n) W) (u : W) :
    ‖L.energyData.stateLift u‖ = ‖u‖ := by
  calc
    ‖L.energyData.stateLift u‖ = dist (L.energyData.stateLift u) 0 :=
      (dist_zero_right _).symm
    _ = dist (L.energyData.stateLift u) (L.energyData.stateLift 0) := by
      rw [map_zero]
    _ = dist u 0 := L.stateLift_isometry.dist_eq u 0
    _ = ‖u‖ := dist_zero_right u

variable {a b : ℝ} {t₀ : Icc a b}
variable {forcing : ℝ → W →L[ℝ] ℝ} {initial : W}

/-- An actual finite coefficient solution lifted to a bounded continuous path
in the completed box energy space. -/
def solutionEnergyPath
    (L : SmoothBoxVariationalGalerkinLevel (n := n) W)
    (u : (L.problem forcing initial).LocalSolutionOn t₀) :
    Icc a b →ᵇ BoxH1ZeroSigma L.transport.box :=
  BoundedContinuousFunction.mkOfCompact
    { toFun := fun t => L.energyData.energyLift (u.toFun t)
      continuous_toFun :=
        L.energyData.energyLift.continuous.comp u.continuousOn.restrict }

/-- The lifted path transported along an identification of the level's box
with a fixed box shared by the whole Galerkin tower. -/
def solutionEnergyPathOn
    (L : SmoothBoxVariationalGalerkinLevel (n := n) W)
    (I : BoxIntegral.Box (Fin (n + 1)))
    (hbox : L.transport.box = I)
    (u : (L.problem forcing initial).LocalSolutionOn t₀) :
    Icc a b →ᵇ BoxH1ZeroSigma I := by
  rw [← hbox]
  exact L.solutionEnergyPath u

@[simp]
theorem solutionEnergyPath_apply
    (L : SmoothBoxVariationalGalerkinLevel (n := n) W)
    (u : (L.problem forcing initial).LocalSolutionOn t₀)
    (t : Icc a b) :
    L.solutionEnergyPath u t = L.energyData.energyLift (u.toFun t) :=
  rfl

@[simp]
theorem solutionEnergyPath_state_apply
    (L : SmoothBoxVariationalGalerkinLevel (n := n) W)
    (u : (L.problem forcing initial).LocalSolutionOn t₀)
    (t : Icc a b) :
    boxEnergyStatePath L.transport.box (L.solutionEnergyPath u) t =
      L.energyData.stateLift (u.toFun t) :=
  rfl

@[simp]
theorem solutionEnergyPath_gradient_apply
    (L : SmoothBoxVariationalGalerkinLevel (n := n) W)
    (u : (L.problem forcing initial).LocalSolutionOn t₀)
    (t : Icc a b) :
    boxEnergyGradientPath L.transport.box (L.solutionEnergyPath u) t =
      L.energyData.gradientLift (u.toFun t) :=
  rfl

/-- Lebesgue measure on a closed time interval, transported to its subtype. -/
def intervalSubtypeMeasure (a b : ℝ) : Measure (Icc a b) :=
  Measure.comap Subtype.val volume

instance intervalSubtypeMeasure_isFinite (a b : ℝ) :
    IsFiniteMeasure (intervalSubtypeMeasure a b) where
  measure_univ_lt_top := by
    rw [intervalSubtypeMeasure,
      comap_subtype_coe_apply measurableSet_Icc]
    simp only [image_univ, Subtype.range_val]
    simp [Real.volume_Icc]

/-- Integration over the interval subtype agrees with the ordered interval
integral. -/
theorem integral_intervalSubtypeMeasure
    (hab : a ≤ b) (f : ℝ → ℝ) :
    ∫ t : Icc a b, f t ∂intervalSubtypeMeasure a b =
      ∫ t in a..b, f t := by
  rw [intervalSubtypeMeasure, integral_subtype_comap measurableSet_Icc]
  rw [integral_Icc_eq_integral_Ioc]
  exact (intervalIntegral.integral_of_le hab).symm

/-- The gradient component of a lifted solution has exactly the accumulated
finite-level diffusion energy as its `L²` norm. -/
theorem solutionGradient_toLp_norm_sq_eq_diffusion
    (L : SmoothBoxVariationalGalerkinLevel (n := n) W)
    (hab : a ≤ b)
    (u : (L.problem forcing initial).LocalSolutionOn t₀) :
    ‖BoundedContinuousFunction.toLp (2 : ℝ≥0∞)
      (intervalSubtypeMeasure a b) ℝ
      (boxEnergyGradientPath L.transport.box
        (L.solutionEnergyPath u))‖ ^ 2 =
      ∫ t in a..b,
        (L.problem forcing initial).system.diffusion
          (u.toFun t) (u.toFun t) := by
  rw [BoundedContinuousFunction.norm_toLp_two_sq_eq_integral_norm_sq]
  calc
    ∫ t : Icc a b,
          ‖boxEnergyGradientPath L.transport.box
            (L.solutionEnergyPath u) t‖ ^ 2
          ∂intervalSubtypeMeasure a b =
        ∫ t : Icc a b,
          ‖L.energyData.gradientLift (u.toFun t)‖ ^ 2
          ∂intervalSubtypeMeasure a b := by rfl
    _ = ∫ t in a..b,
          ‖L.energyData.gradientLift (u.toFun t)‖ ^ 2 :=
      integral_intervalSubtypeMeasure (a := a) (b := b) hab
        (fun t => ‖L.energyData.gradientLift (u.toFun t)‖ ^ 2)
    _ = ∫ t in a..b,
          (L.problem forcing initial).system.diffusion
            (u.toFun t) (u.toFun t) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      change ‖L.energyData.gradientLift (u.toFun t)‖ ^ 2 =
        (L.problem forcing initial).system.diffusion
          (u.toFun t) (u.toFun t)
      rw [L.problem_diffusion_apply, real_inner_self_eq_norm_sq]

/-- A coefficient state bound is exactly the corresponding physical state
bound for the lifted path. -/
theorem solutionEnergyPath_state_bound
    (L : SmoothBoxVariationalGalerkinLevel (n := n) W)
    (u : (L.problem forcing initial).LocalSolutionOn t₀)
    (R : ℝ) (hR : ∀ t ∈ Icc a b, ‖u.toFun t‖ ≤ R) :
    ∀ t : Icc a b,
      ‖boxEnergyToState L.transport.box (L.solutionEnergyPath u t)‖ ≤ R := by
  intro t
  rw [show boxEnergyToState L.transport.box (L.solutionEnergyPath u t) =
      L.energyData.stateLift (u.toFun t) by rfl]
  rw [L.norm_stateLift]
  exact hR t t.property

/-- Fixed-box form of the physical state bound. -/
theorem solutionEnergyPathOn_state_bound
    (L : SmoothBoxVariationalGalerkinLevel (n := n) W)
    (I : BoxIntegral.Box (Fin (n + 1)))
    (hbox : L.transport.box = I)
    (u : (L.problem forcing initial).LocalSolutionOn t₀)
    (R : ℝ) (hR : ∀ t ∈ Icc a b, ‖u.toFun t‖ ≤ R) :
    ∀ t : Icc a b,
      ‖boxEnergyToState I (L.solutionEnergyPathOn I hbox u t)‖ ≤ R := by
  subst I
  exact L.solutionEnergyPath_state_bound u R hR

/-- Uniform state and accumulated diffusion estimates on a finite solution
give the full `L²_t H¹` graph bound needed by spectral compactness. -/
theorem solutionEnergyPath_toLp_norm_le
    (L : SmoothBoxVariationalGalerkinLevel (n := n) W)
    (hab : a ≤ b)
    (u : (L.problem forcing initial).LocalSolutionOn t₀)
    (stateRadius gradientRadius : ℝ)
    (hstateRadius : 0 ≤ stateRadius)
    (hgradientRadius : 0 ≤ gradientRadius)
    (hstate : ∀ t ∈ Icc a b, ‖u.toFun t‖ ≤ stateRadius)
    (hgradient :
      ∫ t in a..b,
          (L.problem forcing initial).system.diffusion
            (u.toFun t) (u.toFun t) ≤ gradientRadius ^ 2) :
    ‖BoundedContinuousFunction.toLp (2 : ℝ≥0∞)
      (intervalSubtypeMeasure a b) ℝ (L.solutionEnergyPath u)‖ ≤
      Real.sqrt
        ((measureUnivNNReal (intervalSubtypeMeasure a b) ^
            ((2 : ℝ≥0∞).toReal)⁻¹ * stateRadius) ^ 2 +
          gradientRadius ^ 2) := by
  let stateLpRadius : ℝ :=
    measureUnivNNReal (intervalSubtypeMeasure a b) ^
      ((2 : ℝ≥0∞).toReal)⁻¹ * stateRadius
  have hstateLpRadius : 0 ≤ stateLpRadius := by
    dsimp [stateLpRadius]
    positivity
  have hstateLp :
      ‖BoundedContinuousFunction.toLp (2 : ℝ≥0∞)
        (intervalSubtypeMeasure a b) ℝ
        (boxEnergyStatePath L.transport.box (L.solutionEnergyPath u))‖ ≤
        stateLpRadius := by
    exact boxEnergyStatePath_toLp_norm_le L.transport.box
      (intervalSubtypeMeasure a b) (L.solutionEnergyPath u)
      stateRadius hstateRadius (L.solutionEnergyPath_state_bound u stateRadius hstate)
  have hgradientSq :
      ‖BoundedContinuousFunction.toLp (2 : ℝ≥0∞)
        (intervalSubtypeMeasure a b) ℝ
        (boxEnergyGradientPath L.transport.box
          (L.solutionEnergyPath u))‖ ^ 2 ≤ gradientRadius ^ 2 := by
    rw [L.solutionGradient_toLp_norm_sq_eq_diffusion hab u]
    exact hgradient
  have hgradientLp :
      ‖BoundedContinuousFunction.toLp (2 : ℝ≥0∞)
        (intervalSubtypeMeasure a b) ℝ
        (boxEnergyGradientPath L.transport.box
          (L.solutionEnergyPath u))‖ ≤ gradientRadius :=
    (sq_le_sq₀ (norm_nonneg _) hgradientRadius).mp hgradientSq
  simpa only [stateLpRadius] using
    boxEnergyPath_toLp_norm_le_sqrt L.transport.box
      (intervalSubtypeMeasure a b) (L.solutionEnergyPath u)
      stateLpRadius gradientRadius hstateLpRadius hgradientRadius
      hstateLp hgradientLp

/-- Fixed-box form of the full `L²_t H¹` graph estimate. -/
theorem solutionEnergyPathOn_toLp_norm_le
    (L : SmoothBoxVariationalGalerkinLevel (n := n) W)
    (I : BoxIntegral.Box (Fin (n + 1)))
    (hbox : L.transport.box = I)
    (hab : a ≤ b)
    (u : (L.problem forcing initial).LocalSolutionOn t₀)
    (stateRadius gradientRadius : ℝ)
    (hstateRadius : 0 ≤ stateRadius)
    (hgradientRadius : 0 ≤ gradientRadius)
    (hstate : ∀ t ∈ Icc a b, ‖u.toFun t‖ ≤ stateRadius)
    (hgradient :
      ∫ t in a..b,
          (L.problem forcing initial).system.diffusion
            (u.toFun t) (u.toFun t) ≤ gradientRadius ^ 2) :
    ‖BoundedContinuousFunction.toLp (2 : ℝ≥0∞)
      (intervalSubtypeMeasure a b) ℝ
      (L.solutionEnergyPathOn I hbox u)‖ ≤
      Real.sqrt
        ((measureUnivNNReal (intervalSubtypeMeasure a b) ^
            ((2 : ℝ≥0∞).toReal)⁻¹ * stateRadius) ^ 2 +
          gradientRadius ^ 2) := by
  subst I
  exact L.solutionEnergyPath_toLp_norm_le hab u
    stateRadius gradientRadius hstateRadius hgradientRadius hstate hgradient

end SmoothBoxVariationalGalerkinLevel

end
