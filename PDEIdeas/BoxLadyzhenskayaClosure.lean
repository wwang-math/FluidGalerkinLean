import PDEIdeas.BoxL4Convection
import PDEIdeas.LpExponentInclusion

/-!
# Extending a box Ladyzhenskaya realization from the graph core

A continuous `L4` representative on the smooth graph span extends along its
dense isometric inclusion into the closed energy space. The finite-measure
inclusion `L4 -> L2` shows that the extension represents the same velocity as
the canonical state map. The Ladyzhenskaya inequality passes to the closure by
continuity.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

local instance boxLadyClosureFactOneLeFour : Fact (1 ≤ (4 : ℝ≥0∞)) :=
  ⟨by norm_num⟩

variable {n : ℕ}
variable (I : BoxIntegral.Box (Fin (n + 1)))

private theorem boxLadyClosureMeasure_isFinite :
    IsFiniteMeasure (BoxMeasure I) := by
  rw [isFiniteMeasure_restrict]
  exact (I.measure_Icc_lt_top volume).ne

local instance boxLadyClosureFiniteMeasure : IsFiniteMeasure (BoxMeasure I) :=
  boxLadyClosureMeasure_isFinite I

local instance boxLadyClosureIsUniformAddGroup :
    IsUniformAddGroup (smoothBoxGraphCore I) :=
  (smoothBoxGraphCore I).toAddSubgroup.isUniformAddGroup

/-- Continuous finite-measure inclusion of box velocities from `L4` to `L2`. -/
noncomputable def boxVelocityL4ToL2 :
    BoxVelocityL4 I →L[ℝ] BoxVelocityL2 I :=
  lpFourToTwo (BoxMeasure I)

/-- Inclusion of the closed divergence-free state space into ambient vector
`L2`. -/
def boxStateAmbientInclusion :
    BoxL2Sigma I →L[ℝ] BoxVelocityL2 I :=
  (smoothBoxVelocityCore I).topologicalClosure.subtypeL

/-- A Ladyzhenskaya realization on the dense smooth graph core. -/
structure BoxCoreLadyzhenskayaRealization where
  toLp4 : smoothBoxGraphCore I →L[ℝ] BoxVelocityL4 I
  compatible : ∀ u : smoothBoxGraphCore I,
    boxVelocityL4ToL2 I (toLp4 u) =
      boxStateAmbientInclusion I
        (boxEnergyToState I (boxSmoothGraphCoreInclusion I u))
  constant : ℝ
  constant_nonneg : 0 ≤ constant
  l4_sq_le : ∀ u : smoothBoxGraphCore I,
    ‖toLp4 u‖ ^ 2 ≤
      constant *
        ‖boxEnergyToState I (boxSmoothGraphCoreInclusion I u)‖ *
        ‖boxEnergyGradient I (boxSmoothGraphCoreInclusion I u)‖

namespace BoxCoreLadyzhenskayaRealization

variable (C : BoxCoreLadyzhenskayaRealization I)

/-- Continuous extension of the core `L4` representative to the closed energy
space. -/
noncomputable def toLp4Extension :
    BoxH1ZeroSigma I →L[ℝ] BoxVelocityL4 I :=
  ContinuousLinearMap.extend (𝕜₂ := ℝ)
    (E := smoothBoxGraphCore I) (Eₗ := BoxH1ZeroSigma I)
    (F := BoxVelocityL4 I) C.toLp4 (boxSmoothGraphCoreInclusion I)

@[simp]
theorem toLp4Extension_apply_core (u : smoothBoxGraphCore I) :
    C.toLp4Extension I (boxSmoothGraphCoreInclusion I u) = C.toLp4 u := by
  exact ContinuousLinearMap.extend_eq C.toLp4
    (boxSmoothGraphCoreInclusion_denseRange I)
    (boxSmoothGraphCoreInclusion_isUniformInducing I) u

theorem toLp4Extension_l2_compatible (u : BoxH1ZeroSigma I) :
    boxVelocityL4ToL2 I (C.toLp4Extension I u) =
      boxStateAmbientInclusion I (boxEnergyToState I u) := by
  let left : BoxH1ZeroSigma I →L[ℝ] BoxVelocityL2 I :=
    (boxVelocityL4ToL2 I).comp (C.toLp4Extension I)
  let right : BoxH1ZeroSigma I →L[ℝ] BoxVelocityL2 I :=
    (boxStateAmbientInclusion I).comp (boxEnergyToState I)
  refine DenseRange.induction_on (boxSmoothGraphCoreInclusion_denseRange I)
    (p := fun u => left u = right u) u ?_ ?_
  · exact isClosed_eq left.continuous right.continuous
  · intro v
    change boxVelocityL4ToL2 I
        (C.toLp4Extension I (boxSmoothGraphCoreInclusion I v)) =
      boxStateAmbientInclusion I
        (boxEnergyToState I (boxSmoothGraphCoreInclusion I v))
    rw [C.toLp4Extension_apply_core I]
    exact C.compatible v

theorem toLp4Extension_l4_sq_le (u : BoxH1ZeroSigma I) :
    ‖C.toLp4Extension I u‖ ^ 2 ≤
      C.constant * ‖boxEnergyToState I u‖ * ‖boxEnergyGradient I u‖ := by
  refine DenseRange.induction_on (boxSmoothGraphCoreInclusion_denseRange I)
    (p := fun u => ‖C.toLp4Extension I u‖ ^ 2 ≤
      C.constant * ‖boxEnergyToState I u‖ * ‖boxEnergyGradient I u‖)
    u ?_ ?_
  · apply isClosed_le <;> fun_prop
  · intro v
    rw [C.toLp4Extension_apply_core I]
    exact C.l4_sq_le v

/-- Closed box Ladyzhenskaya realization obtained from its graph-core data. -/
noncomputable def toBoxLadyzhenskayaRealization :
    BoxLadyzhenskayaRealization I where
  toLp4 := C.toLp4Extension I
  coeFn_toLp4_eq_state := by
    intro u
    have hL2 := C.toLp4Extension_l2_compatible I u
    have hae :
        (boxVelocityL4ToL2 I (C.toLp4Extension I u) :
            (Fin (n + 1) → ℝ) → BoxVelocityValue n) =ᵐ[BoxMeasure I]
          (boxStateAmbientInclusion I (boxEnergyToState I u) :
            (Fin (n + 1) → ℝ) → BoxVelocityValue n) := by
      rw [← Lp.ext_iff]
      exact hL2
    exact hae
  constant := C.constant
  constant_nonneg := C.constant_nonneg
  l4_sq_le := C.toLp4Extension_l4_sq_le I

end BoxCoreLadyzhenskayaRealization

end
