import PDEIdeas.BoxLadyzhenskayaClosure
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Ladyzhenskaya control from finite smooth box combinations

Every smooth box energy field defines an `L4` velocity on the compact box.
Finite linear combinations of their graph points and `L4` velocities give
linear maps from a free coefficient module. The graph-combination map is
surjective onto the smooth graph core. A linear section and the injective
finite-measure map `L4 -> L2` therefore produce a well-defined core `L4` map.
A uniform Ladyzhenskaya inequality for these finite combinations makes the
core map continuous and yields the closed-space realization.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

local instance boxSmoothLadyFactOneLeFour : Fact (1 ≤ (4 : ℝ≥0∞)) :=
  ⟨by norm_num⟩

variable {n : ℕ}
variable (I : BoxIntegral.Box (Fin (n + 1)))

private theorem boxSmoothLadyMeasure_isFinite :
    IsFiniteMeasure (BoxMeasure I) := by
  rw [isFiniteMeasure_restrict]
  exact (I.measure_Icc_lt_top volume).ne

local instance boxSmoothL4FiniteMeasure : IsFiniteMeasure (BoxMeasure I) :=
  boxSmoothLadyMeasure_isFinite I

theorem SmoothBoxEnergyField.velocity_memLp_four
    (u : SmoothBoxEnergyField I) :
    MemLp (boxVelocityValue u.field) 4 (BoxMeasure I) := by
  have hcont : ContinuousOn (boxVelocityValue u.field)
      (BoxIntegral.Box.Icc I) := by
    simpa only [boxVelocityValue] using
      (PiLp.continuous_toLp (p := (2 : ℝ≥0∞))
        (β := fun _ : Fin (n + 1) => ℝ)).comp_continuousOn
          u.continuousOn_field
  rcases I.isCompact_Icc.bddAbove_image hcont.norm with ⟨C, hC⟩
  apply MemLp.of_bound u.velocity_memLp.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem I.measurableSet_Icc] with x hx
  exact hC ⟨x, hx, rfl⟩

/-- A smooth box velocity as an `L4` function. -/
noncomputable def SmoothBoxEnergyField.velocityLp4
    (u : SmoothBoxEnergyField I) : BoxVelocityL4 I :=
  (u.velocity_memLp_four I).toLp (boxVelocityValue u.field)

theorem SmoothBoxEnergyField.coeFn_velocityLp4
    (u : SmoothBoxEnergyField I) :
    (u.velocityLp4 I : (Fin (n + 1) → ℝ) → BoxVelocityValue n)
      =ᵐ[BoxMeasure I] boxVelocityValue u.field :=
  (u.velocity_memLp_four I).coeFn_toLp

/-- Finitely supported coefficients of smooth box energy fields. -/
abbrev SmoothBoxCombination := SmoothBoxEnergyField I →₀ ℝ

def boxSmoothGraphCombination :
    SmoothBoxCombination I →ₗ[ℝ] BoxEnergyAmbient I :=
  Finsupp.linearCombination ℝ (fun u : SmoothBoxEnergyField I => u.graphPoint)

def boxSmoothVelocityL4Combination :
    SmoothBoxCombination I →ₗ[ℝ] BoxVelocityL4 I :=
  Finsupp.linearCombination ℝ (fun u : SmoothBoxEnergyField I => u.velocityLp4 I)

theorem boxVelocityL4ToL2_velocityLp4
    (u : SmoothBoxEnergyField I) :
    boxVelocityL4ToL2 I (u.velocityLp4 I) = u.velocityLp := by
  apply Lp.ext
  filter_upwards [u.coeFn_velocityLp4 I,
    u.velocity_memLp.coeFn_toLp] with x h4 h2
  change u.velocityLp4 I x = u.velocityLp x
  exact h4.trans h2.symm

theorem boxVelocityL4ToL2_boxSmoothVelocityL4Combination
    (c : SmoothBoxCombination I) :
    boxVelocityL4ToL2 I (boxSmoothVelocityL4Combination I c) =
      boxEnergyVelocityProjection I (boxSmoothGraphCombination I c) := by
  calc
    boxVelocityL4ToL2 I (boxSmoothVelocityL4Combination I c) =
        Finsupp.linearCombination ℝ
          ((boxVelocityL4ToL2 I).toLinearMap ∘
            fun u : SmoothBoxEnergyField I => u.velocityLp4 I) c :=
      Finsupp.apply_linearCombination
        ℝ (boxVelocityL4ToL2 I).toLinearMap _ c
    _ = Finsupp.linearCombination ℝ
          ((boxEnergyVelocityProjection I).toLinearMap ∘
            fun u : SmoothBoxEnergyField I => u.graphPoint) c := by
      apply congrArg (fun v => Finsupp.linearCombination ℝ v c)
      funext u
      change boxVelocityL4ToL2 I (u.velocityLp4 I) =
        boxEnergyVelocityProjection I u.graphPoint
      rw [boxVelocityL4ToL2_velocityLp4 I,
        boxEnergyVelocityProjection_graphPoint]
    _ = boxEnergyVelocityProjection I (boxSmoothGraphCombination I c) :=
      (Finsupp.apply_linearCombination
        ℝ (boxEnergyVelocityProjection I).toLinearMap _ c).symm

theorem boxSmoothGraphCombination_range :
    LinearMap.range (boxSmoothGraphCombination I) = smoothBoxGraphCore I := by
  rw [boxSmoothGraphCombination, Finsupp.range_linearCombination]
  rfl

theorem boxSmoothGraphCombination_ker_le_velocityL4_ker :
    LinearMap.ker (boxSmoothGraphCombination I) ≤
      LinearMap.ker (boxSmoothVelocityL4Combination I) := by
  intro c hc
  rw [LinearMap.mem_ker] at hc ⊢
  apply lpFourToTwo_injective (BoxMeasure I)
  change boxVelocityL4ToL2 I (boxSmoothVelocityL4Combination I c) =
    boxVelocityL4ToL2 I 0
  rw [map_zero,
    boxVelocityL4ToL2_boxSmoothVelocityL4Combination I, hc, map_zero]

def boxSmoothGraphCombinationToCore :
    SmoothBoxCombination I →ₗ[ℝ] smoothBoxGraphCore I :=
  (boxSmoothGraphCombination I).codRestrict (smoothBoxGraphCore I) fun c => by
    rw [← boxSmoothGraphCombination_range I]
    exact LinearMap.mem_range_self (boxSmoothGraphCombination I) c

theorem boxSmoothGraphCombinationToCore_surjective :
    Function.Surjective (boxSmoothGraphCombinationToCore I) := by
  intro u
  have hu : (u : BoxEnergyAmbient I) ∈
      LinearMap.range (boxSmoothGraphCombination I) := by
    rw [boxSmoothGraphCombination_range I]
    exact u.property
  rcases hu with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  apply Subtype.ext
  exact hc

noncomputable def boxSmoothGraphCoreSection :
    smoothBoxGraphCore I →ₗ[ℝ] SmoothBoxCombination I :=
  Classical.choose
    ((boxSmoothGraphCombinationToCore I).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.2
        (boxSmoothGraphCombinationToCore_surjective I)))

@[simp]
theorem boxSmoothGraphCombinationToCore_section
    (u : smoothBoxGraphCore I) :
    boxSmoothGraphCombinationToCore I (boxSmoothGraphCoreSection I u) = u := by
  have h := Classical.choose_spec
    ((boxSmoothGraphCombinationToCore I).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.2
        (boxSmoothGraphCombinationToCore_surjective I)))
  exact LinearMap.congr_fun h u

def boxSmoothGraphCoreVelocityLp4Linear :
    smoothBoxGraphCore I →ₗ[ℝ] BoxVelocityL4 I :=
  (boxSmoothVelocityL4Combination I).comp (boxSmoothGraphCoreSection I)

theorem boxVelocityL4ToL2_boxSmoothGraphCoreVelocityLp4Linear
    (u : smoothBoxGraphCore I) :
    boxVelocityL4ToL2 I (boxSmoothGraphCoreVelocityLp4Linear I u) =
      boxEnergyVelocityProjection I (u : BoxEnergyAmbient I) := by
  calc
    boxVelocityL4ToL2 I (boxSmoothGraphCoreVelocityLp4Linear I u) =
        boxEnergyVelocityProjection I
          (boxSmoothGraphCombination I (boxSmoothGraphCoreSection I u)) :=
      boxVelocityL4ToL2_boxSmoothVelocityL4Combination I _
    _ = boxEnergyVelocityProjection I (u : BoxEnergyAmbient I) := by
      have h := congrArg Subtype.val
        (boxSmoothGraphCombinationToCore_section I u)
      exact congrArg (boxEnergyVelocityProjection I) h

/-- A uniform Ladyzhenskaya inequality for finite combinations of smooth box
energy fields. -/
structure BoxSmoothLadyzhenskayaEstimate where
  constant : ℝ
  constant_nonneg : 0 ≤ constant
  bound : ∀ c : SmoothBoxCombination I,
    ‖boxSmoothVelocityL4Combination I c‖ ^ 2 ≤
      constant *
        ‖boxEnergyVelocityProjection I (boxSmoothGraphCombination I c)‖ *
        ‖boxEnergyGradientProjection I (boxSmoothGraphCombination I c)‖

namespace BoxSmoothLadyzhenskayaEstimate

variable (E : BoxSmoothLadyzhenskayaEstimate I)

theorem coreVelocityLp4_sq_le (u : smoothBoxGraphCore I) :
    ‖boxSmoothGraphCoreVelocityLp4Linear I u‖ ^ 2 ≤
      E.constant * ‖boxEnergyToState I (boxSmoothGraphCoreInclusion I u)‖ *
        ‖boxEnergyGradient I (boxSmoothGraphCoreInclusion I u)‖ := by
  let c := boxSmoothGraphCoreSection I u
  have hgraph := congrArg Subtype.val
    (boxSmoothGraphCombinationToCore_section I u)
  have hgraph' : boxSmoothGraphCombination I c = (u : BoxEnergyAmbient I) := by
    exact hgraph
  change ‖boxSmoothVelocityL4Combination I c‖ ^ 2 ≤
    E.constant * ‖boxEnergyVelocityProjection I (u : BoxEnergyAmbient I)‖ *
      ‖boxEnergyGradientProjection I (u : BoxEnergyAmbient I)‖
  calc
    ‖boxSmoothVelocityL4Combination I c‖ ^ 2 ≤
        E.constant *
          ‖boxEnergyVelocityProjection I (boxSmoothGraphCombination I c)‖ *
          ‖boxEnergyGradientProjection I (boxSmoothGraphCombination I c)‖ :=
      E.bound c
    _ = E.constant * ‖boxEnergyVelocityProjection I (u : BoxEnergyAmbient I)‖ *
          ‖boxEnergyGradientProjection I (u : BoxEnergyAmbient I)‖ := by
      rw [hgraph']

theorem norm_coreVelocityLp4Linear_le (u : smoothBoxGraphCore I) :
    ‖boxSmoothGraphCoreVelocityLp4Linear I u‖ ≤
      Real.sqrt E.constant * ‖u‖ := by
  have hstate :
      ‖boxEnergyToState I (boxSmoothGraphCoreInclusion I u)‖ ≤ ‖u‖ := by
    exact (norm_boxEnergyToState_le I (boxSmoothGraphCoreInclusion I u)).trans_eq rfl
  have hgrad :
      ‖boxEnergyGradient I (boxSmoothGraphCoreInclusion I u)‖ ≤ ‖u‖ := by
    exact (norm_boxEnergyGradient_le I (boxSmoothGraphCoreInclusion I u)).trans_eq rfl
  have hsquare :
      ‖boxSmoothGraphCoreVelocityLp4Linear I u‖ ^ 2 ≤
        (Real.sqrt E.constant * ‖u‖) ^ 2 := by
    calc
      ‖boxSmoothGraphCoreVelocityLp4Linear I u‖ ^ 2 ≤
          E.constant * ‖boxEnergyToState I (boxSmoothGraphCoreInclusion I u)‖ *
            ‖boxEnergyGradient I (boxSmoothGraphCoreInclusion I u)‖ :=
        E.coreVelocityLp4_sq_le I u
      _ ≤ E.constant * ‖u‖ * ‖u‖ := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hstate E.constant_nonneg) hgrad
          (norm_nonneg _)
          (mul_nonneg E.constant_nonneg (norm_nonneg _))
      _ = (Real.sqrt E.constant * ‖u‖) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt E.constant_nonneg]
        ring
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp hsquare

noncomputable def coreVelocityLp4 :
    smoothBoxGraphCore I →L[ℝ] BoxVelocityL4 I :=
  LinearMap.mkContinuous (boxSmoothGraphCoreVelocityLp4Linear I)
    (Real.sqrt E.constant) (E.norm_coreVelocityLp4Linear_le I)

theorem coreVelocityLp4_compatible (u : smoothBoxGraphCore I) :
    boxVelocityL4ToL2 I (E.coreVelocityLp4 I u) =
      boxStateAmbientInclusion I
        (boxEnergyToState I (boxSmoothGraphCoreInclusion I u)) := by
  change boxVelocityL4ToL2 I (boxSmoothGraphCoreVelocityLp4Linear I u) =
    boxEnergyVelocityProjection I (u : BoxEnergyAmbient I)
  exact boxVelocityL4ToL2_boxSmoothGraphCoreVelocityLp4Linear I u

noncomputable def toBoxCoreLadyzhenskayaRealization :
    BoxCoreLadyzhenskayaRealization I where
  toLp4 := E.coreVelocityLp4 I
  compatible := E.coreVelocityLp4_compatible I
  constant := E.constant
  constant_nonneg := E.constant_nonneg
  l4_sq_le := E.coreVelocityLp4_sq_le I

/-- Closed Ladyzhenskaya realization generated by the smooth finite-combination
estimate. -/
noncomputable def toBoxLadyzhenskayaRealization :
    BoxLadyzhenskayaRealization I :=
  (E.toBoxCoreLadyzhenskayaRealization I).toBoxLadyzhenskayaRealization I

end BoxSmoothLadyzhenskayaEstimate

end
