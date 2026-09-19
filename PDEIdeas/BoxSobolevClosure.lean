import PDEIdeas.BoundaryConditions
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Algebra.Module.LinearMap

open MeasureTheory Real InnerProductSpace Set
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

variable {n : ℕ}

/-- Euclidean velocity values in dimension `n + 1`. -/
abbrev BoxVelocityValue (n : ℕ) := EuclideanSpace ℝ (Fin (n + 1))

/-- Euclidean matrix values for the full spatial derivative. -/
abbrev BoxGradientValue (n : ℕ) :=
  EuclideanSpace ℝ (Fin (n + 1) × Fin (n + 1))

/-- Lebesgue measure restricted to a closed rectangular box. -/
abbrev BoxMeasure (I : BoxIntegral.Box (Fin (n + 1))) :=
  volume.restrict (BoxIntegral.Box.Icc I)

/-- The ambient vector-valued `L²` space on a box. -/
abbrev BoxVelocityL2 (I : BoxIntegral.Box (Fin (n + 1))) :=
  Lp (BoxVelocityValue n) (2 : ℝ≥0∞) (BoxMeasure I)

/-- The ambient matrix-valued `L²` space on a box. -/
abbrev BoxGradientL2 (I : BoxIntegral.Box (Fin (n + 1))) :=
  Lp (BoxGradientValue n) (2 : ℝ≥0∞) (BoxMeasure I)

/-- Product `L²` space carrying a velocity and its full derivative. -/
abbrev BoxEnergyAmbient (I : BoxIntegral.Box (Fin (n + 1))) :=
  WithLp 2 (BoxVelocityL2 I × BoxGradientL2 I)

/-- Coordinate realization of a vector field as a Euclidean-valued function. -/
def boxVelocityValue
    (u : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (x : Fin (n + 1) → ℝ) : BoxVelocityValue n :=
  WithLp.toLp 2 (u x)

/-- Coordinate realization of a Fréchet derivative as a Euclidean matrix.
The entry `(i,j)` is the `i`th component of the derivative in direction
`e_j`. -/
def boxGradientValue
    (u' : (Fin (n + 1) → ℝ) →
      (Fin (n + 1) → ℝ) →L[ℝ] Fin (n + 1) → ℝ)
    (x : Fin (n + 1) → ℝ) : BoxGradientValue n :=
  WithLp.toLp 2 fun ij => u' x (Pi.single ij.2 1) ij.1

/-- Compactly supported `C¹`, divergence-free box fields with square-integrable
velocity and derivative. The support condition makes this the standard smooth
core for the zero-trace energy space. -/
structure SmoothBoxEnergyField
    (I : BoxIntegral.Box (Fin (n + 1))) where
  field : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ
  derivative : (Fin (n + 1) → ℝ) →
    (Fin (n + 1) → ℝ) →L[ℝ] Fin (n + 1) → ℝ
  contDiff_field : ContDiff ℝ 1 field
  support_field : Function.support field ⊆ BoxIntegral.Box.Icc I
  hasFDerivAt_field :
    ∀ x ∈ interior (BoxIntegral.Box.Icc I),
      HasFDerivAt field (derivative x) x
  continuousOn_field : ContinuousOn field (BoxIntegral.Box.Icc I)
  zeroDirichlet_field : ZeroDirichletVectorOnBox I field
  divergence_field :
    ∀ x ∈ BoxIntegral.Box.Icc I,
      ∑ i : Fin (n + 1), derivative x (Pi.single i 1) i = 0
  velocity_memLp :
    MemLp (boxVelocityValue field) 2 (BoxMeasure I)
  gradient_memLp :
    MemLp (boxGradientValue derivative) 2 (BoxMeasure I)

namespace SmoothBoxEnergyField

/-- The velocity represented in the ambient vector-valued `L²` space. -/
def velocityLp
    {I : BoxIntegral.Box (Fin (n + 1))}
    (u : SmoothBoxEnergyField I) : BoxVelocityL2 I :=
  u.velocity_memLp.toLp (boxVelocityValue u.field)

/-- The derivative represented in the ambient matrix-valued `L²` space. -/
def gradientLp
    {I : BoxIntegral.Box (Fin (n + 1))}
    (u : SmoothBoxEnergyField I) : BoxGradientL2 I :=
  u.gradient_memLp.toLp (boxGradientValue u.derivative)

/-- Graph point `(u, Du)` in the product `L²` space. -/
def graphPoint
    {I : BoxIntegral.Box (Fin (n + 1))}
    (u : SmoothBoxEnergyField I) : BoxEnergyAmbient I :=
  WithLp.toLp 2 (u.velocityLp, u.gradientLp)

end SmoothBoxEnergyField

/-- Graph points of smooth divergence-free zero-face fields. -/
def smoothBoxGraphSet (I : BoxIntegral.Box (Fin (n + 1))) :
    Set (BoxEnergyAmbient I) :=
  Set.range SmoothBoxEnergyField.graphPoint

/-- Velocity points of smooth divergence-free zero-face fields. -/
def smoothBoxVelocitySet (I : BoxIntegral.Box (Fin (n + 1))) :
    Set (BoxVelocityL2 I) :=
  Set.range SmoothBoxEnergyField.velocityLp

/-- Linear span of the smooth graph core. -/
def smoothBoxGraphCore (I : BoxIntegral.Box (Fin (n + 1))) :
    Submodule ℝ (BoxEnergyAmbient I) :=
  Submodule.span ℝ (smoothBoxGraphSet I)

/-- Linear span of the smooth velocity core. -/
def smoothBoxVelocityCore (I : BoxIntegral.Box (Fin (n + 1))) :
    Submodule ℝ (BoxVelocityL2 I) :=
  Submodule.span ℝ (smoothBoxVelocitySet I)

/-- `H¹_{0,σ}` closure model: closure of the smooth `(u, Du)` graph in the
product `L²` norm. -/
abbrev BoxH1ZeroSigma (I : BoxIntegral.Box (Fin (n + 1))) :=
  (smoothBoxGraphCore I).topologicalClosure

/-- `L²_σ` closure model: closure of smooth divergence-free zero-face
velocities in vector-valued `L²`. -/
abbrev BoxL2Sigma (I : BoxIntegral.Box (Fin (n + 1))) :=
  (smoothBoxVelocityCore I).topologicalClosure

/-- Projection of an energy graph point onto its velocity component. -/
def boxEnergyVelocityProjection
    (I : BoxIntegral.Box (Fin (n + 1))) :
    BoxEnergyAmbient I →L[ℝ] BoxVelocityL2 I :=
  WithLp.fstL 2 ℝ (BoxVelocityL2 I) (BoxGradientL2 I)

/-- Projection of an energy graph point onto its derivative component. -/
def boxEnergyGradientProjection
    (I : BoxIntegral.Box (Fin (n + 1))) :
    BoxEnergyAmbient I →L[ℝ] BoxGradientL2 I :=
  WithLp.sndL 2 ℝ (BoxVelocityL2 I) (BoxGradientL2 I)

@[simp]
theorem boxEnergyVelocityProjection_graphPoint
    {I : BoxIntegral.Box (Fin (n + 1))}
    (u : SmoothBoxEnergyField I) :
    boxEnergyVelocityProjection I u.graphPoint = u.velocityLp := by
  rfl

@[simp]
theorem boxEnergyGradientProjection_graphPoint
    {I : BoxIntegral.Box (Fin (n + 1))}
    (u : SmoothBoxEnergyField I) :
    boxEnergyGradientProjection I u.graphPoint = u.gradientLp := by
  rfl

theorem image_smoothBoxGraphSet_velocity
    (I : BoxIntegral.Box (Fin (n + 1))) :
    boxEnergyVelocityProjection I '' smoothBoxGraphSet I =
      smoothBoxVelocitySet I := by
  ext v
  constructor
  · rintro ⟨x, ⟨u, rfl⟩, rfl⟩
    exact ⟨u, by simp⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u.graphPoint, ⟨u, rfl⟩, by simp⟩

theorem smoothBoxGraphCore_map_velocity
    (I : BoxIntegral.Box (Fin (n + 1))) :
    (smoothBoxGraphCore I).map
        (boxEnergyVelocityProjection I).toLinearMap =
      smoothBoxVelocityCore I := by
  rw [smoothBoxGraphCore, smoothBoxVelocityCore, Submodule.map_span]
  congr 1
  simpa only [ContinuousLinearMap.coe_coe] using
    image_smoothBoxGraphSet_velocity I

/-- Canonical continuous map from the graph closure to the velocity closure. -/
def boxEnergyToState
    (I : BoxIntegral.Box (Fin (n + 1))) :
    BoxH1ZeroSigma I →L[ℝ] BoxL2Sigma I :=
  ((boxEnergyVelocityProjection I).comp
      (smoothBoxGraphCore I).topologicalClosure.subtypeL).codRestrict
    (smoothBoxVelocityCore I).topologicalClosure fun u => by
      have huMap :
          boxEnergyVelocityProjection I (u : BoxEnergyAmbient I) ∈
            (smoothBoxGraphCore I).topologicalClosure.map
              (boxEnergyVelocityProjection I).toLinearMap :=
        ⟨u, u.property, rfl⟩
      have huClosure :=
        (smoothBoxGraphCore I).topologicalClosure_map
          (boxEnergyVelocityProjection I) huMap
      simpa [smoothBoxGraphCore_map_velocity] using huClosure

/-- Canonical derivative component of an element of the graph closure. -/
def boxEnergyGradient
    (I : BoxIntegral.Box (Fin (n + 1))) :
    BoxH1ZeroSigma I →L[ℝ] BoxGradientL2 I :=
  (boxEnergyGradientProjection I).comp
    (smoothBoxGraphCore I).topologicalClosure.subtypeL

theorem norm_boxEnergyToState_le
    (I : BoxIntegral.Box (Fin (n + 1)))
    (u : BoxH1ZeroSigma I) :
    ‖boxEnergyToState I u‖ ≤ ‖u‖ := by
  exact WithLp.norm_fst_le (x := (u : BoxEnergyAmbient I))

/-- The canonical energy-to-state map has dense range because its range
contains the smooth velocity core whose closure defines the state space. -/
theorem boxEnergyToState_denseRange
    (I : BoxIntegral.Box (Fin (n + 1))) :
    DenseRange (boxEnergyToState I) := by
  have hcore :
      DenseRange
        (Set.inclusion
          ((smoothBoxVelocityCore I).le_topologicalClosure)) := by
    apply (denseRange_inclusion_iff _).2
    simpa only [Submodule.topologicalClosure_coe] using
      (Set.Subset.rfl :
        closure (smoothBoxVelocityCore I : Set (BoxVelocityL2 I)) ⊆
          closure (smoothBoxVelocityCore I : Set (BoxVelocityL2 I)))
  apply hcore.mono
  rintro _ ⟨u, rfl⟩
  have huMap :
      (u : BoxVelocityL2 I) ∈
        (smoothBoxGraphCore I).map
          (boxEnergyVelocityProjection I).toLinearMap := by
    rw [smoothBoxGraphCore_map_velocity]
    exact u.property
  rcases huMap with ⟨v, hv, hvu⟩
  refine ⟨⟨v, (smoothBoxGraphCore I).le_topologicalClosure hv⟩, ?_⟩
  apply Subtype.ext
  exact hvu

theorem norm_boxEnergyGradient_le
    (I : BoxIntegral.Box (Fin (n + 1)))
    (u : BoxH1ZeroSigma I) :
    ‖boxEnergyGradient I u‖ ≤ ‖u‖ := by
  exact WithLp.norm_snd_le (x := (u : BoxEnergyAmbient I))

/-- A smooth core field as an element of the `H¹_{0,σ}` closure. -/
def SmoothBoxEnergyField.toEnergy
    {I : BoxIntegral.Box (Fin (n + 1))}
    (u : SmoothBoxEnergyField I) : BoxH1ZeroSigma I :=
  ⟨u.graphPoint,
    (smoothBoxGraphCore I).le_topologicalClosure
      (Submodule.subset_span ⟨u, rfl⟩)⟩

/-- A smooth core field as an element of the `L²_σ` closure. -/
def SmoothBoxEnergyField.toState
    {I : BoxIntegral.Box (Fin (n + 1))}
    (u : SmoothBoxEnergyField I) : BoxL2Sigma I :=
  ⟨u.velocityLp,
    (smoothBoxVelocityCore I).le_topologicalClosure
      (Submodule.subset_span ⟨u, rfl⟩)⟩

@[simp]
theorem boxEnergyToState_toEnergy
    {I : BoxIntegral.Box (Fin (n + 1))}
    (u : SmoothBoxEnergyField I) :
    boxEnergyToState I u.toEnergy = u.toState := by
  rfl

@[simp]
theorem boxEnergyGradient_toEnergy
    {I : BoxIntegral.Box (Fin (n + 1))}
    (u : SmoothBoxEnergyField I) :
    boxEnergyGradient I u.toEnergy = u.gradientLp := by
  rfl

/-- Gradient-pairing diffusion form on the graph closure. -/
def boxGradientDiffusion
    (I : BoxIntegral.Box (Fin (n + 1))) :
    BoxH1ZeroSigma I →L[ℝ] BoxH1ZeroSigma I →L[ℝ] ℝ :=
  let D := boxEnergyGradient I
  ContinuousLinearMap.bilinearComp
    (isBoundedBilinearMap_inner (𝕜 := ℝ)).toContinuousLinearMap D D

@[simp]
theorem boxGradientDiffusion_apply
    (I : BoxIntegral.Box (Fin (n + 1)))
    (u v : BoxH1ZeroSigma I) :
    boxGradientDiffusion I u v =
      ⟪boxEnergyGradient I u, boxEnergyGradient I v⟫_ℝ := by
  rfl

theorem boxGradientDiffusion_nonneg
    (I : BoxIntegral.Box (Fin (n + 1)))
    (u : BoxH1ZeroSigma I) :
    0 ≤ boxGradientDiffusion I u u := by
  rw [boxGradientDiffusion_apply]
  exact real_inner_self_nonneg

theorem boxGradientDiffusion_self
    (I : BoxIntegral.Box (Fin (n + 1)))
    (u : BoxH1ZeroSigma I) :
    boxGradientDiffusion I u u = ‖boxEnergyGradient I u‖ ^ 2 := by
  rw [boxGradientDiffusion_apply, real_inner_self_eq_norm_sq]

theorem norm_boxGradientDiffusion_apply_le
    (I : BoxIntegral.Box (Fin (n + 1)))
    (u v : BoxH1ZeroSigma I) :
    ‖boxGradientDiffusion I u v‖ ≤ ‖u‖ * ‖v‖ := by
  rw [boxGradientDiffusion_apply, Real.norm_eq_abs]
  calc
    |⟪boxEnergyGradient I u, boxEnergyGradient I v⟫_ℝ| ≤
        ‖boxEnergyGradient I u‖ * ‖boxEnergyGradient I v‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ ‖u‖ * ‖v‖ :=
      mul_le_mul (norm_boxEnergyGradient_le I u)
        (norm_boxEnergyGradient_le I v) (norm_nonneg _) (norm_nonneg _)

/-- Pivot map `H → V'` induced by the `L²` pairing and the canonical
`V → H` map. -/
def boxStateToEnergyDual
    (I : BoxIntegral.Box (Fin (n + 1))) :
    BoxL2Sigma I →L[ℝ] BoxH1ZeroSigma I →L[ℝ] ℝ :=
  ContinuousLinearMap.bilinearComp
    (isBoundedBilinearMap_inner (𝕜 := ℝ)).toContinuousLinearMap
    (ContinuousLinearMap.id ℝ (BoxL2Sigma I)) (boxEnergyToState I)

@[simp]
theorem boxStateToEnergyDual_apply
    (I : BoxIntegral.Box (Fin (n + 1)))
    (u : BoxL2Sigma I) (v : BoxH1ZeroSigma I) :
    boxStateToEnergyDual I u v = ⟪u, boxEnergyToState I v⟫_ℝ := by
  rfl

theorem norm_boxStateToEnergyDual_apply_le
    (I : BoxIntegral.Box (Fin (n + 1)))
    (u : BoxL2Sigma I) (v : BoxH1ZeroSigma I) :
    ‖boxStateToEnergyDual I u v‖ ≤ ‖u‖ * ‖v‖ := by
  rw [boxStateToEnergyDual_apply, Real.norm_eq_abs]
  calc
    |⟪u, boxEnergyToState I v⟫_ℝ| ≤
        ‖u‖ * ‖boxEnergyToState I v‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ ‖u‖ * ‖v‖ :=
      mul_le_mul_of_nonneg_left (norm_boxEnergyToState_le I v) (norm_nonneg _)

end
