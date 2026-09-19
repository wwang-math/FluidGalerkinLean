import PDEIdeas.BoxWeakSobolev

/-!
# Reduction of box compactness to the full zero-trace Rellich map

The divergence-free graph closure is a closed subspace of the graph closure
of all smooth zero-face fields. Compactness of the velocity projection on the
larger graph therefore restricts to compactness of the canonical
energy-to-state map.
-/

open MeasureTheory Real InnerProductSpace Set
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

variable {n : ℕ}

/-- Smooth zero-face fields with square-integrable velocity and full
derivative, without an incompressibility constraint. -/
structure SmoothBoxH1ZeroField
    (I : BoxIntegral.Box (Fin (n + 1))) where
  field : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ
  derivative : (Fin (n + 1) → ℝ) →
    (Fin (n + 1) → ℝ) →L[ℝ] Fin (n + 1) → ℝ
  hasFDerivAt_field :
    ∀ x ∈ interior (BoxIntegral.Box.Icc I),
      HasFDerivAt field (derivative x) x
  continuousOn_field : ContinuousOn field (BoxIntegral.Box.Icc I)
  zeroDirichlet_field : ZeroDirichletVectorOnBox I field
  velocity_memLp : MemLp (boxVelocityValue field) 2 (BoxMeasure I)
  gradient_memLp : MemLp (boxGradientValue derivative) 2 (BoxMeasure I)

namespace SmoothBoxH1ZeroField

def velocityLp
    {I : BoxIntegral.Box (Fin (n + 1))}
    (u : SmoothBoxH1ZeroField I) : BoxVelocityL2 I :=
  u.velocity_memLp.toLp (boxVelocityValue u.field)

def gradientLp
    {I : BoxIntegral.Box (Fin (n + 1))}
    (u : SmoothBoxH1ZeroField I) : BoxGradientL2 I :=
  u.gradient_memLp.toLp (boxGradientValue u.derivative)

def graphPoint
    {I : BoxIntegral.Box (Fin (n + 1))}
    (u : SmoothBoxH1ZeroField I) : BoxEnergyAmbient I :=
  WithLp.toLp 2 (u.velocityLp, u.gradientLp)

end SmoothBoxH1ZeroField

/-- Forget incompressibility while retaining all graph data. -/
def SmoothBoxEnergyField.toH1ZeroField
    {I : BoxIntegral.Box (Fin (n + 1))}
    (u : SmoothBoxEnergyField I) : SmoothBoxH1ZeroField I where
  field := u.field
  derivative := u.derivative
  hasFDerivAt_field := u.hasFDerivAt_field
  continuousOn_field := u.continuousOn_field
  zeroDirichlet_field := u.zeroDirichlet_field
  velocity_memLp := u.velocity_memLp
  gradient_memLp := u.gradient_memLp

@[simp]
theorem SmoothBoxEnergyField.toH1ZeroField_graphPoint
    {I : BoxIntegral.Box (Fin (n + 1))}
    (u : SmoothBoxEnergyField I) :
    u.toH1ZeroField.graphPoint = u.graphPoint :=
  rfl

def smoothBoxH1ZeroGraphSet
    (I : BoxIntegral.Box (Fin (n + 1))) :
    Set (BoxEnergyAmbient I) :=
  Set.range SmoothBoxH1ZeroField.graphPoint

def smoothBoxH1ZeroGraphCore
    (I : BoxIntegral.Box (Fin (n + 1))) :
    Submodule ℝ (BoxEnergyAmbient I) :=
  Submodule.span ℝ (smoothBoxH1ZeroGraphSet I)

/-- Full zero-trace H1 graph closure, before imposing incompressibility. -/
abbrev BoxH1ZeroFull
    (I : BoxIntegral.Box (Fin (n + 1))) :=
  (smoothBoxH1ZeroGraphCore I).topologicalClosure

theorem smoothBoxGraphSet_subset_smoothBoxH1ZeroGraphSet
    (I : BoxIntegral.Box (Fin (n + 1))) :
    smoothBoxGraphSet I ⊆ smoothBoxH1ZeroGraphSet I := by
  rintro _ ⟨u, rfl⟩
  exact ⟨u.toH1ZeroField, by simp⟩

theorem smoothBoxGraphCore_le_smoothBoxH1ZeroGraphCore
    (I : BoxIntegral.Box (Fin (n + 1))) :
    smoothBoxGraphCore I ≤ smoothBoxH1ZeroGraphCore I := by
  apply Submodule.span_mono
  exact smoothBoxGraphSet_subset_smoothBoxH1ZeroGraphSet I

theorem boxH1ZeroSigma_le_boxH1ZeroFull
    (I : BoxIntegral.Box (Fin (n + 1))) :
    (smoothBoxGraphCore I).topologicalClosure ≤
      (smoothBoxH1ZeroGraphCore I).topologicalClosure :=
  Submodule.topologicalClosure_mono
    (smoothBoxGraphCore_le_smoothBoxH1ZeroGraphCore I)

/-- Inclusion of the divergence-free graph closure into the full zero-trace
graph closure. -/
def boxSigmaEnergyToFull
    (I : BoxIntegral.Box (Fin (n + 1))) :
    BoxH1ZeroSigma I →L[ℝ] BoxH1ZeroFull I :=
  ((smoothBoxGraphCore I).topologicalClosure.subtypeL).codRestrict
    (smoothBoxH1ZeroGraphCore I).topologicalClosure fun u =>
      boxH1ZeroSigma_le_boxH1ZeroFull I u.property

/-- Velocity projection on the full zero-trace graph closure. -/
def boxFullEnergyToVelocity
    (I : BoxIntegral.Box (Fin (n + 1))) :
    BoxH1ZeroFull I →L[ℝ] BoxVelocityL2 I :=
  (boxEnergyVelocityProjection I).comp
    (smoothBoxH1ZeroGraphCore I).topologicalClosure.subtypeL

@[simp]
theorem boxFullEnergyToVelocity_sigmaEnergy
    (I : BoxIntegral.Box (Fin (n + 1)))
    (u : BoxH1ZeroSigma I) :
    boxFullEnergyToVelocity I (boxSigmaEnergyToFull I u) =
      (boxEnergyToState I u : BoxVelocityL2 I) :=
  rfl

/-- The scalar/vector zero-trace Rellich theorem on the full graph closure
implies compactness of the divergence-free canonical box map. -/
theorem boxEnergyToState_isCompactOperator_of_fullRellich
    (I : BoxIntegral.Box (Fin (n + 1)))
    (hRellich : IsCompactOperator (boxFullEnergyToVelocity I)) :
    IsCompactOperator (boxEnergyToState I) := by
  let T : BoxH1ZeroSigma I →L[ℝ] BoxVelocityL2 I :=
    (boxFullEnergyToVelocity I).comp (boxSigmaEnergyToFull I)
  have hT : IsCompactOperator T :=
    hRellich.comp_clm (boxSigmaEnergyToFull I)
  have hrange : ∀ u, T u ∈
      (smoothBoxVelocityCore I).topologicalClosure := by
    intro u
    simp [T]
  have hcod := hT.codRestrict hrange
    (isClosed_closure :
      IsClosed
        ((smoothBoxVelocityCore I).topologicalClosure :
          Set (BoxVelocityL2 I)))
  simpa [T, boxEnergyToState] using hcod

end
