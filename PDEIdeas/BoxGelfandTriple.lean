import PDEIdeas.BoxFourierRellich
import PDEIdeas.BoxWeakSobolev
import PDEIdeas.CompactGelfandTriple
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# The compact Gelfand triple on a rectangular box

The completed divergence-free velocity-gradient graph is the energy space,
its velocity closure is the pivot space, and the canonical graph projection
is the compact dense injection.
-/

open Function InnerProductSpace MeasureTheory
open scoped ENNReal RealInnerProductSpace

noncomputable section

variable {n : ℕ}

/-- Second countability of vector-valued velocity `L2` on a finite-dimensional
box. -/
@[reducible] noncomputable def boxVelocityL2_secondCountableTopology
    (I : BoxIntegral.Box (Fin (n + 1))) :
    SecondCountableTopology (BoxVelocityL2 I) := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.ofNat_ne_top⟩
  letI : IsSeparable (BoxMeasure I) := inferInstance
  letI : TopologicalSpace.SeparableSpace (BoxVelocityValue n) := inferInstance
  exact MeasureTheory.Lp.SecondCountableTopology

/-- Second countability of matrix-valued gradient `L2` on a
finite-dimensional box. -/
@[reducible] noncomputable def boxGradientL2_secondCountableTopology
    (I : BoxIntegral.Box (Fin (n + 1))) :
    SecondCountableTopology (BoxGradientL2 I) := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.ofNat_ne_top⟩
  letI : IsSeparable (BoxMeasure I) := inferInstance
  letI : TopologicalSpace.SeparableSpace (BoxGradientValue n) := inferInstance
  exact MeasureTheory.Lp.SecondCountableTopology

/-- Second countability of the velocity-gradient energy ambient space. -/
@[reducible] noncomputable def boxEnergyAmbient_secondCountableTopology
    (I : BoxIntegral.Box (Fin (n + 1))) :
    SecondCountableTopology (BoxEnergyAmbient I) := by
  letI : SecondCountableTopology (BoxVelocityL2 I) :=
    boxVelocityL2_secondCountableTopology I
  letI : SecondCountableTopology (BoxGradientL2 I) :=
    boxGradientL2_secondCountableTopology I
  infer_instance

/-- The completed box energy space is second-countable. -/
@[reducible] noncomputable def boxH1ZeroSigma_secondCountableTopology
    (I : BoxIntegral.Box (Fin (n + 1))) :
    SecondCountableTopology (BoxH1ZeroSigma I) := by
  letI : SecondCountableTopology (BoxEnergyAmbient I) :=
    boxEnergyAmbient_secondCountableTopology I
  infer_instance

/-- The completed box energy space is separable. -/
@[reducible] noncomputable def boxH1ZeroSigma_separableSpace
    (I : BoxIntegral.Box (Fin (n + 1))) :
    TopologicalSpace.SeparableSpace (BoxH1ZeroSigma I) := by
  letI : SecondCountableTopology (BoxH1ZeroSigma I) :=
    boxH1ZeroSigma_secondCountableTopology I
  infer_instance

/-- The completed box pivot space is second-countable. -/
@[reducible] noncomputable def boxL2Sigma_secondCountableTopology
    (I : BoxIntegral.Box (Fin (n + 1))) :
    SecondCountableTopology (BoxL2Sigma I) := by
  letI : SecondCountableTopology (BoxVelocityL2 I) :=
    boxVelocityL2_secondCountableTopology I
  infer_instance

/-- The completed box pivot space is separable. -/
@[reducible] noncomputable def boxL2Sigma_separableSpace
    (I : BoxIntegral.Box (Fin (n + 1))) :
    TopologicalSpace.SeparableSpace (BoxL2Sigma I) := by
  letI : SecondCountableTopology (BoxL2Sigma I) :=
    boxL2Sigma_secondCountableTopology I
  infer_instance

/-- The completed velocity graph is a complete Hilbert space. -/
instance boxH1ZeroSigma_completeSpace
    (I : BoxIntegral.Box (Fin (n + 1))) :
    CompleteSpace (BoxH1ZeroSigma I) :=
  Submodule.topologicalClosure.completeSpace (smoothBoxGraphCore I)

/-- The completed divergence-free velocity core is a complete Hilbert
space. -/
instance boxL2Sigma_completeSpace
    (I : BoxIntegral.Box (Fin (n + 1))) :
    CompleteSpace (BoxL2Sigma I) :=
  Submodule.topologicalClosure.completeSpace (smoothBoxVelocityCore I)

/-- The canonical compact Gelfand triple
`BoxH1ZeroSigma I -> BoxL2Sigma I -> (BoxH1ZeroSigma I)'`. -/
def boxGelfandTriple
    (I : BoxIntegral.Box (Fin (n + 1))) :
    CompactGelfandTriple (BoxH1ZeroSigma I) (BoxL2Sigma I) where
  embedding := boxEnergyToState I
  embedding_injective := boxEnergyToState_injective I
  embedding_denseRange := boxEnergyToState_denseRange I
  embedding_compact := boxEnergyToState_isCompactOperator_fourier I
  embedding_contractive := norm_boxEnergyToState_le I

@[simp]
theorem boxGelfandTriple_embedding
    (I : BoxIntegral.Box (Fin (n + 1))) :
    (boxGelfandTriple I).embedding = boxEnergyToState I :=
  rfl

@[simp]
theorem boxGelfandTriple_pivot
    (I : BoxIntegral.Box (Fin (n + 1))) :
    (boxGelfandTriple I).pivot = boxStateToEnergyDual I :=
  rfl

theorem boxStateToEnergyDual_injective
    (I : BoxIntegral.Box (Fin (n + 1))) :
    Function.Injective (boxStateToEnergyDual I) := by
  simpa only [← boxGelfandTriple_pivot] using
    (boxGelfandTriple I).pivot_injective

end
