import PDEIdeas.BoxSobolevClosure
import PDEIdeas.DenseTrilinearExtension
import PDEIdeas.EnergyConvectionForm

/-!
# Extension of box convection from the smooth graph core

The smooth graph core is dense in `BoxH1ZeroSigma`. A continuous trilinear
form on that core therefore has a unique continuous extension to the closed
energy space. Skew symmetry in the transported and test variables passes to
the extension, which supplies an `EnergyConvectionForm` for every spectral
Galerkin level.
-/

open Set

noncomputable section

variable {n : ℕ}

/-- Inclusion of the smooth graph core into its energy closure. -/
def boxSmoothGraphCoreInclusion
    (I : BoxIntegral.Box (Fin (n + 1))) :
    smoothBoxGraphCore I →L[ℝ] BoxH1ZeroSigma I :=
  (smoothBoxGraphCore I).subtypeL.codRestrict
    (smoothBoxGraphCore I).topologicalClosure fun u =>
      (smoothBoxGraphCore I).le_topologicalClosure u.property

@[simp]
theorem boxSmoothGraphCoreInclusion_apply
    (I : BoxIntegral.Box (Fin (n + 1)))
    (u : smoothBoxGraphCore I) :
    ((boxSmoothGraphCoreInclusion I u : BoxH1ZeroSigma I) : BoxEnergyAmbient I) = u :=
  rfl

theorem boxSmoothGraphCoreInclusion_isometry
    (I : BoxIntegral.Box (Fin (n + 1))) :
    Isometry (boxSmoothGraphCoreInclusion I) := by
  intro u v
  rfl

theorem boxSmoothGraphCoreInclusion_denseRange
    (I : BoxIntegral.Box (Fin (n + 1))) :
    DenseRange (boxSmoothGraphCoreInclusion I) := by
  change DenseRange (Set.inclusion
    ((smoothBoxGraphCore I).le_topologicalClosure :
      (smoothBoxGraphCore I : Set (BoxEnergyAmbient I)) ⊆
        ((smoothBoxGraphCore I).topologicalClosure : Set (BoxEnergyAmbient I))))
  apply (denseRange_inclusion_iff _).2
  simpa only [Submodule.topologicalClosure_coe] using
    (Set.Subset.rfl :
      closure (smoothBoxGraphCore I : Set (BoxEnergyAmbient I)) ⊆
        closure (smoothBoxGraphCore I : Set (BoxEnergyAmbient I)))

theorem boxSmoothGraphCoreInclusion_isUniformInducing
    (I : BoxIntegral.Box (Fin (n + 1))) :
    IsUniformInducing (boxSmoothGraphCoreInclusion I) :=
  (boxSmoothGraphCoreInclusion_isometry I).isUniformInducing

/-- Continuous extension of a graph-core trilinear form to the closed box
energy space. -/
def boxCoreConvectionExtension
    (I : BoxIntegral.Box (Fin (n + 1)))
    (B : smoothBoxGraphCore I →L[ℝ]
      smoothBoxGraphCore I →L[ℝ] smoothBoxGraphCore I →L[ℝ] ℝ) :
    BoxH1ZeroSigma I →L[ℝ]
      BoxH1ZeroSigma I →L[ℝ] BoxH1ZeroSigma I →L[ℝ] ℝ :=
  B.trilinearExtend (boxSmoothGraphCoreInclusion I)

@[simp]
theorem boxCoreConvectionExtension_apply_core
    (I : BoxIntegral.Box (Fin (n + 1)))
    (B : smoothBoxGraphCore I →L[ℝ]
      smoothBoxGraphCore I →L[ℝ] smoothBoxGraphCore I →L[ℝ] ℝ)
    (u v w : smoothBoxGraphCore I) :
    boxCoreConvectionExtension I B
      (boxSmoothGraphCoreInclusion I u)
      (boxSmoothGraphCoreInclusion I v)
      (boxSmoothGraphCoreInclusion I w) = B u v w := by
  exact ContinuousLinearMap.trilinearExtend_apply B
    (boxSmoothGraphCoreInclusion I)
    (boxSmoothGraphCoreInclusion_denseRange I)
    (boxSmoothGraphCoreInclusion_isUniformInducing I) u v w

theorem boxCoreConvectionExtension_skew
    (I : BoxIntegral.Box (Fin (n + 1)))
    (B : smoothBoxGraphCore I →L[ℝ]
      smoothBoxGraphCore I →L[ℝ] smoothBoxGraphCore I →L[ℝ] ℝ)
    (hskew : ∀ u v w, B u v w = -B u w v) :
    ∀ u v w, boxCoreConvectionExtension I B u v w =
      -boxCoreConvectionExtension I B u w v :=
  ContinuousLinearMap.trilinearExtend_skew B
    (boxSmoothGraphCoreInclusion I)
    (boxSmoothGraphCoreInclusion_denseRange I)
    (boxSmoothGraphCoreInclusion_isUniformInducing I) hskew

theorem boxCoreConvectionExtension_unique
    (I : BoxIntegral.Box (Fin (n + 1)))
    (B : smoothBoxGraphCore I →L[ℝ]
      smoothBoxGraphCore I →L[ℝ] smoothBoxGraphCore I →L[ℝ] ℝ)
    (C : BoxH1ZeroSigma I →L[ℝ]
      BoxH1ZeroSigma I →L[ℝ] BoxH1ZeroSigma I →L[ℝ] ℝ)
    (hC : ∀ u v w, C
      (boxSmoothGraphCoreInclusion I u)
      (boxSmoothGraphCoreInclusion I v)
      (boxSmoothGraphCoreInclusion I w) = B u v w) :
    boxCoreConvectionExtension I B = C :=
  ContinuousLinearMap.trilinearExtend_unique B
    (boxSmoothGraphCoreInclusion I)
    (boxSmoothGraphCoreInclusion_denseRange I)
    (boxSmoothGraphCoreInclusion_isUniformInducing I) C hC

/-- The unique skew extension of a graph-core convection form, packaged with
its continuity constant for the energy method. -/
noncomputable def boxCoreEnergyConvectionForm
    (I : BoxIntegral.Box (Fin (n + 1)))
    (B : smoothBoxGraphCore I →L[ℝ]
      smoothBoxGraphCore I →L[ℝ] smoothBoxGraphCore I →L[ℝ] ℝ)
    (hskew : ∀ u v w, B u v w = -B u w v) :
    EnergyConvectionForm (BoxH1ZeroSigma I) :=
  EnergyConvectionForm.ofContinuousSkew
    (boxCoreConvectionExtension I B)
    (boxCoreConvectionExtension_skew I B hskew)

@[simp]
theorem boxCoreEnergyConvectionForm_form
    (I : BoxIntegral.Box (Fin (n + 1)))
    (B : smoothBoxGraphCore I →L[ℝ]
      smoothBoxGraphCore I →L[ℝ] smoothBoxGraphCore I →L[ℝ] ℝ)
    (hskew : ∀ u v w, B u v w = -B u w v) :
    (boxCoreEnergyConvectionForm I B hskew).form =
      boxCoreConvectionExtension I B :=
  rfl

end
