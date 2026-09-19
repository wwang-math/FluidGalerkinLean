import PDEIdeas.BoxLadyzhenskayaInequality
import PDEIdeas.BoxSpectralVariationalGalerkin

/-!
# Unconditional two-dimensional spectral Ladyzhenskaya problems

The proved box Ladyzhenskaya inequality supplies the convection realization
used by every level of the canonical spectral tower.  The resulting wrappers
contain no Sobolev or core-convection hypothesis.
-/

open InnerProductSpace MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace BoxCompactSpectralRepresentation

section PlaneLevel

variable {I : BoxIntegral.Box (Fin 2)}
variable (S : BoxCompactSpectralRepresentation I) (m : ℕ)

local instance planeCoeffNormedAddCommGroup :
    NormedAddCommGroup (S.CoefficientSpace m) :=
  S.coefficientSpaceNormedAddCommGroup m

local instance planeCoeffInnerProductSpace :
    InnerProductSpace ℝ (S.CoefficientSpace m) :=
  S.coefficientSpaceInnerProductSpace m

local instance planeCoeffFiniteDimensional :
    FiniteDimensional ℝ (S.CoefficientSpace m) :=
  S.coefficientSpaceFiniteDimensional m

local instance planeCoeffCompleteSpace : CompleteSpace (S.CoefficientSpace m) :=
  S.coefficientSpaceCompleteSpace m

/-- The canonical two-dimensional box variational problem on spectral level
`m`. -/
noncomputable def variationalProblem2D
    (forcing : ℝ → BoxH1ZeroSigma I →L[ℝ] ℝ)
    (initial : S.CoefficientSpace m) :
    VariationalGalerkinProblem (S.CoefficientSpace m) :=
  S.variationalProblemOfLadyzhenskaya m (boxLadyzhenskayaRealization I)
    forcing initial

/-- Squared common-dual estimate for the canonical two-dimensional problem. -/
theorem dualRHS_twoDimensional_norm_sq_le
    (forcing : ℝ → BoxH1ZeroSigma I →L[ℝ] ℝ)
    (initial : S.CoefficientSpace m)
    (t : ℝ) (u : S.CoefficientSpace m)
    (f H : ℝ) (hf : 0 ≤ f) (hH : 0 ≤ H)
    (hforcing : ∀ φ, ‖forcing t φ‖ ≤ f * ‖φ‖)
    (hstate : ‖boxEnergyToState I (S.energySynthesis m u)‖ ≤ H) :
    ‖(S.variationalProblem2D m forcing initial).dualRHS
        (S.testProjection m) t u‖ ^ 2 ≤
      2 * (1 + (boxLpConvectionBound I *
        (boxLadyzhenskayaRealization I).constant) * H) ^ 2 *
          ‖S.energySynthesis m u‖ ^ 2 + 2 * f ^ 2 := by
  exact S.dualRHS_ladyzhenskaya_norm_sq_le m
    (boxLadyzhenskayaRealization I) forcing initial t u f H hf hH
    hforcing hstate

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- Standard energy and measurable-forcing data give a uniform common-dual
`L2` estimate for the canonical two-dimensional spectral problem. -/
theorem twoDimensional_dual_memLp_and_integral_le
    {a b : ℝ} (hab : a ≤ b)
    (forcing : ℝ → BoxH1ZeroSigma I →L[ℝ] ℝ)
    (initial : S.CoefficientSpace m)
    (U : ℝ → S.CoefficientSpace m)
    (f : ℝ → ℝ) (H R F : ℝ)
    (hH : 0 ≤ H)
    (hf_nonneg : ∀ t ∈ Icc a b, 0 ≤ f t)
    (hforcing : ∀ t ∈ Icc a b, ∀ φ, ‖forcing t φ‖ ≤ f t * ‖φ‖)
    (hforcing_meas : AEStronglyMeasurable forcing
      (volume.restrict (Icc a b)))
    (hstate : ∀ t ∈ Icc a b,
      ‖boxEnergyToState I (S.energySynthesis m (U t))‖ ≤ H)
    (henergy : MemLp
      (fun t => S.energySynthesis m (U t)) 2
      (volume.restrict (Icc a b)))
    (henergy_sq :
      ∫ t in a..b, ‖S.energySynthesis m (U t)‖ ^ 2 ≤ R ^ 2)
    (hforce : MemLp f 2 (volume.restrict (Icc a b)))
    (hforce_sq : ∫ t in a..b, ‖f t‖ ^ 2 ≤ F ^ 2) :
    MemLp
        (fun t => (S.variationalProblem2D m forcing initial).dualRHS
          (S.testProjection m) t (U t))
        2 (volume.restrict (Icc a b)) ∧
      ∫ t in a..b,
          ‖(S.variationalProblem2D m forcing initial).dualRHS
            (S.testProjection m) t (U t)‖ ^ 2 ≤
        2 * (1 + (boxLpConvectionBound I *
          (boxLadyzhenskayaRealization I).constant) * H) ^ 2 * R ^ 2 +
          2 * F ^ 2 := by
  exact S.ladyzhenskaya_dual_memLp_and_integral_le_of_forcing_measurable
    m hab (boxLadyzhenskayaRealization I) forcing initial U f H R F hH
    hf_nonneg hforcing hforcing_meas hstate henergy henergy_sq hforce
    hforce_sq

end PlaneLevel

end BoxCompactSpectralRepresentation

end
