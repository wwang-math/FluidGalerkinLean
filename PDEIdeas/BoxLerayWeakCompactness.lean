import PDEIdeas.BoxSpectralLadyzhenskayaCompactness
import PDEIdeas.LeraySpectralWeakContinuity
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Weak energy compactness for the two-dimensional box family

The completed box energy space and its finite-interval `L2` space are
separable.  The canonical unforced spectral family therefore has one strict
subsequence converging strongly in the pivot space and weakly in the energy
space, with both limits identified by the box embedding.
-/

open InnerProductSpace MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

noncomputable section

variable {I : BoxIntegral.Box (Fin 2)}

/-- The finite-interval energy-valued `L2` space is second-countable. -/
@[reducible] noncomputable def boxEnergyTimeLp_secondCountableTopology
    (I : BoxIntegral.Box (Fin 2)) (a b : ℝ) :
    SecondCountableTopology
      (Lp (BoxH1ZeroSigma I) (2 : ℝ≥0∞)
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)) := by
  let htop : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.ofNat_ne_top⟩
  let hE : TopologicalSpace.SeparableSpace (BoxH1ZeroSigma I) :=
    boxH1ZeroSigma_separableSpace I
  let hmu : IsSeparable
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) :=
    inferInstance
  exact @MeasureTheory.Lp.SecondCountableTopology
    (Icc a b) (BoxH1ZeroSigma I) inferInstance inferInstance
    (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)
    (2 : ℝ≥0∞) inferInstance htop hmu hE

/-- The finite-interval energy-valued `L2` space is separable. -/
@[reducible] noncomputable def boxEnergyTimeLp_separableSpace
    (I : BoxIntegral.Box (Fin 2)) (a b : ℝ) :
    TopologicalSpace.SeparableSpace
      (Lp (BoxH1ZeroSigma I) (2 : ℝ≥0∞)
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)) := by
  letI : SecondCountableTopology
      (Lp (BoxH1ZeroSigma I) (2 : ℝ≥0∞)
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)) :=
    boxEnergyTimeLp_secondCountableTopology I a b
  infer_instance

namespace BoxCompactSpectralRepresentation

variable (S : BoxCompactSpectralRepresentation I)

local instance boxWeakCompactnessL2Complete : CompleteSpace (BoxL2Sigma I) :=
  boxL2Sigma_completeSpace I

local instance boxWeakCompactnessH1Complete : CompleteSpace (BoxH1ZeroSigma I) :=
  boxH1ZeroSigma_completeSpace I

/-- The canonical unforced two-dimensional family has one strict subsequence
with simultaneous strong pivot convergence and weak energy convergence. -/
theorem exists_zeroForcing_twoDimensional_strongWeak_subsequence
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I) :
    Nonempty
      (S.zeroForcingLeraySpectralCompactFamily2D hab u₀).StrongWeakSubsequence := by
  letI : TopologicalSpace.SeparableSpace
      (Lp (BoxH1ZeroSigma I) (2 : ℝ≥0∞)
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)) :=
    boxEnergyTimeLp_separableSpace I a b
  exact @LeraySpectralCompactFamily.exists_strongWeakSubsequence
    (Icc a b) (BoxH1ZeroSigma I) (BoxL2Sigma I)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance (boxH1ZeroSigma_completeSpace I)
    inferInstance inferInstance (boxL2Sigma_completeSpace I)
    (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)
    inferInstance
    (S.zeroForcingLeraySpectralCompactFamily2D hab u₀)
    (boxEnergyTimeLp_separableSpace I a b)

/-- The canonical unforced family has one strict subsequence carrying strong
state convergence, weak energy convergence, and uniform convergence of every
finite projected path. -/
theorem exists_zeroForcing_twoDimensional_strongWeakPath_subsequence
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I) :
    Nonempty
      (S.zeroForcingLeraySpectralCompactFamily2D hab u₀).StrongWeakPathSubsequence := by
  obtain ⟨SW⟩ :=
    S.exists_zeroForcing_twoDimensional_strongWeak_subsequence hab u₀
  exact SW.exists_pathwiseRefinement

set_option maxHeartbeats 1000000 in
/-- The finite projectors of the canonical box compactness family are
self-adjoint in the pivot inner product. -/
theorem zeroForcing_projector_inner_eq
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I)
    (m : ℕ) (x y : BoxL2Sigma I) :
    ⟪(S.zeroForcingLeraySpectralCompactFamily2D hab u₀).projector m x, y⟫_ℝ =
      ⟪x,
        (S.zeroForcingLeraySpectralCompactFamily2D hab u₀).projector m y⟫_ℝ := by
  rw [S.zeroForcingLeraySpectralCompactFamily2D_projector hab u₀]
  exact
    GalerkinProjectorSequence.inner_finitePartialProjection_left_eq_right
      S.stateBasis (S.exhaustion.head m) x y

/-- The synchronized box extraction determines a bounded weakly continuous
pivot-space representative of its strong state limit. -/
noncomputable def zeroForcingWeaklyContinuousStateRepresentative
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I)
    (SW : (S.zeroForcingLeraySpectralCompactFamily2D hab u₀).StrongWeakPathSubsequence) :
    LeraySpectralCompactFamily.WeaklyContinuousStateRepresentative SW := by
  exact
    @LeraySpectralCompactFamily.StrongWeakPathSubsequence.weaklyContinuousStateRepresentative
      (Icc a b) (BoxH1ZeroSigma I) (BoxL2Sigma I)
      inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance
      inferInstance inferInstance (boxL2Sigma_completeSpace I)
      (boxL2Sigma_separableSpace I)
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)
      inferInstance
      (S.zeroForcingLeraySpectralCompactFamily2D hab u₀)
      SW (S.zeroForcing_projector_inner_eq hab u₀)

set_option maxHeartbeats 3000000 in
/-- Every finite Galerkin state path starts from the canonical orthogonal
projection of the prescribed pivot-space datum. -/
theorem zeroForcing_statePath_initial
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I) (m : ℕ) :
    (S.zeroForcingLeraySpectralCompactFamily2D hab u₀).statePath m
      (⟨a, le_rfl, hab⟩ : Icc a b) =
        S.stateSynthesis m (S.stateInitialCoefficient m u₀) := by
  let G := S.zeroForcingLeraySpectralCompactFamily2D hab u₀
  change boxEnergyToState I (G.lift m (⟨a, le_rfl, hab⟩ : Icc a b)) = _
  rw [S.zeroForcingLeraySpectralCompactFamily2D_lift_apply,
    S.canonicalSolution_initial,
    S.boxEnergyToState_energySynthesis]

end BoxCompactSpectralRepresentation

end
