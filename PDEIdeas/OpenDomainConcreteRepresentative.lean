import PDEIdeas.OpenDomainConcreteCompactFamily
import PDEIdeas.LeraySpectralWeakContinuity

/-!
Weakly continuous state representative for the concrete open-domain
Galerkin family.
-/

open InnerProductSpace Set
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace OpenDomainConcreteRepresentative

variable {Q : BoxIntegral.Box (Fin 2)} (Ω : OpenDomainInBox Q)
  (L : BoxLadyzhenskayaRealization Q)
  (S : OpenDomainCompactSpectralRepresentation Ω)
  (u₀ : OpenDomainL2Sigma Ω) {T : ℝ} (hT : 0 ≤ T)

private abbrev G := OpenDomainConcreteCompactFamily.compactFamily Ω L S u₀ hT

theorem projector_selfAdjoint (m : ℕ) (x y : OpenDomainL2Sigma Ω) :
    ⟪(G Ω L S u₀ hT).projector m x, y⟫_ℝ =
      ⟪x, (G Ω L S u₀ hT).projector m y⟫_ℝ :=
  GalerkinProjectorSequence.inner_finitePartialProjection_left_eq_right
    S.stateBasis (S.exhaustion.head m) x y

/-- The representative attached to a synchronized strong/weak extraction. -/
def representative
    (SW : (G Ω L S u₀ hT).StrongWeakPathSubsequence) :
    (G Ω L S u₀ hT).WeaklyContinuousStateRepresentative SW := by
  exact
    @LeraySpectralCompactFamily.StrongWeakPathSubsequence.weaklyContinuousStateRepresentative
      (Icc (0 : ℝ) T) (OpenDomainH1ZeroSigma Ω) (OpenDomainL2Sigma Ω)
      inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance
      inferInstance inferInstance (openDomainL2Sigma_completeSpace Ω)
      (openDomainL2Sigma_separableSpace Ω)
      (OpenDomainIntervalMeasureBridge.timeMeasure 0 T)
      inferInstance
      (G Ω L S u₀ hT)
      SW (projector_selfAdjoint Ω L S u₀ hT)

end OpenDomainConcreteRepresentative

end
