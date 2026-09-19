import PDEIdeas.BoxGelfandTriple
import PDEIdeas.CompactEmbeddingSpectral
import PDEIdeas.GalerkinL2Compactness

/-!
# Singular coordinates for the box energy embedding

The compact Gelfand triple on a rectangular box has a canonical singular
coordinate representation. The coordinates are constructed from the compact
self-adjoint Gram operator of the energy-to-state embedding; no spectral
representation is supplied as an assumption.
-/

open Filter Function Real
open scoped ENNReal NNReal Topology

noncomputable section

variable {n : ℕ}

/-- Singular coordinates of the canonical box energy-to-state embedding. -/
abbrev BoxCompactSpectralRepresentation
    (I : BoxIntegral.Box (Fin (n + 1))) :=
  CompactEmbeddingSpectralRepresentation (boxEnergyToState I)

/-- The spectral representation constructed from the compact box Gelfand
triple. -/
noncomputable def boxCompactSpectralRepresentation
    (I : BoxIntegral.Box (Fin (n + 1))) :
    BoxCompactSpectralRepresentation I :=
  @CompactGelfandTriple.spectralRepresentation
    (BoxH1ZeroSigma I) (BoxL2Sigma I)
    inferInstance inferInstance (boxH1ZeroSigma_completeSpace I)
      (boxH1ZeroSigma_separableSpace I)
    inferInstance inferInstance (boxL2Sigma_completeSpace I)
      (boxL2Sigma_separableSpace I)
    (boxGelfandTriple I)

theorem exists_boxCompactSpectralRepresentation
    (I : BoxIntegral.Box (Fin (n + 1))) :
    Nonempty (BoxCompactSpectralRepresentation I) :=
  ⟨boxCompactSpectralRepresentation I⟩

namespace BoxCompactSpectralRepresentation

/-- Compactness of the canonical box embedding, recorded by its constructed
spectral representation. -/
theorem boxEnergyToState_isCompactOperator
    {I : BoxIntegral.Box (Fin (n + 1))}
    (S : BoxCompactSpectralRepresentation I) :
    IsCompactOperator (boxEnergyToState I) :=
  S.embedding_compact

/-- Density of the canonical box embedding, recorded by its constructed
spectral representation. -/
theorem boxEnergyToState_denseRange
    {I : BoxIntegral.Box (Fin (n + 1))}
    (S : BoxCompactSpectralRepresentation I) :
    DenseRange (boxEnergyToState I) :=
  S.embedding_denseRange

/-- Operator left after projection onto the current finite state-space head. -/
def boxEnergyToStateProjectorTail
    {I : BoxIntegral.Box (Fin (n + 1))}
    (S : BoxCompactSpectralRepresentation I)
    (m : ℕ) :
    BoxH1ZeroSigma I →L[ℝ] BoxL2Sigma I :=
  (ContinuousLinearMap.sub :
      Sub (BoxH1ZeroSigma I →L[ℝ] BoxL2Sigma I)).sub
    (boxEnergyToState I)
    ((S.stateProjection m).comp (boxEnergyToState I))

/-- The exhausted state-basis projectors approximate the box embedding in
operator norm. -/
theorem boxEnergyToState_projectorTail_tendsto
    {I : BoxIntegral.Box (Fin (n + 1))}
    (S : BoxCompactSpectralRepresentation I) :
    Tendsto
      (fun m => ContinuousLinearMap.opNorm
        (S.boxEnergyToStateProjectorTail m))
      atTop (𝓝 0) := by
  have htail := compactEmbedding_projectorTail_tendsto
    (boxEnergyToState I) S.embedding_compact S.stateProjection
    (fun m =>
      GalerkinProjectorSequence.finitePartialProjection_norm_le
        S.stateBasis (S.exhaustion.head m))
    (fun x =>
      GalerkinProjectorSequence.finitePartialProjection_tendsto
        S.stateBasis S.exhaustion x)
  simpa only [boxEnergyToStateProjectorTail] using htail

end BoxCompactSpectralRepresentation

end
