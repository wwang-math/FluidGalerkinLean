import PDEIdeas.OpenDomainGelfandTriple
import PDEIdeas.AbstractGalerkinTower
import PDEIdeas.BoxSubspaceEstimates

/-!
# Spectral coordinates and two-dimensional estimates on an open subdomain

The compact domain embedding has singular coordinates and finite Galerkin
heads. Its Ladyzhenskaya and Poincare bounds are inherited from the
containing rectangle through the isometric energy inclusion.
-/

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

variable {n : ℕ} {Q : BoxIntegral.Box (Fin (n + 1))}

@[reducible] noncomputable def openDomainH1ZeroSigma_secondCountableTopology
    (Ω : OpenDomainInBox Q) :
    SecondCountableTopology (OpenDomainH1ZeroSigma Ω) := by
  letI : SecondCountableTopology (BoxEnergyAmbient Q) :=
    boxEnergyAmbient_secondCountableTopology Q
  infer_instance

@[reducible] noncomputable def openDomainH1ZeroSigma_separableSpace
    (Ω : OpenDomainInBox Q) :
    TopologicalSpace.SeparableSpace (OpenDomainH1ZeroSigma Ω) := by
  letI : SecondCountableTopology (OpenDomainH1ZeroSigma Ω) :=
    openDomainH1ZeroSigma_secondCountableTopology Ω
  infer_instance

@[reducible] noncomputable def openDomainL2Sigma_secondCountableTopology
    (Ω : OpenDomainInBox Q) :
    SecondCountableTopology (OpenDomainL2Sigma Ω) := by
  letI : SecondCountableTopology (BoxVelocityL2 Q) :=
    boxVelocityL2_secondCountableTopology Q
  infer_instance

@[reducible] noncomputable def openDomainL2Sigma_separableSpace
    (Ω : OpenDomainInBox Q) :
    TopologicalSpace.SeparableSpace (OpenDomainL2Sigma Ω) := by
  letI : SecondCountableTopology (OpenDomainL2Sigma Ω) :=
    openDomainL2Sigma_secondCountableTopology Ω
  infer_instance

abbrev OpenDomainCompactSpectralRepresentation
    (Ω : OpenDomainInBox Q) :=
  CompactEmbeddingSpectralRepresentation (openDomainEnergyToState Ω)

/-- Singular coordinates for the compact open-domain embedding. -/
noncomputable def openDomainCompactSpectralRepresentation
    (Ω : OpenDomainInBox Q) :
    OpenDomainCompactSpectralRepresentation Ω :=
  @CompactGelfandTriple.spectralRepresentation
    (OpenDomainH1ZeroSigma Ω) (OpenDomainL2Sigma Ω)
    inferInstance inferInstance (openDomainH1ZeroSigma_completeSpace Ω)
      (openDomainH1ZeroSigma_separableSpace Ω)
    inferInstance inferInstance (openDomainL2Sigma_completeSpace Ω)
      (openDomainL2Sigma_separableSpace Ω)
    (openDomainGelfandTriple Ω)

theorem exists_openDomainCompactSpectralRepresentation
    (Ω : OpenDomainInBox Q) :
    Nonempty (OpenDomainCompactSpectralRepresentation Ω) :=
  ⟨openDomainCompactSpectralRepresentation Ω⟩

variable {Q₂ : BoxIntegral.Box (Fin 2)}

/-- The 2D domain energy space inherits the rectangle's L4 and Poincare
estimates through its inclusion into the rectangle energy space. -/
def openDomainEnergyEstimates (Ω : OpenDomainInBox Q₂) :
    BoxSubspaceEnergyEstimates Q₂ (OpenDomainH1ZeroSigma Ω) :=
  boxSubspaceEnergyEstimates Q₂ (boxLadyzhenskayaRealization Q₂)
    (openDomainEnergyToBox Ω)

end
