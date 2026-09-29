import PDEIdeas.OpenDomainCore
import PDEIdeas.BoxGelfandTriple
import PDEIdeas.CompactSubspaceEmbedding

/-!
# Compact Gelfand triple on an open subdomain of a rectangle

The closure spaces of an open subdomain embed isometrically into the
corresponding box spaces. The box Rellich theorem therefore makes the
subdomain energy-to-state map compact.
-/

open Function
open scoped RealInnerProductSpace

noncomputable section

variable {n : ℕ} {Q : BoxIntegral.Box (Fin (n + 1))}

instance openDomainH1ZeroSigma_completeSpace (Ω : OpenDomainInBox Q) :
    CompleteSpace (OpenDomainH1ZeroSigma Ω) :=
  Submodule.topologicalClosure.completeSpace (openDomainGraphCore Ω)

instance openDomainL2Sigma_completeSpace (Ω : OpenDomainInBox Q) :
    CompleteSpace (OpenDomainL2Sigma Ω) :=
  Submodule.topologicalClosure.completeSpace (openDomainVelocityCore Ω)

/-- Inclusion of the subdomain energy closure into the box energy closure. -/
def openDomainEnergyToBox (Ω : OpenDomainInBox Q) :
    OpenDomainH1ZeroSigma Ω →L[ℝ] BoxH1ZeroSigma Q :=
  (OpenDomainH1ZeroSigma Ω).subtypeL.codRestrict (BoxH1ZeroSigma Q)
    (fun u => openDomainH1ZeroSigma_le Ω u.property)

/-- Inclusion of the subdomain velocity closure into the box velocity closure. -/
def openDomainStateToBox (Ω : OpenDomainInBox Q) :
    OpenDomainL2Sigma Ω →L[ℝ] BoxL2Sigma Q :=
  (OpenDomainL2Sigma Ω).subtypeL.codRestrict (BoxL2Sigma Q)
    (fun u => openDomainL2Sigma_le Ω u.property)

@[simp] theorem openDomainEnergyToBox_coe (Ω : OpenDomainInBox Q)
    (u : OpenDomainH1ZeroSigma Ω) :
    ((openDomainEnergyToBox Ω u : BoxH1ZeroSigma Q) : BoxEnergyAmbient Q) = u :=
  rfl

@[simp] theorem openDomainStateToBox_coe (Ω : OpenDomainInBox Q)
    (u : OpenDomainL2Sigma Ω) :
    ((openDomainStateToBox Ω u : BoxL2Sigma Q) : BoxVelocityL2 Q) = u :=
  rfl

/-- The two energy-to-state maps commute with the subdomain inclusions. -/
theorem openDomain_embedding_commutes (Ω : OpenDomainInBox Q)
    (u : OpenDomainH1ZeroSigma Ω) :
    openDomainStateToBox Ω (openDomainEnergyToState Ω u) =
      boxEnergyToState Q (openDomainEnergyToBox Ω u) := by
  apply Subtype.ext
  rfl

theorem openDomainEnergyToState_injective (Ω : OpenDomainInBox Q) :
    Injective (openDomainEnergyToState Ω) := by
  intro u v huv
  have hbox : boxEnergyToState Q (openDomainEnergyToBox Ω u) =
      boxEnergyToState Q (openDomainEnergyToBox Ω v) := by
    rw [← openDomain_embedding_commutes Ω u,
      ← openDomain_embedding_commutes Ω v, huv]
  have heq := boxEnergyToState_injective Q hbox
  apply Subtype.ext
  simpa only [openDomainEnergyToBox_coe] using
    congrArg (fun w : BoxH1ZeroSigma Q => (w : BoxEnergyAmbient Q)) heq

theorem openDomainEnergyToState_isCompactOperator (Ω : OpenDomainInBox Q) :
    IsCompactOperator (openDomainEnergyToState Ω) := by
  have hisometry : Isometry (openDomainStateToBox Ω :
      OpenDomainL2Sigma Ω → BoxL2Sigma Q) := by
    intro u v
    rfl
  have hbox : IsCompactOperator
      ((boxEnergyToState Q : BoxH1ZeroSigma Q → BoxL2Sigma Q) ∘
        (openDomainEnergyToBox Ω :
          OpenDomainH1ZeroSigma Ω → BoxH1ZeroSigma Q)) :=
    (boxEnergyToState_isCompactOperator_fourier Q).comp_clm
      (openDomainEnergyToBox Ω)
  have hcomp :
      (openDomainStateToBox Ω : OpenDomainL2Sigma Ω → BoxL2Sigma Q) ∘
          (openDomainEnergyToState Ω :
            OpenDomainH1ZeroSigma Ω → OpenDomainL2Sigma Ω) =
        (boxEnergyToState Q : BoxH1ZeroSigma Q → BoxL2Sigma Q) ∘
          (openDomainEnergyToBox Ω :
            OpenDomainH1ZeroSigma Ω → BoxH1ZeroSigma Q) := by
    funext u
    exact openDomain_embedding_commutes Ω u
  exact isCompactOperator_of_isometry_comp hisometry (hcomp ▸ hbox)

/-- The compact dense injection from the subdomain energy closure to its
velocity closure. -/
def openDomainGelfandTriple (Ω : OpenDomainInBox Q) :
    CompactGelfandTriple (OpenDomainH1ZeroSigma Ω) (OpenDomainL2Sigma Ω) where
  embedding := openDomainEnergyToState Ω
  embedding_injective := openDomainEnergyToState_injective Ω
  embedding_denseRange := openDomainEnergyToState_denseRange Ω
  embedding_compact := openDomainEnergyToState_isCompactOperator Ω
  embedding_contractive := norm_openDomainEnergyToState_le Ω

@[simp] theorem openDomainGelfandTriple_embedding (Ω : OpenDomainInBox Q) :
    (openDomainGelfandTriple Ω).embedding = openDomainEnergyToState Ω :=
  rfl

end
