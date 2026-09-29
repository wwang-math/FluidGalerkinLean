import PDEIdeas.OpenDomainBoundedEnclosure
import PDEIdeas.OpenDomainGlobalLerayHopf

/-! Global unforced Leray--Hopf solutions on bounded open planar domains. -/

noncomputable section

namespace OpenDomainGlobalBoundedEnclosure

/-- A single global weak trajectory exists on every bounded open planar set. -/
theorem exists_global_solution (U : Set (Fin 2 → ℝ))
    (hOpen : IsOpen U) (hBound : Bornology.IsBounded U) :
    ∃ (Q : BoxIntegral.Box (Fin 2)) (Ω : OpenDomainInBox Q),
      Ω.carrier = U ∧
      ∀ u₀ : OpenDomainL2Sigma Ω,
        Nonempty (OpenDomainGlobalLerayHopf.GlobalSolution Ω
          (boxLadyzhenskayaRealization Q) u₀) := by
  obtain ⟨Q, Ω, hΩ⟩ :=
    OpenDomainBoundedEnclosure.exists_openDomainInBox U hOpen hBound
  refine ⟨Q, Ω, hΩ, ?_⟩
  intro u₀
  exact OpenDomainGlobalLerayHopf.exists_globalSolution Ω
    (boxLadyzhenskayaRealization Q) u₀
    (openDomainCompactSpectralRepresentation Ω)

end OpenDomainGlobalBoundedEnclosure

end
