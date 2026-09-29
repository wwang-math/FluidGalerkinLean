import PDEIdeas.OpenDomainUnforcedUniformBounds
import PDEIdeas.VariationalGalerkinUniqueness

/-! The canonical unforced coefficient paths agree on overlapping horizons. -/

open Set

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace OpenDomainGalerkinHorizonCompatibility

variable {Q : BoxIntegral.Box (Fin 2)} (Ω : OpenDomainInBox Q)
  (R : BoxEnergyL4Realization Q)
  (S : OpenDomainCompactSpectralRepresentation Ω)
  (m : ℕ) (u₀ : OpenDomainL2Sigma Ω)
  {T₁ T₂ : ℝ} (hT₁ : 0 ≤ T₁) (hT₂ : T₁ ≤ T₂)

theorem solution_eqOn :
    EqOn
      (OpenDomainUnforcedUniformBounds.solution Ω R S m u₀ hT₁).toFun
      (OpenDomainUnforcedUniformBounds.solution Ω R S m u₀
        (hT₁.trans hT₂)).toFun
      (Icc (0 : ℝ) T₁) := by
  let P := OpenDomainUnforcedGalerkin.unforcedProblem Ω R
    ((boxGradientDiffusion Q).bilinearCompSame (openDomainEnergyToBox Ω))
    (fun w => boxGradientDiffusion_nonneg Q (openDomainEnergyToBox Ω w))
    S m (OpenDomainUnforcedUniformBounds.stateHeadProjection S m u₀)
  let u := OpenDomainUnforcedUniformBounds.solution Ω R S m u₀ hT₁
  let v := OpenDomainUnforcedUniformBounds.solution Ω R S m u₀
    (hT₁.trans hT₂)
  apply VariationalGalerkinProblem.eqOn_of_bounded P hT₁ hT₂ u v
    ‖u₀‖ (norm_nonneg u₀)
  · intro t ht
    exact OpenDomainUnforcedUniformBounds.norm_solution_le Ω R S m u₀ hT₁ ht
  · intro t ht
    exact OpenDomainUnforcedUniformBounds.norm_solution_le Ω R S m u₀
      (hT₁.trans hT₂) ⟨ht.1, ht.2.trans hT₂⟩

end OpenDomainGalerkinHorizonCompatibility

end
