import PDEIdeas.OpenDomainConcreteWeakEquation

/-! Finite-horizon unforced Leray--Hopf solutions on an open subdomain. -/

open Filter InnerProductSpace MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 400000

namespace OpenDomainLerayHopfStatement

variable {Q : BoxIntegral.Box (Fin 2)} (Ω : OpenDomainInBox Q)
  (L : BoxLadyzhenskayaRealization Q)
  (u₀ : OpenDomainL2Sigma Ω) {T : ℝ} (hT : 0 ≤ T)

/-- An unforced weak solution on a compact time interval. -/
structure SolutionOn where
  energyPath : Lp (OpenDomainH1ZeroSigma Ω) (2 : ℝ≥0∞)
    (OpenDomainIntervalMeasureBridge.timeMeasure 0 T)
  statePath : Icc (0 : ℝ) T → OpenDomainL2Sigma Ω
  weaklyContinuous : ∀ y : OpenDomainL2Sigma Ω,
    Continuous fun t => ⟪statePath t, y⟫_ℝ
  state_eq_energy : statePath =ᵐ[OpenDomainIntervalMeasureBridge.timeMeasure 0 T]
    fun t => openDomainEnergyToState Ω (energyPath t)
  initial : statePath (⟨0, le_rfl, hT⟩ : Icc (0 : ℝ) T) = u₀
  energyInequality : ∀ t : Icc (0 : ℝ) T,
    ‖statePath t‖ ^ 2 +
      2 * ∫ s in Iic t,
        ‖openDomainEnergyGradient Ω (energyPath s)‖ ^ 2
          ∂OpenDomainIntervalMeasureBridge.timeMeasure 0 T ≤ ‖u₀‖ ^ 2
  weakEquation : ∀ (eta : LerayIntervalTimeTest 0 T),
    eta.value T = 0 → ∀ φ : OpenDomainH1ZeroSigma Ω,
      OpenDomainConcreteWeakEquation.TestedEquation Ω L u₀ energyPath eta φ

/-- The canonical spectral Galerkin family yields a finite-horizon solution. -/
theorem exists_solution_on
    (S : OpenDomainCompactSpectralRepresentation Ω) :
    Nonempty (SolutionOn Ω L u₀ hT) := by
  obtain ⟨SW⟩ := OpenDomainConcreteCompactFamily.exists_strongWeakPathSubsequence
    Ω L S u₀ hT
  let E := OpenDomainConcreteEnergyLimit.energyLimit Ω L S u₀ hT SW
  refine ⟨{
    energyPath := SW.energyLimit
    statePath := E.path
    weaklyContinuous := E.inner_continuous
    state_eq_energy := ?_
    initial := E.initial
    energyInequality := E.energy_inequality
    weakEquation := ?_
  }⟩
  · have h := OpenDomainWeakEnergySubsequence.stateLimit_ae_eq_embed_energyLimit
      (G := OpenDomainConcreteCompactFamily.compactFamily Ω L S u₀ hT)
      SW.toStrongWeakSubsequence
    exact E.path_ae_eq_stateLimit.trans h
  · intro eta heta φ
    exact OpenDomainConcreteWeakEquation.tested_weak_equation Ω L S u₀ hT
      SW eta heta φ

/-- Existence with the spectral representation and Ladyzhenskaya realization
chosen canonically from the subdomain and its enclosing rectangle. -/
theorem exists_solution_on_canonical :
    Nonempty (SolutionOn Ω (boxLadyzhenskayaRealization Q) u₀ hT) :=
  exists_solution_on Ω (boxLadyzhenskayaRealization Q) u₀ hT
    (openDomainCompactSpectralRepresentation Ω)

end OpenDomainLerayHopfStatement

end
