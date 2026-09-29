import PDEIdeas.OpenDomainConcreteBoundedPaths
import PDEIdeas.OpenDomainCoordinateDerivative
import PDEIdeas.OpenDomainIntervalMeasureBridge
import PDEIdeas.OpenDomainWeakEnergySubsequence

/-!
The canonical unforced Galerkin trajectories satisfy every input of the
open-domain spectral compactness family on a fixed finite interval.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace OpenDomainConcreteCompactFamily

variable {Q : BoxIntegral.Box (Fin 2)} (Ω : OpenDomainInBox Q)
  (L : BoxLadyzhenskayaRealization Q)
  (S : OpenDomainCompactSpectralRepresentation Ω)
  (u₀ : OpenDomainL2Sigma Ω) {T : ℝ} (hT : 0 ≤ T)

private theorem energyLp_norm_le (m : ℕ) :
    ‖BoundedContinuousFunction.toLp (2 : ℝ≥0∞)
      (OpenDomainIntervalMeasureBridge.timeMeasure 0 T) ℝ
      (OpenDomainConcreteBoundedPaths.energyBounded Ω
        L.toBoxEnergyL4Realization S m u₀ hT)‖ ≤
      Real.sqrt (T * ‖u₀‖ ^ 2 + ‖u₀‖ ^ 2 / 2) := by
  let w := BoundedContinuousFunction.toLp (2 : ℝ≥0∞)
    (OpenDomainIntervalMeasureBridge.timeMeasure 0 T) ℝ
    (OpenDomainConcreteBoundedPaths.energyBounded Ω
      L.toBoxEnergyL4Realization S m u₀ hT)
  have hae : (w : Icc (0 : ℝ) T → OpenDomainH1ZeroSigma Ω) =ᵐ[
      OpenDomainIntervalMeasureBridge.timeMeasure 0 T]
      fun t => OpenDomainUnforcedLpFamily.energyPath Ω
        L.toBoxEnergyL4Realization S m u₀ hT t := by
    simpa only [w, OpenDomainConcreteBoundedPaths.energyBounded_apply] using
      BoundedContinuousFunction.coeFn_toLp (2 : ℝ≥0∞)
        (OpenDomainIntervalMeasureBridge.timeMeasure 0 T) ℝ
        (OpenDomainConcreteBoundedPaths.energyBounded Ω
          L.toBoxEnergyL4Realization S m u₀ hT)
  have hsq := OpenDomainIntervalMeasureBridge.norm_sq_eq_intervalIntegral_of_ae
    hT w (OpenDomainUnforcedLpFamily.energyPath Ω
      L.toBoxEnergyL4Realization S m u₀ hT) hae
  have hbound := OpenDomainUnforcedLpFamily.integral_norm_energyPath_sq_le
    Ω L.toBoxEnergyL4Realization S m u₀ hT
  have hnonneg : 0 ≤ T * ‖u₀‖ ^ 2 + ‖u₀‖ ^ 2 / 2 := by positivity
  change ‖w‖ ≤ _
  nlinarith [Real.sq_sqrt hnonneg, Real.sqrt_nonneg
    (T * ‖u₀‖ ^ 2 + ‖u₀‖ ^ 2 / 2), norm_nonneg w]

/-- Compactness data built from the actual unforced solutions on `[0,T]`. -/
def compactFamily : LeraySpectralCompactFamily
    (I := Icc (0 : ℝ) T)
    (V := OpenDomainH1ZeroSigma Ω) (H := OpenDomainL2Sigma Ω)
    (μ := OpenDomainIntervalMeasureBridge.timeMeasure 0 T) :=
  OpenDomainCoordinateDerivative.compactFamilyOfPath Ω L S u₀ hT
    (fun m => OpenDomainConcreteBoundedPaths.energyBounded Ω
      L.toBoxEnergyL4Realization S m u₀ hT)
    (by intro m t; rfl)
    ‖u₀‖
    (by
      intro m t
      rw [OpenDomainConcreteBoundedPaths.openDomainEnergyToState_energyBounded]
      exact OpenDomainConcreteBoundedPaths.norm_stateBounded_apply_le
        Ω L.toBoxEnergyL4Realization S m u₀ hT t)
    (Real.sqrt (T * ‖u₀‖ ^ 2 + ‖u₀‖ ^ 2 / 2))
    (Real.sqrt_nonneg _)
    (energyLp_norm_le Ω L S u₀ hT)

/-- A single subsequence with strong state convergence, weak energy convergence,
and pointwise weak state convergence. -/
theorem exists_strongWeakPathSubsequence :
    Nonempty (compactFamily Ω L S u₀ hT).StrongWeakPathSubsequence :=
  OpenDomainWeakEnergySubsequence.exists_strongWeakPathSubsequence Ω
    (compactFamily Ω L S u₀ hT)

end OpenDomainConcreteCompactFamily

end
