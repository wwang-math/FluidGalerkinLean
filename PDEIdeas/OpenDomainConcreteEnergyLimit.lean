import PDEIdeas.OpenDomainConcreteRepresentative
import PDEIdeas.OpenDomainEnergyInequalityBridge
import PDEIdeas.OpenDomainForcingEstimates

/-!
The finite-level energy identities of the concrete open-domain family pass
to its weakly continuous representative.
-/

open Filter InnerProductSpace MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace OpenDomainConcreteEnergyLimit

variable {Q : BoxIntegral.Box (Fin 2)} (Ω : OpenDomainInBox Q)
  (L : BoxLadyzhenskayaRealization Q)
  (S : OpenDomainCompactSpectralRepresentation Ω)
  (u₀ : OpenDomainL2Sigma Ω) {T : ℝ} (hT : 0 ≤ T)

private abbrev G := OpenDomainConcreteCompactFamily.compactFamily Ω L S u₀ hT

local instance openDomainEnergyComplete (Ω : OpenDomainInBox Q) :
    CompleteSpace (OpenDomainH1ZeroSigma Ω) :=
  openDomainH1ZeroSigma_completeSpace Ω

local instance openDomainStateComplete (Ω : OpenDomainInBox Q) :
    CompleteSpace (OpenDomainL2Sigma Ω) :=
  openDomainL2Sigma_completeSpace Ω

private theorem statePath_eq (m : ℕ) (t : Icc (0 : ℝ) T) :
    (G Ω L S u₀ hT).statePath m t =
      OpenDomainConcreteBoundedPaths.stateBounded Ω
        L.toBoxEnergyL4Realization S m u₀ hT t := by
  rw [LeraySpectralCompactFamily.statePath_apply]
  exact OpenDomainConcreteBoundedPaths.openDomainEnergyToState_energyBounded
    Ω L.toBoxEnergyL4Realization S m u₀ hT t

private theorem energyLp_ae (m : ℕ) :
    ((G Ω L S u₀ hT).energyLp m : Icc (0 : ℝ) T →
      OpenDomainH1ZeroSigma Ω) =ᵐ[
        OpenDomainIntervalMeasureBridge.timeMeasure 0 T]
      fun t => OpenDomainUnforcedLpFamily.energyPath Ω
        L.toBoxEnergyL4Realization S m u₀ hT t := by
  change BoundedContinuousFunction.toLp (2 : ℝ≥0∞)
      (OpenDomainIntervalMeasureBridge.timeMeasure 0 T) ℝ
      (OpenDomainConcreteBoundedPaths.energyBounded Ω
        L.toBoxEnergyL4Realization S m u₀ hT) =ᵐ[
          OpenDomainIntervalMeasureBridge.timeMeasure 0 T] _
  simpa only [OpenDomainConcreteBoundedPaths.energyBounded_apply] using
    BoundedContinuousFunction.coeFn_toLp (2 : ℝ≥0∞)
      (OpenDomainIntervalMeasureBridge.timeMeasure 0 T) ℝ
      (OpenDomainConcreteBoundedPaths.energyBounded Ω
        L.toBoxEnergyL4Realization S m u₀ hT)

private theorem statePath_initial (m : ℕ) :
    (G Ω L S u₀ hT).statePath m
      (⟨0, le_rfl, hT⟩ : Icc (0 : ℝ) T) = S.stateProjection m u₀ := by
  calc
    (G Ω L S u₀ hT).statePath m _ =
        OpenDomainConcreteBoundedPaths.stateBounded Ω
          L.toBoxEnergyL4Realization S m u₀ hT _ :=
      statePath_eq Ω L S u₀ hT m _
    _ = S.stateSynthesis m
          ((OpenDomainUnforcedUniformBounds.solution Ω
            L.toBoxEnergyL4Realization S m u₀ hT).toFun 0) :=
      OpenDomainConcreteBoundedPaths.stateBounded_apply_solution
        Ω L.toBoxEnergyL4Realization S m u₀ hT _
    _ = S.stateProjection m u₀ := by
      calc
        S.stateSynthesis m
            ((OpenDomainUnforcedUniformBounds.solution Ω
              L.toBoxEnergyL4Realization S m u₀ hT).toFun 0) =
            S.stateSynthesis m
              (OpenDomainUnforcedUniformBounds.stateHeadProjection S m u₀) :=
          congrArg (S.stateSynthesis m)
            (OpenDomainUnforcedUniformBounds.solution Ω
              L.toBoxEnergyL4Realization S m u₀ hT).initial
        _ = S.stateProjection m u₀ := by
          exact OpenDomainUnforcedUniformBounds.stateHeadProjection_apply S m u₀

private theorem dissipation_eq (m : ℕ) (t : Icc (0 : ℝ) T) :
    (∫ s in Iic t,
      ‖openDomainEnergyGradient Ω ((G Ω L S u₀ hT).energyLp m s)‖ ^ 2
        ∂(OpenDomainIntervalMeasureBridge.timeMeasure 0 T)) =
      ∫ s in (0 : ℝ)..(t : ℝ),
        ‖openDomainEnergyGradient Ω
          (OpenDomainUnforcedLpFamily.energyPath Ω
            L.toBoxEnergyL4Realization S m u₀ hT s)‖ ^ 2 :=
  OpenDomainIntervalMeasureBridge.setIntegral_Iic_norm_grad_sq_of_ae
    (openDomainEnergyGradient Ω) ((G Ω L S u₀ hT).energyLp m)
    (OpenDomainUnforcedLpFamily.energyPath Ω
      L.toBoxEnergyL4Realization S m u₀ hT)
    (energyLp_ae Ω L S u₀ hT m) t

private theorem state_norm_eq (m : ℕ) (t : Icc (0 : ℝ) T) :
    ‖(G Ω L S u₀ hT).statePath m t‖ =
      ‖(OpenDomainUnforcedUniformBounds.solution Ω
        L.toBoxEnergyL4Realization S m u₀ hT).toFun (t : ℝ)‖ := by
  calc
    ‖(G Ω L S u₀ hT).statePath m t‖ =
        ‖OpenDomainConcreteBoundedPaths.stateBounded Ω
          L.toBoxEnergyL4Realization S m u₀ hT t‖ :=
      congrArg norm (statePath_eq Ω L S u₀ hT m t)
    _ = ‖S.stateSynthesis m
          ((OpenDomainUnforcedUniformBounds.solution Ω
            L.toBoxEnergyL4Realization S m u₀ hT).toFun (t : ℝ))‖ :=
      congrArg norm (OpenDomainConcreteBoundedPaths.stateBounded_apply_solution
        Ω L.toBoxEnergyL4Realization S m u₀ hT t)
    _ = _ := S.norm_stateSynthesis m _

private theorem dissipation_eq_diffusion (m : ℕ) (t : Icc (0 : ℝ) T) :
    (∫ s in Iic t,
      ‖openDomainEnergyGradient Ω ((G Ω L S u₀ hT).energyLp m s)‖ ^ 2
        ∂(OpenDomainIntervalMeasureBridge.timeMeasure 0 T)) =
      ∫ s in (0 : ℝ)..(t : ℝ),
        ((boxGradientDiffusion Q).bilinearCompSame (openDomainEnergyToBox Ω))
          (S.energySynthesis m
            ((OpenDomainUnforcedUniformBounds.solution Ω
              L.toBoxEnergyL4Realization S m u₀ hT).toFun s))
          (S.energySynthesis m
            ((OpenDomainUnforcedUniformBounds.solution Ω
              L.toBoxEnergyL4Realization S m u₀ hT).toFun s)) := by
  calc
    (∫ s in Iic t,
        ‖openDomainEnergyGradient Ω ((G Ω L S u₀ hT).energyLp m s)‖ ^ 2
          ∂(OpenDomainIntervalMeasureBridge.timeMeasure 0 T)) =
        ∫ s in (0 : ℝ)..(t : ℝ),
          ‖openDomainEnergyGradient Ω
            (OpenDomainUnforcedLpFamily.energyPath Ω
              L.toBoxEnergyL4Realization S m u₀ hT s)‖ ^ 2 :=
      dissipation_eq Ω L S u₀ hT m t
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro s _
      let w := S.energySynthesis m
        ((OpenDomainUnforcedUniformBounds.solution Ω
          L.toBoxEnergyL4Realization S m u₀ hT).toFun s)
      change ‖openDomainEnergyGradient Ω w‖ ^ 2 =
        boxGradientDiffusion Q (openDomainEnergyToBox Ω w)
          (openDomainEnergyToBox Ω w)
      calc
        ‖openDomainEnergyGradient Ω w‖ ^ 2 =
            ‖boxEnergyGradient Q (openDomainEnergyToBox Ω w)‖ ^ 2 := by
          rw [boxEnergyGradient_openDomainEnergyToBox]
        _ = _ := (boxGradientDiffusion_self Q (openDomainEnergyToBox Ω w)).symm

private theorem finite_bound :
    ∀ (t : Icc (0 : ℝ) T) (m : ℕ),
      ‖(G Ω L S u₀ hT).statePath m t‖ ^ 2 +
        2 * ∫ s in Iic t,
          ‖openDomainEnergyGradient Ω
            ((G Ω L S u₀ hT).energyLp m s)‖ ^ 2
            ∂(OpenDomainIntervalMeasureBridge.timeMeasure 0 T) ≤
      ‖OpenDomainEnergyInequalityBridge.stateInitialCoefficient S m u₀‖ ^ 2 := by
  refine OpenDomainEnergyInequalityBridge.hfinite_of_unforcedSolutions
    Ω L.toBoxEnergyL4Realization
    ((boxGradientDiffusion Q).bilinearCompSame (openDomainEnergyToBox Ω))
    (fun w => boxGradientDiffusion_nonneg Q (openDomainEnergyToBox Ω w))
    S hT (G Ω L S u₀ hT) (openDomainEnergyGradient Ω)
    (fun t => Iic t) id u₀
    (fun m => OpenDomainUnforcedUniformBounds.solution Ω
      L.toBoxEnergyL4Realization S m u₀ hT) ?_ ?_
  · intro m t
    exact state_norm_eq Ω L S u₀ hT m t
  · intro m t
    exact le_of_eq (dissipation_eq_diffusion Ω L S u₀ hT m t)

/-- The extracted representative attains the initial datum and satisfies the
Leray energy inequality on the fixed interval. -/
def energyLimit
    (SW : (G Ω L S u₀ hT).StrongWeakPathSubsequence) :
    OpenDomainEnergyLimit.EnergyLimit (G Ω L S u₀ hT) SW
      (openDomainEnergyGradient Ω) (fun t => Iic t)
      (⟨0, le_rfl, hT⟩ : Icc (0 : ℝ) T) u₀
      (fun _ => ‖u₀‖ ^ 2) := by
  letI : CompleteSpace (OpenDomainH1ZeroSigma Ω) :=
    openDomainH1ZeroSigma_completeSpace Ω
  letI : CompleteSpace (OpenDomainL2Sigma Ω) :=
    openDomainL2Sigma_completeSpace Ω
  exact @OpenDomainEnergyLimit.energyLimitOfFiniteLevel
    (Icc (0 : ℝ) T) (OpenDomainH1ZeroSigma Ω) (OpenDomainL2Sigma Ω)
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance (openDomainH1ZeroSigma_completeSpace Ω)
    inferInstance inferInstance
    (OpenDomainIntervalMeasureBridge.timeMeasure 0 T) inferInstance
    (BoxGradientL2 Q) inferInstance inferInstance
    (G Ω L S u₀ hT) SW
    (OpenDomainConcreteRepresentative.representative Ω L S u₀ hT SW)
    (openDomainEnergyGradient Ω) (fun t => Iic t)
    (⟨0, le_rfl, hT⟩ : Icc (0 : ℝ) T) u₀
    (fun _ m =>
      ‖OpenDomainEnergyInequalityBridge.stateInitialCoefficient S m u₀‖ ^ 2)
    (fun _ => ‖u₀‖ ^ 2)
    (finite_bound Ω L S u₀ hT)
    (fun _ => OpenDomainEnergyInequalityBridge.hC_of_unforcedSolutions
      Ω S id tendsto_id u₀)
    (OpenDomainEnergyInequalityBridge.hinit_of_unforcedSolutions
      Ω S hT (G Ω L S u₀ hT) id tendsto_id u₀
      (fun m => by
        change (G Ω L S u₀ hT).statePath m
          (⟨0, le_rfl, hT⟩ : Icc (0 : ℝ) T) = S.stateProjection m u₀
        exact statePath_initial Ω L S u₀ hT m))

end OpenDomainConcreteEnergyLimit

end
