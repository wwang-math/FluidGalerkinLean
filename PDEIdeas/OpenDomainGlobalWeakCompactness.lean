import PDEIdeas.OpenDomainGlobalStrongCompactness
import PDEIdeas.CountableWeakHilbertSubsequence

/-! One spectral subsequence with strong states and weak energies on every integer horizon. -/

open Filter InnerProductSpace MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace OpenDomainGlobalWeakCompactness

variable {Q : BoxIntegral.Box (Fin 2)} (Ω : OpenDomainInBox Q)
  (L : BoxLadyzhenskayaRealization Q)
  (S : OpenDomainCompactSpectralRepresentation Ω)
  (u₀ : OpenDomainL2Sigma Ω)

private abbrev StateTime (n : ℕ) :=
  Lp (OpenDomainL2Sigma Ω) (2 : ℝ≥0∞)
    (OpenDomainIntervalMeasureBridge.timeMeasure 0 (n : ℝ))

private abbrev EnergyTime (n : ℕ) :=
  Lp (OpenDomainH1ZeroSigma Ω) (2 : ℝ≥0∞)
    (OpenDomainIntervalMeasureBridge.timeMeasure 0 (n : ℝ))

private def G (n : ℕ) :=
  OpenDomainConcreteCompactFamily.compactFamily Ω L S u₀ (Nat.cast_nonneg n)

local instance energyComplete : CompleteSpace (OpenDomainH1ZeroSigma Ω) :=
  openDomainH1ZeroSigma_completeSpace Ω

local instance stateComplete : CompleteSpace (OpenDomainL2Sigma Ω) :=
  openDomainL2Sigma_completeSpace Ω

structure StrongWeakSubsequence where
  subseq : ExtractedSubsequence
  stateLimit : ∀ n, StateTime Ω n
  energyLimit : ∀ n, EnergyTime Ω n
  state_strong : ∀ n,
    Tendsto (fun k => (G Ω L S u₀ n).stateLp (subseq.idx k))
      atTop (nhds (stateLimit n))
  energy_weak : ∀ n (w : EnergyTime Ω n),
    Tendsto (fun k => ⟪(G Ω L S u₀ n).energyLp (subseq.idx k), w⟫_ℝ)
      atTop (nhds ⟪energyLimit n, w⟫_ℝ)

def StrongWeakSubsequence.toFiniteHorizon
    (SW : StrongWeakSubsequence Ω L S u₀) (n : ℕ) :
    (G Ω L S u₀ n).StrongWeakSubsequence :=
  @LeraySpectralCompactFamily.strongWeakSubsequenceOfLimits
    (Icc (0 : ℝ) (n : ℝ))
    (OpenDomainH1ZeroSigma Ω) (OpenDomainL2Sigma Ω)
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance (openDomainH1ZeroSigma_completeSpace Ω)
    inferInstance inferInstance (openDomainL2Sigma_completeSpace Ω)
    (OpenDomainIntervalMeasureBridge.timeMeasure 0 (n : ℝ)) inferInstance
    (G Ω L S u₀ n)
    SW.subseq (SW.stateLimit n) (SW.energyLimit n)
    (SW.state_strong n) (SW.energy_weak n)

theorem exists_strongWeakSubsequence :
    Nonempty (StrongWeakSubsequence Ω L S u₀) := by
  letI : CompleteSpace (OpenDomainH1ZeroSigma Ω) :=
    openDomainH1ZeroSigma_completeSpace Ω
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  letI : ∀ n, CompleteSpace (EnergyTime Ω n) := fun n =>
    @MeasureTheory.Lp.instCompleteSpace
      (Icc (0 : ℝ) (n : ℝ)) inferInstance (2 : ℝ≥0∞)
      (OpenDomainIntervalMeasureBridge.timeMeasure 0 (n : ℝ))
      (OpenDomainH1ZeroSigma Ω) inferInstance
      (openDomainH1ZeroSigma_completeSpace Ω) inferInstance
  letI : ∀ n, TopologicalSpace.SeparableSpace (EnergyTime Ω n) :=
    fun n => OpenDomainWeakEnergySubsequence.openDomainEnergyTimeLp_separableSpace
      Ω (OpenDomainIntervalMeasureBridge.timeMeasure 0 (n : ℝ))
  obtain ⟨GS⟩ := OpenDomainGlobalStrongCompactness.exists_strongSubsequence
    Ω L S u₀
  let x : ℕ → ∀ n, EnergyTime Ω n :=
    fun k n => (G Ω L S u₀ n).energyLp (GS.subseq.idx k)
  have hbound : ∀ k n, ‖x k n‖ ≤ (G Ω L S u₀ n).liftLpRadius := by
    intro k n
    exact (G Ω L S u₀ n).energyLp_norm_le _
  obtain ⟨e, τ, hτ, hweak⟩ :=
    CountableWeakHilbertSubsequence.exists_subsequence
      (fun n => EnergyTime Ω n) x
      (fun n => (G Ω L S u₀ n).liftLpRadius) hbound
  let sub := GS.subseq.comp ⟨τ, hτ⟩
  refine ⟨{
    subseq := sub
    stateLimit := GS.stateLimit
    energyLimit := e
    state_strong := ?_
    energy_weak := ?_
  }⟩
  · intro n
    simpa only [sub, ExtractedSubsequence.comp_idx, Function.comp_def] using
      (GS.state_strong n).comp hτ.tendsto_atTop
  · intro n w
    simpa only [sub, x, ExtractedSubsequence.comp_idx] using hweak n w

end OpenDomainGlobalWeakCompactness

end
