import PDEIdeas.OpenDomainConcreteCompactFamily
import PDEIdeas.OpenDomainGlobalGalerkinPath
import PDEIdeas.CountableCompactSubsequence

/-! Strong state compactness on all integer time horizons along one subsequence. -/

open Filter MeasureTheory Set
open scoped ENNReal

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace OpenDomainGlobalStrongCompactness

variable {Q : BoxIntegral.Box (Fin 2)} (Ω : OpenDomainInBox Q)
  (L : BoxLadyzhenskayaRealization Q)
  (S : OpenDomainCompactSpectralRepresentation Ω)
  (u₀ : OpenDomainL2Sigma Ω)

private abbrev StateTime (Ω : OpenDomainInBox Q) (n : ℕ) :=
  Lp (OpenDomainL2Sigma Ω) (2 : ℝ≥0∞)
    (OpenDomainIntervalMeasureBridge.timeMeasure 0 (n : ℝ))

private def G (n : ℕ) :=
  OpenDomainConcreteCompactFamily.compactFamily Ω L S u₀ (Nat.cast_nonneg n)

/-- One extraction converging strongly in the pivot space on every integer horizon. -/
structure StrongSubsequence where
  subseq : ExtractedSubsequence
  stateLimit : ∀ n, StateTime Ω n
  state_strong : ∀ n,
    Tendsto (fun k => (G Ω L S u₀ n).stateLp (subseq.idx k))
      atTop (nhds (stateLimit n))

theorem exists_strongSubsequence : Nonempty (StrongSubsequence Ω L S u₀) := by
  letI : CompleteSpace (OpenDomainL2Sigma Ω) :=
    openDomainL2Sigma_completeSpace Ω
  let f : ℕ → ∀ n, StateTime Ω n :=
    fun m n => (G Ω L S u₀ n).stateLp m
  let K : ∀ n, Set (StateTime Ω n) :=
    fun n => closure (Set.range (fun m => f m n))
  have hK : ∀ n, IsCompact (K n) := by
    intro n
    letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
    have hcomplete : CompleteSpace (StateTime Ω n) :=
      @MeasureTheory.Lp.instCompleteSpace
        (Icc (0 : ℝ) (n : ℝ)) inferInstance (2 : ℝ≥0∞)
        (OpenDomainIntervalMeasureBridge.timeMeasure 0 (n : ℝ))
        (OpenDomainL2Sigma Ω) inferInstance
        (openDomainL2Sigma_completeSpace Ω) inferInstance
    exact @CompactApproximationSequence.compact_closure_range
      (StateTime Ω n) inferInstance hcomplete
      (G Ω L S u₀ n).compactApproximation
  have hf : ∀ m n, f m n ∈ K n := by
    intro m n
    exact subset_closure ⟨m, rfl⟩
  obtain ⟨g, σ, hσ, hconv⟩ :=
    CountableCompactSubsequence.exists_coordinatewise_convergent f K hK hf
  exact ⟨{
    subseq := ⟨σ, hσ⟩
    stateLimit := g
    state_strong := hconv
  }⟩

end OpenDomainGlobalStrongCompactness

end
