import PDEIdeas.OpenDomainGlobalWeakCompactness
import PDEIdeas.OpenDomainConcreteRepresentative

/-! Uniform convergence of finite spectral projections on all integer horizons. -/

open BoundedContinuousFunction Filter InnerProductSpace MeasureTheory Set
open scoped ENNReal

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace OpenDomainGlobalProjectedCompactness

variable {Q : BoxIntegral.Box (Fin 2)} (Ω : OpenDomainInBox Q)
  (L : BoxLadyzhenskayaRealization Q)
  (S : OpenDomainCompactSpectralRepresentation Ω)
  (u₀ : OpenDomainL2Sigma Ω)

private def G (n : ℕ) :=
  OpenDomainConcreteCompactFamily.compactFamily Ω L S u₀ (Nat.cast_nonneg n)

local instance stateComplete : CompleteSpace (OpenDomainL2Sigma Ω) :=
  openDomainL2Sigma_completeSpace Ω

structure ProjectedSubsequence extends
    OpenDomainGlobalWeakCompactness.StrongWeakSubsequence Ω L S u₀ where
  projectedLimit : ∀ n : ℕ, ℕ → Icc (0 : ℝ) (n : ℝ) →ᵇ OpenDomainL2Sigma Ω
  projected_uniform : ∀ (n m : ℕ),
    Tendsto (fun k => (G Ω L S u₀ n).projectedPath m (subseq.idx k))
      atTop (nhds (projectedLimit n m))

def ProjectedSubsequence.toFiniteHorizon
    (P : ProjectedSubsequence Ω L S u₀) (n : ℕ) :
    (G Ω L S u₀ n).StrongWeakPathSubsequence := by
  refine {
    toStrongWeakSubsequence :=
      P.toStrongWeakSubsequence.toFiniteHorizon Ω L S u₀ n
    projectedLimit := P.projectedLimit n
    projected_uniform := ?_
  }
  intro m
  exact P.projected_uniform n m

theorem statePath_eqOn (n N m : ℕ) (h : n ≤ N)
    (t : Icc (0 : ℝ) (n : ℝ)) :
    (G Ω L S u₀ n).statePath m t =
      (G Ω L S u₀ N).statePath m
        ⟨t.1, t.2.1, t.2.2.trans (by exact_mod_cast h)⟩ := by
  rw [LeraySpectralCompactFamily.statePath_apply,
    LeraySpectralCompactFamily.statePath_apply]
  change openDomainEnergyToState Ω
      (OpenDomainConcreteBoundedPaths.energyBounded Ω
        L.toBoxEnergyL4Realization S m u₀ (Nat.cast_nonneg n) t) =
    openDomainEnergyToState Ω
      (OpenDomainConcreteBoundedPaths.energyBounded Ω
        L.toBoxEnergyL4Realization S m u₀ (Nat.cast_nonneg N)
          ⟨t.1, t.2.1, t.2.2.trans (by exact_mod_cast h)⟩)
  rw [OpenDomainConcreteBoundedPaths.openDomainEnergyToState_energyBounded,
    OpenDomainConcreteBoundedPaths.openDomainEnergyToState_energyBounded]
  change S.stateSynthesis m
      ((OpenDomainUnforcedUniformBounds.solution Ω L.toBoxEnergyL4Realization
        S m u₀ (Nat.cast_nonneg n)).toFun t) =
    S.stateSynthesis m
      ((OpenDomainUnforcedUniformBounds.solution Ω L.toBoxEnergyL4Realization
        S m u₀ (Nat.cast_nonneg N)).toFun t)
  exact congrArg (S.stateSynthesis m)
    (OpenDomainGalerkinHorizonCompatibility.solution_eqOn Ω
      L.toBoxEnergyL4Realization S m u₀ (Nat.cast_nonneg n)
      (by exact_mod_cast h) t.2)

theorem projectedPath_eqOn (n N m j : ℕ) (h : n ≤ N)
    (t : Icc (0 : ℝ) (n : ℝ)) :
    (G Ω L S u₀ n).projectedPath m j t =
      (G Ω L S u₀ N).projectedPath m j
        ⟨t.1, t.2.1, t.2.2.trans (by exact_mod_cast h)⟩ := by
  rw [LeraySpectralCompactFamily.projectedPath_apply,
    LeraySpectralCompactFamily.projectedPath_apply,
    statePath_eqOn Ω L S u₀ n N j h t]
  rfl

theorem ProjectedSubsequence.projectedLimit_eqOn
    (P : ProjectedSubsequence Ω L S u₀)
    (n N m : ℕ) (h : n ≤ N) (t : Icc (0 : ℝ) (n : ℝ)) :
    P.projectedLimit n m t =
      P.projectedLimit N m
        ⟨t.1, t.2.1, t.2.2.trans (by exact_mod_cast h)⟩ := by
  let tN : Icc (0 : ℝ) (N : ℝ) :=
    ⟨t.1, t.2.1, t.2.2.trans (by exact_mod_cast h)⟩
  have hleft : Tendsto
      (fun k => (G Ω L S u₀ n).projectedPath m (P.subseq.idx k) t)
      atTop (nhds (P.projectedLimit n m t)) := by
    simpa only [Function.comp_def] using
      ((BoundedContinuousFunction.lipschitz_eval_const t).continuous.tendsto
        (P.projectedLimit n m)).comp
        (P.projected_uniform n m)
  have hright : Tendsto
      (fun k => (G Ω L S u₀ N).projectedPath m (P.subseq.idx k) tN)
      atTop (nhds (P.projectedLimit N m tN)) := by
    simpa only [Function.comp_def] using
      ((BoundedContinuousFunction.lipschitz_eval_const tN).continuous.tendsto
        (P.projectedLimit N m)).comp
        (P.projected_uniform N m)
  have hsame (k : ℕ) := projectedPath_eqOn Ω L S u₀ n N m
    (P.subseq.idx k) h t
  have hleft' : Tendsto
      (fun k => (G Ω L S u₀ N).projectedPath m (P.subseq.idx k) tN)
      atTop (nhds (P.projectedLimit n m t)) := by
    simpa only [hsame] using hleft
  exact tendsto_nhds_unique hleft' hright

private theorem ProjectedSubsequence.representative_projected_inner
    (P : ProjectedSubsequence Ω L S u₀)
    (n m : ℕ) (t : Icc (0 : ℝ) (n : ℝ))
    (y : OpenDomainL2Sigma Ω) :
    ⟪P.projectedLimit n m t, y⟫_ℝ =
      ⟪(OpenDomainConcreteRepresentative.representative Ω L S u₀
        (Nat.cast_nonneg n) (P.toFiniteHorizon Ω L S u₀ n)).path t,
        (G Ω L S u₀ n).projector m y⟫_ℝ := by
  let R := OpenDomainConcreteRepresentative.representative Ω L S u₀
    (Nat.cast_nonneg n) (P.toFiniteHorizon Ω L S u₀ n)
  obtain ⟨rho, hrho, hweak⟩ := R.pointwise_weak_subsequence t
  have hp : Tendsto
      (fun j => (G Ω L S u₀ n).projectedPath m (P.subseq.idx (rho j)) t)
      atTop (nhds (P.projectedLimit n m t)) := by
    simpa only [Function.comp_def] using
      ((BoundedContinuousFunction.lipschitz_eval_const t).continuous.tendsto
        (P.projectedLimit n m)).comp
        ((P.projected_uniform n m).comp hrho.tendsto_atTop)
  have hi : Tendsto
      (fun j => ⟪(G Ω L S u₀ n).projectedPath m
        (P.subseq.idx (rho j)) t, y⟫_ℝ)
      atTop (nhds ⟪P.projectedLimit n m t, y⟫_ℝ) :=
    ((innerSLFlip ℝ y).continuous.tendsto (P.projectedLimit n m t)).comp hp
  have hself := OpenDomainConcreteRepresentative.projector_selfAdjoint Ω L S u₀
    (Nat.cast_nonneg n)
  have heq (j : ℕ) :
      ⟪(G Ω L S u₀ n).projectedPath m (P.subseq.idx (rho j)) t, y⟫_ℝ =
        ⟪(G Ω L S u₀ n).statePath (P.subseq.idx (rho j)) t,
          (G Ω L S u₀ n).projector m y⟫_ℝ := by
    rw [LeraySpectralCompactFamily.projectedPath_apply]
    exact hself m _ y
  have hi' : Tendsto
      (fun j => ⟪(G Ω L S u₀ n).statePath (P.subseq.idx (rho j)) t,
        (G Ω L S u₀ n).projector m y⟫_ℝ)
      atTop (nhds ⟪P.projectedLimit n m t, y⟫_ℝ) := by
    simpa only [heq] using hi
  exact tendsto_nhds_unique hi' (hweak ((G Ω L S u₀ n).projector m y))

theorem ProjectedSubsequence.weakStatePath_eqOn
    (P : ProjectedSubsequence Ω L S u₀)
    (n N : ℕ) (h : n ≤ N) (t : Icc (0 : ℝ) (n : ℝ)) :
    (OpenDomainConcreteRepresentative.representative Ω L S u₀
      (Nat.cast_nonneg n) (P.toFiniteHorizon Ω L S u₀ n)).path t =
      (OpenDomainConcreteRepresentative.representative Ω L S u₀
        (Nat.cast_nonneg N) (P.toFiniteHorizon Ω L S u₀ N)).path
        ⟨t.1, t.2.1, t.2.2.trans (by exact_mod_cast h)⟩ := by
  let A := OpenDomainConcreteRepresentative.representative Ω L S u₀
    (Nat.cast_nonneg n) (P.toFiniteHorizon Ω L S u₀ n)
  let B := OpenDomainConcreteRepresentative.representative Ω L S u₀
    (Nat.cast_nonneg N) (P.toFiniteHorizon Ω L S u₀ N)
  let tN : Icc (0 : ℝ) (N : ℝ) :=
    ⟨t.1, t.2.1, t.2.2.trans (by exact_mod_cast h)⟩
  apply ext_inner_right ℝ
  intro y
  have hcoord (m : ℕ) :
      ⟪A.path t, (G Ω L S u₀ n).projector m y⟫_ℝ =
        ⟪B.path tN, (G Ω L S u₀ n).projector m y⟫_ℝ := by
    calc
      ⟪A.path t, (G Ω L S u₀ n).projector m y⟫_ℝ =
          ⟪P.projectedLimit n m t, y⟫_ℝ :=
        (P.representative_projected_inner Ω L S u₀ n m t y).symm
      _ = ⟪P.projectedLimit N m tN, y⟫_ℝ := by
        rw [P.projectedLimit_eqOn Ω L S u₀ n N m h t]
      _ = ⟪B.path tN, (G Ω L S u₀ n).projector m y⟫_ℝ :=
        P.representative_projected_inner Ω L S u₀ N m tN y
  have hproj := (G Ω L S u₀ n).projector_tendsto y
  have hleft : Tendsto
      (fun m => ⟪A.path t, (G Ω L S u₀ n).projector m y⟫_ℝ)
      atTop (nhds ⟪A.path t, y⟫_ℝ) := by
    simpa only [innerSL_apply_apply] using
      ((innerSL ℝ (A.path t)).continuous.tendsto y).comp hproj
  have hright : Tendsto
      (fun m => ⟪B.path tN, (G Ω L S u₀ n).projector m y⟫_ℝ)
      atTop (nhds ⟪B.path tN, y⟫_ℝ) := by
    simpa only [innerSL_apply_apply] using
      ((innerSL ℝ (B.path tN)).continuous.tendsto y).comp hproj
  have hleft' : Tendsto
      (fun m => ⟪B.path tN, (G Ω L S u₀ n).projector m y⟫_ℝ)
      atTop (nhds ⟪A.path t, y⟫_ℝ) := by
    simpa only [hcoord] using hleft
  exact tendsto_nhds_unique hleft' hright

theorem exists_projectedSubsequence :
    Nonempty (ProjectedSubsequence Ω L S u₀) := by
  obtain ⟨SW⟩ := OpenDomainGlobalWeakCompactness.exists_strongWeakSubsequence
    Ω L S u₀
  let X : ℕ × ℕ → Type := fun i =>
    Icc (0 : ℝ) (i.1 : ℝ) →ᵇ OpenDomainL2Sigma Ω
  let f : ℕ → ∀ i, X i := fun k i =>
    (G Ω L S u₀ i.1).projectedPath i.2 (SW.subseq.idx k)
  let K : ∀ i, Set (X i) := fun i =>
    closure (Set.range
      ((G Ω L S u₀ i.1).projectedPath i.2))
  have hK : ∀ i, IsCompact (K i) := by
    intro i
    exact (G Ω L S u₀ i.1).projectedPath_compact_closure i.2
  have hf : ∀ k i, f k i ∈ K i := by
    intro k i
    exact subset_closure ⟨SW.subseq.idx k, rfl⟩
  obtain ⟨g, τ, hτ, hconv⟩ :=
    CountableCompactSubsequence.exists_coordinatewise_convergent f K hK hf
  let sub := SW.subseq.comp ⟨τ, hτ⟩
  let base : OpenDomainGlobalWeakCompactness.StrongWeakSubsequence Ω L S u₀ := {
    subseq := sub
    stateLimit := SW.stateLimit
    energyLimit := SW.energyLimit
    state_strong := by
      intro n
      simpa only [sub, ExtractedSubsequence.comp_idx, Function.comp_def] using
        (SW.state_strong n).comp hτ.tendsto_atTop
    energy_weak := by
      intro n w
      simpa only [sub, ExtractedSubsequence.comp_idx] using
        (SW.energy_weak n w).comp hτ.tendsto_atTop
  }
  refine ⟨{
    toStrongWeakSubsequence := base
    projectedLimit := fun n m => g (n, m)
    projected_uniform := ?_
  }⟩
  intro n m
  simpa only [base, sub, f, ExtractedSubsequence.comp_idx] using
    hconv (n, m)

end OpenDomainGlobalProjectedCompactness

end
