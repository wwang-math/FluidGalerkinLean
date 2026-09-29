import PDEIdeas.OpenDomainGlobalProjectedCompactness
import PDEIdeas.OpenDomainLerayHopfStatement

/-! Finite-horizon solutions extracted from one subsequence on all horizons. -/

open InnerProductSpace MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace OpenDomainGlobalLocalSolutions

variable {Q : BoxIntegral.Box (Fin 2)} (Ω : OpenDomainInBox Q)
  (L : BoxLadyzhenskayaRealization Q)
  (S : OpenDomainCompactSpectralRepresentation Ω)
  (u₀ : OpenDomainL2Sigma Ω)

private def G (n : ℕ) :=
  OpenDomainConcreteCompactFamily.compactFamily Ω L S u₀ (Nat.cast_nonneg n)

def solution
    (D : OpenDomainGlobalProjectedCompactness.ProjectedSubsequence Ω L S u₀)
    (n : ℕ) :
    OpenDomainLerayHopfStatement.SolutionOn Ω L u₀ (Nat.cast_nonneg n) := by
  let P := D.toFiniteHorizon Ω L S u₀ n
  let E := OpenDomainConcreteEnergyLimit.energyLimit Ω L S u₀ (Nat.cast_nonneg n) P
  refine {
    energyPath := P.energyLimit
    statePath := E.path
    weaklyContinuous := E.inner_continuous
    state_eq_energy := ?_
    initial := E.initial
    energyInequality := E.energy_inequality
    weakEquation := ?_
  }
  · have h := OpenDomainWeakEnergySubsequence.stateLimit_ae_eq_embed_energyLimit
      (G := G Ω L S u₀ n) P.toStrongWeakSubsequence
    exact E.path_ae_eq_stateLimit.trans h
  · intro eta heta φ
    exact OpenDomainConcreteWeakEquation.tested_weak_equation Ω L S u₀
      (Nat.cast_nonneg n) P eta heta φ

theorem solution_statePath_eqOn
    (D : OpenDomainGlobalProjectedCompactness.ProjectedSubsequence Ω L S u₀)
    (n N : ℕ) (h : n ≤ N) (t : Icc (0 : ℝ) (n : ℝ)) :
    (solution Ω L S u₀ D n).statePath t =
      (solution Ω L S u₀ D N).statePath
        ⟨t.1, t.2.1, t.2.2.trans (by exact_mod_cast h)⟩ := by
  change
    (OpenDomainConcreteRepresentative.representative Ω L S u₀
      (Nat.cast_nonneg n) (D.toFiniteHorizon Ω L S u₀ n)).path t =
    (OpenDomainConcreteRepresentative.representative Ω L S u₀
      (Nat.cast_nonneg N) (D.toFiniteHorizon Ω L S u₀ N)).path
        ⟨t.1, t.2.1, t.2.2.trans (by exact_mod_cast h)⟩
  exact D.weakStatePath_eqOn Ω L S u₀ n N h t

end OpenDomainGlobalLocalSolutions

end
