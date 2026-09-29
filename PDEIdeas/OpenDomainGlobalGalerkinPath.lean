import PDEIdeas.OpenDomainGalerkinHorizonCompatibility

/-! A horizon-compatible unforced Galerkin path at each spectral level. -/

open Set

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace OpenDomainGlobalGalerkinPath

variable {Q : BoxIntegral.Box (Fin 2)} (Ω : OpenDomainInBox Q)
  (R : BoxEnergyL4Realization Q)
  (S : OpenDomainCompactSpectralRepresentation Ω)
  (m : ℕ) (u₀ : OpenDomainL2Sigma Ω)

/-- The coefficient path is read from any finite horizon extending its time. -/
def path (t : ℝ) : S.stateSpace m :=
  (OpenDomainUnforcedUniformBounds.solution Ω R S m u₀
    (Nat.cast_nonneg (Nat.ceil t))).toFun t

theorem path_eq_solution {T : ℝ} (hT : 0 ≤ T)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    path Ω R S m u₀ t =
      (OpenDomainUnforcedUniformBounds.solution Ω R S m u₀ hT).toFun t := by
  let n := Nat.ceil t
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have htn : t ∈ Icc (0 : ℝ) (n : ℝ) := ⟨ht.1, Nat.le_ceil t⟩
  rcases le_total T (n : ℝ) with h | h
  · exact (OpenDomainGalerkinHorizonCompatibility.solution_eqOn Ω R S m u₀
      hT h ht).symm
  · exact OpenDomainGalerkinHorizonCompatibility.solution_eqOn Ω R S m u₀
      hn h htn

theorem path_initial : path Ω R S m u₀ 0 =
    OpenDomainUnforcedUniformBounds.stateHeadProjection S m u₀ := by
  let hT : (0 : ℝ) ≤ 0 := le_rfl
  rw [path_eq_solution Ω R S m u₀ hT (t := 0) ⟨le_rfl, le_rfl⟩]
  exact (OpenDomainUnforcedUniformBounds.solution Ω R S m u₀ hT).initial

theorem continuousOn_path {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (path Ω R S m u₀) (Icc (0 : ℝ) T) :=
  (OpenDomainUnforcedUniformBounds.solution Ω R S m u₀ hT).continuousOn.congr
    (fun _ ht => path_eq_solution Ω R S m u₀ hT ht)

theorem norm_path_le {T : ℝ} (hT : 0 ≤ T)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ‖path Ω R S m u₀ t‖ ≤ ‖u₀‖ := by
  rw [path_eq_solution Ω R S m u₀ hT ht]
  exact OpenDomainUnforcedUniformBounds.norm_solution_le Ω R S m u₀ hT ht

end OpenDomainGlobalGalerkinPath

end
