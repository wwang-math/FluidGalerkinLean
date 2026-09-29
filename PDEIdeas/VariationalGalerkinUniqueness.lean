import PDEIdeas.ClosedIntervalRightDerivative

/-! Uniqueness of bounded coefficient trajectories on overlapping horizons. -/

open Set Metric

noncomputable section

namespace VariationalGalerkinProblem

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [CompleteSpace W] (P : VariationalGalerkinProblem W)
  {T₁ T₂ : ℝ} (hT₁ : 0 ≤ T₁) (hT₂ : T₁ ≤ T₂)
  (u : P.LocalSolutionOn (⟨0, le_rfl, hT₁⟩ : Icc (0 : ℝ) T₁))
  (v : P.LocalSolutionOn (⟨0, le_rfl, hT₁.trans hT₂⟩ : Icc (0 : ℝ) T₂))

theorem eqOn_of_bounded (R : ℝ) (hR : 0 ≤ R)
    (hu : ∀ t ∈ Icc (0 : ℝ) T₁, ‖u.toFun t‖ ≤ R)
    (hv : ∀ t ∈ Icc (0 : ℝ) T₁, ‖v.toFun t‖ ≤ R) :
    EqOn u.toFun v.toFun (Icc (0 : ℝ) T₁) := by
  let K := P.rhsLipschitzConstant R hR
  apply ODE_solution_unique_of_mem_Icc_right
    (K := K) (s := fun _ => closedBall (0 : W) R)
    (v := fun t x => P.rhs t x)
  · intro t _
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro x hx y hy
    have hxR : ‖x‖ ≤ R := by simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    have hyR : ‖y‖ ≤ R := by simpa [Metric.mem_closedBall, dist_eq_norm] using hy
    simpa [K, rhsLipschitzConstant, dist_eq_norm] using
      P.rhs_lipschitz_on_norm_ball R t hxR hyR
  · exact u.continuousOn
  · intro t ht
    exact ClosedIntervalRightDerivative.of_Icc ht
      (u.hasDerivWithinAt t ⟨ht.1, ht.2.le⟩)
  · intro t ht
    simpa [Metric.mem_closedBall, dist_eq_norm] using
      hu t ⟨ht.1, ht.2.le⟩
  · exact v.continuousOn.mono (Icc_subset_Icc_right hT₂)
  · intro t ht
    exact ClosedIntervalRightDerivative.of_Icc
      ⟨ht.1, lt_of_lt_of_le ht.2 hT₂⟩
      (v.hasDerivWithinAt t ⟨ht.1, (ht.2.le.trans hT₂)⟩)
  · intro t ht
    simpa [Metric.mem_closedBall, dist_eq_norm] using
      hv t ⟨ht.1, ht.2.le⟩
  · exact u.initial.trans v.initial.symm

end VariationalGalerkinProblem

end
