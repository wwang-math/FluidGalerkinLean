import PDEIdeas.OpenDomainLerayHopfStatement

/-! Every bounded open planar set admits an enclosing rectangle. -/

open Set

noncomputable section

namespace OpenDomainBoundedEnclosure

theorem exists_box (U : Set (Fin 2 → ℝ))
    (hU : Bornology.IsBounded U) :
    ∃ Q : BoxIntegral.Box (Fin 2),
      U ⊆ interior (BoxIntegral.Box.Icc Q) := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hU
  let R : ℝ := max 1 (C + 1)
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let Q : BoxIntegral.Box (Fin 2) :=
    ⟨fun _ => -R, fun _ => R, fun _ => by linarith⟩
  refine ⟨Q, ?_⟩
  intro x hx
  rw [mem_interior_boxIcc_iff]
  intro i
  have hcoord : |x i| ≤ C := by
    calc
      |x i| = ‖x i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖x‖ := norm_le_pi_norm x i
      _ ≤ C := hC x hx
  have hlt : |x i| < R := by
    have : C + 1 ≤ R := le_max_right _ _
    linarith
  simpa only [Q] using (abs_lt.mp hlt)

theorem exists_openDomainInBox (U : Set (Fin 2 → ℝ))
    (hOpen : IsOpen U) (hBound : Bornology.IsBounded U) :
    ∃ (Q : BoxIntegral.Box (Fin 2)) (Ω : OpenDomainInBox Q),
      Ω.carrier = U := by
  obtain ⟨Q, hQ⟩ := exists_box U hBound
  exact ⟨Q, ⟨U, hOpen, hQ⟩, rfl⟩

/-- A bounded open planar set admits finite-horizon unforced solutions for
every initial state in its solenoidal pivot space. -/
theorem exists_finite_horizon_solutions (U : Set (Fin 2 → ℝ))
    (hOpen : IsOpen U) (hBound : Bornology.IsBounded U) :
    ∃ (Q : BoxIntegral.Box (Fin 2)) (Ω : OpenDomainInBox Q),
      Ω.carrier = U ∧
      ∀ (u₀ : OpenDomainL2Sigma Ω) (T : ℝ) (hT : 0 ≤ T),
        Nonempty (OpenDomainLerayHopfStatement.SolutionOn Ω
          (boxLadyzhenskayaRealization Q) u₀ hT) := by
  obtain ⟨Q, Ω, hΩ⟩ := exists_openDomainInBox U hOpen hBound
  refine ⟨Q, Ω, hΩ, ?_⟩
  intro u₀ T hT
  exact OpenDomainLerayHopfStatement.exists_solution_on_canonical Ω u₀ hT

end OpenDomainBoundedEnclosure

end
