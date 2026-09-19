import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

section ScalarAbsorption

/-- Scalar helper: absorb the dissipative term after combining Young's
inequality with the energy identity. Keeping this as a real-variable lemma
prevents the main a priori theorem from asking `linarith` to reason directly
about opaque interval integrals. -/
lemma apriori_scalar_bound
    (u u0 work forcing diss : ℝ)
    (hEnergy : u + 2 * diss = u0 + 2 * work)
    (hYoung : 2 * work ≤ forcing + diss)
    (hDiss : 0 ≤ diss) :
    u ≤ u0 + forcing := by
  have hEnergy' := congrArg (fun x : ℝ => x - 2 * diss) hEnergy
  ring_nf at hEnergy'
  have hYoung' := add_le_add_right hYoung (-2 * diss)
  ring_nf at hYoung'
  have hEnergy'' : u = u0 + (2 * work - 2 * diss) := by
    calc
      u = -(diss * 2) + u0 + work * 2 := hEnergy'
      _ = u0 + (2 * work - 2 * diss) := by ring
  have hYoung'' : 2 * work - 2 * diss ≤ forcing - diss := by
    calc
      2 * work - 2 * diss = -(diss * 2) + work * 2 := by ring
      _ ≤ -diss + forcing := hYoung'
      _ = forcing - diss := by ring
  have hDrop : forcing - diss ≤ forcing := by
    simpa using sub_le_self forcing hDiss
  calc
    u = u0 + (2 * work - 2 * diss) := hEnergy''
    _ ≤ u0 + (forcing - diss) := by
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hYoung'' u0
    _ ≤ u0 + forcing := by
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hDrop u0

/-- Absorption with one copy of the dissipative term retained. -/
lemma apriori_scalar_bound_with_dissipation
    (u u0 work forcing diss : ℝ)
    (hEnergy : u + 2 * diss = u0 + 2 * work)
    (hYoung : 2 * work ≤ forcing + diss) :
    u + diss ≤ u0 + forcing := by
  linarith

/-- Scalar helper in the one-time-at-`T` setting, written separately so the
fixed-time a priori theorem can share the same small arithmetic argument. -/
lemma apriori_scalar_bound_atTime
    (u u0 work forcing diss : ℝ)
    (hEnergy : u + 2 * diss = u0 + 2 * work)
    (hYoung : 2 * work ≤ forcing + diss)
    (hDiss : 0 ≤ diss) :
    u ≤ u0 + forcing :=
  apriori_scalar_bound u u0 work forcing diss hEnergy hYoung hDiss

end ScalarAbsorption
