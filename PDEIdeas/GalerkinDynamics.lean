import PDEIdeas.GalerkinSystem
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

open Real InnerProductSpace

noncomputable section

section AbstractDynamics

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [GalerkinSystem H]

/-- The abstract right-hand side of the Galerkin ODE:
`U' = - \mathcal A U - \mathcal B(U,U) + F(t)`. -/
def abstractRHS (F : ℝ → H) (U : H) (t : ℝ) : H :=
  -(GalerkinSystem.linOp U) - GalerkinSystem.bilin U U + F t

/-- The cubic term contributes no energy in any `GalerkinSystem`. This is the
abstract form of the classical fluid identity
`\langle (u \cdot \nabla)u, u \rangle = 0`. -/
theorem abstract_trilinear_cancel (U : H) :
    ⟪GalerkinSystem.bilin U U, U⟫_ℝ = 0 :=
  GalerkinSystem.cancel U

/-- The abstract Galerkin vector field is locally Lipschitz on bounded sets.
This is the ODE-theoretic input needed for finite-dimensional Galerkin
well-posedness, independent of the concrete fluid system. -/
theorem abstract_galerkin_lipschitz
    (F : ℝ → H)
    (R : ℝ) (hR : 0 < R) :
    ∃ L : ℝ, 0 ≤ L ∧
    ∀ U V : H, ‖U‖ ≤ R → ‖V‖ ≤ R → ∀ t : ℝ,
      ‖abstractRHS F U t - abstractRHS F V t‖ ≤ L * ‖U - V‖ := by
  let A : H →L[ℝ] H := GalerkinSystem.linOp (H := H)
  let B : H →L[ℝ] (H →L[ℝ] H) := GalerkinSystem.bilin (H := H)
  use ‖A‖ + 2 * ‖B‖ * R
  refine ⟨add_nonneg (norm_nonneg A) (mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg B)) hR.le), ?_⟩
  intro U V hU hV t
  simp only [abstractRHS]
  rw [show -(A U) - B U U + F t - (-(A V) - B V V + F t) =
      -(A (U - V)) - (B U U - B V V) by
        simp [map_sub]
        abel]
  have hA : ‖A (U - V)‖ ≤ ‖A‖ * ‖U - V‖ := A.le_opNorm _
  have hBdecomp : B U U - B V V = B (U - V) U + B V (U - V) := by
    simp [map_sub]
  have hB :
      ‖B U U - B V V‖ ≤ ‖B‖ * (‖U‖ + ‖V‖) * ‖U - V‖ := by
    rw [hBdecomp]
    have h1 :
        ‖B (U - V) U‖ ≤ ‖B‖ * ‖U - V‖ * ‖U‖ :=
      (B (U - V)).le_opNorm U |>.trans
        (mul_le_mul_of_nonneg_right (B.le_opNorm _) (norm_nonneg _))
    have h2 :
        ‖B V (U - V)‖ ≤ ‖B‖ * ‖V‖ * ‖U - V‖ :=
      (B V).le_opNorm _ |>.trans
        (mul_le_mul_of_nonneg_right (B.le_opNorm _) (norm_nonneg _))
    calc
      ‖B (U - V) U + B V (U - V)‖
          ≤ ‖B (U - V) U‖ + ‖B V (U - V)‖ := norm_add_le _ _
      _ ≤ ‖B‖ * ‖U - V‖ * ‖U‖ + ‖B‖ * ‖V‖ * ‖U - V‖ := by
          linarith
      _ = ‖B‖ * (‖U‖ + ‖V‖) * ‖U - V‖ := by ring
  calc
    ‖-(A (U - V)) - (B U U - B V V)‖
        ≤ ‖A (U - V)‖ + ‖B U U - B V V‖ := by
            rw [← norm_neg (A (U - V))]
            exact norm_sub_le _ _
    _ ≤ ‖A‖ * ‖U - V‖ + ‖B‖ * (‖U‖ + ‖V‖) * ‖U - V‖ := by
          exact add_le_add hA hB
    _ ≤ (‖A‖ + 2 * ‖B‖ * R) * ‖U - V‖ := by
          have hUV : ‖U‖ + ‖V‖ ≤ 2 * R := by
            linarith
          have hBterm :
              ‖B‖ * (‖U‖ + ‖V‖) * ‖U - V‖ ≤ ‖B‖ * (2 * R) * ‖U - V‖ := by
            gcongr
          calc
            ‖A‖ * ‖U - V‖ + ‖B‖ * (‖U‖ + ‖V‖) * ‖U - V‖
                ≤ ‖A‖ * ‖U - V‖ + ‖B‖ * (2 * R) * ‖U - V‖ := by
                    gcongr
            _ = (‖A‖ + 2 * ‖B‖ * R) * ‖U - V‖ := by ring

end AbstractDynamics
