import PDEIdeas.HilbertWeakCompactness
import Mathlib.Topology.Sequences

/-! Simultaneous weak convergence in countably many separable real Hilbert spaces. -/

open Filter Function InnerProductSpace Metric

noncomputable section

namespace CountableWeakHilbertSubsequence

variable (E : ℕ → Type*)
  [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℝ (E n)]
  [∀ n, CompleteSpace (E n)]
  [∀ n, TopologicalSpace.SeparableSpace (E n)]

private def ball (R : ℕ → ℝ) (n : ℕ) : Set (WeakDual ℝ (E n)) :=
  WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ (E n)) (R n)

omit [∀ n, CompleteSpace (E n)]
  [∀ n, TopologicalSpace.SeparableSpace (E n)] in
private theorem ball_compact (R : ℕ → ℝ) (n : ℕ) :
    IsCompact (ball E R n) :=
  WeakDual.isCompact_closedBall (0 : StrongDual ℝ (E n)) (R n)

private instance ballCompactSpace (R : ℕ → ℝ) (n : ℕ) :
    CompactSpace (ball E R n) :=
  isCompact_iff_compactSpace.mp (ball_compact E R n)

private instance ballMetrizableSpace (R : ℕ → ℝ) (n : ℕ) :
    TopologicalSpace.MetrizableSpace (ball E R n) :=
  WeakDual.metrizable_of_isCompact ℝ (E n) (ball E R n)
    (ball_compact E R n)

theorem exists_subsequence (x : ℕ → ∀ n, E n)
    (R : ℕ → ℝ) (hbound : ∀ m n, ‖x m n‖ ≤ R n) :
    ∃ (limit : ∀ n, E n) (σ : ℕ → ℕ), StrictMono σ ∧
      ∀ n (y : E n),
        Tendsto (fun k => ⟪x (σ k) n, y⟫_ℝ) atTop
          (nhds ⟪limit n, y⟫_ℝ) := by
  let f : ℕ → ∀ n, ball E R n := fun m n =>
    ⟨StrongDual.toWeakDual (InnerProductSpace.toDual ℝ (E n) (x m n)), by
      change dist (InnerProductSpace.toDual ℝ (E n) (x m n)) 0 ≤ R n
      simpa [dist_zero_right] using hbound m n⟩
  letI : CompactSpace (∀ n, ball E R n) := Pi.compactSpace
  obtain ⟨g, σ, hσ, hconv⟩ := SeqCompactSpace.tendsto_subseq f
  let limit : ∀ n, E n := fun n =>
    (InnerProductSpace.toDual ℝ (E n)).symm (WeakDual.toStrongDual (g n))
  refine ⟨limit, σ, hσ, ?_⟩
  intro n y
  have hEval : Continuous (fun h : ∀ n, ball E R n =>
      (h n : WeakDual ℝ (E n))) :=
    continuous_subtype_val.comp (continuous_apply n)
  have hcoord : Tendsto (fun k => (f (σ k) n : WeakDual ℝ (E n)))
      atTop (nhds (g n : WeakDual ℝ (E n))) := by
    simpa only [Function.comp_def] using (hEval.tendsto g).comp hconv
  have heval := ((WeakDual.eval_continuous y).tendsto
    (g n : WeakDual ℝ (E n))).comp hcoord
  simpa only [f, limit, Function.comp_apply,
    InnerProductSpace.toDual_apply_apply,
    InnerProductSpace.toDual_symm_apply] using heval

end CountableWeakHilbertSubsequence

end
