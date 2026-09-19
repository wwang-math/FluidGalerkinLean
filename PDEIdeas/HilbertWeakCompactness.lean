import PDEIdeas.AubinLionsInterface
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.WeakDual

/-!
# Sequential weak compactness in separable real Hilbert spaces

Sequential Banach--Alaoglu applied through the Frechet--Riesz equivalence
gives a strict weakly convergent subsequence of every bounded Hilbert-space
sequence.  The result is stated directly in terms of inner products, which is
the form used by the Galerkin limit passage.
-/

open Filter Function InnerProductSpace Metric

noncomputable section

namespace ExtractedSubsequence

/-- Composition of two strict extractions. -/
def comp (outer inner : ExtractedSubsequence) : ExtractedSubsequence where
  idx := outer.idx ∘ inner.idx
  strictMono_idx := outer.strictMono_idx.comp inner.strictMono_idx

@[simp]
theorem comp_idx (outer inner : ExtractedSubsequence) (k : ℕ) :
    (outer.comp inner).idx k = outer.idx (inner.idx k) :=
  rfl

end ExtractedSubsequence

/-- A strict subsequence converging weakly against every Hilbert-space test
vector. -/
structure WeakHilbertSubsequence
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : ℕ → E) where
  subseq : ExtractedSubsequence
  limit : E
  inner_tendsto : ∀ y : E,
    Tendsto (fun k => ⟪x (subseq.idx k), y⟫_ℝ)
      atTop (nhds ⟪limit, y⟫_ℝ)

namespace WeakHilbertSubsequence

/-- A weak Hilbert-space limit inherits the uniform norm bound of the
extracted sequence. -/
theorem limit_norm_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x : ℕ → E} (W : WeakHilbertSubsequence x)
    (R : ℝ) (hbound : ∀ n, ‖x n‖ ≤ R) :
    ‖W.limit‖ ≤ R := by
  have hsq : ‖W.limit‖ ^ 2 ≤ R * ‖W.limit‖ := by
    rw [← real_inner_self_eq_norm_sq]
    apply le_of_tendsto (W.inner_tendsto W.limit)
    filter_upwards with k
    calc
      ⟪x (W.subseq.idx k), W.limit⟫_ℝ ≤
          ‖x (W.subseq.idx k)‖ * ‖W.limit‖ :=
        real_inner_le_norm _ _
      _ ≤ R * ‖W.limit‖ :=
        mul_le_mul_of_nonneg_right
          (hbound (W.subseq.idx k)) (norm_nonneg _)
  by_cases hzero : ‖W.limit‖ = 0
  · rw [hzero]
    exact (norm_nonneg (x 0)).trans (hbound 0)
  · have hpos : 0 < ‖W.limit‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    nlinarith [hsq]

end WeakHilbertSubsequence

/-- Every uniformly bounded sequence in a separable real Hilbert space has a
strict weakly convergent subsequence. -/
theorem exists_weakHilbertSubsequence
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    (x : ℕ → E) (R : ℝ) (hbound : ∀ n, ‖x n‖ ≤ R) :
    Nonempty (WeakHilbertSubsequence x) := by
  let xDual : ℕ → WeakDual ℝ E := fun n =>
    StrongDual.toWeakDual (InnerProductSpace.toDual ℝ E (x n))
  have hxDual : ∀ n,
      xDual n ∈ WeakDual.toStrongDual ⁻¹'
        closedBall (0 : StrongDual ℝ E) R := by
    intro n
    change dist (InnerProductSpace.toDual ℝ E (x n)) 0 ≤ R
    simpa [dist_zero_right] using hbound n
  obtain ⟨f, _hf, phi, hphi, hconv⟩ :=
    (WeakDual.isSeqCompact_closedBall ℝ E
      (0 : StrongDual ℝ E) R) hxDual
  let u : E :=
    (InnerProductSpace.toDual ℝ E).symm (WeakDual.toStrongDual f)
  refine ⟨{
    subseq := ⟨phi, hphi⟩
    limit := u
    inner_tendsto := ?_
  }⟩
  intro y
  have heval := ((WeakDual.eval_continuous y).tendsto f).comp hconv
  simpa only [xDual, Function.comp_apply,
    InnerProductSpace.toDual_apply_apply,
    u, InnerProductSpace.toDual_symm_apply] using heval

end
