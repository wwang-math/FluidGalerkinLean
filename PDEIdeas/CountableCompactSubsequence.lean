import PDEIdeas.GalerkinL2Compactness

/-! A single subsequence converging in every coordinate of a countable compact product. -/

open Filter Set

namespace CountableCompactSubsequence

variable {ι : Type*} [Countable ι]
  {X : ι → Type*} [∀ i, PseudoMetricSpace (X i)]

theorem exists_coordinatewise_convergent
    (f : ℕ → ∀ i, X i)
    (K : ∀ i, Set (X i))
    (hK : ∀ i, IsCompact (K i))
    (hf : ∀ m i, f m i ∈ K i) :
    ∃ (g : ∀ i, X i) (σ : ℕ → ℕ), StrictMono σ ∧
      ∀ i, Tendsto (fun k => f (σ k) i) atTop (nhds (g i)) := by
  have hcompact : IsCompact (Set.pi Set.univ K) := isCompact_univ_pi hK
  have hmem (m : ℕ) : f m ∈ Set.pi Set.univ K := by
    intro i _
    exact hf m i
  obtain ⟨g, _, σ, hσ, hconv⟩ := hcompact.tendsto_subseq hmem
  refine ⟨g, σ, hσ, ?_⟩
  intro i
  simpa only [Function.comp_def] using
    ((continuous_apply i).tendsto g).comp hconv

end CountableCompactSubsequence
