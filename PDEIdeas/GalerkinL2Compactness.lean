import PDEIdeas.GalerkinStrongCompactness
import PDEIdeas.IntervalL2Holder
import PDEIdeas.VariationalGalerkin
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Topology.MetricSpace.Holder

open Filter Function InnerProductSpace Metric Set
open scoped NNReal

noncomputable section

/-!
# Strong compactness in time-space L2

The compact-approximation argument below is the functional-analytic core of
the spectral Galerkin version of Aubin--Lions.  A sequence is precompact when
it is uniformly approximable by relatively compact finite-mode families.
-/

/-- A sequence uniformly approximable by relatively compact families. -/
structure CompactApproximationSequence
    (X : Type*) [PseudoMetricSpace X] where
  sequence : ℕ → X
  approximation : ℕ → ℕ → X
  approximation_compact :
    ∀ m, IsCompact (closure (Set.range (approximation m)))
  tail : ∀ ε > 0, ∃ m, ∀ n, dist (sequence n) (approximation m n) < ε

/-- A genuinely extracted strongly convergent subsequence in a metric space. -/
structure StrongMetricSubsequence
    {X : Type*} [TopologicalSpace X]
    (x : ℕ → X) where
  subseq : ExtractedSubsequence
  limit : X
  converges : Tendsto (x ∘ subseq.idx) atTop (nhds limit)

namespace CompactApproximationSequence

variable {X : Type*} [PseudoMetricSpace X]

/-- Uniform approximation by compact families makes the original range
totally bounded. -/
theorem totallyBounded_range (S : CompactApproximationSequence X) :
    TotallyBounded (Set.range S.sequence) := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨m, hm⟩ := S.tail (ε / 2) (half_pos hε)
  have htb := (S.approximation_compact m).totallyBounded
  rw [Metric.totallyBounded_iff] at htb
  obtain ⟨t, htfin, htcover⟩ := htb (ε / 2) (half_pos hε)
  refine ⟨t, htfin, ?_⟩
  rintro x ⟨n, rfl⟩
  have ha : S.approximation m n ∈ closure (Set.range (S.approximation m)) :=
    subset_closure ⟨n, rfl⟩
  rcases Set.mem_iUnion₂.mp (htcover ha) with ⟨y, hy, hmy⟩
  apply Set.mem_iUnion₂.mpr
  refine ⟨y, hy, ?_⟩
  rw [mem_ball] at hmy ⊢
  calc
    dist (S.sequence n) y
        ≤ dist (S.sequence n) (S.approximation m n)
            + dist (S.approximation m n) y := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hm n) hmy
    _ = ε := by ring

variable [CompleteSpace X]

/-- The closure of a compactly approximable sequence is compact. -/
theorem compact_closure_range (S : CompactApproximationSequence X) :
    IsCompact (closure (Set.range S.sequence)) :=
  S.totallyBounded_range.closure.isCompact_of_isClosed isClosed_closure

/-- Compact approximation produces, rather than assumes, a strict convergent
subsequence. -/
theorem exists_stronglyConvergent_subsequence
    (S : CompactApproximationSequence X) :
    Nonempty (StrongMetricSubsequence S.sequence) := by
  obtain ⟨x, _hx, φ, hφ, hconv⟩ :=
    S.compact_closure_range.tendsto_subseq
      (x := S.sequence)
      (fun n => subset_closure ⟨n, rfl⟩)
  exact ⟨{
    subseq := ⟨φ, hφ⟩
    limit := x
    converges := hconv
  }⟩

end CompactApproximationSequence

section UniformHolderFamily

variable {ι X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

/-- A subtype of function-like objects with one positive-exponent Hölder
modulus is equicontinuous. -/
theorem equicontinuous_subtype_of_uniform_holder
    {A : Type*} [CoeFun A (fun _ => X → Y)]
    (S : Set A) (C r : ℝ≥0) (hr : 0 < r)
    (hS : ∀ f : S, HolderWith C r (f : X → Y)) :
    Equicontinuous ((↑) : S → X → Y) := by
  let modulus : ℝ → ℝ := fun d => (C : ℝ) * d ^ (r : ℝ)
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hmodulus : Tendsto modulus (nhds 0) (nhds 0) := by
    have hcont : Continuous modulus :=
      continuous_const.mul (Real.continuous_rpow_const r.coe_nonneg)
    have hzero : modulus 0 = 0 := by
      simp only [modulus, Real.zero_rpow hrR.ne', mul_zero]
    have ht : Tendsto modulus (nhds 0) (nhds (modulus 0)) :=
      hcont.continuousAt
    rw [hzero] at ht
    exact ht
  apply Metric.equicontinuous_of_continuity_modulus modulus hmodulus
  intro x y f
  exact (hS f).dist_le x y

end UniformHolderFamily

section QuadraticLp

open MeasureTheory
open scoped ENNReal

variable {α H N : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup N] [NormedSpace ℝ N]

namespace ContinuousLinearMap

/-- The pointwise diagonal of a continuous bilinear map, acting from
`L²(α;H)` to `L¹(α;N)`. -/
noncomputable def quadraticLp
    (B : H →L[ℝ] H →L[ℝ] N)
    (u : Lp H (2 : ℝ≥0∞) μ) : Lp N (1 : ℝ≥0∞) μ :=
  B.holder (1 : ℝ≥0∞) u u

/-- Quantitative `L² × L² → L¹` continuity of a quadratic observable. -/
theorem norm_quadraticLp_sub_le
    (B : H →L[ℝ] H →L[ℝ] N)
    (u v : Lp H (2 : ℝ≥0∞) μ) :
    ‖B.quadraticLp u - B.quadraticLp v‖
      ≤ ‖B‖ * (‖u‖ + ‖v‖) * ‖u - v‖ := by
  let L :
      Lp H (2 : ℝ≥0∞) μ →L[ℝ]
        Lp H (2 : ℝ≥0∞) μ →L[ℝ] Lp N (1 : ℝ≥0∞) μ :=
    B.holderL μ (2 : ℝ≥0∞) (2 : ℝ≥0∞) (1 : ℝ≥0∞)
  have hidentity :
      L u u - L v v = L (u - v) u + L v (u - v) := by
    calc
      L u u - L v v = (L u u - L v u) + (L v u - L v v) := by abel
      _ = L (u - v) u + L v (u - v) := by
        rw [map_sub, map_sub, ContinuousLinearMap.sub_apply]
  change ‖L u u - L v v‖ ≤ _
  rw [hidentity]
  calc
    ‖L (u - v) u + L v (u - v)‖
        ≤ ‖L (u - v) u‖ + ‖L v (u - v)‖ := norm_add_le _ _
    _ ≤ ‖B‖ * ‖u - v‖ * ‖u‖
          + ‖B‖ * ‖v‖ * ‖u - v‖ := by
        exact add_le_add
          (B.norm_holder_apply_apply_le (u - v) u)
          (B.norm_holder_apply_apply_le v (u - v))
    _ = ‖B‖ * (‖u‖ + ‖v‖) * ‖u - v‖ := by ring

/-- The quadratic `L² → L¹` observable induced by a continuous bilinear map
is continuous. -/
theorem continuous_quadraticLp
    (B : H →L[ℝ] H →L[ℝ] N) :
    Continuous (B.quadraticLp (μ := μ)) := by
  let L :
      Lp H (2 : ℝ≥0∞) μ →L[ℝ]
        Lp H (2 : ℝ≥0∞) μ →L[ℝ] Lp N (1 : ℝ≥0∞) μ :=
    B.holderL μ (2 : ℝ≥0∞) (2 : ℝ≥0∞) (1 : ℝ≥0∞)
  change Continuous (fun u => L u u)
  exact L.continuous₂.comp (continuous_id.prodMk continuous_id)

end ContinuousLinearMap

/-- Strong `L²` convergence along a strict subsequence yields strong `L¹`
convergence of every continuous quadratic observable. -/
theorem StrongMetricSubsequence.quadraticLp_tendsto
    {x : ℕ → Lp H (2 : ℝ≥0∞) μ}
    (S : StrongMetricSubsequence x)
    (B : H →L[ℝ] H →L[ℝ] N) :
    Tendsto
      (fun k => B.quadraticLp (x (S.subseq.idx k)))
      atTop (nhds (B.quadraticLp S.limit)) :=
  B.continuous_quadraticLp.continuousAt.tendsto.comp S.converges

end QuadraticLp

section CompactEmbeddingTail

variable {V H : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- A compact embedding converts strong convergence of uniformly
contractive ambient projectors into operator-norm convergence of the
projected embedding. -/
theorem compactEmbedding_projectorTail_tendsto
    (embed : V →L[ℝ] H) (hembed : IsCompactOperator embed)
    (projector : ℕ → H →L[ℝ] H)
    (hcontractive : ∀ n, ‖projector n‖ ≤ 1)
    (hstrong : ∀ x, Tendsto (fun n => projector n x) atTop (nhds x)) :
    Tendsto
      (fun n => ‖embed - (projector n).comp embed‖)
      atTop (nhds 0) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    exact Filter.Eventually.of_forall fun n =>
      ha.trans_le (norm_nonneg (embed - (projector n).comp embed))
  · intro ε hε
    let δ : ℝ := ε / 4
    have hδ : 0 < δ := div_pos hε (by norm_num)
    obtain ⟨K, hKcompact, himage⟩ :=
      hembed.image_closedBall_subset_compact 1
    obtain ⟨t, _htK, htfinite, hcover⟩ :=
      Metric.finite_approx_of_totallyBounded
        hKcompact.totallyBounded δ hδ
    have hcenters :
        ∀ᶠ n in atTop, ∀ z ∈ t, dist (projector n z) z < δ := by
      rw [htfinite.eventually_all]
      intro z hz
      exact Metric.tendsto_nhds.1 (hstrong z) δ hδ
    filter_upwards [hcenters] with n hn
    have hunit :
        ∀ x : V, ‖x‖ = 1 →
          ‖(embed - (projector n).comp embed) x‖ ≤ 3 * δ := by
      intro x hx
      have hembedK : embed x ∈ K := by
        apply himage
        refine ⟨x, ?_, rfl⟩
        exact mem_closedBall_zero_iff.mpr hx.le
      rcases Set.mem_iUnion₂.mp (hcover hembedK) with ⟨z, hzt, hz⟩
      have hyz : dist (embed x) z < δ := by
        simpa only [mem_ball] using hz
      have hcenter : dist z (projector n z) < δ := by
        simpa only [dist_comm] using hn z hzt
      have hprojected :
          dist (projector n z) (projector n (embed x)) < δ := by
        calc
          dist (projector n z) (projector n (embed x))
              ≤ ‖projector n‖ * dist z (embed x) :=
            (projector n).dist_le_opNorm z (embed x)
          _ ≤ 1 * dist z (embed x) := by
            gcongr
            exact hcontractive n
          _ < 1 * δ := by
            simpa only [one_mul, dist_comm] using hyz
          _ = δ := one_mul δ
      have hpath :
          dist (embed x) (projector n (embed x)) < 3 * δ := by
        calc
          dist (embed x) (projector n (embed x))
              ≤ dist (embed x) z + dist z (projector n z)
                  + dist (projector n z) (projector n (embed x)) := by
            calc
              dist (embed x) (projector n (embed x))
                  ≤ dist (embed x) z
                      + dist z (projector n (embed x)) :=
                    dist_triangle _ _ _
              _ ≤ dist (embed x) z
                    + (dist z (projector n z)
                      + dist (projector n z) (projector n (embed x))) := by
                    gcongr
                    exact dist_triangle _ _ _
              _ = dist (embed x) z + dist z (projector n z)
                    + dist (projector n z) (projector n (embed x)) := by ring
          _ < δ + δ + δ := by gcongr
          _ = 3 * δ := by ring
      have happly :
          (embed - (projector n).comp embed) x =
            embed x - projector n (embed x) := by simp
      rw [happly, ← dist_eq_norm]
      exact hpath.le
    have hop : ‖embed - (projector n).comp embed‖ ≤ 3 * δ :=
      ContinuousLinearMap.opNorm_le_of_unit_norm
        (mul_nonneg (by norm_num) hδ.le) hunit
    exact hop.trans_lt (by dsimp [δ]; linarith)

/-- Compact embeddings have vanishing tails along any contractive Galerkin
projector sequence. -/
theorem GalerkinProjectorSequence.compactEmbedding_tail_tendsto
    (P : GalerkinProjectorSequence H)
    (embed : V →L[ℝ] H) (hembed : IsCompactOperator embed)
    (hcontractive : ∀ n, ‖P.proj n‖ ≤ 1) :
    Tendsto (fun n => ‖embed - (P.proj n).comp embed‖) atTop (nhds 0) :=
  compactEmbedding_projectorTail_tendsto
    embed hembed P.proj hcontractive P.proj_tendsto

/-- The Hilbert-basis Galerkin projectors approximate every compact
embedding in operator norm. -/
theorem GalerkinProjectorSequence.HilbertBasis.compactEmbedding_tail_tendsto
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ℕ ℝ H)
    (embed : V →L[ℝ] H) (hembed : IsCompactOperator embed) :
    Tendsto
      (fun n => ‖embed -
        (GalerkinProjectorSequence.partialProjection b n).comp embed‖)
      atTop (nhds 0) :=
  compactEmbedding_projectorTail_tendsto embed hembed
    (GalerkinProjectorSequence.partialProjection b)
    (GalerkinProjectorSequence.partialProjection_norm_le b)
    (GalerkinProjectorSequence.partialProjection_tendsto b)

end CompactEmbeddingTail

open BoundedContinuousFunction MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

section LeraySpectral

variable {I V H : Type*}
    [PseudoMetricSpace I] [CompactSpace I]
    [MeasurableSpace I] [BorelSpace I] [SecondCountableTopology I]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    {μ : Measure I} [IsFiniteMeasure μ]

/-- Ambient state path obtained from a source-space lift. -/
noncomputable def lerayStatePath
    (embed : V →L[ℝ] H) (lift : ℕ → I →ᵇ V) (n : ℕ) : I →ᵇ H :=
  embed.compLeftContinuousBounded I (lift n)

/-- Finite-mode projection of a lifted state path. -/
noncomputable def lerayProjectedPath
    (embed : V →L[ℝ] H) (projector : ℕ → H →L[ℝ] H)
    (lift : ℕ → I →ᵇ V) (m n : ℕ) : I →ᵇ H :=
  (projector m).compLeftContinuousBounded I (lerayStatePath embed lift n)

/-- Leray-scale compactness data.  The `L²(I;V)` bound controls spatial
tails, the `L∞(I;H)` bound controls each finite-mode range, and finite-mode
equicontinuity supplies Arzelà--Ascoli compactness. -/
structure LeraySpectralCompactFamily where
  embed : V →L[ℝ] H
  embed_compact : IsCompactOperator embed
  projector : ℕ → H →L[ℝ] H
  projector_compact : ∀ m, IsCompactOperator (projector m)
  projector_contractive : ∀ m, ‖projector m‖ ≤ 1
  projector_tendsto : ∀ x,
    Tendsto (fun m => projector m x) atTop (nhds x)
  lift : ℕ → I →ᵇ V
  stateRadius : ℝ
  state_bound : ∀ n t, ‖embed (lift n t)‖ ≤ stateRadius
  liftLpRadius : ℝ
  liftLpRadius_nonneg : 0 ≤ liftLpRadius
  liftLp_bound : ∀ n,
    ‖BoundedContinuousFunction.toLp (2 : ℝ≥0∞) μ ℝ (lift n)‖ ≤ liftLpRadius
  projected_equicontinuous : ∀ m,
    Equicontinuous
      ((↑) : Set.range (lerayProjectedPath embed projector lift m) → I → H)

namespace LeraySpectralCompactFamily

variable {I V H : Type*}
    [PseudoMetricSpace I] [CompactSpace I]
    [MeasurableSpace I] [BorelSpace I] [SecondCountableTopology I]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {μ : Measure I} [IsFiniteMeasure μ]

/-- Canonical spectral compactness data generated by a countable Hilbert
basis.  Finite-rank compactness, projector contractivity, and strong
convergence are discharged by the Hilbert-basis construction. -/
noncomputable def ofHilbertBasis
    (basis : HilbertBasis ℕ ℝ H)
    (embed : V →L[ℝ] H) (embed_compact : IsCompactOperator embed)
    (lift : ℕ → I →ᵇ V)
    (stateRadius : ℝ)
    (state_bound : ∀ n t, ‖embed (lift n t)‖ ≤ stateRadius)
    (liftLpRadius : ℝ) (liftLpRadius_nonneg : 0 ≤ liftLpRadius)
    (liftLp_bound : ∀ n,
      ‖BoundedContinuousFunction.toLp (2 : ℝ≥0∞) μ ℝ (lift n)‖
        ≤ liftLpRadius)
    (projected_equicontinuous : ∀ m,
      Equicontinuous
        ((↑) : Set.range
          (lerayProjectedPath embed
            (GalerkinProjectorSequence.partialProjection basis) lift m) →
              I → H)) :
    LeraySpectralCompactFamily (I := I) (V := V) (H := H) (μ := μ) where
  embed := embed
  embed_compact := embed_compact
  projector := GalerkinProjectorSequence.partialProjection basis
  projector_compact :=
    GalerkinProjectorSequence.partialProjection_isCompactOperator basis
  projector_contractive :=
    GalerkinProjectorSequence.partialProjection_norm_le basis
  projector_tendsto :=
    GalerkinProjectorSequence.partialProjection_tendsto basis
  lift := lift
  stateRadius := stateRadius
  state_bound := state_bound
  liftLpRadius := liftLpRadius
  liftLpRadius_nonneg := liftLpRadius_nonneg
  liftLp_bound := liftLp_bound
  projected_equicontinuous := projected_equicontinuous

/-- Spectral compactness data generated by an arbitrarily indexed Hilbert
basis together with an increasing finite exhaustion of its index. -/
noncomputable def ofHilbertBasisExhaustion
    {ι : Type*}
    (basis : HilbertBasis ι ℝ H)
    (exhaustion : HilbertBasisExhaustion ι)
    (embed : V →L[ℝ] H) (embed_compact : IsCompactOperator embed)
    (lift : ℕ → I →ᵇ V)
    (stateRadius : ℝ)
    (state_bound : ∀ n t, ‖embed (lift n t)‖ ≤ stateRadius)
    (liftLpRadius : ℝ) (liftLpRadius_nonneg : 0 ≤ liftLpRadius)
    (liftLp_bound : ∀ n,
      ‖BoundedContinuousFunction.toLp (2 : ℝ≥0∞) μ ℝ (lift n)‖
        ≤ liftLpRadius)
    (projected_equicontinuous : ∀ m,
      Equicontinuous
        ((↑) : Set.range
          (lerayProjectedPath embed
            (fun k =>
              GalerkinProjectorSequence.finitePartialProjection
                basis (exhaustion.head k))
            lift m) → I → H)) :
    LeraySpectralCompactFamily (I := I) (V := V) (H := H) (μ := μ) where
  embed := embed
  embed_compact := embed_compact
  projector := fun m =>
    GalerkinProjectorSequence.finitePartialProjection
      basis (exhaustion.head m)
  projector_compact := fun m =>
    GalerkinProjectorSequence.finitePartialProjection_isCompactOperator
      basis (exhaustion.head m)
  projector_contractive := fun m =>
    GalerkinProjectorSequence.finitePartialProjection_norm_le
      basis (exhaustion.head m)
  projector_tendsto :=
    GalerkinProjectorSequence.finitePartialProjection_tendsto basis exhaustion
  lift := lift
  stateRadius := stateRadius
  state_bound := state_bound
  liftLpRadius := liftLpRadius
  liftLpRadius_nonneg := liftLpRadius_nonneg
  liftLp_bound := liftLp_bound
  projected_equicontinuous := projected_equicontinuous

/-- Hilbert-basis spectral data from quantitative finite-mode time
regularity.  A uniform Hölder estimate at every fixed mode cutoff supplies
the Arzelà--Ascoli equicontinuity field. -/
noncomputable def ofHilbertBasisOfUniformHolder
    (basis : HilbertBasis ℕ ℝ H)
    (embed : V →L[ℝ] H) (embed_compact : IsCompactOperator embed)
    (lift : ℕ → I →ᵇ V)
    (stateRadius : ℝ)
    (state_bound : ∀ n t, ‖embed (lift n t)‖ ≤ stateRadius)
    (liftLpRadius : ℝ) (liftLpRadius_nonneg : 0 ≤ liftLpRadius)
    (liftLp_bound : ∀ n,
      ‖BoundedContinuousFunction.toLp (2 : ℝ≥0∞) μ ℝ (lift n)‖
        ≤ liftLpRadius)
    (r : ℝ≥0) (hr : 0 < r)
    (projected_holder : ∀ m, ∃ C : ℝ≥0, ∀ n,
      HolderWith C r
        (lerayProjectedPath embed
          (GalerkinProjectorSequence.partialProjection basis) lift m n)) :
    LeraySpectralCompactFamily (I := I) (V := V) (H := H) (μ := μ) := by
  apply ofHilbertBasis basis embed embed_compact lift
    stateRadius state_bound liftLpRadius liftLpRadius_nonneg liftLp_bound
  intro m
  obtain ⟨C, hC⟩ := projected_holder m
  apply equicontinuous_subtype_of_uniform_holder
    (Set.range (lerayProjectedPath embed
      (GalerkinProjectorSequence.partialProjection basis) lift m)) C r hr
  intro f
  rcases f with ⟨_, n, rfl⟩
  exact hC n

/-- Hilbert-basis spectral data from genuine projected time derivatives.
Uniform `L²` bounds for those derivatives imply the fixed-mode square-root
modulus by the interval fundamental theorem and Cauchy--Schwarz. -/
noncomputable def ofHilbertBasisOfProjectedL2Derivative
    {a b : ℝ} (hab : a ≤ b)
    {μI : Measure (Icc a b)} [IsFiniteMeasure μI]
    (basis : HilbertBasis ℕ ℝ H)
    (embed : V →L[ℝ] H) (embed_compact : IsCompactOperator embed)
    (lift : ℕ → Icc a b →ᵇ V)
    (stateRadius : ℝ)
    (state_bound : ∀ n t, ‖embed (lift n t)‖ ≤ stateRadius)
    (liftLpRadius : ℝ) (liftLpRadius_nonneg : 0 ≤ liftLpRadius)
    (liftLp_bound : ∀ n,
      ‖BoundedContinuousFunction.toLp (2 : ℝ≥0∞) μI ℝ (lift n)‖
        ≤ liftLpRadius)
    (projectedExtension : ℕ → ℕ → ℝ → H)
    (projectedDerivative : ℕ → ℕ → ℝ → H)
    (projectedExtension_eq : ∀ m n (t : Icc a b),
      projectedExtension m n t =
        lerayProjectedPath embed
          (GalerkinProjectorSequence.partialProjection basis) lift m n t)
    (projected_hasDeriv : ∀ m n x (_hx : x ∈ Icc a b),
      HasDerivWithinAt
        (projectedExtension m n)
        (projectedDerivative m n x)
        (Icc a b) x)
    (projected_memLp : ∀ m n,
      MemLp (projectedDerivative m n) 2
        (volume.restrict (Icc a b)))
    (projected_sq_integral_bound : ∀ m, ∃ C : ℝ≥0, ∀ n,
      ∫ x in a..b, ‖projectedDerivative m n x‖ ^ 2
        ≤ (C : ℝ) ^ 2) :
    LeraySpectralCompactFamily
      (I := Icc a b) (V := V) (H := H) (μ := μI) := by
  apply ofHilbertBasis basis embed embed_compact lift
    stateRadius state_bound liftLpRadius liftLpRadius_nonneg liftLp_bound
  intro m
  obtain ⟨C, hC⟩ := projected_sq_integral_bound m
  apply equicontinuous_subtype_of_uniform_sqrt
    (Set.range (lerayProjectedPath embed
      (GalerkinProjectorSequence.partialProjection basis) lift m)) C
  intro f s t
  rcases f with ⟨_, n, rfl⟩
  change
    dist
      (lerayProjectedPath embed
        (GalerkinProjectorSequence.partialProjection basis) lift m n s)
      (lerayProjectedPath embed
        (GalerkinProjectorSequence.partialProjection basis) lift m n t)
      ≤ (C : ℝ) * √(dist s t)
  rw [← projectedExtension_eq m n s, ← projectedExtension_eq m n t]
  exact dist_le_sqrt_mul_of_hasDerivWithinAt_of_memLp
    hab (projectedExtension m n) (projectedDerivative m n) C
    (projected_hasDeriv m n) (projected_memLp m n) (hC n) s t

/-- Spectral compactness data obtained directly from variational Galerkin
solutions with a uniform common-test-space dual `L²` bound.  The finite
Hilbert-basis projection is reconstructed from tested coordinates, and the
tested scalar derivative identities assemble into its vector derivative. -/
noncomputable def ofHilbertBasisOfVariationalDualL2
    {a b : ℝ} (hab : a ≤ b)
    {μI : Measure (Icc a b)} [IsFiniteMeasure μI]
    {W Test : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    [NormedAddCommGroup Test] [NormedSpace ℝ Test]
    (basis : HilbertBasis ℕ ℝ H)
    (embed : V →L[ℝ] H) (embed_compact : IsCompactOperator embed)
    (lift : ℕ → Icc a b →ᵇ V)
    (stateRadius : ℝ)
    (state_bound : ∀ n t, ‖embed (lift n t)‖ ≤ stateRadius)
    (liftLpRadius : ℝ) (liftLpRadius_nonneg : 0 ≤ liftLpRadius)
    (liftLp_bound : ∀ n,
      ‖BoundedContinuousFunction.toLp (2 : ℝ≥0∞) μI ℝ (lift n)‖
        ≤ liftLpRadius)
    (problem : ℕ → VariationalGalerkinProblem W)
    (solution : ∀ n,
      (problem n).LocalSolutionOn (⟨a, le_rfl, hab⟩ : Icc a b))
    (testProjection : ℕ → Test →L[ℝ] W)
    (testMode : ℕ → Test)
    (coordinate_eq : ∀ n (t : Icc a b) i,
      ⟪(solution n).toFun t, testProjection n (testMode i)⟫_ℝ =
        ⟪embed (lift n t), basis i⟫_ℝ)
    (dualRadius : ℝ≥0)
    (dual_memLp : ∀ n,
      MemLp
        (fun t =>
          (problem n).dualRHS (testProjection n) t ((solution n).toFun t))
        2 (volume.restrict (Icc a b)))
    (dual_sq_integral_bound : ∀ n,
      ∫ t in a..b,
          ‖(problem n).dualRHS
            (testProjection n) t ((solution n).toFun t)‖ ^ 2
        ≤ (dualRadius : ℝ) ^ 2) :
    LeraySpectralCompactFamily
      (I := Icc a b) (V := V) (H := H) (μ := μI) := by
  let projectedExtension : ℕ → ℕ → ℝ → H := fun m n t =>
    ∑ i ∈ Finset.range m,
      ⟪(solution n).toFun t, testProjection n (testMode i)⟫_ℝ • basis i
  let projectedDerivative : ℕ → ℕ → ℝ → H := fun m n t =>
    VariationalGalerkinProblem.finiteModeSynthesis
      testMode basis (Finset.range m)
      ((problem n).dualRHS
        (testProjection n) t ((solution n).toFun t))
  apply ofHilbertBasisOfProjectedL2Derivative hab basis embed embed_compact
    lift stateRadius state_bound liftLpRadius liftLpRadius_nonneg liftLp_bound
    projectedExtension projectedDerivative
  · intro m n t
    change
      (∑ i ∈ Finset.range m,
        ⟪(solution n).toFun t, testProjection n (testMode i)⟫_ℝ • basis i) =
      GalerkinProjectorSequence.partialProjection basis m (embed (lift n t))
    rw [GalerkinProjectorSequence.partialProjection_apply_eq_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [coordinate_eq n t i]
  · intro m n t ht
    exact
      (solution n).hasDerivWithinAt_finiteModeReconstruction
        (testProjection n) testMode basis (Finset.range m) t ht
  · intro m n
    exact VariationalGalerkinProblem.finiteModeSynthesis_memLp
      (fun t =>
        (problem n).dualRHS
          (testProjection n) t ((solution n).toFun t))
      2 (volume.restrict (Icc a b))
      testMode basis (Finset.range m) (dual_memLp n)
  · intro m
    refine
      ⟨VariationalGalerkinProblem.finiteModeSynthesisConstant
          testMode basis (Finset.range m) * dualRadius, ?_⟩
    intro n
    exact
      ((solution n).finiteModeReconstruction_l2Derivative hab
        (testProjection n) testMode basis (Finset.range m) dualRadius
        (dual_memLp n) (dual_sq_integral_bound n)).2.2

/-- Spectral compactness for a genuine tower of variational problems whose
finite coefficient type may depend on the Galerkin level.  All estimates and
coordinate identities are still expressed in one common test space and one
common pivot Hilbert space. -/
noncomputable def ofHilbertBasisOfVariationalDualL2Family
    {a b : ℝ} (hab : a ≤ b)
    {μI : Measure (Icc a b)} [IsFiniteMeasure μI]
    {W : ℕ → Type*} {Test : Type*}
    [∀ n, NormedAddCommGroup (W n)]
    [∀ n, InnerProductSpace ℝ (W n)]
    [∀ n, CompleteSpace (W n)]
    [NormedAddCommGroup Test] [NormedSpace ℝ Test]
    (basis : HilbertBasis ℕ ℝ H)
    (embed : V →L[ℝ] H) (embed_compact : IsCompactOperator embed)
    (lift : ℕ → Icc a b →ᵇ V)
    (stateRadius : ℝ)
    (state_bound : ∀ n t, ‖embed (lift n t)‖ ≤ stateRadius)
    (liftLpRadius : ℝ) (liftLpRadius_nonneg : 0 ≤ liftLpRadius)
    (liftLp_bound : ∀ n,
      ‖BoundedContinuousFunction.toLp (2 : ℝ≥0∞) μI ℝ (lift n)‖
        ≤ liftLpRadius)
    (problem : ∀ n, VariationalGalerkinProblem (W n))
    (solution : ∀ n,
      (problem n).LocalSolutionOn (⟨a, le_rfl, hab⟩ : Icc a b))
    (testProjection : ∀ n, Test →L[ℝ] W n)
    (testMode : ℕ → Test)
    (coordinate_eq : ∀ n (t : Icc a b) i,
      ⟪(solution n).toFun t, testProjection n (testMode i)⟫_ℝ =
        ⟪embed (lift n t), basis i⟫_ℝ)
    (dualRadius : ℝ≥0)
    (dual_memLp : ∀ n,
      MemLp
        (fun t =>
          (problem n).dualRHS
            (testProjection n) t ((solution n).toFun t))
        2 (volume.restrict (Icc a b)))
    (dual_sq_integral_bound : ∀ n,
      ∫ t in a..b,
          ‖(problem n).dualRHS
            (testProjection n) t ((solution n).toFun t)‖ ^ 2
        ≤ (dualRadius : ℝ) ^ 2) :
    LeraySpectralCompactFamily
      (I := Icc a b) (V := V) (H := H) (μ := μI) := by
  let projectedExtension : ℕ → ℕ → ℝ → H := fun m n t =>
    ∑ i ∈ Finset.range m,
      ⟪(solution n).toFun t, testProjection n (testMode i)⟫_ℝ • basis i
  let projectedDerivative : ℕ → ℕ → ℝ → H := fun m n t =>
    VariationalGalerkinProblem.finiteModeSynthesis
      testMode basis (Finset.range m)
      ((problem n).dualRHS
        (testProjection n) t ((solution n).toFun t))
  apply ofHilbertBasisOfProjectedL2Derivative hab basis embed embed_compact
    lift stateRadius state_bound liftLpRadius liftLpRadius_nonneg liftLp_bound
    projectedExtension projectedDerivative
  · intro m n t
    change
      (∑ i ∈ Finset.range m,
        ⟪(solution n).toFun t, testProjection n (testMode i)⟫_ℝ • basis i) =
      GalerkinProjectorSequence.partialProjection basis m (embed (lift n t))
    rw [GalerkinProjectorSequence.partialProjection_apply_eq_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [coordinate_eq n t i]
  · intro m n t ht
    exact
      (solution n).hasDerivWithinAt_finiteModeReconstruction
        (testProjection n) testMode basis (Finset.range m) t ht
  · intro m n
    exact VariationalGalerkinProblem.finiteModeSynthesis_memLp
      (fun t =>
        (problem n).dualRHS
          (testProjection n) t ((solution n).toFun t))
      2 (volume.restrict (Icc a b))
      testMode basis (Finset.range m) (dual_memLp n)
  · intro m
    refine
      ⟨VariationalGalerkinProblem.finiteModeSynthesisConstant
          testMode basis (Finset.range m) * dualRadius, ?_⟩
    intro n
    exact
      ((solution n).finiteModeReconstruction_l2Derivative hab
        (testProjection n) testMode basis (Finset.range m) dualRadius
        (dual_memLp n) (dual_sq_integral_bound n)).2.2

/-- Varying finite-dimensional variational compactness for an arbitrarily
indexed Hilbert basis equipped with a finite exhaustion. -/
noncomputable def ofHilbertBasisExhaustionOfVariationalDualL2Family
    {a b : ℝ} (hab : a ≤ b)
    {μI : Measure (Icc a b)} [IsFiniteMeasure μI]
    {ι : Type*} {W : ℕ → Type*} {Test : Type*}
    [∀ n, NormedAddCommGroup (W n)]
    [∀ n, InnerProductSpace ℝ (W n)]
    [∀ n, CompleteSpace (W n)]
    [NormedAddCommGroup Test] [NormedSpace ℝ Test]
    (basis : HilbertBasis ι ℝ H)
    (exhaustion : HilbertBasisExhaustion ι)
    (embed : V →L[ℝ] H) (embed_compact : IsCompactOperator embed)
    (lift : ℕ → Icc a b →ᵇ V)
    (stateRadius : ℝ)
    (state_bound : ∀ n t, ‖embed (lift n t)‖ ≤ stateRadius)
    (liftLpRadius : ℝ) (liftLpRadius_nonneg : 0 ≤ liftLpRadius)
    (liftLp_bound : ∀ n,
      ‖BoundedContinuousFunction.toLp (2 : ℝ≥0∞) μI ℝ (lift n)‖
        ≤ liftLpRadius)
    (problem : ∀ n, VariationalGalerkinProblem (W n))
    (solution : ∀ n,
      (problem n).LocalSolutionOn (⟨a, le_rfl, hab⟩ : Icc a b))
    (testProjection : ∀ n, Test →L[ℝ] W n)
    (testMode : ι → Test)
    (coordinate_eq : ∀ n (t : Icc a b) i,
      ⟪(solution n).toFun t, testProjection n (testMode i)⟫_ℝ =
        ⟪embed (lift n t), basis i⟫_ℝ)
    (dualRadius : ℝ≥0)
    (dual_memLp : ∀ n,
      MemLp
        (fun t =>
          (problem n).dualRHS
            (testProjection n) t ((solution n).toFun t))
        2 (volume.restrict (Icc a b)))
    (dual_sq_integral_bound : ∀ n,
      ∫ t in a..b,
          ‖(problem n).dualRHS
            (testProjection n) t ((solution n).toFun t)‖ ^ 2
        ≤ (dualRadius : ℝ) ^ 2) :
    LeraySpectralCompactFamily
      (I := Icc a b) (V := V) (H := H) (μ := μI) := by
  let projector : ℕ → H →L[ℝ] H := fun m =>
    GalerkinProjectorSequence.finitePartialProjection
      basis (exhaustion.head m)
  let projectedExtension : ℕ → ℕ → ℝ → H := fun m n t =>
    ∑ i ∈ exhaustion.head m,
      ⟪(solution n).toFun t, testProjection n (testMode i)⟫_ℝ • basis i
  let projectedDerivative : ℕ → ℕ → ℝ → H := fun m n t =>
    VariationalGalerkinProblem.finiteModeSynthesis
      testMode basis (exhaustion.head m)
      ((problem n).dualRHS
        (testProjection n) t ((solution n).toFun t))
  apply ofHilbertBasisExhaustion basis exhaustion embed embed_compact
    lift stateRadius state_bound liftLpRadius liftLpRadius_nonneg liftLp_bound
  intro m
  let C :=
    VariationalGalerkinProblem.finiteModeSynthesisConstant
      testMode basis (exhaustion.head m) * dualRadius
  apply equicontinuous_subtype_of_uniform_sqrt
    (Set.range (lerayProjectedPath embed projector lift m)) C
  intro f s t
  rcases f with ⟨_, n, rfl⟩
  change
    dist
      (lerayProjectedPath embed projector lift m n s)
      (lerayProjectedPath embed projector lift m n t)
      ≤ (C : ℝ) * √(dist s t)
  have hext (q : Icc a b) :
      projectedExtension m n q =
        lerayProjectedPath embed projector lift m n q := by
    change
      (∑ i ∈ exhaustion.head m,
        ⟪(solution n).toFun q, testProjection n (testMode i)⟫_ℝ • basis i) =
      GalerkinProjectorSequence.finitePartialProjection
        basis (exhaustion.head m) (embed (lift n q))
    rw [GalerkinProjectorSequence.finitePartialProjection_apply_eq_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [coordinate_eq n q i]
  rw [← hext s, ← hext t]
  exact dist_le_sqrt_mul_of_hasDerivWithinAt_of_memLp
    hab (projectedExtension m n) (projectedDerivative m n) C
    (fun x hx =>
      (solution n).hasDerivWithinAt_finiteModeReconstruction
        (testProjection n) testMode basis (exhaustion.head m) x hx)
    (VariationalGalerkinProblem.finiteModeSynthesis_memLp
      (fun x =>
        (problem n).dualRHS
          (testProjection n) x ((solution n).toFun x))
      2 (volume.restrict (Icc a b))
      testMode basis (exhaustion.head m) (dual_memLp n))
    (((solution n).finiteModeReconstruction_l2Derivative hab
      (testProjection n) testMode basis (exhaustion.head m) dualRadius
      (dual_memLp n) (dual_sq_integral_bound n)).2.2)
    s t

variable (G : LeraySpectralCompactFamily (I := I) (V := V) (H := H) (μ := μ))

noncomputable def statePath (n : ℕ) : I →ᵇ H :=
  lerayStatePath G.embed G.lift n

noncomputable def projectedPath (m n : ℕ) : I →ᵇ H :=
  lerayProjectedPath G.embed G.projector G.lift m n

omit [CompactSpace I] [CompleteSpace V] [CompleteSpace H] in
@[simp]
theorem statePath_apply (n : ℕ) (t : I) :
    G.statePath n t = G.embed (G.lift n t) :=
  rfl

omit [CompactSpace I] [CompleteSpace V] [CompleteSpace H] in
@[simp]
theorem projectedPath_apply (m n : ℕ) (t : I) :
    G.projectedPath m n t = G.projector m (G.statePath n t) :=
  rfl

noncomputable def stateLp (n : ℕ) : Lp H (2 : ℝ≥0∞) μ :=
  BoundedContinuousFunction.toLp (2 : ℝ≥0∞) μ ℝ (G.statePath n)

noncomputable def projectedLp (m n : ℕ) : Lp H (2 : ℝ≥0∞) μ :=
  BoundedContinuousFunction.toLp (2 : ℝ≥0∞) μ ℝ (G.projectedPath m n)

noncomputable def tailOperator (m : ℕ) : V →L[ℝ] H :=
  G.embed - (G.projector m).comp G.embed

omit [CompactSpace I] [CompleteSpace V] [CompleteSpace H] in
/-- Compactness of the source embedding and strong convergence of the
contractive projectors imply operator-norm decay of every spatial tail. -/
theorem tailOperator_tendsto :
    Tendsto (fun m => ‖G.tailOperator m‖) atTop (nhds 0) := by
  simpa only [tailOperator] using
    compactEmbedding_projectorTail_tendsto
      G.embed G.embed_compact G.projector
      G.projector_contractive G.projector_tendsto

omit [CompleteSpace V] [CompleteSpace H] in
/-- Each fixed finite-mode family has compact closure in the uniform path
topology. -/
theorem projectedPath_compact_closure (m : ℕ) :
    IsCompact (closure (Set.range (G.projectedPath m))) := by
  obtain ⟨K, hKcompact, hK⟩ :=
    (G.projector_compact m).image_closedBall_subset_compact G.stateRadius
  have hRange :
      ∀ (f : I →ᵇ H) (t : I),
        f ∈ Set.range (G.projectedPath m) → f t ∈ K := by
    rintro f t ⟨n, rfl⟩
    apply hK
    refine ⟨G.statePath n t, ?_, rfl⟩
    exact mem_closedBall_zero_iff.mpr (G.state_bound n t)
  exact BoundedContinuousFunction.arzela_ascoli
    K hKcompact (Set.range (G.projectedPath m)) hRange
      (G.projected_equicontinuous m)

/-- One strict extraction of a prescribed source sequence on which every
finite-mode path converges uniformly in time. -/
structure ProjectedPathSubsequence (source : ℕ → ℕ) where
  subseq : ExtractedSubsequence
  limit : ℕ → I →ᵇ H
  converges : ∀ m,
    Tendsto (fun k => G.projectedPath m (source (subseq.idx k)))
      atTop (nhds (limit m))

omit [CompleteSpace V] [CompleteSpace H] in
/-- Countable compactness combines the fixed-mode Arzelà--Ascoli extractions
into a single subsequence. -/
theorem exists_projectedPathSubsequence :
    ∀ source : ℕ → ℕ, Nonempty (G.ProjectedPathSubsequence source) := by
  intro source
  let K : ℕ → Type _ := fun m =>
    closure (Set.range (G.projectedPath m))
  letI (m : ℕ) : CompactSpace (K m) :=
    isCompact_iff_compactSpace.mp (G.projectedPath_compact_closure m)
  let x : ℕ → ∀ m, K m := fun n m =>
    ⟨G.projectedPath m (source n),
      subset_closure ⟨source n, rfl⟩⟩
  obtain ⟨f, phi, hphi, hconv⟩ := CompactSpace.tendsto_subseq x
  refine ⟨{
    subseq := ⟨phi, hphi⟩
    limit := fun m => f m
    converges := ?_
  }⟩
  intro m
  have hm : Tendsto (fun k => ((x (phi k)) m : I →ᵇ H))
      atTop (nhds (f m : I →ᵇ H)) :=
    (continuous_subtype_val.tendsto (f m)).comp
      (tendsto_pi_nhds.mp hconv m)
  simpa only [x, Function.comp_apply] using hm

omit [CompleteSpace V] [CompleteSpace H] in
/-- Uniform finite-mode compactness passes continuously from the sup-norm
path space to `L²(I;H)`. -/
theorem projectedLp_compact_closure (m : ℕ) :
    IsCompact (closure (Set.range (G.projectedLp m))) := by
  let L : (I →ᵇ H) →L[ℝ] Lp H (2 : ℝ≥0∞) μ :=
    BoundedContinuousFunction.toLp (2 : ℝ≥0∞) μ ℝ
  have hImage : IsCompact (L '' closure (Set.range (G.projectedPath m))) :=
    (G.projectedPath_compact_closure m).image L.continuous
  apply hImage.of_isClosed_subset isClosed_closure
  apply closure_minimal
  · rintro x ⟨n, rfl⟩
    exact ⟨G.projectedPath m n, subset_closure ⟨n, rfl⟩, rfl⟩
  · exact hImage.isClosed

omit [CompactSpace I] [CompleteSpace V] [CompleteSpace H] in
/-- Applying a continuous linear map before or after embedding a bounded
continuous path into `L²` gives the same element. -/
theorem toLp_compLeftContinuousBounded
    (L : V →L[ℝ] H) (f : I →ᵇ V) :
    BoundedContinuousFunction.toLp (2 : ℝ≥0∞) μ ℝ
        (L.compLeftContinuousBounded I f)
      = L.compLpL (2 : ℝ≥0∞) μ
        (BoundedContinuousFunction.toLp (2 : ℝ≥0∞) μ ℝ f) := by
  ext1
  filter_upwards
    [BoundedContinuousFunction.coeFn_toLp (2 : ℝ≥0∞) μ ℝ
      (L.compLeftContinuousBounded I f),
     L.coeFn_compLpL
      (BoundedContinuousFunction.toLp (2 : ℝ≥0∞) μ ℝ f),
     BoundedContinuousFunction.coeFn_toLp (2 : ℝ≥0∞) μ ℝ f]
    with x hx hcomp hf
  simp only [hx, hcomp, hf, ContinuousLinearMap.compLeftContinuousBounded_apply]

omit [CompactSpace I] [CompleteSpace V] [CompleteSpace H] in
/-- The `L²` tail is the pointwise spatial tail operator acting on the lifted
`L²(I;V)` path. -/
theorem stateLp_sub_projectedLp_eq (m n : ℕ) :
    G.stateLp n - G.projectedLp m n =
      (G.tailOperator m).compLpL (2 : ℝ≥0∞) μ
        (BoundedContinuousFunction.toLp (2 : ℝ≥0∞) μ ℝ (G.lift n)) := by
  rw [stateLp, projectedLp, ← map_sub]
  rw [← toLp_compLeftContinuousBounded (μ := μ)
    (G.tailOperator m) (G.lift n)]
  congr 1

omit [CompactSpace I] [CompleteSpace V] [CompleteSpace H] in
/-- The spectral tail in `L²(I;H)` is bounded by the spatial tail operator
norm times the uniform `L²(I;V)` radius. -/
theorem tail_dist_le (m n : ℕ) :
    dist (G.stateLp n) (G.projectedLp m n)
      ≤ ‖G.tailOperator m‖ * G.liftLpRadius := by
  rw [dist_eq_norm, G.stateLp_sub_projectedLp_eq m n]
  exact (ContinuousLinearMap.norm_compLp_le (G.tailOperator m) _).trans
    (mul_le_mul_of_nonneg_left (G.liftLp_bound n) (norm_nonneg _))

omit [CompactSpace I] [CompleteSpace V] [CompleteSpace H] in
/-- Operator-norm decay of the spatial tails gives a mode cutoff uniformly
for the whole Galerkin family. -/
theorem tail (ε : ℝ) (hε : 0 < ε) :
    ∃ m, ∀ n, dist (G.stateLp n) (G.projectedLp m n) < ε := by
  have hprod :
      Tendsto
        (fun m => ‖G.tailOperator m‖ * G.liftLpRadius)
        atTop (nhds 0) := by
    simpa [tailOperator] using
      G.tailOperator_tendsto.mul_const G.liftLpRadius
  have hev : ∀ᶠ m in atTop, ‖G.tailOperator m‖ * G.liftLpRadius < ε :=
    (tendsto_order.1 hprod).2 ε hε
  obtain ⟨m, hm⟩ := hev.exists
  exact ⟨m, fun n => (G.tail_dist_le m n).trans_lt hm⟩

/-- The Leray-scale data instantiate the abstract compact-approximation
criterion in `L²(I;H)`. -/
noncomputable def compactApproximation :
    CompactApproximationSequence (Lp H (2 : ℝ≥0∞) μ) where
  sequence := G.stateLp
  approximation := G.projectedLp
  approximation_compact := G.projectedLp_compact_closure
  tail := G.tail

omit [CompleteSpace V] in
/-- Spectral Galerkin compactness: the `L∞(I;H)` and `L²(I;V)` bounds,
finite-mode time equicontinuity, and compact spatial approximation produce a
strict subsequence converging strongly in `L²(I;H)`. -/
theorem exists_strongL2_subsequence :
    Nonempty (StrongMetricSubsequence G.stateLp) :=
  G.compactApproximation.exists_stronglyConvergent_subsequence

omit [CompleteSpace V] in
/-- The extracted strong `L²` subsequence carries every continuous quadratic
observable to its strong `L¹` limit. -/
theorem exists_strongL2_quadraticL1_subsequence
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (B : H →L[ℝ] H →L[ℝ] N) :
    ∃ S : StrongMetricSubsequence G.stateLp,
      Tendsto
        (fun k => B.quadraticLp (G.stateLp (S.subseq.idx k)))
        atTop (nhds (B.quadraticLp S.limit)) := by
  obtain ⟨S⟩ := G.exists_strongL2_subsequence
  exact ⟨S, S.quadraticLp_tendsto B⟩

end LeraySpectralCompactFamily

end LeraySpectral
