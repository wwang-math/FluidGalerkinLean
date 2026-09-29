import PDEIdeas.GalerkinL2Compactness
import PDEIdeas.HilbertWeakCompactness
import PDEIdeas.QuadraticWeakFormLimit
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Simultaneous strong-state and weak-energy compactness

A Leray spectral family is strongly precompact in `L2` of the pivot space and
uniformly bounded in `L2` of the energy space.  Sequential weak compactness of
separable Hilbert spaces refines the strong subsequence to one carrying both
limits.  The adjoint of the space-time embedding identifies the two limits.
-/

open BoundedContinuousFunction Filter Function InnerProductSpace MeasureTheory
open scoped ENNReal

noncomputable section

section LeraySpectral

variable {I V H : Type*}
    [PseudoMetricSpace I] [CompactSpace I]
    [MeasurableSpace I] [BorelSpace I] [SecondCountableTopology I]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {μ : Measure I} [IsFiniteMeasure μ]

namespace LeraySpectralCompactFamily

variable (G : LeraySpectralCompactFamily
  (I := I) (V := V) (H := H) (μ := μ))

/-- Space-time energy lift of one member of the spectral family. -/
noncomputable def energyLp (n : ℕ) : Lp V (2 : ℝ≥0∞) μ :=
  BoundedContinuousFunction.toLp (2 : ℝ≥0∞) μ ℝ (G.lift n)

omit [CompactSpace I] [CompleteSpace V] [CompleteSpace H] in
/-- The space-time embedding sends the energy lift to the state path. -/
theorem stateLp_eq_embed_energyLp (n : ℕ) :
    G.stateLp n =
      G.embed.compLpL (2 : ℝ≥0∞) μ (G.energyLp n) := by
  simpa only [stateLp, statePath, energyLp, lerayStatePath] using
    toLp_compLeftContinuousBounded (μ := μ) G.embed (G.lift n)

omit [CompactSpace I] [CompleteSpace V] [CompleteSpace H] in
/-- The space-time energy lift satisfies the radius stored by the compact
family. -/
theorem energyLp_norm_le (n : ℕ) :
    ‖G.energyLp n‖ ≤ G.liftLpRadius :=
  G.liftLp_bound n

/-- One strict subsequence with a strong pivot-space limit and a weak
energy-space limit representing the same space-time trajectory. -/
structure StrongWeakSubsequence where
  subseq : ExtractedSubsequence
  stateLimit : Lp H (2 : ℝ≥0∞) μ
  energyLimit : Lp V (2 : ℝ≥0∞) μ
  state_strong :
    Tendsto (G.stateLp ∘ subseq.idx) atTop (nhds stateLimit)
  energy_weak : ∀ w : Lp V (2 : ℝ≥0∞) μ,
    Tendsto (fun k => ⟪G.energyLp (subseq.idx k), w⟫_ℝ)
      atTop (nhds ⟪energyLimit, w⟫_ℝ)
  embed_energyLimit :
    G.embed.compLpL (2 : ℝ≥0∞) μ energyLimit = stateLimit

/-- A simultaneous strong-state/weak-energy extraction that also retains
uniform-in-time limits of every finite spectral projection. -/
structure StrongWeakPathSubsequence extends G.StrongWeakSubsequence where
  projectedLimit : ℕ → I →ᵇ H
  projected_uniform : ∀ m,
    Tendsto (G.projectedPath m ∘ subseq.idx)
      atTop (nhds (projectedLimit m))

/-- Strong convergence of embedded states identifies any simultaneous weak
energy limit with its state limit. -/
def strongWeakSubsequenceOfLimits
    (subseq : ExtractedSubsequence)
    (stateLimit : Lp H (2 : ℝ≥0∞) μ)
    (energyLimit : Lp V (2 : ℝ≥0∞) μ)
    (hstate : Tendsto (G.stateLp ∘ subseq.idx) atTop (nhds stateLimit))
    (henergy : ∀ w : Lp V (2 : ℝ≥0∞) μ,
      Tendsto (fun k => ⟪G.energyLp (subseq.idx k), w⟫_ℝ)
        atTop (nhds ⟪energyLimit, w⟫_ℝ)) :
    G.StrongWeakSubsequence := by
  let A : Lp V (2 : ℝ≥0∞) μ →L[ℝ] Lp H (2 : ℝ≥0∞) μ :=
    G.embed.compLpL (2 : ℝ≥0∞) μ
  have hidentify : A energyLimit = stateLimit := by
    apply ext_inner_right ℝ
    intro z
    have hweak := henergy (ContinuousLinearMap.adjoint A z)
    have hweak' : Tendsto
        (fun k => ⟪G.stateLp (subseq.idx k), z⟫_ℝ)
        atTop (nhds ⟪A energyLimit, z⟫_ℝ) := by
      simpa only [A, G.stateLp_eq_embed_energyLp,
        ContinuousLinearMap.adjoint_inner_right] using hweak
    have hstrong : Tendsto
        (fun k => ⟪G.stateLp (subseq.idx k), z⟫_ℝ)
        atTop (nhds ⟪stateLimit, z⟫_ℝ) :=
      ((innerSLFlip ℝ z).continuous.tendsto stateLimit).comp hstate
    exact tendsto_nhds_unique hweak' hstrong
  exact {
    subseq := subseq
    stateLimit := stateLimit
    energyLimit := energyLimit
    state_strong := hstate
    energy_weak := henergy
    embed_energyLimit := hidentify
  }

namespace StrongWeakSubsequence

variable {G : LeraySpectralCompactFamily
  (I := I) (V := V) (H := H) (μ := μ)}

/-- Forgetting the weak energy channel leaves the strong state extraction. -/
def toStrongMetricSubsequence (S : G.StrongWeakSubsequence) :
    StrongMetricSubsequence G.stateLp where
  subseq := S.subseq
  limit := S.stateLimit
  converges := S.state_strong

omit [CompleteSpace V] [CompleteSpace H] in
/-- Refining a simultaneous strong/weak extraction by countable finite-mode
compactness preserves both space-time limits. -/
theorem exists_pathwiseRefinement
    (S : G.StrongWeakSubsequence) :
    Nonempty G.StrongWeakPathSubsequence := by
  obtain ⟨P⟩ := G.exists_projectedPathSubsequence S.subseq.idx
  let sigma := S.subseq.comp P.subseq
  have hstate :
      Tendsto (G.stateLp ∘ sigma.idx) atTop (nhds S.stateLimit) :=
    S.state_strong.comp P.subseq.strictMono_idx.tendsto_atTop
  have henergy : ∀ w : Lp V (2 : ℝ≥0∞) μ,
      Tendsto (fun k => ⟪G.energyLp (sigma.idx k), w⟫_ℝ)
        atTop (nhds ⟪S.energyLimit, w⟫_ℝ) := by
    intro w
    simpa only [sigma, ExtractedSubsequence.comp_idx] using
      (S.energy_weak w).comp P.subseq.strictMono_idx.tendsto_atTop
  let base : G.StrongWeakSubsequence := {
    subseq := sigma
    stateLimit := S.stateLimit
    energyLimit := S.energyLimit
    state_strong := hstate
    energy_weak := henergy
    embed_energyLimit := S.embed_energyLimit
  }
  refine ⟨{
    toStrongWeakSubsequence := base
    projectedLimit := P.limit
    projected_uniform := ?_
  }⟩
  intro m
  simpa only [base, sigma, ExtractedSubsequence.comp_idx,
    Function.comp_apply] using P.converges m

omit [CompleteSpace V] [CompleteSpace H] in
/-- The pathwise refinement can be chosen without changing either space-time
limit of the original strong/weak extraction. -/
theorem exists_pathwiseRefinement_preserving
    (S : G.StrongWeakSubsequence) :
    ∃ P : G.StrongWeakPathSubsequence,
      P.stateLimit = S.stateLimit ∧ P.energyLimit = S.energyLimit := by
  obtain ⟨P⟩ := G.exists_projectedPathSubsequence S.subseq.idx
  let sigma := S.subseq.comp P.subseq
  have hstate : Tendsto (G.stateLp ∘ sigma.idx) atTop (nhds S.stateLimit) :=
    S.state_strong.comp P.subseq.strictMono_idx.tendsto_atTop
  have henergy : ∀ w : Lp V (2 : ℝ≥0∞) μ,
      Tendsto (fun k => ⟪G.energyLp (sigma.idx k), w⟫_ℝ)
        atTop (nhds ⟪S.energyLimit, w⟫_ℝ) := by
    intro w
    simpa only [sigma, ExtractedSubsequence.comp_idx] using
      (S.energy_weak w).comp P.subseq.strictMono_idx.tendsto_atTop
  let base : G.StrongWeakSubsequence := {
    subseq := sigma
    stateLimit := S.stateLimit
    energyLimit := S.energyLimit
    state_strong := hstate
    energy_weak := henergy
    embed_energyLimit := S.embed_energyLimit
  }
  let result : G.StrongWeakPathSubsequence := {
    toStrongWeakSubsequence := base
    projectedLimit := P.limit
    projected_uniform := by
      intro m
      simpa only [base, sigma, ExtractedSubsequence.comp_idx,
        Function.comp_apply] using P.converges m
  }
  exact ⟨result, rfl, rfl⟩

omit [CompactSpace I] [CompleteSpace H] in
/-- Weak energy convergence applies to every continuous linear functional,
not only to its Riesz inner-product representative. -/
theorem energy_clm_tendsto
    (S : G.StrongWeakSubsequence)
    (ell : Lp V (2 : ℝ≥0∞) μ →L[ℝ] ℝ) :
    Tendsto (fun k => ell (G.energyLp (S.subseq.idx k)))
      atTop (nhds (ell S.energyLimit)) := by
  let w : Lp V (2 : ℝ≥0∞) μ :=
    (InnerProductSpace.toDual ℝ (Lp V (2 : ℝ≥0∞) μ)).symm ell
  have hrepr (x : Lp V (2 : ℝ≥0∞) μ) : ⟪x, w⟫_ℝ = ell x := by
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  simpa only [hrepr] using S.energy_weak w

omit [CompactSpace I] [CompleteSpace V] [CompleteSpace H] in
/-- The weak energy limit inherits the uniform energy-space radius. -/
theorem energyLimit_norm_le
    (S : G.StrongWeakSubsequence) :
    ‖S.energyLimit‖ ≤ G.liftLpRadius := by
  have hsq : ‖S.energyLimit‖ ^ 2 ≤
      G.liftLpRadius * ‖S.energyLimit‖ := by
    rw [← real_inner_self_eq_norm_sq]
    apply le_of_tendsto (S.energy_weak S.energyLimit)
    filter_upwards with k
    calc
      ⟪G.energyLp (S.subseq.idx k), S.energyLimit⟫_ℝ ≤
          ‖G.energyLp (S.subseq.idx k)‖ * ‖S.energyLimit‖ :=
        real_inner_le_norm _ _
      _ ≤ G.liftLpRadius * ‖S.energyLimit‖ :=
        mul_le_mul_of_nonneg_right
          (G.energyLp_norm_le (S.subseq.idx k)) (norm_nonneg _)
  by_cases hzero : ‖S.energyLimit‖ = 0
  · rw [hzero]
    exact G.liftLpRadius_nonneg
  · have hpos : 0 < ‖S.energyLimit‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    nlinarith [hsq]

omit [CompactSpace I] [CompleteSpace V] [CompleteSpace H] in
/-- Every state member has the essential-supremum bound stored by the compact
family, independently of its canonical `L2` bundling. -/
theorem stateLp_eLpNorm_top_le (n : ℕ) :
    eLpNorm (G.stateLp n : I → H) ∞ μ ≤ ENNReal.ofReal G.stateRadius := by
  rw [eLpNorm_exponent_top]
  apply eLpNormEssSup_le_of_ae_bound
  filter_upwards [BoundedContinuousFunction.coeFn_toLp (2 : ℝ≥0∞) μ ℝ
    (G.statePath n)] with t ht
  change ‖(BoundedContinuousFunction.toLp (2 : ℝ≥0∞) μ ℝ
    (G.statePath n)) t‖ ≤ G.stateRadius
  rw [ht]
  exact G.state_bound n t

omit [CompactSpace I] [CompleteSpace V] [CompleteSpace H] in
/-- Strong `L2` convergence transfers the uniform state bound to the common
limit as an essential-supremum estimate. -/
theorem stateLimit_eLpNorm_top_le
    (S : G.StrongWeakSubsequence) :
    eLpNorm (S.stateLimit : I → H) ∞ μ ≤ ENNReal.ofReal G.stateRadius := by
  have hmeasure : TendstoInMeasure μ
      (fun k => (G.stateLp (S.subseq.idx k) : I → H)) atTop
      (S.stateLimit : I → H) := by
    simpa only [Function.comp_apply] using
      tendstoInMeasure_of_tendsto_Lp S.state_strong
  exact eLpNorm_le_of_tendstoInMeasure
    (Eventually.of_forall fun k =>
      stateLp_eLpNorm_top_le (G := G) (S.subseq.idx k))
    hmeasure (fun k => Lp.aestronglyMeasurable _)

omit [CompactSpace I] [CompleteSpace V] [CompleteSpace H] in
/-- The common state limit belongs to `L-infinity` in time. -/
theorem stateLimit_memLp_top
    (S : G.StrongWeakSubsequence) :
    MemLp (S.stateLimit : I → H) ∞ μ :=
  ⟨Lp.aestronglyMeasurable S.stateLimit,
    S.stateLimit_eLpNorm_top_le.trans_lt ENNReal.ofReal_lt_top⟩

/-- A fixed space-time energy test induces the integrated bilinear
functional used for diffusion terms. -/
noncomputable def energyBilinearTestCLM
    (A : V →L[ℝ] V →L[ℝ] ℝ)
    (psi : Lp V (2 : ℝ≥0∞) μ) :
    Lp V (2 : ℝ≥0∞) μ →L[ℝ] ℝ :=
  (A.lpPairing μ 2 2).flip psi

omit [PseudoMetricSpace I] [CompactSpace I] [BorelSpace I]
  [SecondCountableTopology I] [CompleteSpace V] [IsFiniteMeasure μ] in
theorem energyBilinearTestCLM_apply
    (A : V →L[ℝ] V →L[ℝ] ℝ)
    (psi w : Lp V (2 : ℝ≥0∞) μ) :
    energyBilinearTestCLM A psi w =
      ∫ t, A (w t) (psi t) ∂μ := by
  exact A.lpPairing_eq_integral w psi

omit [CompactSpace I] [CompleteSpace H] in
/-- Weak energy convergence passes every integrated continuous bilinear form
against a fixed `L2` energy test. -/
theorem energyBilinearIntegral_tendsto
    (S : G.StrongWeakSubsequence)
    (A : V →L[ℝ] V →L[ℝ] ℝ)
    (psi : Lp V (2 : ℝ≥0∞) μ) :
    Tendsto
      (fun k => ∫ t,
        A (G.energyLp (S.subseq.idx k) t) (psi t) ∂μ)
      atTop
      (nhds (∫ t, A (S.energyLimit t) (psi t) ∂μ)) := by
  simpa only [energyBilinearTestCLM_apply] using
    S.energy_clm_tendsto (energyBilinearTestCLM A psi)

omit [CompactSpace I] [CompleteSpace H] in
/-- Weak energy convergence may be paired with a simultaneously strongly
convergent sequence of `L2` energy tests. -/
theorem energyBilinearIntegral_tendsto_of_test_tendsto
    (S : G.StrongWeakSubsequence)
    (A : V →L[ℝ] V →L[ℝ] ℝ)
    (psi : ℕ → Lp V (2 : ℝ≥0∞) μ)
    (psiLimit : Lp V (2 : ℝ≥0∞) μ)
    (hpsi : Tendsto psi atTop (nhds psiLimit)) :
    Tendsto
      (fun k => ∫ t,
        A (G.energyLp (S.subseq.idx k) t) (psi k t) ∂μ)
      atTop
      (nhds (∫ t, A (S.energyLimit t) (psiLimit t) ∂μ)) := by
  let P := A.lpPairing μ 2 2
  let e : ℕ → Lp V (2 : ℝ≥0∞) μ :=
    fun k => G.energyLp (S.subseq.idx k)
  have hmain : Tendsto (fun k => P (e k) psiLimit) atTop
      (nhds (P S.energyLimit psiLimit)) := by
    simpa only [P, e, A.lpPairing_eq_integral] using
      S.energyBilinearIntegral_tendsto A psiLimit
  have hpsiNorm : Tendsto (fun k => ‖psi k - psiLimit‖) atTop (nhds 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hpsi
  have hpairBound (f g : Lp V (2 : ℝ≥0∞) μ) :
      ‖P f g‖ ≤ ‖A‖ * ‖f‖ * ‖g‖ := by
    let h : Lp ℝ (1 : ℝ≥0∞) μ := A.holder 1 f g
    change ‖A.lpPairing μ 2 2 f g‖ ≤ ‖A‖ * ‖f‖ * ‖g‖
    calc
      ‖A.lpPairing μ 2 2 f g‖ = ‖∫ t, A (f t) (g t) ∂μ‖ := by
        rw [A.lpPairing_eq_integral]
      _ = ‖∫ t, h t ∂μ‖ := by
        congr 1
        exact integral_congr_ae (A.coeFn_holder f g).symm
      _ = ‖L1.integral h‖ := congrArg norm (L1.integral_eq_integral h).symm
      _ ≤ ‖h‖ := L1.norm_integral_le h
      _ ≤ ‖A‖ * ‖f‖ * ‖g‖ := A.norm_holder_apply_apply_le f g
  have herrorNorm : Tendsto
      (fun k => ‖P (e k) (psi k - psiLimit)‖) atTop (nhds 0) := by
    apply squeeze_zero
      (fun _ => norm_nonneg _)
      (fun k => by
        calc
          ‖P (e k) (psi k - psiLimit)‖ ≤
              (‖A‖ * ‖e k‖) * ‖psi k - psiLimit‖ :=
            hpairBound (e k) (psi k - psiLimit)
          _ ≤ (‖A‖ * G.liftLpRadius) * ‖psi k - psiLimit‖ := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left
                (G.energyLp_norm_le (S.subseq.idx k)) (norm_nonneg A))
              (norm_nonneg _))
    simpa using (tendsto_const_nhds.mul hpsiNorm)
  have herror : Tendsto
      (fun k => P (e k) (psi k - psiLimit)) atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr herrorNorm
  have hsum := hmain.add herror
  have hpaired : Tendsto (fun k => P (e k) (psi k)) atTop
      (nhds (P S.energyLimit psiLimit)) := by
    convert hsum using 1
    · funext k
      rw [map_sub]
      ring
    · simp
  simpa only [P, e, A.lpPairing_eq_integral] using hpaired

omit [CompactSpace I] [CompleteSpace V] [CompleteSpace H] in
/-- Strong state convergence passes every integrated continuous bilinear form
against a fixed `L2` state test. -/
theorem stateBilinearIntegral_tendsto
    (S : G.StrongWeakSubsequence)
    (A : H →L[ℝ] H →L[ℝ] ℝ)
    (psi : Lp H (2 : ℝ≥0∞) μ) :
    Tendsto
      (fun k => ∫ t,
        A (G.stateLp (S.subseq.idx k) t) (psi t) ∂μ)
      atTop
      (nhds (∫ t, A (S.stateLimit t) (psi t) ∂μ)) := by
  let ell : Lp H (2 : ℝ≥0∞) μ →L[ℝ] ℝ :=
    (A.lpPairing μ 2 2).flip psi
  have hcontinuous : Tendsto ell (nhds S.stateLimit) (nhds (ell S.stateLimit)) :=
    ell.continuous.continuousAt
  have h := hcontinuous.comp S.state_strong
  simpa only [Function.comp_def, ell, ContinuousLinearMap.flip_apply,
    A.lpPairing_eq_integral] using h

omit [CompactSpace I] [CompleteSpace V] [CompleteSpace H] in
/-- The same strong/weak extraction carries the canonical quadratic tensor
limit. -/
theorem projectiveTensorSquareLp_tendsto
    (S : G.StrongWeakSubsequence) :
    Tendsto
      (fun k => projectiveTensorSquareLp
        (G.stateLp (S.subseq.idx k)))
      atTop
      (nhds (projectiveTensorSquareLp S.stateLimit)) :=
  S.toStrongMetricSubsequence.projectiveTensorSquareLp_tendsto

omit [CompactSpace I] [CompleteSpace V] [CompleteSpace H] in
/-- Every continuous pivot-space trilinear form converges on the same
strong/weak subsequence against every bounded time-dependent test. -/
theorem trilinearIntegral_tendsto
    (S : G.StrongWeakSubsequence)
    {Test : Type*} [NormedAddCommGroup Test] [NormedSpace ℝ Test]
    (T : H →L[ℝ] H →L[ℝ] Test →L[ℝ] ℝ)
    (psi : Lp Test (∞ : ℝ≥0∞) μ) :
    Tendsto
      (fun k => ∫ t,
        T (G.stateLp (S.subseq.idx k) t)
          (G.stateLp (S.subseq.idx k) t) (psi t) ∂μ)
      atTop
      (nhds (∫ t,
        T (S.stateLimit t) (S.stateLimit t) (psi t) ∂μ)) :=
  S.toStrongMetricSubsequence.projectiveTrilinearIntegral_tendsto T psi

end StrongWeakSubsequence

variable [TopologicalSpace.SeparableSpace (Lp V (2 : ℝ≥0∞) μ)]

/-- Strong `L2_t H` compactness and the uniform `L2_t V` bound produce a
simultaneous strong/weak subsequence, with the limits identified by the
space-time embedding. -/
theorem exists_strongWeakSubsequence :
    Nonempty G.StrongWeakSubsequence := by
  obtain ⟨S⟩ := G.exists_strongL2_subsequence
  obtain ⟨W⟩ := exists_weakHilbertSubsequence
    (fun k => G.energyLp (S.subseq.idx k)) G.liftLpRadius
    (fun k => G.liftLp_bound (S.subseq.idx k))
  let sigma := S.subseq.comp W.subseq
  have hstate : Tendsto (G.stateLp ∘ sigma.idx) atTop (nhds S.limit) := by
    exact S.converges.comp W.subseq.strictMono_idx.tendsto_atTop
  have henergy : ∀ w : Lp V (2 : ℝ≥0∞) μ,
      Tendsto (fun k => ⟪G.energyLp (sigma.idx k), w⟫_ℝ)
        atTop (nhds ⟪W.limit, w⟫_ℝ) := by
    intro w
    simpa only [sigma, ExtractedSubsequence.comp_idx] using W.inner_tendsto w
  let L : Lp V (2 : ℝ≥0∞) μ →L[ℝ] Lp H (2 : ℝ≥0∞) μ :=
    G.embed.compLpL (2 : ℝ≥0∞) μ
  have hidentify : L W.limit = S.limit := by
    apply ext_inner_right ℝ
    intro z
    have hweak := henergy (ContinuousLinearMap.adjoint L z)
    have hweak' :
        Tendsto (fun k => ⟪G.stateLp (sigma.idx k), z⟫_ℝ)
          atTop (nhds ⟪L W.limit, z⟫_ℝ) := by
      simpa only [L, G.stateLp_eq_embed_energyLp,
        ContinuousLinearMap.adjoint_inner_right] using hweak
    have hstrong :
        Tendsto (fun k => ⟪G.stateLp (sigma.idx k), z⟫_ℝ)
          atTop (nhds ⟪S.limit, z⟫_ℝ) :=
      ((innerSLFlip ℝ z).continuous.tendsto S.limit).comp hstate
    exact tendsto_nhds_unique hweak' hstrong
  exact ⟨{
    subseq := sigma
    stateLimit := S.limit
    energyLimit := W.limit
    state_strong := hstate
    energy_weak := henergy
    embed_energyLimit := hidentify
  }⟩

/-- Strong state convergence, weak energy convergence, and uniform convergence
of every finite spectral projection can be realized on one strict
subsequence. -/
theorem exists_strongWeakPathSubsequence :
    Nonempty G.StrongWeakPathSubsequence := by
  obtain ⟨S⟩ := G.exists_strongWeakSubsequence
  exact S.exists_pathwiseRefinement

end LeraySpectralCompactFamily

end LeraySpectral

end
