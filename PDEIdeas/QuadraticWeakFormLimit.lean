import PDEIdeas.QuadraticTensorLimit

open Filter MeasureTheory
open scoped ENNReal

noncomputable section

/-!
# Quadratic weak-form limits

A continuous trilinear form can be viewed as a continuous linear family of
bilinear forms indexed by its test argument.  The canonical projective tensor
limit therefore yields the direct weak-form convergence used for quadratic
transport terms with a bounded time-dependent test path.
-/

/-- Move the test argument of a curried continuous trilinear form to the
front, continuously and linearly. -/
noncomputable def trilinearTestCLM
    {H Test : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup Test] [NormedSpace ℝ Test]
    (T : H →L[ℝ] H →L[ℝ] Test →L[ℝ] ℝ) :
    Test →L[ℝ] H →L[ℝ] H →L[ℝ] ℝ := by
  let flipInner :
      (H →L[ℝ] Test →L[ℝ] ℝ) →L[ℝ]
        Test →L[ℝ] H →L[ℝ] ℝ :=
    (ContinuousLinearMap.flipₗᵢ ℝ H Test ℝ).toLinearIsometry.toContinuousLinearMap
  let first : H →L[ℝ] Test →L[ℝ] H →L[ℝ] ℝ :=
    flipInner.comp T
  exact (ContinuousLinearMap.flipₗᵢ ℝ H Test (H →L[ℝ] ℝ)) first

theorem trilinearTestCLM_apply
    {H Test : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup Test] [NormedSpace ℝ Test]
    (T : H →L[ℝ] H →L[ℝ] Test →L[ℝ] ℝ)
    (ψ : Test) (x y : H) :
    trilinearTestCLM T ψ x y = T x y ψ := by
  rfl

/-- The projective tensor paired with the test argument of a continuous
trilinear form. -/
noncomputable def trilinearProjectiveTensorPairing
    {H Test : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup Test] [NormedSpace ℝ Test]
    (T : H →L[ℝ] H →L[ℝ] Test →L[ℝ] ℝ) :
    SeparatedProjectiveTensorSquare H →L[ℝ] Test →L[ℝ] ℝ := by
  let lifted : Test →L[ℝ] SeparatedProjectiveTensorSquare H →L[ℝ] ℝ :=
    (projectiveTensorLiftCLM H ℝ).comp (trilinearTestCLM T)
  exact (ContinuousLinearMap.flipₗᵢ ℝ Test
    (SeparatedProjectiveTensorSquare H) ℝ) lifted

theorem trilinearProjectiveTensorPairing_tmul
    {H Test : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup Test] [NormedSpace ℝ Test]
    (T : H →L[ℝ] H →L[ℝ] Test →L[ℝ] ℝ)
    (x y : H) (ψ : Test) :
    trilinearProjectiveTensorPairing T
        (projectiveTensorBilinear H x y) ψ =
      T x y ψ := by
  change projectiveTensorLiftCLM H ℝ (trilinearTestCLM T ψ)
      (projectiveTensorBilinear H x y) = T x y ψ
  rw [projectiveTensorLiftCLM_tmul, trilinearTestCLM_apply]

/-- A bounded time-dependent test path induces a continuous linear functional
on tensor-valued `L1` through a continuous trilinear form. -/
noncomputable def projectiveTrilinearTimeDependentTest
    {α H Test : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup Test] [NormedSpace ℝ Test]
    (T : H →L[ℝ] H →L[ℝ] Test →L[ℝ] ℝ)
    (ψ : Lp Test (∞ : ℝ≥0∞) μ) :
    Lp (SeparatedProjectiveTensorSquare H) (1 : ℝ≥0∞) μ →L[ℝ] ℝ := by
  let pairing := trilinearProjectiveTensorPairing T
  let pairingLp :
      Lp (SeparatedProjectiveTensorSquare H) (1 : ℝ≥0∞) μ →L[ℝ]
        Lp Test (∞ : ℝ≥0∞) μ →L[ℝ] ℝ :=
    ContinuousLinearMap.lpPairing (𝕜 := ℝ)
      μ (1 : ℝ≥0∞) (∞ : ℝ≥0∞) pairing
  exact
    (ContinuousLinearMap.flipₗᵢ ℝ
      (Lp (SeparatedProjectiveTensorSquare H) (1 : ℝ≥0∞) μ)
      (Lp Test (∞ : ℝ≥0∞) μ) ℝ) pairingLp ψ

/-- Evaluation of the trilinear tensor test is its `L1`-`L-infinity`
integral pairing. -/
theorem projectiveTrilinearTimeDependentTest_apply
    {α H Test : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup Test] [NormedSpace ℝ Test]
    (T : H →L[ℝ] H →L[ℝ] Test →L[ℝ] ℝ)
    (ψ : Lp Test (∞ : ℝ≥0∞) μ)
    (w : Lp (SeparatedProjectiveTensorSquare H) (1 : ℝ≥0∞) μ) :
    projectiveTrilinearTimeDependentTest T ψ w =
      ∫ t, trilinearProjectiveTensorPairing T (w t) (ψ t) ∂μ := by
  change
    ContinuousLinearMap.lpPairing (𝕜 := ℝ)
      μ (1 : ℝ≥0∞) (∞ : ℝ≥0∞)
        (trilinearProjectiveTensorPairing T) w ψ = _
  exact (trilinearProjectiveTensorPairing T).lpPairing_eq_integral w ψ

/-- On the canonical diagonal tensor, the induced test is exactly the
quadratic trilinear weak-form integral. -/
theorem projectiveTrilinearTimeDependentTest_apply_tensorSquareLp
    {α H Test : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup Test] [NormedSpace ℝ Test]
    (T : H →L[ℝ] H →L[ℝ] Test →L[ℝ] ℝ)
    (ψ : Lp Test (∞ : ℝ≥0∞) μ)
    (u : Lp H (2 : ℝ≥0∞) μ) :
    projectiveTrilinearTimeDependentTest T ψ
        (projectiveTensorSquareLp u) =
      ∫ t, T (u t) (u t) (ψ t) ∂μ := by
  rw [projectiveTrilinearTimeDependentTest_apply]
  apply integral_congr_ae
  filter_upwards [(projectiveTensorBilinear H).coeFn_holder
      (r := (1 : ℝ≥0∞)) u u] with t ht
  change
    trilinearProjectiveTensorPairing T
      (((projectiveTensorBilinear H).holder (1 : ℝ≥0∞) u u) t) (ψ t) =
      T (u t) (u t) (ψ t)
  rw [ht]
  exact trilinearProjectiveTensorPairing_tmul T (u t) (u t) (ψ t)

/-- The jointly continuous space-time pairing between a projective tensor
path and a bounded test path. -/
noncomputable def projectiveTrilinearLpPairing
    {α H Test : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup Test] [NormedSpace ℝ Test]
    (T : H →L[ℝ] H →L[ℝ] Test →L[ℝ] ℝ) :
    Lp (SeparatedProjectiveTensorSquare H) (1 : ℝ≥0∞) μ →L[ℝ]
      Lp Test (∞ : ℝ≥0∞) μ →L[ℝ] ℝ :=
  ContinuousLinearMap.lpPairing (𝕜 := ℝ)
    μ (1 : ℝ≥0∞) (∞ : ℝ≥0∞)
      (trilinearProjectiveTensorPairing T)

/-- Evaluation of the joint tensor-test pairing on a diagonal tensor. -/
theorem projectiveTrilinearLpPairing_apply_tensorSquareLp
    {α H Test : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup Test] [NormedSpace ℝ Test]
    (T : H →L[ℝ] H →L[ℝ] Test →L[ℝ] ℝ)
    (u : Lp H (2 : ℝ≥0∞) μ)
    (ψ : Lp Test (∞ : ℝ≥0∞) μ) :
    projectiveTrilinearLpPairing T (projectiveTensorSquareLp u) ψ =
      ∫ t, T (u t) (u t) (ψ t) ∂μ := by
  change projectiveTrilinearTimeDependentTest T ψ
      (projectiveTensorSquareLp u) = _
  exact projectiveTrilinearTimeDependentTest_apply_tensorSquareLp T ψ u

/-- Direct quadratic weak-form convergence against every bounded
time-dependent test path. -/
theorem StrongMetricSubsequence.projectiveTrilinearIntegral_tendsto
    {α H Test : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup Test] [NormedSpace ℝ Test]
    {x : ℕ → Lp H (2 : ℝ≥0∞) μ}
    (S : StrongMetricSubsequence x)
    (T : H →L[ℝ] H →L[ℝ] Test →L[ℝ] ℝ)
    (ψ : Lp Test (∞ : ℝ≥0∞) μ) :
    Tendsto
      (fun k => ∫ t,
        T (x (S.subseq.idx k) t) (x (S.subseq.idx k) t) (ψ t) ∂μ)
      atTop
      (nhds (∫ t, T (S.limit t) (S.limit t) (ψ t) ∂μ)) := by
  have h := S.projectiveTensorSquareLp_test_tendsto
    (projectiveTrilinearTimeDependentTest T ψ)
  simpa only [projectiveTrilinearTimeDependentTest_apply_tensorSquareLp] using h

/-- Quadratic trilinear integrals remain convergent when the bounded test
path converges simultaneously with the strongly convergent state path. -/
theorem StrongMetricSubsequence.projectiveTrilinearIntegral_tendsto_of_test_tendsto
    {α H Test : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup Test] [NormedSpace ℝ Test]
    {x : ℕ → Lp H (2 : ℝ≥0∞) μ}
    (S : StrongMetricSubsequence x)
    (T : H →L[ℝ] H →L[ℝ] Test →L[ℝ] ℝ)
    (ψ : ℕ → Lp Test (∞ : ℝ≥0∞) μ)
    (ψLimit : Lp Test (∞ : ℝ≥0∞) μ)
    (hψ : Tendsto ψ atTop (nhds ψLimit)) :
    Tendsto
      (fun k => ∫ t,
        T (x (S.subseq.idx k) t) (x (S.subseq.idx k) t) (ψ k t) ∂μ)
      atTop
      (nhds (∫ t, T (S.limit t) (S.limit t) (ψLimit t) ∂μ)) := by
  have hpairs := S.projectiveTensorSquareLp_tendsto.prodMk_nhds hψ
  have hcontinuous :
      Tendsto
        (fun p => projectiveTrilinearLpPairing T p.1 p.2)
        (nhds (projectiveTensorSquareLp S.limit, ψLimit))
        (nhds (projectiveTrilinearLpPairing T
          (projectiveTensorSquareLp S.limit) ψLimit)) :=
    (projectiveTrilinearLpPairing T).continuous₂.continuousAt
  have hpairing := hcontinuous.comp hpairs
  simpa only [Function.comp_def,
    projectiveTrilinearLpPairing_apply_tensorSquareLp] using hpairing

section SpectralEndpoint

open BoundedContinuousFunction
open scoped NNReal RealInnerProductSpace

variable {I V H Test : Type*}
    [PseudoMetricSpace I] [CompactSpace I]
    [MeasurableSpace I] [BorelSpace I] [SecondCountableTopology I]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup Test] [NormedSpace ℝ Test]
    {μ : Measure I} [IsFiniteMeasure μ]

namespace LeraySpectralCompactFamily

variable (G : LeraySpectralCompactFamily
  (I := I) (V := V) (H := H) (μ := μ))

omit [CompleteSpace V] in
/-- One strict spectral subsequence carries the canonical tensor limit and
the tested integral for every continuous trilinear form and every bounded
time-dependent path in a fixed test space. -/
theorem exists_strongL2_projectiveTensorL1_trilinear_tested_subsequence :
    ∃ S : StrongMetricSubsequence G.stateLp,
      Tendsto
          (fun k =>
            projectiveTensorSquareLp (G.stateLp (S.subseq.idx k)))
          atTop (nhds (projectiveTensorSquareLp S.limit)) ∧
        ∀ (T : H →L[ℝ] H →L[ℝ] Test →L[ℝ] ℝ)
            (ψ : Lp Test (∞ : ℝ≥0∞) μ),
          Tendsto
            (fun k => ∫ t,
              T
                (G.stateLp (S.subseq.idx k) t)
                (G.stateLp (S.subseq.idx k) t)
                (ψ t) ∂μ)
            atTop
            (nhds (∫ t, T (S.limit t) (S.limit t) (ψ t) ∂μ)) := by
  obtain ⟨S, hTensor⟩ := G.exists_strongL2_projectiveTensorL1_subsequence
  exact ⟨S, hTensor, fun T ψ =>
    S.projectiveTrilinearIntegral_tendsto T ψ⟩

end LeraySpectralCompactFamily

end SpectralEndpoint
