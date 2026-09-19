import PDEIdeas.GalerkinL2Compactness
import Mathlib.Analysis.Normed.Module.PiTensorProduct.InjectiveSeminorm
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.Algebra.SeparationQuotient.Hom
import Mathlib.Topology.Algebra.SeparationQuotient.Section

open Filter MeasureTheory
open scoped ENNReal TensorProduct

noncomputable section

/-!
# Canonical projective tensor limits

The projective seminorm on the algebraic tensor square makes the elementary
tensor map continuous and bilinear.  Its separation quotient removes the
seminorm kernel, producing a normed target through which every continuous
bilinear map factors.  Applied pointwise, this gives a canonical
`L2 -> L1` quadratic observable and a tensor-valued form of the nonlinear
limit passage.
-/

/-- The algebraic tensor square with the projective seminorm, separated by
its zero-distance relation.  No completion is taken. -/
abbrev SeparatedProjectiveTensorSquare
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] :=
  SeparationQuotient (⨂[ℝ] _ : Fin 2, H)

/-- The canonical continuous bilinear elementary-tensor map into the
separated projective tensor square. -/
noncomputable def projectiveTensorBilinear
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] :
    H →L[ℝ] H →L[ℝ] SeparatedProjectiveTensorSquare H := by
  let quotientMap :
      (⨂[ℝ] _ : Fin 2, H) →L[ℝ] SeparatedProjectiveTensorSquare H :=
    SeparationQuotient.mkCLM ℝ (⨂[ℝ] _ : Fin 2, H)
  let tensorMap :
      ContinuousMultilinearMap ℝ (fun _ : Fin 2 => H)
        (SeparatedProjectiveTensorSquare H) :=
    quotientMap.compContinuousMultilinearMap (PiTensorProduct.tprodL ℝ)
  let curry :
      ContinuousMultilinearMap ℝ (fun _ : Fin 1 => H)
          (SeparatedProjectiveTensorSquare H) →L[ℝ]
        H →L[ℝ] SeparatedProjectiveTensorSquare H :=
    (continuousMultilinearCurryFin1 ℝ H
      (SeparatedProjectiveTensorSquare H)).toLinearIsometry.toContinuousLinearMap
  exact curry.comp tensorMap.curryLeft

/-- The canonical bilinear map sends `(x,y)` to the class of the elementary
projective tensor with entries `x` and `y`. -/
theorem projectiveTensorBilinear_apply
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H]
    (x y : H) :
    projectiveTensorBilinear H x y =
      SeparationQuotient.mk
        (PiTensorProduct.tprod ℝ
          (Fin.cons x (Fin.cons y (fun i : Fin 0 => nomatch i)))) := by
  simp [projectiveTensorBilinear]
  apply Inseparable.of_eq
  congr
  funext i
  fin_cases i

/-- A curried continuous bilinear map, viewed as a two-variable continuous
multilinear map. -/
noncomputable def projectiveTensorUncurryBilinear
    {H N : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (B : H →L[ℝ] H →L[ℝ] N) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 2 => H) N := by
  let uncurryOne :
      (H →L[ℝ] N) →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin 1 => H) N :=
    (continuousMultilinearCurryFin1 ℝ H N).symm.toLinearIsometry.toContinuousLinearMap
  exact (uncurryOne.comp B).uncurryLeft

theorem projectiveTensorUncurryBilinear_apply
    {H N : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (B : H →L[ℝ] H →L[ℝ] N) (x y : H) :
    projectiveTensorUncurryBilinear B
      (Fin.cons x (Fin.cons y (fun i : Fin 0 => nomatch i))) = B x y := by
  simp [projectiveTensorUncurryBilinear]

/-- Universal continuous linear factorization of a continuous bilinear map
through the separated projective tensor square. -/
noncomputable def projectiveTensorLift
    {H N : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (B : H →L[ℝ] H →L[ℝ] N) :
    SeparatedProjectiveTensorSquare H →L[ℝ] N := by
  let tensorLift : (⨂[ℝ] _ : Fin 2, H) →L[ℝ] N :=
    PiTensorProduct.liftIsometry ℝ (fun _ : Fin 2 => H) N
      (projectiveTensorUncurryBilinear B)
  exact SeparationQuotient.liftCLM tensorLift
    (fun x y hxy => (hxy.map tensorLift.continuous).eq)

/-- The universal lift agrees with the original bilinear map on elementary
tensors. -/
theorem projectiveTensorLift_tmul
    {H N : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (B : H →L[ℝ] H →L[ℝ] N) (x y : H) :
    projectiveTensorLift B (projectiveTensorBilinear H x y) = B x y := by
  simp [projectiveTensorLift, projectiveTensorBilinear,
    projectiveTensorUncurryBilinear]

/-- Continuous linear dependence of the projective-tensor lift on the
continuous bilinear map. -/
noncomputable def projectiveTensorLiftCLM
    (H N : Type*)
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup N] [NormedSpace ℝ N] :
    (H →L[ℝ] H →L[ℝ] N) →L[ℝ]
      SeparatedProjectiveTensorSquare H →L[ℝ] N := by
  let oneVariableUncurry :
      (H →L[ℝ] N) →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin 1 => H) N :=
    (continuousMultilinearCurryFin1 ℝ H N).symm.toLinearIsometry.toContinuousLinearMap
  let uncurryInner :
      (H →L[ℝ] H →L[ℝ] N) →L[ℝ]
        H →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin 1 => H) N :=
    (ContinuousLinearMap.compL ℝ H (H →L[ℝ] N)
      (ContinuousMultilinearMap ℝ (fun _ : Fin 1 => H) N))
        oneVariableUncurry
  let uncurryOuter :
      (H →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin 1 => H) N) →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin 2 => H) N :=
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => H) N).symm
      |>.toLinearIsometry.toContinuousLinearMap
  let tensorLift :
      ContinuousMultilinearMap ℝ (fun _ : Fin 2 => H) N →L[ℝ]
        (⨂[ℝ] _ : Fin 2, H) →L[ℝ] N :=
    (PiTensorProduct.liftIsometry ℝ (fun _ : Fin 2 => H) N)
      |>.toLinearIsometry.toContinuousLinearMap
  let quotientLift :
      ((⨂[ℝ] _ : Fin 2, H) →L[ℝ] N) →L[ℝ]
        SeparatedProjectiveTensorSquare H →L[ℝ] N :=
    (ContinuousLinearMap.compL ℝ (SeparatedProjectiveTensorSquare H)
      (⨂[ℝ] _ : Fin 2, H) N).flip
        (SeparationQuotient.outCLM ℝ (⨂[ℝ] _ : Fin 2, H))
  exact quotientLift.comp (tensorLift.comp (uncurryOuter.comp uncurryInner))

/-- The continuously bundled lift agrees with the bilinear map on elementary
tensors. -/
theorem projectiveTensorLiftCLM_tmul
    {H N : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (B : H →L[ℝ] H →L[ℝ] N) (x y : H) :
    projectiveTensorLiftCLM H N B (projectiveTensorBilinear H x y) = B x y := by
  rw [projectiveTensorBilinear_apply]
  change
    (PiTensorProduct.liftIsometry ℝ (fun _ : Fin 2 => H) N
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => H) N).symm
        ((ContinuousLinearMap.compL ℝ H (H →L[ℝ] N)
          (ContinuousMultilinearMap ℝ (fun _ : Fin 1 => H) N)
          ((continuousMultilinearCurryFin1 ℝ H N).symm.toLinearIsometry.toContinuousLinearMap)) B)))
      (SeparationQuotient.outCLM ℝ (⨂[ℝ] _ : Fin 2, H)
        (SeparationQuotient.mk
          (PiTensorProduct.tprod ℝ
            (Fin.cons x (Fin.cons y (fun i : Fin 0 => nomatch i)))))) = B x y
  let z : (⨂[ℝ] _ : Fin 2, H) :=
    PiTensorProduct.tprod ℝ
      (Fin.cons x (Fin.cons y (fun i : Fin 0 => nomatch i)))
  let tensorLift : (⨂[ℝ] _ : Fin 2, H) →L[ℝ] N :=
    PiTensorProduct.liftIsometry ℝ (fun _ : Fin 2 => H) N
      (projectiveTensorUncurryBilinear B)
  have hsep :
      Inseparable
        (SeparationQuotient.outCLM ℝ (⨂[ℝ] _ : Fin 2, H)
          (SeparationQuotient.mk z)) z :=
    SeparationQuotient.mk_eq_mk.mp (by simp)
  rw [show
    PiTensorProduct.liftIsometry ℝ (fun _ : Fin 2 => H) N
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => H) N).symm
        ((ContinuousLinearMap.compL ℝ H (H →L[ℝ] N)
          (ContinuousMultilinearMap ℝ (fun _ : Fin 1 => H) N)
          ((continuousMultilinearCurryFin1 ℝ H N).symm.toLinearIsometry.toContinuousLinearMap)) B)) =
      tensorLift by
    congr]
  rw [(hsep.map tensorLift.continuous).eq]
  simp [tensorLift, z, projectiveTensorUncurryBilinear]

/-- The canonical diagonal tensor observable from `L2` to tensor-valued
`L1`. -/
noncomputable def projectiveTensorSquareLp
    {α H : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (u : Lp H (2 : ℝ≥0∞) μ) :
    Lp (SeparatedProjectiveTensorSquare H) (1 : ℝ≥0∞) μ :=
  (projectiveTensorBilinear H).quadraticLp u

/-- Every continuous quadratic `L1` observable is the pointwise continuous
linear image of the canonical tensor square. -/
theorem projectiveTensorLift_tensorSquareLp
    {α H N : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (B : H →L[ℝ] H →L[ℝ] N)
    (u : Lp H (2 : ℝ≥0∞) μ) :
    (projectiveTensorLift B).compLpL (1 : ℝ≥0∞) μ
        (projectiveTensorSquareLp u) =
      B.quadraticLp u := by
  apply Lp.ext
  filter_upwards [
    (projectiveTensorLift B).coeFn_compLpL
      (projectiveTensorSquareLp u),
    (projectiveTensorBilinear H).coeFn_holder
      (r := (1 : ℝ≥0∞)) u u,
    B.coeFn_holder (r := (1 : ℝ≥0∞)) u u] with x hLift hTensor hB
  rw [hLift]
  change
    projectiveTensorLift B
        (((projectiveTensorBilinear H).holder (1 : ℝ≥0∞) u u) x) =
      (B.holder (1 : ℝ≥0∞) u u) x
  rw [hTensor, hB]
  exact projectiveTensorLift_tmul B (u x) (u x)

/-- The canonical tensor-square map is continuous from `L2` to `L1`. -/
theorem continuous_projectiveTensorSquareLp
    {α H : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup H] [NormedSpace ℝ H] :
    Continuous
      (projectiveTensorSquareLp (α := α) (H := H) (μ := μ)) := by
  simpa only [projectiveTensorSquareLp] using
    (projectiveTensorBilinear H).continuous_quadraticLp (μ := μ)

/-- Strong `L2` convergence gives strong tensor-valued `L1` convergence of
the diagonal projective tensor. -/
theorem StrongMetricSubsequence.projectiveTensorSquareLp_tendsto
    {α H : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {x : ℕ → Lp H (2 : ℝ≥0∞) μ}
    (S : StrongMetricSubsequence x) :
    Tendsto
      (fun k => projectiveTensorSquareLp (x (S.subseq.idx k)))
      atTop (nhds (projectiveTensorSquareLp S.limit)) := by
  simpa only [projectiveTensorSquareLp] using
    S.quadraticLp_tendsto (projectiveTensorBilinear H)

/-- Every continuous linear test on tensor-valued `L1` passes to the strong
tensor limit. -/
theorem StrongMetricSubsequence.projectiveTensorSquareLp_test_tendsto
    {α H : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {x : ℕ → Lp H (2 : ℝ≥0∞) μ}
    (S : StrongMetricSubsequence x)
    (test :
      Lp (SeparatedProjectiveTensorSquare H) (1 : ℝ≥0∞) μ →L[ℝ] ℝ) :
    Tendsto
      (fun k => test (projectiveTensorSquareLp (x (S.subseq.idx k))))
      atTop (nhds (test (projectiveTensorSquareLp S.limit))) :=
  test.continuous.continuousAt.tendsto.comp
    S.projectiveTensorSquareLp_tendsto

/-- Apply a continuous tensor functional pointwise and integrate its scalar
value.  This is a continuous linear test on tensor-valued `L1`. -/
noncomputable def projectiveTensorIntegralTest
    {α H : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (test : SeparatedProjectiveTensorSquare H →L[ℝ] ℝ) :
    Lp (SeparatedProjectiveTensorSquare H) (1 : ℝ≥0∞) μ →L[ℝ] ℝ :=
  (L1.integralCLM (α := α) (E := ℝ) (μ := μ)).comp
    (test.compLpL (1 : ℝ≥0∞) μ)

/-- Evaluation of the integrated test is the Bochner integral of the
pointwise tensor functional. -/
theorem projectiveTensorIntegralTest_apply
    {α H : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (test : SeparatedProjectiveTensorSquare H →L[ℝ] ℝ)
    (w : Lp (SeparatedProjectiveTensorSquare H) (1 : ℝ≥0∞) μ) :
    projectiveTensorIntegralTest test w = ∫ x, test (w x) ∂μ := by
  rw [projectiveTensorIntegralTest, ContinuousLinearMap.comp_apply,
    ← L1.integral_eq, L1.integral_eq_integral]
  exact integral_congr_ae (test.coeFn_compLpL w)

/-- Integrated pointwise tensor tests converge along every strong `L2`
subsequence. -/
theorem StrongMetricSubsequence.projectiveTensorIntegralTest_tendsto
    {α H : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {x : ℕ → Lp H (2 : ℝ≥0∞) μ}
    (S : StrongMetricSubsequence x)
    (test : SeparatedProjectiveTensorSquare H →L[ℝ] ℝ) :
    Tendsto
      (fun k => projectiveTensorIntegralTest test
        (projectiveTensorSquareLp (x (S.subseq.idx k))))
      atTop
      (nhds (projectiveTensorIntegralTest test
        (projectiveTensorSquareLp S.limit))) :=
  S.projectiveTensorSquareLp_test_tendsto
    (projectiveTensorIntegralTest test)

/-- Pair a tensor-valued `L1` function against a bounded time-dependent field
of continuous tensor functionals in `L-infinity`. -/
noncomputable def projectiveTensorTimeDependentTest
    {α H : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (test : Lp (SeparatedProjectiveTensorSquare H →L[ℝ] ℝ)
      (∞ : ℝ≥0∞) μ) :
    Lp (SeparatedProjectiveTensorSquare H) (1 : ℝ≥0∞) μ →L[ℝ] ℝ :=
  ((ContinuousLinearMap.apply ℝ ℝ :
      SeparatedProjectiveTensorSquare H →L[ℝ]
        (SeparatedProjectiveTensorSquare H →L[ℝ] ℝ) →L[ℝ] ℝ).lpPairing
      μ (1 : ℝ≥0∞) (∞ : ℝ≥0∞)).flip test

/-- The time-dependent tensor test is the integral of the pointwise dual
pairing. -/
theorem projectiveTensorTimeDependentTest_apply
    {α H : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (test : Lp (SeparatedProjectiveTensorSquare H →L[ℝ] ℝ)
      (∞ : ℝ≥0∞) μ)
    (w : Lp (SeparatedProjectiveTensorSquare H) (1 : ℝ≥0∞) μ) :
    projectiveTensorTimeDependentTest test w =
      ∫ x, test x (w x) ∂μ := by
  simpa [projectiveTensorTimeDependentTest] using
    ((ContinuousLinearMap.apply ℝ ℝ :
      SeparatedProjectiveTensorSquare H →L[ℝ]
        (SeparatedProjectiveTensorSquare H →L[ℝ] ℝ) →L[ℝ] ℝ).lpPairing_eq_integral
          w test)

/-- Bounded time-dependent tensor tests converge along every strong `L2`
subsequence. -/
theorem StrongMetricSubsequence.projectiveTensorTimeDependentTest_tendsto
    {α H : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {x : ℕ → Lp H (2 : ℝ≥0∞) μ}
    (S : StrongMetricSubsequence x)
    (test : Lp (SeparatedProjectiveTensorSquare H →L[ℝ] ℝ)
      (∞ : ℝ≥0∞) μ) :
    Tendsto
      (fun k => projectiveTensorTimeDependentTest test
        (projectiveTensorSquareLp (x (S.subseq.idx k))))
      atTop
      (nhds (projectiveTensorTimeDependentTest test
        (projectiveTensorSquareLp S.limit))) :=
  S.projectiveTensorSquareLp_test_tendsto
    (projectiveTensorTimeDependentTest test)

/-- Convert a bounded time-dependent family of continuous bilinear forms into
a continuous test on the canonical tensor-valued `L1` space. -/
noncomputable def projectiveBilinearTimeDependentTest
    {α H : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (test : Lp (H →L[ℝ] H →L[ℝ] ℝ) (∞ : ℝ≥0∞) μ) :
    Lp (SeparatedProjectiveTensorSquare H) (1 : ℝ≥0∞) μ →L[ℝ] ℝ := by
  let pairing :
      SeparatedProjectiveTensorSquare H →L[ℝ]
        (H →L[ℝ] H →L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.flipₗᵢ ℝ
      (H →L[ℝ] H →L[ℝ] ℝ)
      (SeparatedProjectiveTensorSquare H) ℝ)
        (projectiveTensorLiftCLM H ℝ)
  let pairingLp :
      Lp (SeparatedProjectiveTensorSquare H) (1 : ℝ≥0∞) μ →L[ℝ]
        Lp (H →L[ℝ] H →L[ℝ] ℝ) (∞ : ℝ≥0∞) μ →L[ℝ] ℝ :=
    ContinuousLinearMap.lpPairing (𝕜 := ℝ)
      μ (1 : ℝ≥0∞) (∞ : ℝ≥0∞) pairing
  exact
    (ContinuousLinearMap.flipₗᵢ ℝ
      (Lp (SeparatedProjectiveTensorSquare H) (1 : ℝ≥0∞) μ)
      (Lp (H →L[ℝ] H →L[ℝ] ℝ) (∞ : ℝ≥0∞) μ) ℝ)
        pairingLp test

/-- Evaluation of a time-dependent bilinear test on a tensor-valued `L1`
function is its `L1`-`L-infinity` integral pairing. -/
theorem projectiveBilinearTimeDependentTest_apply
    {α H : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (test : Lp (H →L[ℝ] H →L[ℝ] ℝ) (∞ : ℝ≥0∞) μ)
    (w : Lp (SeparatedProjectiveTensorSquare H) (1 : ℝ≥0∞) μ) :
    projectiveBilinearTimeDependentTest test w =
      ∫ x, projectiveTensorLiftCLM H ℝ (test x) (w x) ∂μ := by
  let pairing :
      SeparatedProjectiveTensorSquare H →L[ℝ]
        (H →L[ℝ] H →L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.flipₗᵢ ℝ
      (H →L[ℝ] H →L[ℝ] ℝ)
      (SeparatedProjectiveTensorSquare H) ℝ)
        (projectiveTensorLiftCLM H ℝ)
  change
    ContinuousLinearMap.lpPairing (𝕜 := ℝ)
      μ (1 : ℝ≥0∞) (∞ : ℝ≥0∞) pairing w test = _
  simpa [pairing] using
    (ContinuousLinearMap.lpPairing_eq_integral (𝕜 := ℝ) pairing w test)

/-- On a diagonal elementary tensor, the bundled time-dependent test is the
integral of the original bilinear form. -/
theorem projectiveBilinearTimeDependentTest_apply_tensorSquareLp
    {α H : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (test : Lp (H →L[ℝ] H →L[ℝ] ℝ) (∞ : ℝ≥0∞) μ)
    (u : Lp H (2 : ℝ≥0∞) μ) :
    projectiveBilinearTimeDependentTest test
        (projectiveTensorSquareLp u) =
      ∫ x, test x (u x) (u x) ∂μ := by
  rw [projectiveBilinearTimeDependentTest_apply]
  apply integral_congr_ae
  filter_upwards [(projectiveTensorBilinear H).coeFn_holder
      (r := (1 : ℝ≥0∞)) u u] with x hTensor
  change
    projectiveTensorLiftCLM H ℝ (test x)
        (((projectiveTensorBilinear H).holder (1 : ℝ≥0∞) u u) x) =
      test x (u x) (u x)
  rw [hTensor]
  exact projectiveTensorLiftCLM_tmul (test x) (u x) (u x)

/-- A bounded time-dependent bilinear form converges when tested on the
canonical tensor squares of a strong `L2` subsequence. -/
theorem StrongMetricSubsequence.projectiveBilinearTimeDependentTest_tendsto
    {α H : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {x : ℕ → Lp H (2 : ℝ≥0∞) μ}
    (S : StrongMetricSubsequence x)
    (test : Lp (H →L[ℝ] H →L[ℝ] ℝ) (∞ : ℝ≥0∞) μ) :
    Tendsto
      (fun k => projectiveBilinearTimeDependentTest test
        (projectiveTensorSquareLp (x (S.subseq.idx k))))
      atTop
      (nhds (projectiveBilinearTimeDependentTest test
        (projectiveTensorSquareLp S.limit))) :=
  S.projectiveTensorSquareLp_test_tendsto
    (projectiveBilinearTimeDependentTest test)

/-- Direct tested-integral form of the quadratic limit: every bounded
time-dependent continuous bilinear form passes along a strong `L2`
subsequence. -/
theorem StrongMetricSubsequence.projectiveBilinearIntegral_tendsto
    {α H : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {x : ℕ → Lp H (2 : ℝ≥0∞) μ}
    (S : StrongMetricSubsequence x)
    (test : Lp (H →L[ℝ] H →L[ℝ] ℝ) (∞ : ℝ≥0∞) μ) :
    Tendsto
      (fun k => ∫ t,
        test t (x (S.subseq.idx k) t) (x (S.subseq.idx k) t) ∂μ)
      atTop
      (nhds (∫ t, test t (S.limit t) (S.limit t) ∂μ)) := by
  simpa only [projectiveBilinearTimeDependentTest_apply_tensorSquareLp] using
    S.projectiveBilinearTimeDependentTest_tendsto test

section SpectralEndpoint

open BoundedContinuousFunction
open scoped NNReal RealInnerProductSpace

variable {I V H : Type*}
    [PseudoMetricSpace I] [CompactSpace I]
    [MeasurableSpace I] [BorelSpace I] [SecondCountableTopology I]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {μ : Measure I} [IsFiniteMeasure μ]

namespace LeraySpectralCompactFamily

variable (G : LeraySpectralCompactFamily
  (I := I) (V := V) (H := H) (μ := μ))

omit [CompleteSpace V] in
/-- Spectral Galerkin compactness produces a strict subsequence whose
canonical diagonal projective tensors converge strongly in `L1`. -/
theorem exists_strongL2_projectiveTensorL1_subsequence :
    ∃ S : StrongMetricSubsequence G.stateLp,
      Tendsto
        (fun k =>
          projectiveTensorSquareLp (G.stateLp (S.subseq.idx k)))
        atTop (nhds (projectiveTensorSquareLp S.limit)) := by
  obtain ⟨S⟩ := G.exists_strongL2_subsequence
  exact ⟨S, S.projectiveTensorSquareLp_tendsto⟩

omit [CompleteSpace V] in
/-- One extracted spectral subsequence simultaneously carries tensor-valued
strong `L1` convergence and every bounded time-dependent tensor test. -/
theorem exists_strongL2_projectiveTensorL1_tested_subsequence :
    ∃ S : StrongMetricSubsequence G.stateLp,
      Tendsto
          (fun k =>
            projectiveTensorSquareLp (G.stateLp (S.subseq.idx k)))
          atTop (nhds (projectiveTensorSquareLp S.limit)) ∧
        ∀ test :
            Lp (SeparatedProjectiveTensorSquare H →L[ℝ] ℝ)
              (∞ : ℝ≥0∞) μ,
          Tendsto
            (fun k => projectiveTensorTimeDependentTest test
              (projectiveTensorSquareLp
                (G.stateLp (S.subseq.idx k))))
            atTop
            (nhds (projectiveTensorTimeDependentTest test
              (projectiveTensorSquareLp S.limit))) := by
  obtain ⟨S, hTensor⟩ := G.exists_strongL2_projectiveTensorL1_subsequence
  exact ⟨S, hTensor, fun test =>
    S.projectiveTensorTimeDependentTest_tendsto test⟩

omit [CompleteSpace V] in
/-- One extracted spectral subsequence carries the tensor limit together with
the tested integral for every bounded time-dependent continuous bilinear
form. -/
theorem exists_strongL2_projectiveTensorL1_bilinear_tested_subsequence :
    ∃ S : StrongMetricSubsequence G.stateLp,
      Tendsto
          (fun k =>
            projectiveTensorSquareLp (G.stateLp (S.subseq.idx k)))
          atTop (nhds (projectiveTensorSquareLp S.limit)) ∧
        ∀ test : Lp (H →L[ℝ] H →L[ℝ] ℝ) (∞ : ℝ≥0∞) μ,
          Tendsto
            (fun k => ∫ t,
              test t
                (G.stateLp (S.subseq.idx k) t)
                (G.stateLp (S.subseq.idx k) t) ∂μ)
            atTop
            (nhds (∫ t, test t (S.limit t) (S.limit t) ∂μ)) := by
  obtain ⟨S, hTensor⟩ := G.exists_strongL2_projectiveTensorL1_subsequence
  exact ⟨S, hTensor, fun test =>
    S.projectiveBilinearIntegral_tendsto test⟩

end LeraySpectralCompactFamily

end SpectralEndpoint
