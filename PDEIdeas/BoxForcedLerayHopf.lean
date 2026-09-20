import PDEIdeas.BoxForcedLerayHopfLimit

/-!
# Forced Leray--Hopf weak solutions on a two-dimensional box

The exact finite energy balance of a forced spectral trajectory pairs the
accumulated dissipation with the accumulated work of the forcing.  Restriction
to an initial time segment turns the accumulated work into a bounded
functional on the time--energy space, so weak convergence passes it to the
limit while weak lower semicontinuity handles the state and gradient terms.
Together with the forced time-tested weak equation this produces a forced
Leray--Hopf weak solution on every finite interval, for every continuous
energy-dual forcing with a continuous nonnegative dual-norm majorant.
-/

open BoundedContinuousFunction Filter InnerProductSpace MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

noncomputable section

local instance box_forced_solution_fact_one_le_four : Fact (1 ≤ (4 : ℝ≥0∞)) :=
  ⟨by norm_num⟩

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 500000

/-- Normed-group specialization of the indicator membership lemma. -/
theorem memLp_indicator_normed {α E : Type*} {m : MeasurableSpace α}
    [NormedAddCommGroup E] {μ : Measure α} {p : ℝ≥0∞} {s : Set α}
    {f : α → E} (hs : MeasurableSet s) (hf : MemLp f p μ) :
    MemLp (Set.indicator s f) p μ :=
  MeasureTheory.MemLp.indicator hs hf

/-- Pairing a truncated field against a test field truncates the pointwise
pairing. -/
theorem inner_indicator_left {α E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {s : Set α} (f g : α → E) {x : α} :
    ⟪Set.indicator s f x, g x⟫_ℝ =
      Set.indicator s (fun y => ⟪f y, g y⟫_ℝ) x := by
  by_cases hmem : x ∈ s
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem,
      inner_zero_left]

namespace BoxDualForcing

variable {I : BoxIntegral.Box (Fin 2)} (Φ : BoxDualForcing I)

/-- The Riesz path of the forcing truncated to an initial time segment. -/
def repIicLp (a b : ℝ) (t : Icc a b) :
    Lp (BoxH1ZeroSigma I) (2 : ℝ≥0∞)
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) :=
  MeasureTheory.MemLp.toLp _
    (memLp_indicator_normed (s := Set.Iic t) measurableSet_Iic
      (Lp.memLp (Φ.repLp a b)))

/-- The truncated Riesz path is represented by the truncated forcing path. -/
theorem repIicLp_ae (a b : ℝ) (t : Icc a b) :
    Φ.repIicLp a b t =ᵐ[
      SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b]
        Set.indicator (Set.Iic t) (fun s : Icc a b => Φ.rep (s : ℝ)) := by
  refine (MeasureTheory.MemLp.coeFn_toLp _).trans ?_
  filter_upwards [Φ.repLp_ae a b] with s hs
  by_cases hmem : s ∈ Set.Iic t
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, hs]
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]

/-- Accumulated forcing work up to a time, as a bounded functional on the
time--energy space. -/
def workCLM (a b : ℝ) (t : Icc a b) :
    Lp (BoxH1ZeroSigma I) (2 : ℝ≥0∞)
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) →L[ℝ]
      ℝ :=
  innerSL ℝ (Φ.repIicLp a b t)

/-- The work functional is the pairing with the truncated Riesz path. -/
theorem workCLM_inner {a b : ℝ} (t : Icc a b)
    (w : Lp (BoxH1ZeroSigma I) (2 : ℝ≥0∞)
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)) :
    Φ.workCLM a b t w = ⟪Φ.repIicLp a b t, w⟫_ℝ := rfl

set_option maxHeartbeats 16000000 in
/-- The work functional accumulates the action of the forcing on an initial
time segment. -/
theorem workCLM_apply {a b : ℝ} (t : Icc a b)
    (w : Lp (BoxH1ZeroSigma I) (2 : ℝ≥0∞)
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)) :
    Φ.workCLM a b t w =
      ∫ s : Icc a b in Set.Iic t, Φ.value (s : ℝ) (w s)
        ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b := by
  rw [Φ.workCLM_inner t w, MeasureTheory.L2.inner_def]
  refine Eq.trans ?_ (MeasureTheory.integral_indicator
    (μ := SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)
    (f := fun r : Icc a b => Φ.value (r : ℝ) (w r))
    (s := Set.Iic t) measurableSet_Iic)
  apply integral_congr_ae
  filter_upwards [Φ.repIicLp_ae a b t] with s hs
  rw [hs]
  refine (inner_indicator_left (s := Set.Iic t) (x := s)
    (fun r : Icc a b => Φ.rep (r : ℝ))
    (fun r : Icc a b => (w : Icc a b → BoxH1ZeroSigma I) r)).trans ?_
  exact congrArg (fun F : Icc a b → ℝ => Set.indicator (Set.Iic t) F s)
    (funext fun r => (Φ.value_apply (r : ℝ)
      ((w : Icc a b → BoxH1ZeroSigma I) r)).symm)

end BoxDualForcing

namespace BoxCompactSpectralRepresentation

variable {I : BoxIntegral.Box (Fin 2)}
    (S : BoxCompactSpectralRepresentation I)

local instance box_forced_energy_h_complete : CompleteSpace (BoxL2Sigma I) :=
  boxL2Sigma_completeSpace I

local instance box_forced_energy_v_complete : CompleteSpace (BoxH1ZeroSigma I) :=
  boxH1ZeroSigma_completeSpace I

section ForcedEnergy

variable {a b : ℝ} (hab : a ≤ b) (Φ : BoxDualForcing I) (u₀ : BoxL2Sigma I)

set_option maxHeartbeats 5000000 in
/-- The gradient part of every forced spectral lift satisfies the explicit
dissipation bound inherited from the finite energy balance. -/
theorem forced_gradientTimeMap_norm_le (m : ℕ) :
    ‖(boxEnergyGradient I).compLpL 2
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)
        ((S.forcedLeraySpectralCompactFamily2D hab Φ u₀).energyLp m)‖ ≤
      Φ.stateRadius a b u₀ := by
  let G := S.forcedLeraySpectralCompactFamily2D hab Φ u₀
  let μ := SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b
  let gradLp : Lp (BoxGradientL2 I) (2 : ℝ≥0∞) μ :=
    (boxEnergyGradient I).compLpL 2 μ (G.energyLp m)
  have hgradAe : gradLp =ᵐ[μ] fun t =>
      boxEnergyGradient I (S.forcedEnergyTrajectory2D hab Φ u₀ m t) := by
    filter_upwards [(boxEnergyGradient I).coeFn_compLpL (G.energyLp m),
      S.forced_energyLp_eq_trajectory_ae hab Φ u₀ m] with t hgrad henergy
    rw [hgrad, henergy]
    rfl
  have hsq : ‖gradLp‖ ^ 2 ≤ Φ.stateRadius a b u₀ ^ 2 := by
    calc
      ‖gradLp‖ ^ 2 = ∫ t, ‖gradLp t‖ ^ 2 ∂μ :=
        Lp.norm_two_sq_eq_integral_norm_sq gradLp
      _ = ∫ t : Icc a b,
          ‖boxEnergyGradient I
            (S.forcedEnergyTrajectory2D hab Φ u₀ m t)‖ ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [hgradAe] with t ht
        rw [ht]
      _ = ∫ t : Icc a b,
          boxGradientDiffusion I
            (S.forcedEnergyTrajectory2D hab Φ u₀ m t)
            (S.forcedEnergyTrajectory2D hab Φ u₀ m t) ∂μ := by
        apply integral_congr_ae
        filter_upwards with t
        exact (boxGradientDiffusion_self I _).symm
      _ = ∫ t in a..b,
          boxGradientDiffusion I
            (S.forcedEnergyTrajectory2D hab Φ u₀ m t)
            (S.forcedEnergyTrajectory2D hab Φ u₀ m t) := by
          simpa only [μ] using
            SmoothBoxVariationalGalerkinLevel.integral_intervalSubtypeMeasure
              hab (fun t => boxGradientDiffusion I
                (S.forcedEnergyTrajectory2D hab Φ u₀ m t)
                (S.forcedEnergyTrajectory2D hab Φ u₀ m t))
      _ = ∫ t in a..b,
          (S.variationalProblem2D m Φ.value
            (S.stateInitialCoefficient m u₀)).system.diffusion
            (S.forcedCoefficientTrajectory2D hab Φ u₀ m t)
            (S.forcedCoefficientTrajectory2D hab Φ u₀ m t) := by
        apply intervalIntegral.integral_congr
        intro t _ht
        exact (S.variationalProblem2D_diffusion_apply m Φ.value (S.stateInitialCoefficient m u₀)
          (S.forcedCoefficientTrajectory2D hab Φ u₀ m t)
          (S.forcedCoefficientTrajectory2D hab Φ u₀ m t)).symm
      _ ≤ Φ.stateRadius a b u₀ ^ 2 :=
        S.forcedSolution2D_diffusion_integral_le hab m Φ u₀
          (S.forcedSolution2D hab m Φ u₀)
  exact (sq_le_sq₀ (norm_nonneg gradLp)
    (Φ.stateRadius_nonneg a b u₀)).mp hsq

set_option maxHeartbeats 5000000 in
/-- The forced weak energy limit inherits the accumulated gradient bound. -/
theorem forced_gradientLimit_norm_le
    (SW : (S.forcedLeraySpectralCompactFamily2D hab Φ u₀).StrongWeakSubsequence) :
    ‖(boxEnergyGradient I).compLpL 2
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)
        SW.energyLimit‖ ≤ Φ.stateRadius a b u₀ := by
  let G := S.forcedLeraySpectralCompactFamily2D hab Φ u₀
  let μ := SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b
  let A : Lp (BoxH1ZeroSigma I) (2 : ℝ≥0∞) μ →L[ℝ]
      Lp (BoxGradientL2 I) (2 : ℝ≥0∞) μ :=
    (boxEnergyGradient I).compLpL 2 μ
  let y : Lp (BoxGradientL2 I) (2 : ℝ≥0∞) μ := A SW.energyLimit
  let ell : Lp (BoxH1ZeroSigma I) (2 : ℝ≥0∞) μ →L[ℝ] ℝ :=
    (innerSLFlip ℝ y).comp A
  have hweak : Tendsto
      (fun k => ⟪A (G.energyLp (SW.subseq.idx k)), y⟫_ℝ)
      atTop (nhds ⟪y, y⟫_ℝ) := by
    have hbase :=
      @LeraySpectralCompactFamily.StrongWeakSubsequence.energy_clm_tendsto
        (Icc a b) (BoxH1ZeroSigma I) (BoxL2Sigma I)
        inferInstance inferInstance inferInstance inferInstance
        inferInstance inferInstance (boxH1ZeroSigma_completeSpace I)
        inferInstance inferInstance μ inferInstance G SW ell
    simpa only [ell, y, ContinuousLinearMap.comp_apply,
      innerSLFlip_apply_apply] using hbase
  have hsq : ‖y‖ ^ 2 ≤ Φ.stateRadius a b u₀ * ‖y‖ := by
    calc
      ‖y‖ ^ 2 = ⟪y, y⟫_ℝ := (real_inner_self_eq_norm_sq y).symm
      _ ≤ Φ.stateRadius a b u₀ * ‖y‖ := by
        apply le_of_tendsto hweak
        filter_upwards with k
        calc
          ⟪A (G.energyLp (SW.subseq.idx k)), y⟫_ℝ ≤
              ‖A (G.energyLp (SW.subseq.idx k))‖ * ‖y‖ :=
            real_inner_le_norm _ _
          _ ≤ Φ.stateRadius a b u₀ * ‖y‖ :=
            mul_le_mul_of_nonneg_right
              (S.forced_gradientTimeMap_norm_le hab Φ u₀ (SW.subseq.idx k))
              (norm_nonneg _)
  change ‖y‖ ≤ Φ.stateRadius a b u₀
  by_cases hzero : ‖y‖ = 0
  · rw [hzero]
    exact Φ.stateRadius_nonneg a b u₀
  · have hpos : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    nlinarith [hsq]

set_option maxHeartbeats 3000000 in
/-- At one forced spectral level, the restricted gradient norm is the
accumulated gradient integral from `a` to `t`. -/
theorem forced_restrictedGradientTimeMap_norm_sq (m : ℕ) (t : Icc a b) :
    ‖restrictedGradientTimeMap (I := I) t
        ((S.forcedLeraySpectralCompactFamily2D hab Φ u₀).energyLp m)‖ ^ 2 =
      ∫ s in a..(t : ℝ),
        ‖boxEnergyGradient I
          (S.forcedEnergyTrajectory2D hab Φ u₀ m s)‖ ^ 2 := by
  let G := S.forcedLeraySpectralCompactFamily2D hab Φ u₀
  let μ := SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b
  let gradLp := restrictedGradientTimeMap (I := I) t (G.energyLp m)
  have hgradAe : gradLp =ᵐ[μ.restrict (Set.Iic t)] fun s =>
      boxEnergyGradient I (S.forcedEnergyTrajectory2D hab Φ u₀ m s) := by
    filter_upwards [restrictedGradientTimeMap_ae (I := I) t (G.energyLp m),
      ae_restrict_of_ae
        (S.forced_energyLp_eq_trajectory_ae hab Φ u₀ m)] with s hgrad henergy
    rw [hgrad, henergy]
  calc
    ‖restrictedGradientTimeMap (I := I) t (G.energyLp m)‖ ^ 2 =
        ∫ s, ‖gradLp s‖ ^ 2 ∂(μ.restrict (Set.Iic t)) := by
      simpa only [gradLp] using Lp.norm_two_sq_eq_integral_norm_sq gradLp
    _ = ∫ s : Icc a b in Set.Iic t,
        ‖boxEnergyGradient I
          (S.forcedEnergyTrajectory2D hab Φ u₀ m s)‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hgradAe] with s hs
      rw [hs]
    _ = ∫ s in a..(t : ℝ),
        ‖boxEnergyGradient I
          (S.forcedEnergyTrajectory2D hab Φ u₀ m s)‖ ^ 2 := by
      simpa only [μ] using integral_Iic_intervalSubtypeMeasure hab t
        (fun s => ‖boxEnergyGradient I
          (S.forcedEnergyTrajectory2D hab Φ u₀ m s)‖ ^ 2)

set_option maxHeartbeats 2000000 in
/-- Diffusion energy of a finite forced trajectory is integrable on every
initial subinterval. -/
theorem forced_diffusion_intervalIntegrable (m : ℕ) (t : Icc a b) :
    IntervalIntegrable
      (fun s => (S.variationalProblem2D m Φ.value (S.stateInitialCoefficient m u₀)).system.diffusion
        (S.forcedCoefficientTrajectory2D hab Φ u₀ m s)
        (S.forcedCoefficientTrajectory2D hab Φ u₀ m s)) volume a (t : ℝ) := by
  simpa only [forcedCoefficientTrajectory2D, canonicalSolutionToFun] using
    @VariationalGalerkinProblem.LocalSolutionOn.diffusion_intervalIntegrable
      (S.CoefficientSpace m)
      (S.coefficientSpaceNormedAddCommGroup m)
      (S.coefficientSpaceInnerProductSpace m)
      (S.coefficientSpaceCompleteSpace m)
      (S.variationalProblem2D m Φ.value (S.stateInitialCoefficient m u₀)) a b
      (⟨a, le_rfl, hab⟩ : Icc a b)
      (S.forcedSolution2D hab m Φ u₀)
      a (t : ℝ) (⟨le_rfl, hab⟩ : a ∈ Icc a b) t.property t.property.1

set_option maxHeartbeats 2000000 in
/-- Forcing work of a finite forced trajectory is integrable on every initial
subinterval. -/
theorem forced_forcing_intervalIntegrable (m : ℕ) (t : Icc a b) :
    IntervalIntegrable
      (fun s => (S.variationalProblem2D m Φ.value (S.stateInitialCoefficient m u₀)).forcing s
        (S.forcedCoefficientTrajectory2D hab Φ u₀ m s)) volume a (t : ℝ) := by
  simpa only [forcedCoefficientTrajectory2D, canonicalSolutionToFun] using
    @VariationalGalerkinProblem.LocalSolutionOn.forcing_intervalIntegrable
      (S.CoefficientSpace m)
      (S.coefficientSpaceNormedAddCommGroup m)
      (S.coefficientSpaceInnerProductSpace m)
      (S.coefficientSpaceCompleteSpace m)
      (S.variationalProblem2D m Φ.value (S.stateInitialCoefficient m u₀)) a b
      (⟨a, le_rfl, hab⟩ : Icc a b)
      (S.forcedSolution2D hab m Φ u₀)
      (S.forcedProblem2D_forcing_continuous m Φ u₀)
      a (t : ℝ) (⟨le_rfl, hab⟩ : a ∈ Icc a b) t.property t.property.1

set_option maxHeartbeats 3000000 in
/-- Exact coefficient-space energy balance of a forced trajectory on every
initial subinterval. -/
theorem forced_coefficient_energy_balance (m : ℕ) (t : Icc a b) :
    ‖S.forcedCoefficientTrajectory2D hab Φ u₀ m t‖ ^ 2 +
        2 * ∫ s in a..(t : ℝ),
          (S.variationalProblem2D m Φ.value (S.stateInitialCoefficient m u₀)).system.diffusion
            (S.forcedCoefficientTrajectory2D hab Φ u₀ m s)
            (S.forcedCoefficientTrajectory2D hab Φ u₀ m s) =
      ‖S.stateInitialCoefficient m u₀‖ ^ 2 +
        2 * ∫ s in a..(t : ℝ),
          (S.variationalProblem2D m Φ.value (S.stateInitialCoefficient m u₀)).forcing s
            (S.forcedCoefficientTrajectory2D hab Φ u₀ m s) := by
  have hbalance :=
    @VariationalGalerkinProblem.LocalSolutionOn.energyIdentityOn
      (S.CoefficientSpace m)
      (S.coefficientSpaceNormedAddCommGroup m)
      (S.coefficientSpaceInnerProductSpace m)
      (S.coefficientSpaceCompleteSpace m)
      (S.variationalProblem2D m Φ.value (S.stateInitialCoefficient m u₀)) a b
      (⟨a, le_rfl, hab⟩ : Icc a b)
      (S.forcedSolution2D hab m Φ u₀)
      a (t : ℝ) (⟨le_rfl, hab⟩ : a ∈ Icc a b) t.property t.property.1
      (S.forced_diffusion_intervalIntegrable hab Φ u₀ m t)
      (S.forced_forcing_intervalIntegrable hab Φ u₀ m t)
  have hinitial :
      S.forcedCoefficientTrajectory2D hab Φ u₀ m a =
        S.stateInitialCoefficient m u₀ :=
    S.canonicalSolution_initial m hab (S.forcedSolution2D hab m Φ u₀)
  have hbalance' :
      ‖S.forcedCoefficientTrajectory2D hab Φ u₀ m t‖ ^ 2 +
          2 * ∫ s in a..(t : ℝ),
            (S.variationalProblem2D m Φ.value (S.stateInitialCoefficient m u₀)).system.diffusion
              (S.forcedCoefficientTrajectory2D hab Φ u₀ m s)
              (S.forcedCoefficientTrajectory2D hab Φ u₀ m s) =
        ‖S.forcedCoefficientTrajectory2D hab Φ u₀ m a‖ ^ 2 +
          2 * ∫ s in a..(t : ℝ),
            (S.variationalProblem2D m Φ.value (S.stateInitialCoefficient m u₀)).forcing s
              (S.forcedCoefficientTrajectory2D hab Φ u₀ m s) := hbalance
  have hinitialSq :
      ‖S.forcedCoefficientTrajectory2D hab Φ u₀ m a‖ ^ 2 =
        ‖S.stateInitialCoefficient m u₀‖ ^ 2 := by
    rw [hinitial]
  linarith only [hbalance', hinitialSq]

set_option maxHeartbeats 4000000 in
/-- Exact physical energy balance of a finite forced Galerkin trajectory at
every time in the interval. -/
theorem forced_finite_energy_identity (m : ℕ) (t : Icc a b) :
    ‖S.forcedStateTrajectory2D hab Φ u₀ m t‖ ^ 2 +
        2 * ∫ s in a..(t : ℝ),
          ‖boxEnergyGradient I
            (S.forcedEnergyTrajectory2D hab Φ u₀ m s)‖ ^ 2 =
      ‖S.stateSynthesis m (S.stateInitialCoefficient m u₀)‖ ^ 2 +
        2 * ∫ s in a..(t : ℝ),
          Φ.value s (S.forcedEnergyTrajectory2D hab Φ u₀ m s) := by
  have hstate : ‖S.forcedStateTrajectory2D hab Φ u₀ m t‖ =
      ‖S.forcedCoefficientTrajectory2D hab Φ u₀ m t‖ :=
    S.norm_stateSynthesis m (S.forcedCoefficientTrajectory2D hab Φ u₀ m t)
  have hstateSq : ‖S.forcedStateTrajectory2D hab Φ u₀ m t‖ ^ 2 =
      ‖S.forcedCoefficientTrajectory2D hab Φ u₀ m t‖ ^ 2 := by
    rw [hstate]
  have hinitial : ‖S.stateSynthesis m (S.stateInitialCoefficient m u₀)‖ =
      ‖S.stateInitialCoefficient m u₀‖ :=
    S.norm_stateSynthesis m (S.stateInitialCoefficient m u₀)
  have hinitialSq : ‖S.stateSynthesis m (S.stateInitialCoefficient m u₀)‖ ^ 2 =
      ‖S.stateInitialCoefficient m u₀‖ ^ 2 := by
    rw [hinitial]
  have hdiff : (∫ s in a..(t : ℝ),
        ‖boxEnergyGradient I
          (S.forcedEnergyTrajectory2D hab Φ u₀ m s)‖ ^ 2) =
      ∫ s in a..(t : ℝ),
        (S.variationalProblem2D m Φ.value (S.stateInitialCoefficient m u₀)).system.diffusion
          (S.forcedCoefficientTrajectory2D hab Φ u₀ m s)
          (S.forcedCoefficientTrajectory2D hab Φ u₀ m s) := by
    apply intervalIntegral.integral_congr
    intro s _hs
    calc
      ‖boxEnergyGradient I
          (S.forcedEnergyTrajectory2D hab Φ u₀ m s)‖ ^ 2 =
          boxGradientDiffusion I
            (S.forcedEnergyTrajectory2D hab Φ u₀ m s)
            (S.forcedEnergyTrajectory2D hab Φ u₀ m s) :=
        (boxGradientDiffusion_self I _).symm
      _ = (S.variationalProblem2D m Φ.value (S.stateInitialCoefficient m u₀)).system.diffusion
            (S.forcedCoefficientTrajectory2D hab Φ u₀ m s)
            (S.forcedCoefficientTrajectory2D hab Φ u₀ m s) :=
        (S.variationalProblem2D_diffusion_apply m Φ.value (S.stateInitialCoefficient m u₀)
          (S.forcedCoefficientTrajectory2D hab Φ u₀ m s)
          (S.forcedCoefficientTrajectory2D hab Φ u₀ m s)).symm
  have hwork : (∫ s in a..(t : ℝ),
        (S.variationalProblem2D m Φ.value (S.stateInitialCoefficient m u₀)).forcing s
          (S.forcedCoefficientTrajectory2D hab Φ u₀ m s)) =
      ∫ s in a..(t : ℝ),
        Φ.value s (S.forcedEnergyTrajectory2D hab Φ u₀ m s) := by
    apply intervalIntegral.integral_congr
    intro s _hs
    exact S.variationalProblem2D_forcing_apply m Φ.value (S.stateInitialCoefficient m u₀) s
      (S.forcedCoefficientTrajectory2D hab Φ u₀ m s)
  have hbalance := S.forced_coefficient_energy_balance hab Φ u₀ m t
  linarith only [hbalance, hstateSq, hinitialSq, hdiff, hwork]


set_option maxHeartbeats 3000000 in
/-- The forced compact family state path is the physical pivot-space
trajectory at every time. -/
theorem forced_statePath_eq_trajectory (m : ℕ) (t : Icc a b) :
    (S.forcedLeraySpectralCompactFamily2D hab Φ u₀).statePath m t =
      S.forcedStateTrajectory2D hab Φ u₀ m t := by
  rw [LeraySpectralCompactFamily.statePath_apply,
    S.forcedFamily_embed hab Φ u₀, S.forcedFamily_lift_apply hab Φ u₀]
  exact S.boxEnergyToState_energySynthesis m _

set_option maxHeartbeats 3000000 in
/-- The accumulated forcing work of a finite forced level is the value of the
work functional at its energy class. -/
theorem forced_work_interval_eq (m : ℕ) (t : Icc a b) :
    Φ.workCLM a b t
        ((S.forcedLeraySpectralCompactFamily2D hab Φ u₀).energyLp m) =
      ∫ s in a..(t : ℝ),
        Φ.value s (S.forcedEnergyTrajectory2D hab Φ u₀ m s) := by
  let μ := SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b
  rw [Φ.workCLM_apply t]
  calc
    (∫ s : Icc a b in Set.Iic t,
        Φ.value (s : ℝ)
          ((S.forcedLeraySpectralCompactFamily2D hab Φ u₀).energyLp m s) ∂μ) =
        ∫ s : Icc a b in Set.Iic t,
          Φ.value (s : ℝ)
            (S.forcedEnergyTrajectory2D hab Φ u₀ m s) ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae
        (S.forced_energyLp_eq_trajectory_ae hab Φ u₀ m)] with s hs
      rw [hs]
    _ = ∫ s in a..(t : ℝ),
        Φ.value s (S.forcedEnergyTrajectory2D hab Φ u₀ m s) := by
      simpa only [μ] using integral_Iic_intervalSubtypeMeasure hab t
        (fun s => Φ.value s (S.forcedEnergyTrajectory2D hab Φ u₀ m s))

set_option maxHeartbeats 3000000 in
/-- The finite forced state and its restricted gradient have squared product
norm equal to the initial energy plus twice the accumulated work. -/
theorem forced_finite_stateGradientPair_norm_sq (m : ℕ) (t : Icc a b) :
    ‖WithLp.toLp 2
      (S.forcedStateTrajectory2D hab Φ u₀ m t,
        Real.sqrt 2 •
          restrictedGradientTimeMap (I := I) t
            ((S.forcedLeraySpectralCompactFamily2D hab Φ u₀).energyLp m))‖ ^ 2 =
      ‖S.stateInitialCoefficient m u₀‖ ^ 2 +
        2 * Φ.workCLM a b t
          ((S.forcedLeraySpectralCompactFamily2D hab Φ u₀).energyLp m) := by
  have hsplit : ‖WithLp.toLp 2
        (S.forcedStateTrajectory2D hab Φ u₀ m t,
          Real.sqrt 2 •
            restrictedGradientTimeMap (I := I) t
              ((S.forcedLeraySpectralCompactFamily2D hab Φ u₀).energyLp m))‖ ^ 2 =
      ‖S.forcedStateTrajectory2D hab Φ u₀ m t‖ ^ 2 +
        2 * ‖restrictedGradientTimeMap (I := I) t
          ((S.forcedLeraySpectralCompactFamily2D hab Φ u₀).energyLp m)‖ ^ 2 :=
    norm_sqrtTwo_prodL2_sq _ _
  have hgrad := S.forced_restrictedGradientTimeMap_norm_sq hab Φ u₀ m t
  have hwork := S.forced_work_interval_eq hab Φ u₀ m t
  have hbalance := S.forced_finite_energy_identity hab Φ u₀ m t
  have hinit : ‖S.stateSynthesis m (S.stateInitialCoefficient m u₀)‖ =
      ‖S.stateInitialCoefficient m u₀‖ :=
    S.norm_stateSynthesis m (S.stateInitialCoefficient m u₀)
  have hinitSq : ‖S.stateSynthesis m (S.stateInitialCoefficient m u₀)‖ ^ 2 =
      ‖S.stateInitialCoefficient m u₀‖ ^ 2 := by
    rw [hinit]
  linarith only [hsplit, hgrad, hwork, hbalance, hinitSq]

set_option maxHeartbeats 8000000 in
/-- The synchronized forced weak limit satisfies the forced energy inequality
at every time in the interval. -/
theorem forced_localEnergyInequality
    (SW : (S.forcedLeraySpectralCompactFamily2D hab Φ u₀).StrongWeakPathSubsequence)
    (t : Icc a b) :
    ‖(S.forcedWeaklyContinuousStateRepresentative hab Φ u₀ SW).path t‖ ^ 2 +
        2 * ∫ s : Icc a b in Set.Iic t,
          ‖boxEnergyGradient I (SW.energyLimit s)‖ ^ 2
          ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b ≤
      ‖u₀‖ ^ 2 +
        2 * ∫ s : Icc a b in Set.Iic t,
          Φ.value (s : ℝ) (SW.energyLimit s)
          ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b := by
  let G := S.forcedLeraySpectralCompactFamily2D hab Φ u₀
  let μ := SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b
  let base := SW.toStrongWeakSubsequence
  let A := restrictedGradientTimeMap (I := I) t
  let R := S.forcedWeaklyContinuousStateRepresentative hab Φ u₀ SW
  obtain ⟨rho, hrho, hstate⟩ := R.pointwise_weak_subsequence t
  let pairSeq : ℕ → WithLp 2
      (BoxL2Sigma I ×
        Lp (BoxGradientL2 I) (2 : ℝ≥0∞) (μ.restrict (Set.Iic t))) := fun j =>
    WithLp.toLp 2
      (G.statePath (SW.subseq.idx (rho j)) t,
        Real.sqrt 2 • A (G.energyLp (SW.subseq.idx (rho j))))
  let pairLimit : WithLp 2
      (BoxL2Sigma I ×
        Lp (BoxGradientL2 I) (2 : ℝ≥0∞) (μ.restrict (Set.Iic t))) :=
    WithLp.toLp 2 (R.path t, Real.sqrt 2 • A base.energyLimit)
  have henergy (z : Lp (BoxGradientL2 I) (2 : ℝ≥0∞)
      (μ.restrict (Set.Iic t))) :
      Tendsto
        (fun j => ⟪A (G.energyLp (SW.subseq.idx (rho j))), z⟫_ℝ)
        atTop (nhds ⟪A base.energyLimit, z⟫_ℝ) := by
    let ell : Lp (BoxH1ZeroSigma I) (2 : ℝ≥0∞) μ →L[ℝ] ℝ :=
      (innerSLFlip ℝ z).comp A
    have hbase :=
      @LeraySpectralCompactFamily.StrongWeakSubsequence.energy_clm_tendsto
        (Icc a b) (BoxH1ZeroSigma I) (BoxL2Sigma I)
        inferInstance inferInstance inferInstance inferInstance
        inferInstance inferInstance (boxH1ZeroSigma_completeSpace I)
        inferInstance inferInstance μ inferInstance G base ell
    have hsub := hbase.comp hrho.tendsto_atTop
    simpa only [ell, A, G, base, ContinuousLinearMap.comp_apply,
      innerSLFlip_apply_apply] using hsub
  have hpairWeak (z : WithLp 2
      (BoxL2Sigma I ×
        Lp (BoxGradientL2 I) (2 : ℝ≥0∞) (μ.restrict (Set.Iic t)))) :
      Tendsto (fun j => ⟪pairSeq j, z⟫_ℝ)
        atTop (nhds ⟪pairLimit, z⟫_ℝ) := by
    have hs := hstate z.fst
    have hg := henergy z.snd
    have hgScaled : Tendsto
        (fun j => Real.sqrt 2 *
          ⟪A (G.energyLp (SW.subseq.idx (rho j))), z.snd⟫_ℝ)
        atTop
        (nhds (Real.sqrt 2 * ⟪A base.energyLimit, z.snd⟫_ℝ)) :=
      tendsto_const_nhds.mul hg
    have hsum := hs.add hgScaled
    simpa only [pairSeq, pairLimit, WithLp.prod_inner_apply,
      WithLp.toLp_fst, WithLp.toLp_snd, real_inner_smul_left] using hsum
  let c : ℕ → ℝ := fun j =>
    ‖S.stateInitialCoefficient (SW.subseq.idx (rho j)) u₀‖ ^ 2 +
      2 * Φ.workCLM a b t (G.energyLp (SW.subseq.idx (rho j)))
  have hc : ∀ j, ‖pairSeq j‖ ^ 2 ≤ c j := by
    intro j
    apply le_of_eq
    simpa only [pairSeq, A, G, c,
      S.forced_statePath_eq_trajectory hab Φ u₀] using
        S.forced_finite_stateGradientPair_norm_sq hab Φ u₀
          (SW.subseq.idx (rho j)) t
  have hinitialTendsto : Tendsto
      (fun j => ‖S.stateInitialCoefficient (SW.subseq.idx (rho j)) u₀‖ ^ 2)
      atTop (nhds (‖u₀‖ ^ 2)) := by
    have hbase := (S.stateInitialCoefficient_tendsto u₀).comp
      (SW.subseq.strictMono_idx.tendsto_atTop.comp hrho.tendsto_atTop)
    have hnorm : Tendsto
        (fun j => ‖S.stateSynthesis (SW.subseq.idx (rho j))
          (S.stateInitialCoefficient (SW.subseq.idx (rho j)) u₀)‖ ^ 2)
        atTop (nhds (‖u₀‖ ^ 2)) := by
      exact ((continuous_norm.tendsto u₀).comp hbase).pow 2
    simpa only [S.norm_stateSynthesis] using hnorm
  have hworkTendsto : Tendsto
      (fun j => Φ.workCLM a b t (G.energyLp (SW.subseq.idx (rho j))))
      atTop (nhds (Φ.workCLM a b t base.energyLimit)) := by
    have hbase :=
      @LeraySpectralCompactFamily.StrongWeakSubsequence.energy_clm_tendsto
        (Icc a b) (BoxH1ZeroSigma I) (BoxL2Sigma I)
        inferInstance inferInstance inferInstance inferInstance
        inferInstance inferInstance (boxH1ZeroSigma_completeSpace I)
        inferInstance inferInstance μ inferInstance G base
        (Φ.workCLM a b t)
    exact hbase.comp hrho.tendsto_atTop
  have hC : Tendsto c atTop
      (nhds (‖u₀‖ ^ 2 + 2 * Φ.workCLM a b t base.energyLimit)) := by
    dsimp only [c]
    exact hinitialTendsto.add (tendsto_const_nhds.mul hworkTendsto)
  have hlimit : ‖pairLimit‖ ^ 2 ≤
      ‖u₀‖ ^ 2 + 2 * Φ.workCLM a b t base.energyLimit :=
    norm_sq_le_of_weak_tendsto hpairWeak hc hC
  have hpairNorm : ‖pairLimit‖ ^ 2 =
      ‖(S.forcedWeaklyContinuousStateRepresentative hab Φ u₀ SW).path t‖ ^ 2 +
        2 * ∫ s : Icc a b in Set.Iic t,
          ‖boxEnergyGradient I (SW.energyLimit s)‖ ^ 2
          ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b := by
    rw [norm_sqrtTwo_prodL2_sq]
    exact congrArg (fun r : ℝ => ‖R.path t‖ ^ 2 + 2 * r)
      (restrictedGradientTimeMap_norm_sq_eq_setIntegral
        (I := I) t base.energyLimit)
  have hwork : Φ.workCLM a b t base.energyLimit =
      ∫ s : Icc a b in Set.Iic t, Φ.value (s : ℝ) (SW.energyLimit s)
        ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b :=
    Φ.workCLM_apply t base.energyLimit
  linarith only [hlimit, hpairNorm, hwork]

end ForcedEnergy

section ForcedSolution

/-- A forced Leray--Hopf weak solution on a bounded plane box over a finite
interval, driven by a continuous energy-dual forcing with a continuous
nonnegative dual-norm majorant. -/
structure BoxForcedLerayHopfSolutionOn
    (I : BoxIntegral.Box (Fin 2)) (a b : ℝ)
    (Φ : BoxDualForcing I) (u₀ : BoxL2Sigma I) where
  interval_nonempty : a ≤ b
  state : Lp (BoxL2Sigma I) (2 : ℝ≥0∞)
    (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)
  energy : Lp (BoxH1ZeroSigma I) (2 : ℝ≥0∞)
    (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)
  weakState : Icc a b → BoxL2Sigma I
  weakState_norm_le : ∀ t, ‖weakState t‖ ≤ Φ.stateRadius a b u₀
  weakState_inner_continuous : ∀ y : BoxL2Sigma I,
    Continuous (fun t => ⟪weakState t, y⟫_ℝ)
  weakState_ae_eq_state :
    weakState =ᵐ[SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b]
      (state : Icc a b → BoxL2Sigma I)
  weakState_initial :
    weakState (⟨a, le_rfl, interval_nonempty⟩ : Icc a b) = u₀
  state_eq_energy :
    boxEnergyTimeStateMap energy = state
  state_memLp_top :
    MemLp (state : Icc a b → BoxL2Sigma I) ∞
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)
  state_eLpNorm_top_le :
    eLpNorm (state : Icc a b → BoxL2Sigma I) ∞
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) ≤
        ENNReal.ofReal (Φ.stateRadius a b u₀)
  energy_norm_le :
    ‖energy‖ ≤ Φ.energyRadius a b u₀
  gradient_norm_le :
    ‖(boxEnergyGradient I).compLpL 2
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) energy‖ ≤
      Φ.stateRadius a b u₀
  energy_inequality : ∀ t : Icc a b,
    ‖weakState t‖ ^ 2 +
        2 * ∫ s : Icc a b in Set.Iic t,
          ‖boxEnergyGradient I (energy s)‖ ^ 2
          ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b ≤
      ‖u₀‖ ^ 2 +
        2 * ∫ s : Icc a b in Set.Iic t,
          Φ.value (s : ℝ) (energy s)
          ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b
  weak_equation : ∀ (φ : BoxH1ZeroSigma I)
      (eta : LerayIntervalTimeTest a b), eta.value b = 0 →
    -(∫ t : Icc a b,
        ⟪state t, boxEnergyToState I φ⟫_ℝ * eta.deriv t
        ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) +
      (∫ t : Icc a b,
        boxGradientDiffusion I (energy t) φ * eta.value t
        ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) +
      (∫ t : Icc a b,
        (boxLadyzhenskayaRealization I).toBoxEnergyL4Realization.convectionForm I
          (energy t) (energy t) φ * eta.value t
        ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) =
      ⟪u₀, boxEnergyToState I φ⟫_ℝ * eta.value a +
        ∫ t : Icc a b, Φ.value (t : ℝ) φ * eta.value t
          ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b

set_option maxHeartbeats 2000000 in
/-- The synchronized forced Galerkin limit is a forced Leray--Hopf weak
solution. -/
noncomputable def forcedLerayHopfSolutionOfStrongWeakPath
    {a b : ℝ} (hab : a ≤ b) (Φ : BoxDualForcing I) (u₀ : BoxL2Sigma I)
    (SW : (S.forcedLeraySpectralCompactFamily2D hab Φ u₀).StrongWeakPathSubsequence) :
    BoxForcedLerayHopfSolutionOn I a b Φ u₀ := by
  let base := SW.toStrongWeakSubsequence
  let W := S.forcedWeaklyContinuousStateRepresentative hab Φ u₀ SW
  exact {
    interval_nonempty := hab
    state := base.stateLimit
    energy := base.energyLimit
    weakState := W.path
    weakState_norm_le := fun t => by
      simpa only [S.forcedFamily_stateRadius hab Φ u₀] using W.norm_le t
    weakState_inner_continuous := W.inner_continuous
    weakState_ae_eq_state := W.path_ae_eq_stateLimit
    weakState_initial := by
      simpa only [W] using
        S.forcedWeaklyContinuousStateRepresentative_initial hab Φ u₀ SW
    state_eq_energy := by
      simpa only [boxEnergyTimeStateMap,
        S.forcedFamily_embed hab Φ u₀] using base.embed_energyLimit
    state_memLp_top := base.stateLimit_memLp_top
    state_eLpNorm_top_le := by
      simpa only [S.forcedFamily_stateRadius hab Φ u₀] using
        base.stateLimit_eLpNorm_top_le
    energy_norm_le := by
      simpa only [S.forcedFamily_liftLpRadius hab Φ u₀] using
        base.energyLimit_norm_le
    gradient_norm_le := S.forced_gradientLimit_norm_le hab Φ u₀ base
    energy_inequality := fun t => by
      simpa only [W, base] using
        S.forced_localEnergyInequality hab Φ u₀ SW t
    weak_equation := fun φ eta heta =>
      S.forced_limit_timeTested_identity hab Φ u₀ base φ eta heta
  }

/-- Existence of a forced energy-class weak solution for every pivot-space
initial datum, every continuous energy-dual forcing with a continuous
nonnegative dual-norm majorant, and every nonempty finite interval. -/
theorem exists_forced_twoDimensional_energyWeakSolution
    (S : BoxCompactSpectralRepresentation I)
    {a b : ℝ} (hab : a ≤ b) (Φ : BoxDualForcing I) (u₀ : BoxL2Sigma I) :
    Nonempty (BoxForcedLerayHopfSolutionOn I a b Φ u₀) := by
  obtain ⟨SW⟩ :=
    S.exists_forced_twoDimensional_strongWeakPath_subsequence hab Φ u₀
  exact ⟨S.forcedLerayHopfSolutionOfStrongWeakPath hab Φ u₀ SW⟩

end ForcedSolution

end BoxCompactSpectralRepresentation

/-- **Forced two-dimensional box Leray--Hopf theorem.**  For every
nondegenerate plane box, every finite interval, every pivot-space initial
state, and every continuous energy-dual forcing with a continuous nonnegative
dual-norm majorant, there is a forced Leray--Hopf weak solution: a
weakly continuous state path attaining the datum, the time-tested forced weak
equation, and the forced energy inequality at every time. -/
theorem exists_forced_twoDimensional_lerayHopfSolution
    {I : BoxIntegral.Box (Fin 2)} {a b : ℝ} (hab : a ≤ b)
    (Φ : BoxDualForcing I) (u₀ : BoxL2Sigma I) :
    Nonempty
      (BoxCompactSpectralRepresentation.BoxForcedLerayHopfSolutionOn
        I a b Φ u₀) :=
  BoxCompactSpectralRepresentation.exists_forced_twoDimensional_energyWeakSolution
    (boxCompactSpectralRepresentation I) hab Φ u₀

end
