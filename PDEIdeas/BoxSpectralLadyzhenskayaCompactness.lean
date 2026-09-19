import PDEIdeas.BoxLeraySpectralFamily
import PDEIdeas.BoxSpectralLadyzhenskaya
import PDEIdeas.QuadraticTensorLimit

/-!
# Two-dimensional spectral solutions as compactness families

The canonical energy synthesis sends every finite spectral solution to a
bounded continuous path in the box energy space. This file connects its
physical energy bounds and the concrete two-dimensional common-dual estimate
to the varying-level strong-`L2` compactness constructor.
-/

open BoundedContinuousFunction Filter InnerProductSpace MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 500000

namespace BoxCompactSpectralRepresentation

variable {I : BoxIntegral.Box (Fin 2)}

/-- A spectral local solution with the canonical coefficient-space instances
made explicit. This avoids asking typeclass search to reconstruct `S` from an
abbreviated submodule type. -/
abbrev CanonicalSolution2D
    (S : BoxCompactSpectralRepresentation I) (m : ℕ)
    {a b : ℝ} (hab : a ≤ b)
    (forcing : ℝ → BoxH1ZeroSigma I →L[ℝ] ℝ)
    (initial : S.CoefficientSpace m) :=
  @VariationalGalerkinProblem.LocalSolutionOn
    (S.CoefficientSpace m)
    (S.coefficientSpaceNormedAddCommGroup m)
    (S.coefficientSpaceInnerProductSpace m)
    (S.coefficientSpaceCompleteSpace m)
    (S.variationalProblem2D m forcing initial)
    a b (⟨a, le_rfl, hab⟩ : Icc a b)

/-- Coefficient path of a canonical spectral solution. -/
def canonicalSolutionToFun
    (S : BoxCompactSpectralRepresentation I) (m : ℕ)
    {a b : ℝ} (hab : a ≤ b)
    {forcing : ℝ → BoxH1ZeroSigma I →L[ℝ] ℝ}
    {initial : S.CoefficientSpace m}
    (u : S.CanonicalSolution2D m hab forcing initial) :
    ℝ → S.CoefficientSpace m :=
  @VariationalGalerkinProblem.LocalSolutionOn.toFun
    (S.CoefficientSpace m)
    (S.coefficientSpaceNormedAddCommGroup m)
    (S.coefficientSpaceInnerProductSpace m)
    (S.coefficientSpaceCompleteSpace m)
    (S.variationalProblem2D m forcing initial)
    a b (⟨a, le_rfl, hab⟩ : Icc a b) u

/-- Canonical spectral solution paths are continuous on their defining
interval. -/
theorem canonicalSolution_continuousOn
    (S : BoxCompactSpectralRepresentation I) (m : ℕ)
    {a b : ℝ} (hab : a ≤ b)
    {forcing : ℝ → BoxH1ZeroSigma I →L[ℝ] ℝ}
    {initial : S.CoefficientSpace m}
    (u : S.CanonicalSolution2D m hab forcing initial) :
    ContinuousOn (S.canonicalSolutionToFun m hab u) (Icc a b) :=
  @VariationalGalerkinProblem.LocalSolutionOn.continuousOn
    (S.CoefficientSpace m)
    (S.coefficientSpaceNormedAddCommGroup m)
    (S.coefficientSpaceInnerProductSpace m)
    (S.coefficientSpaceCompleteSpace m)
    (S.variationalProblem2D m forcing initial)
    a b (⟨a, le_rfl, hab⟩ : Icc a b) u

/-- Initial-value identity for a canonical spectral solution. -/
theorem canonicalSolution_initial
    (S : BoxCompactSpectralRepresentation I) (m : ℕ)
    {a b : ℝ} (hab : a ≤ b)
    {forcing : ℝ → BoxH1ZeroSigma I →L[ℝ] ℝ}
    {initial : S.CoefficientSpace m}
    (u : S.CanonicalSolution2D m hab forcing initial) :
    S.canonicalSolutionToFun m hab u a = initial := by
  exact @VariationalGalerkinProblem.LocalSolutionOn.initial
    (S.CoefficientSpace m)
    (S.coefficientSpaceNormedAddCommGroup m)
    (S.coefficientSpaceInnerProductSpace m)
    (S.coefficientSpaceCompleteSpace m)
    (S.variationalProblem2D m forcing initial)
    a b (⟨a, le_rfl, hab⟩ : Icc a b) u

section LevelPath

variable (S : BoxCompactSpectralRepresentation I) (m : ℕ)

/-- The canonical energy lift of a continuous coefficient path. -/
def solutionEnergyPath2D
    {a b : ℝ} (U : ℝ → S.CoefficientSpace m)
    (hU : ContinuousOn U (Icc a b)) :
    Icc a b →ᵇ BoxH1ZeroSigma I :=
  BoundedContinuousFunction.mkOfCompact
    { toFun := fun t => S.energySynthesis m (U t)
      continuous_toFun :=
        (S.energySynthesis m).continuous.comp hU.restrict }

@[simp]
theorem solutionEnergyPath2D_apply
    {a b : ℝ} (U : ℝ → S.CoefficientSpace m)
    (hU : ContinuousOn U (Icc a b)) (t : Icc a b) :
    S.solutionEnergyPath2D m U hU t = S.energySynthesis m (U t) :=
  rfl

/-- A continuous finite spectral energy lift is in `L2` on every closed
interval. -/
theorem solutionEnergyPath2D_memLp
    {a b : ℝ} (_hab : a ≤ b) (U : ℝ → S.CoefficientSpace m)
    (hU : ContinuousOn U (Icc a b)) :
    MemLp (fun t => S.energySynthesis m (U t)) 2
      (volume.restrict (Icc a b)) := by
  have hcont : ContinuousOn
      (fun t => S.energySynthesis m (U t)) (Icc a b) :=
    (S.energySynthesis m).continuous.comp_continuousOn hU
  have hmeas : AEStronglyMeasurable
      (fun t => S.energySynthesis m (U t))
      (volume.restrict (Icc a b)) :=
    hcont.aestronglyMeasurable_of_isCompact isCompact_Icc measurableSet_Icc
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  apply MemLp.of_bound hmeas C
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact hC t ht

/-- The subtype `L2` norm is the ordered real-interval integral of the squared
energy norm. -/
theorem solutionEnergyPath2D_toLp_norm_sq_eq
    {a b : ℝ} (hab : a ≤ b)
    (U : ℝ → S.CoefficientSpace m)
    (hU : ContinuousOn U (Icc a b)) :
    ‖BoundedContinuousFunction.toLp (2 : ℝ≥0∞)
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) ℝ
        (S.solutionEnergyPath2D m U hU)‖ ^ 2 =
      ∫ t in a..b, ‖S.energySynthesis m (U t)‖ ^ 2 := by
  rw [BoundedContinuousFunction.norm_toLp_two_sq_eq_integral_norm_sq]
  exact SmoothBoxVariationalGalerkinLevel.integral_intervalSubtypeMeasure
    hab (fun t => ‖S.energySynthesis m (U t)‖ ^ 2)

/-- A real-interval energy-square estimate gives the lift radius used by
spectral compactness. -/
theorem solutionEnergyPath2D_toLp_norm_le
    {a b : ℝ} (hab : a ≤ b)
    (U : ℝ → S.CoefficientSpace m)
    (hU : ContinuousOn U (Icc a b))
    (R : ℝ) (hR : 0 ≤ R)
    (henergy :
      ∫ t in a..b, ‖S.energySynthesis m (U t)‖ ^ 2 ≤ R ^ 2) :
    ‖BoundedContinuousFunction.toLp (2 : ℝ≥0∞)
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) ℝ
        (S.solutionEnergyPath2D m U hU)‖ ≤ R := by
  let V := BoundedContinuousFunction.toLp (2 : ℝ≥0∞)
    (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) ℝ
    (S.solutionEnergyPath2D m U hU)
  have hsquare : ‖V‖ ^ 2 ≤ R ^ 2 := by
    dsimp only [V]
    rw [S.solutionEnergyPath2D_toLp_norm_sq_eq m hab U hU]
    exact henergy
  exact (sq_le_sq₀ (norm_nonneg V) hR).mp hsquare

@[simp]
theorem variationalProblem2D_diffusion_apply
    (forcing : ℝ → BoxH1ZeroSigma I →L[ℝ] ℝ)
    (initial u v : S.CoefficientSpace m) :
    (S.variationalProblem2D m forcing initial).system.diffusion u v =
      boxGradientDiffusion I
        (S.energySynthesis m u) (S.energySynthesis m v) :=
  rfl

@[simp]
theorem variationalProblem2D_convection_apply
    (forcing : ℝ → BoxH1ZeroSigma I →L[ℝ] ℝ)
    (initial u v w : S.CoefficientSpace m) :
    (S.variationalProblem2D m forcing initial).system.convection u v w =
      (boxLadyzhenskayaRealization I).toBoxEnergyL4Realization.convectionForm I
        (S.energySynthesis m u) (S.energySynthesis m v)
        (S.energySynthesis m w) :=
  rfl

/-- The `L2` norm of the closed gradient is exactly the accumulated
finite-level diffusion. -/
theorem solutionGradientPath2D_toLp_norm_sq_eq_diffusion
    {a b : ℝ} (hab : a ≤ b)
    (forcing : ℝ → BoxH1ZeroSigma I →L[ℝ] ℝ)
    (initial : S.CoefficientSpace m)
    (U : ℝ → S.CoefficientSpace m)
    (hU : ContinuousOn U (Icc a b)) :
    ‖BoundedContinuousFunction.toLp (2 : ℝ≥0∞)
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) ℝ
        (boxEnergyGradientPath I (S.solutionEnergyPath2D m U hU))‖ ^ 2 =
      ∫ t in a..b,
        (S.variationalProblem2D m forcing initial).system.diffusion
          (U t) (U t) := by
  calc
    ‖BoundedContinuousFunction.toLp (2 : ℝ≥0∞)
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) ℝ
        (boxEnergyGradientPath I (S.solutionEnergyPath2D m U hU))‖ ^ 2 =
        ∫ t : Icc a b,
          ‖boxEnergyGradient I (S.energySynthesis m (U t))‖ ^ 2
          ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b := by
      exact BoundedContinuousFunction.norm_toLp_two_sq_eq_integral_norm_sq
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)
        (boxEnergyGradientPath I (S.solutionEnergyPath2D m U hU))
    _ = ∫ t in a..b,
          ‖boxEnergyGradient I (S.energySynthesis m (U t))‖ ^ 2 :=
      SmoothBoxVariationalGalerkinLevel.integral_intervalSubtypeMeasure
        hab (fun t => ‖boxEnergyGradient I
          (S.energySynthesis m (U t))‖ ^ 2)
    _ = ∫ t in a..b,
        (S.variationalProblem2D m forcing initial).system.diffusion
          (U t) (U t) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      calc
        ‖boxEnergyGradient I (S.energySynthesis m (U t))‖ ^ 2 =
            boxGradientDiffusion I
              (S.energySynthesis m (U t))
              (S.energySynthesis m (U t)) :=
          (boxGradientDiffusion_self I _).symm
        _ = (S.variationalProblem2D m forcing initial).system.diffusion
              (U t) (U t) :=
          (S.variationalProblem2D_diffusion_apply m forcing initial
            (U t) (U t)).symm

/-- Uniform physical state and accumulated diffusion bounds give the full
spectral lift radius. -/
theorem solutionEnergyPath2D_toLp_norm_le_of_state_diffusion
    {a b : ℝ} (hab : a ≤ b)
    (forcing : ℝ → BoxH1ZeroSigma I →L[ℝ] ℝ)
    (initial : S.CoefficientSpace m)
    (U : ℝ → S.CoefficientSpace m)
    (hU : ContinuousOn U (Icc a b))
    (H D : ℝ) (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hstate : ∀ t ∈ Icc a b,
      ‖boxEnergyToState I (S.energySynthesis m (U t))‖ ≤ H)
    (hdiffusion :
      ∫ t in a..b,
        (S.variationalProblem2D m forcing initial).system.diffusion
          (U t) (U t) ≤ D ^ 2) :
    ‖BoundedContinuousFunction.toLp (2 : ℝ≥0∞)
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) ℝ
        (S.solutionEnergyPath2D m U hU)‖ ≤
      Real.sqrt
        ((measureUnivNNReal
          (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) ^
            ((2 : ℝ≥0∞).toReal)⁻¹ * H) ^ 2 + D ^ 2) := by
  let V := S.solutionEnergyPath2D m U hU
  let stateLpRadius :=
    measureUnivNNReal
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) ^
        ((2 : ℝ≥0∞).toReal)⁻¹ * H
  have hstateLpRadius : 0 ≤ stateLpRadius := by
    dsimp [stateLpRadius]
    positivity
  have hstateLp :
      ‖BoundedContinuousFunction.toLp (2 : ℝ≥0∞)
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) ℝ
        (boxEnergyStatePath I V)‖ ≤ stateLpRadius := by
    exact boxEnergyStatePath_toLp_norm_le I
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)
      V H hH (fun t => hstate t t.property)
  have hgradientSq :
      ‖BoundedContinuousFunction.toLp (2 : ℝ≥0∞)
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) ℝ
        (boxEnergyGradientPath I V)‖ ^ 2 ≤ D ^ 2 := by
    rw [S.solutionGradientPath2D_toLp_norm_sq_eq_diffusion m hab
      forcing initial U hU]
    exact hdiffusion
  have hgradientLp :
      ‖BoundedContinuousFunction.toLp (2 : ℝ≥0∞)
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) ℝ
        (boxEnergyGradientPath I V)‖ ≤ D :=
    (sq_le_sq₀ (norm_nonneg _) hD).mp hgradientSq
  simpa only [V, stateLpRadius] using
    boxEnergyPath_toLp_norm_le_sqrt I
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)
      V stateLpRadius D hstateLpRadius hD hstateLp hgradientLp

end LevelPath

section CompactFamily

variable (S : BoxCompactSpectralRepresentation I)

/-- Orthogonal projection of a common pivot-space initial state onto one
spectral coefficient level. -/
def stateInitialCoefficient (m : ℕ) (u₀ : BoxL2Sigma I) :
    S.CoefficientSpace m :=
  ⟨S.stateProjection m u₀, by
    change
      GalerkinProjectorSequence.finitePartialProjection
          S.stateBasis (S.exhaustion.head m) u₀ ∈
        GalerkinProjectorSequence.finitePartialSpace
          S.stateBasis (S.exhaustion.head m)
    rw [← GalerkinProjectorSequence.range_finitePartialProjection]
    exact ⟨u₀, rfl⟩⟩

theorem norm_stateInitialCoefficient_le (m : ℕ) (u₀ : BoxL2Sigma I) :
    ‖S.stateInitialCoefficient m u₀‖ ≤ ‖u₀‖ := by
  let P := S.stateProjection m
  change ‖P u₀‖ ≤ ‖u₀‖
  calc
    ‖P u₀‖ ≤ ‖P‖ * ‖u₀‖ := P.le_opNorm u₀
    _ ≤ 1 * ‖u₀‖ := mul_le_mul_of_nonneg_right
      (GalerkinProjectorSequence.finitePartialProjection_norm_le
        S.stateBasis (S.exhaustion.head m))
      (norm_nonneg u₀)
    _ = ‖u₀‖ := one_mul _

@[simp]
theorem stateSynthesis_stateInitialCoefficient
    (m : ℕ) (u₀ : BoxL2Sigma I) :
    S.stateSynthesis m (S.stateInitialCoefficient m u₀) =
      S.stateProjection m u₀ :=
  rfl

/-- The physical initial states converge strongly to the prescribed pivot
state. -/
theorem stateInitialCoefficient_tendsto (u₀ : BoxL2Sigma I) :
    Tendsto
      (fun m => S.stateSynthesis m (S.stateInitialCoefficient m u₀))
      atTop (nhds u₀) := by
  simpa only [S.stateSynthesis_stateInitialCoefficient] using
    GalerkinProjectorSequence.finitePartialProjection_tendsto
      S.stateBasis S.exhaustion u₀

/-- Canonical unforced two-dimensional problem on one spectral level. -/
noncomputable def zeroForcingProblem2D (m : ℕ) (u₀ : BoxL2Sigma I) :
    VariationalGalerkinProblem (S.CoefficientSpace m) :=
  S.variationalProblem2D m
    (fun _ => (0 : BoxH1ZeroSigma I →L[ℝ] ℝ))
    (S.stateInitialCoefficient m u₀)

@[simp]
theorem zeroForcingProblem2D_initial (m : ℕ) (u₀ : BoxL2Sigma I) :
    (S.zeroForcingProblem2D m u₀).initial =
      S.stateInitialCoefficient m u₀ :=
  rfl

@[simp]
theorem zeroForcingProblem2D_forcing
    (m : ℕ) (u₀ : BoxL2Sigma I) (t : ℝ) :
    (S.zeroForcingProblem2D m u₀).forcing t = 0 :=
  rfl

theorem zeroForcingProblem2D_forcing_continuous
    (m : ℕ) (u₀ : BoxL2Sigma I) :
    Continuous (S.zeroForcingProblem2D m u₀).forcing := by
  simpa only [S.zeroForcingProblem2D_forcing m u₀] using
    (continuous_const : Continuous
      (fun _ : ℝ => (0 : S.CoefficientSpace m →L[ℝ] ℝ)))

@[simp]
theorem zeroForcingProblem2D_diffusion_apply
    (m : ℕ) (u₀ : BoxL2Sigma I)
    (u v : S.CoefficientSpace m) :
    (S.zeroForcingProblem2D m u₀).system.diffusion u v =
      boxGradientDiffusion I
        (S.energySynthesis m u) (S.energySynthesis m v) :=
  rfl

@[simp]
theorem zeroForcingProblem2D_convection_apply
    (m : ℕ) (u₀ : BoxL2Sigma I)
    (u v w : S.CoefficientSpace m) :
    (S.zeroForcingProblem2D m u₀).system.convection u v w =
      (boxLadyzhenskayaRealization I).toBoxEnergyL4Realization.convectionForm I
        (S.energySynthesis m u) (S.energySynthesis m v)
        (S.energySynthesis m w) :=
  rfl

/-- Energy-driven continuation gives an unforced solution on every finite
time interval at every canonical spectral level. -/
theorem exists_zeroForcingSolution2D
    {a b : ℝ} (hab : a ≤ b)
    (m : ℕ) (u₀ : BoxL2Sigma I) :
    Nonempty (S.CanonicalSolution2D m hab
      (fun _ => (0 : BoxH1ZeroSigma I →L[ℝ] ℝ))
      (S.stateInitialCoefficient m u₀)) := by
  letI : NormedAddCommGroup (S.CoefficientSpace m) :=
    S.coefficientSpaceNormedAddCommGroup m
  letI : InnerProductSpace ℝ (S.CoefficientSpace m) :=
    S.coefficientSpaceInnerProductSpace m
  letI : CompleteSpace (S.CoefficientSpace m) :=
    S.coefficientSpaceCompleteSpace m
  let P := S.zeroForcingProblem2D m u₀
  change Nonempty (@VariationalGalerkinProblem.LocalSolutionOn
    (S.CoefficientSpace m)
    (S.coefficientSpaceNormedAddCommGroup m)
    (S.coefficientSpaceInnerProductSpace m)
    (S.coefficientSpaceCompleteSpace m)
    P a b (⟨a, le_rfl, hab⟩ : Icc a b))
  apply @VariationalGalerkinProblem.exists_solutionOn_of_energy_budget
    (S.CoefficientSpace m)
    (S.coefficientSpaceNormedAddCommGroup m)
    (S.coefficientSpaceInnerProductSpace m)
    (S.coefficientSpaceCompleteSpace m)
    P a b hab
    (S.zeroForcingProblem2D_forcing_continuous m u₀)
    0 ‖u₀‖ (by norm_num) (norm_nonneg u₀)
  · intro t ht
    simp [P]
  · exact (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume a b)
  · intro t ht
    simp
  · intro t ht x
    simp [P]
  · simp only [P, S.zeroForcingProblem2D_initial,
      intervalIntegral.integral_zero, add_zero]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg u₀)).2
      (S.norm_stateInitialCoefficient_le m u₀)

/-- A chosen canonical unforced solution on one finite interval. -/
noncomputable def zeroForcingSolution2D
    {a b : ℝ} (hab : a ≤ b)
    (m : ℕ) (u₀ : BoxL2Sigma I) :
    S.CanonicalSolution2D m hab
      (fun _ => (0 : BoxH1ZeroSigma I →L[ℝ] ℝ))
      (S.stateInitialCoefficient m u₀) :=
  Classical.choice (S.exists_zeroForcingSolution2D hab m u₀)

/-- Every unforced spectral solution stays in the initial pivot-space energy
ball. -/
theorem zeroForcingSolution2D_norm_le
    {a b : ℝ} (hab : a ≤ b)
    (m : ℕ) (u₀ : BoxL2Sigma I)
    (u : S.CanonicalSolution2D m hab
      (fun _ => (0 : BoxH1ZeroSigma I →L[ℝ] ℝ))
      (S.stateInitialCoefficient m u₀)) :
    ∀ t ∈ Icc a b,
      ‖S.canonicalSolutionToFun m hab u t‖ ≤ ‖u₀‖ := by
  let P := S.zeroForcingProblem2D m u₀
  exact @VariationalGalerkinProblem.LocalSolutionOn.norm_le_energyRadius
    (S.CoefficientSpace m)
    (S.coefficientSpaceNormedAddCommGroup m)
    (S.coefficientSpaceInnerProductSpace m)
    (S.coefficientSpaceCompleteSpace m)
    P a b hab u (fun _ => 0)
    (S.zeroForcingProblem2D_forcing_continuous m u₀)
    (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume a b)
    (fun t ht => by simp)
    (fun t ht x => by simp [P])
    ‖u₀‖ (norm_nonneg u₀)
    (by
      simp only [P, S.zeroForcingProblem2D_initial,
        intervalIntegral.integral_zero, add_zero]
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg u₀)).2
        (S.norm_stateInitialCoefficient_le m u₀))

private theorem diffusion_integral_le_initial_sq_of_forcing_eq_zero
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [CompleteSpace W]
    {P : VariationalGalerkinProblem W}
    {a b : ℝ} (hab : a ≤ b)
    (u : P.LocalSolutionOn (⟨a, le_rfl, hab⟩ : Icc a b))
    (hFzero : P.forcing = fun _ => 0) :
    ∫ t in a..b, P.system.diffusion (u.toFun t) (u.toFun t) ≤
      ‖P.initial‖ ^ 2 := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hFcont : Continuous P.forcing := by
    rw [hFzero]
    exact continuous_const
  have hAint := u.diffusion_intervalIntegrable ha hb hab
  have hFint := u.forcing_intervalIntegrable hFcont ha hb hab
  have hEnergy := u.energyIdentityOn ha hb hab hAint hFint
  rw [u.initial] at hEnergy
  simp only [hFzero, ContinuousLinearMap.zero_apply,
    intervalIntegral.integral_zero, mul_zero, add_zero] at hEnergy
  have hD : 0 ≤ ∫ t in a..b,
      P.system.diffusion (u.toFun t) (u.toFun t) := by
    apply intervalIntegral.integral_nonneg hab
    intro t _ht
    exact P.system.diffusion_nonneg _
  linarith [sq_nonneg ‖u.toFun b‖]

/-- The accumulated gradient diffusion of an unforced spectral solution is
bounded by the squared initial pivot norm. -/
theorem zeroForcingSolution2D_diffusion_integral_le
    {a b : ℝ} (hab : a ≤ b)
    (m : ℕ) (u₀ : BoxL2Sigma I)
    (u : S.CanonicalSolution2D m hab
      (fun _ => (0 : BoxH1ZeroSigma I →L[ℝ] ℝ))
      (S.stateInitialCoefficient m u₀)) :
    ∫ t in a..b,
        (S.zeroForcingProblem2D m u₀).system.diffusion
          (S.canonicalSolutionToFun m hab u t)
          (S.canonicalSolutionToFun m hab u t) ≤ ‖u₀‖ ^ 2 := by
  let P := S.zeroForcingProblem2D m u₀
  have hzero : P.forcing = fun _ => 0 := by
    funext t
    exact S.zeroForcingProblem2D_forcing m u₀ t
  have hdiff :=
    @diffusion_integral_le_initial_sq_of_forcing_eq_zero
      (S.CoefficientSpace m)
      (S.coefficientSpaceNormedAddCommGroup m)
      (S.coefficientSpaceInnerProductSpace m)
      (S.coefficientSpaceCompleteSpace m)
      P a b hab u hzero
  have hinitial : ‖P.initial‖ ^ 2 ≤ ‖u₀‖ ^ 2 := by
    simp only [P, S.zeroForcingProblem2D_initial]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg u₀)).2
      (S.norm_stateInitialCoefficient_le m u₀)
  exact hdiff.trans hinitial

/-- Uniform graph-space radius for the unforced spectral family. -/
def zeroForcingEnergyRadius (a b : ℝ) (u₀ : BoxL2Sigma I) : ℝ :=
  Real.sqrt
    ((measureUnivNNReal
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) ^
        ((2 : ℝ≥0∞).toReal)⁻¹ * ‖u₀‖) ^ 2 + ‖u₀‖ ^ 2)

theorem zeroForcingEnergyRadius_nonneg
    (a b : ℝ) (u₀ : BoxL2Sigma I) :
    0 ≤ zeroForcingEnergyRadius a b u₀ :=
  Real.sqrt_nonneg _

/-- The coefficient bound is exactly the physical pivot-space state bound. -/
theorem zeroForcingSolution2D_state_bound
    {a b : ℝ} (hab : a ≤ b)
    (m : ℕ) (u₀ : BoxL2Sigma I)
    (u : S.CanonicalSolution2D m hab
      (fun _ => (0 : BoxH1ZeroSigma I →L[ℝ] ℝ))
      (S.stateInitialCoefficient m u₀)) :
    ∀ t ∈ Icc a b,
      ‖boxEnergyToState I
        (S.energySynthesis m (S.canonicalSolutionToFun m hab u t))‖ ≤
        ‖u₀‖ := by
  intro t ht
  rw [S.boxEnergyToState_energySynthesis, S.norm_stateSynthesis]
  exact S.zeroForcingSolution2D_norm_le hab m u₀ u t ht

/-- State and diffusion estimates give the uniform graph-space `L2` radius. -/
theorem zeroForcingSolution2D_energy_toLp_norm_le
    {a b : ℝ} (hab : a ≤ b)
    (m : ℕ) (u₀ : BoxL2Sigma I)
    (u : S.CanonicalSolution2D m hab
      (fun _ => (0 : BoxH1ZeroSigma I →L[ℝ] ℝ))
      (S.stateInitialCoefficient m u₀)) :
    let U := S.canonicalSolutionToFun m hab u
    ‖BoundedContinuousFunction.toLp (2 : ℝ≥0∞)
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) ℝ
        (S.solutionEnergyPath2D m U
          (S.canonicalSolution_continuousOn m hab u))‖ ≤
      zeroForcingEnergyRadius a b u₀ := by
  dsimp only
  simpa only [zeroForcingEnergyRadius] using
    S.solutionEnergyPath2D_toLp_norm_le_of_state_diffusion m hab
      (fun _ => (0 : BoxH1ZeroSigma I →L[ℝ] ℝ))
      (S.stateInitialCoefficient m u₀)
      (S.canonicalSolutionToFun m hab u)
      (S.canonicalSolution_continuousOn m hab u)
      ‖u₀‖ ‖u₀‖ (norm_nonneg u₀) (norm_nonneg u₀)
      (S.zeroForcingSolution2D_state_bound hab m u₀ u)
      (S.zeroForcingSolution2D_diffusion_integral_le hab m u₀ u)

/-- Ordered-interval form of the uniform graph-energy estimate. -/
theorem zeroForcingSolution2D_energy_integral_le
    {a b : ℝ} (hab : a ≤ b)
    (m : ℕ) (u₀ : BoxL2Sigma I)
    (u : S.CanonicalSolution2D m hab
      (fun _ => (0 : BoxH1ZeroSigma I →L[ℝ] ℝ))
      (S.stateInitialCoefficient m u₀)) :
    ∫ t in a..b,
        ‖S.energySynthesis m (S.canonicalSolutionToFun m hab u t)‖ ^ 2 ≤
      zeroForcingEnergyRadius a b u₀ ^ 2 := by
  let U := S.canonicalSolutionToFun m hab u
  let hU := S.canonicalSolution_continuousOn m hab u
  rw [← S.solutionEnergyPath2D_toLp_norm_sq_eq m hab U hU]
  let V := BoundedContinuousFunction.toLp (2 : ℝ≥0∞)
    (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) ℝ
    (S.solutionEnergyPath2D m U hU)
  have hV : ‖V‖ ≤ zeroForcingEnergyRadius a b u₀ := by
    simpa only [V, U, hU] using
      S.zeroForcingSolution2D_energy_toLp_norm_le hab m u₀ u
  exact (sq_le_sq₀ (norm_nonneg V)
    (zeroForcingEnergyRadius_nonneg a b u₀)).2 hV

/-- Explicit uniform common-dual radius from the two-dimensional estimate. -/
def twoDimensionalDualRadius (H R F : ℝ) : ℝ≥0 :=
  ⟨Real.sqrt
      (2 * (1 + (boxLpConvectionBound I *
        (boxLadyzhenskayaRealization I).constant) * H) ^ 2 * R ^ 2 +
        2 * F ^ 2),
    Real.sqrt_nonneg _⟩

@[simp]
theorem coe_twoDimensionalDualRadius_sq (H R F : ℝ) :
    (twoDimensionalDualRadius (I := I) H R F : ℝ) ^ 2 =
      2 * (1 + (boxLpConvectionBound I *
        (boxLadyzhenskayaRealization I).constant) * H) ^ 2 * R ^ 2 +
        2 * F ^ 2 := by
  change Real.sqrt
      (2 * (1 + (boxLpConvectionBound I *
        (boxLadyzhenskayaRealization I).constant) * H) ^ 2 * R ^ 2 +
        2 * F ^ 2) ^ 2 = _
  rw [Real.sq_sqrt]
  positivity

/-- Physical state and energy bounds plus measurable forcing assemble the
canonical spectral solutions into the strong-`L2` compactness family. -/
noncomputable def leraySpectralCompactFamily2D
    {a b : ℝ} (hab : a ≤ b)
    (forcing : ℝ → BoxH1ZeroSigma I →L[ℝ] ℝ)
    (initial : ∀ m, S.CoefficientSpace m)
    (solution : ∀ m, S.CanonicalSolution2D m hab forcing (initial m))
    (f : ℝ → ℝ) (H R F : ℝ)
    (hH : 0 ≤ H) (hR : 0 ≤ R)
    (hf_nonneg : ∀ t ∈ Icc a b, 0 ≤ f t)
    (hforcing : ∀ t ∈ Icc a b, ∀ φ,
      ‖forcing t φ‖ ≤ f t * ‖φ‖)
    (hforcing_meas : AEStronglyMeasurable forcing
      (volume.restrict (Icc a b)))
    (hstate : ∀ (m : ℕ) (t : ℝ), t ∈ Icc a b →
      ‖boxEnergyToState I
        (S.energySynthesis m
          (S.canonicalSolutionToFun m hab (solution m) t))‖ ≤ H)
    (henergy : ∀ m,
      ∫ t in a..b,
        ‖S.energySynthesis m
          (S.canonicalSolutionToFun m hab (solution m) t)‖ ^ 2 ≤ R ^ 2)
    (hforce : MemLp f 2 (volume.restrict (Icc a b)))
    (hforce_sq : ∫ t in a..b, ‖f t‖ ^ 2 ≤ F ^ 2) :
    LeraySpectralCompactFamily
      (I := Icc a b) (V := BoxH1ZeroSigma I) (H := BoxL2Sigma I)
      (μ := SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) := by
  letI allNormed : ∀ m, NormedAddCommGroup (S.CoefficientSpace m) :=
    fun m => S.coefficientSpaceNormedAddCommGroup m
  letI allInner : ∀ m, InnerProductSpace ℝ (S.CoefficientSpace m) :=
    fun m => S.coefficientSpaceInnerProductSpace m
  letI allComplete : ∀ m, CompleteSpace (S.CoefficientSpace m) :=
    fun m => S.coefficientSpaceCompleteSpace m
  let U : ∀ m, ℝ → S.CoefficientSpace m :=
    fun m => S.canonicalSolutionToFun m hab (solution m)
  let hU : ∀ m, ContinuousOn (U m) (Icc a b) :=
    fun m => S.canonicalSolution_continuousOn m hab (solution m)
  refine @boxLeraySpectralCompactFamilyOfVariationalDualL2Family
    1 a b hab I
    S.Index (fun m => S.CoefficientSpace m) (BoxH1ZeroSigma I)
    allNormed allInner allComplete inferInstance inferInstance
    S.stateBasis S.exhaustion
    (fun m => S.solutionEnergyPath2D m (U m) (hU m)) H
    ?_ R hR ?_
    (fun m => S.variationalProblem2D m forcing (initial m))
    (fun m => solution m)
    S.testProjection S.energyMode ?_
    (twoDimensionalDualRadius (I := I) H R F) ?_ ?_
  · intro m t
    simpa [U] using hstate m t t.property
  · intro m
    exact S.solutionEnergyPath2D_toLp_norm_le m hab (U m) (hU m)
      R hR (by simpa [U] using henergy m)
  · intro m t i
    simpa [U, canonicalSolutionToFun] using
      S.inner_testProjection_energyMode m i (U m t)
  · intro m
    exact (S.twoDimensional_dual_memLp_and_integral_le m hab forcing
      (initial m) (U m) f H R F hH hf_nonneg hforcing
      hforcing_meas (by simpa [U] using hstate m)
      (S.solutionEnergyPath2D_memLp m hab (U m) (hU m))
      (by simpa [U] using henergy m) hforce hforce_sq).1
  · intro m
    rw [coe_twoDimensionalDualRadius_sq (I := I) H R F]
    exact (S.twoDimensional_dual_memLp_and_integral_le m hab forcing
      (initial m) (U m) f H R F hH hf_nonneg hforcing
      hforcing_meas (by simpa [U] using hstate m)
      (S.solutionEnergyPath2D_memLp m hab (U m) (hU m))
      (by simpa [U] using henergy m) hforce hforce_sq).2

/-- The canonical unforced spectral solutions form a Leray compactness family
for every pivot-space initial state and finite interval. -/
noncomputable def zeroForcingLeraySpectralCompactFamily2D
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I) :
    LeraySpectralCompactFamily
      (I := Icc a b) (V := BoxH1ZeroSigma I) (H := BoxL2Sigma I)
      (μ := SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) := by
  apply S.leraySpectralCompactFamily2D hab
    (fun _ => (0 : BoxH1ZeroSigma I →L[ℝ] ℝ))
    (fun m => S.stateInitialCoefficient m u₀)
    (fun m => S.zeroForcingSolution2D hab m u₀)
    (fun _ => 0) ‖u₀‖ (zeroForcingEnergyRadius a b u₀) 0
  · exact norm_nonneg u₀
  · exact zeroForcingEnergyRadius_nonneg a b u₀
  · intro t ht
    simp
  · intro t ht φ
    simp
  · exact aestronglyMeasurable_const
  · intro m t ht
    exact S.zeroForcingSolution2D_state_bound hab m u₀
      (S.zeroForcingSolution2D hab m u₀) t ht
  · intro m
    exact S.zeroForcingSolution2D_energy_integral_le hab m u₀
      (S.zeroForcingSolution2D hab m u₀)
  · exact MemLp.zero'
  · simp

@[simp]
theorem zeroForcingLeraySpectralCompactFamily2D_stateRadius
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I) :
    (S.zeroForcingLeraySpectralCompactFamily2D hab u₀).stateRadius = ‖u₀‖ :=
  rfl

@[simp]
theorem zeroForcingLeraySpectralCompactFamily2D_liftLpRadius
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I) :
    (S.zeroForcingLeraySpectralCompactFamily2D hab u₀).liftLpRadius =
      zeroForcingEnergyRadius a b u₀ :=
  rfl

@[simp]
theorem zeroForcingLeraySpectralCompactFamily2D_embed
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I) :
    (S.zeroForcingLeraySpectralCompactFamily2D hab u₀).embed =
      boxEnergyToState I :=
  rfl

@[simp]
theorem zeroForcingLeraySpectralCompactFamily2D_projector
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I) :
    (S.zeroForcingLeraySpectralCompactFamily2D hab u₀).projector =
      S.stateProjection :=
  rfl

@[simp]
theorem zeroForcingLeraySpectralCompactFamily2D_lift_apply
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I)
    (m : ℕ) (t : Icc a b) :
    (S.zeroForcingLeraySpectralCompactFamily2D hab u₀).lift m t =
      S.energySynthesis m
        (S.canonicalSolutionToFun m hab
          (S.zeroForcingSolution2D hab m u₀) t) :=
  rfl

/-- The unforced canonical box tower has a strict subsequence converging
strongly in `L2((a,b); L2_sigma)`. -/
theorem exists_zeroForcing_twoDimensional_strongL2_subsequence
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I) :
    Nonempty (StrongMetricSubsequence
      (S.zeroForcingLeraySpectralCompactFamily2D hab u₀).stateLp) :=
  exists_boxLeray_strongL2_subsequence
    (S.zeroForcingLeraySpectralCompactFamily2D hab u₀)

/-- The same unforced subsequence may be selected with strong `L1`
convergence of its canonical quadratic projective tensors. -/
theorem exists_zeroForcing_twoDimensional_projectiveTensorL1_subsequence
    {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I) :
    ∃ T : StrongMetricSubsequence
        (S.zeroForcingLeraySpectralCompactFamily2D hab u₀).stateLp,
      Tendsto
        (fun k => projectiveTensorSquareLp
          ((S.zeroForcingLeraySpectralCompactFamily2D hab u₀).stateLp
            (T.subseq.idx k)))
        atTop (nhds (projectiveTensorSquareLp T.limit)) := by
  exact @LeraySpectralCompactFamily.exists_strongL2_projectiveTensorL1_subsequence
    (Icc a b) (BoxH1ZeroSigma I) (BoxL2Sigma I)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    (boxL2Sigma_completeSpace I)
    (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)
    inferInstance
    (S.zeroForcingLeraySpectralCompactFamily2D hab u₀)

/-- Every family assembled from the concrete dual estimate has a strict
strong-`L2` subsequence. -/
theorem exists_twoDimensional_strongL2_subsequence
    {a b : ℝ}
    (G : LeraySpectralCompactFamily
      (I := Icc a b) (V := BoxH1ZeroSigma I) (H := BoxL2Sigma I)
      (μ := SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)) :
    Nonempty (StrongMetricSubsequence G.stateLp) :=
  exists_boxLeray_strongL2_subsequence G

end CompactFamily

end BoxCompactSpectralRepresentation

end
