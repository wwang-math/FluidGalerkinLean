import PDEIdeas.BoxPoincare
import PDEIdeas.BoxLerayWeakCompactness

/-!
# Arbitrary forcing in the two-dimensional spectral Galerkin tower

The box Poincaré inequality absorbs an arbitrary energy-dual forcing
functional into the diffusion form with a state-independent remainder.  The
energy-driven continuation theorem therefore applies verbatim, and every
spectral level carries a solution on the whole prescribed interval, with
state and graph-energy radii determined by the initial state and the
square-integral of the dual forcing majorant.  Those radii, the Ladyzhenskaya
common-dual estimate, and the compact energy-to-state embedding assemble the
forced family into a `LeraySpectralCompactFamily` and yield the synchronized
strong--weak extraction.
-/

open InnerProductSpace MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

variable {I : BoxIntegral.Box (Fin 2)}

/-- A time-dependent energy-dual forcing, presented through a continuous
path of Riesz representatives in the energy space, together with a continuous
nonnegative majorant of its dual norm.  By the Riesz isomorphism the field
`rep` carries exactly the same information as a continuous path of
functionals on the energy space. -/
structure BoxDualForcing (I : BoxIntegral.Box (Fin 2)) where
  /-- The forcing functional at each time. -/
  value : ℝ → BoxH1ZeroSigma I →L[ℝ] ℝ
  /-- The Riesz representative of the forcing at each time. -/
  rep : ℝ → BoxH1ZeroSigma I
  /-- A majorant of the dual norm of the forcing. -/
  bound : ℝ → ℝ
  continuous_value : Continuous value
  continuous_rep : Continuous rep
  value_apply : ∀ (t : ℝ) (w : BoxH1ZeroSigma I),
    value t w = ⟪rep t, w⟫_ℝ
  aestronglyMeasurable_value :
    ∀ μ : Measure ℝ, AEStronglyMeasurable value μ
  continuous_bound : Continuous bound
  bound_nonneg : ∀ t, 0 ≤ bound t
  norm_le : ∀ (t : ℝ) (w : BoxH1ZeroSigma I), ‖value t w‖ ≤ bound t * ‖w‖

namespace BoxDualForcing

variable (Φ : BoxDualForcing I)

/-- The zero forcing, with zero majorant. -/
def zero (I : BoxIntegral.Box (Fin 2)) : BoxDualForcing I where
  value := fun _ => 0
  rep := fun _ => 0
  bound := fun _ => 0
  continuous_value := continuous_const
  continuous_rep := continuous_const
  value_apply := by
    intro t w
    simp
  aestronglyMeasurable_value := fun _ => aestronglyMeasurable_const
  continuous_bound := continuous_const
  bound_nonneg := fun _ => le_rfl
  norm_le := by
    intro t w
    simp

/-- **Energy-path forcing.**  A continuous path in the energy space acts on
that space through its inner product.  Every continuous path of functionals
on the energy space arises this way, by the Riesz isomorphism. -/
def ofEnergyPath (r : ℝ → BoxH1ZeroSigma I) (hr : Continuous r) :
    BoxDualForcing I where
  value := fun t => innerSL ℝ (r t)
  rep := r
  bound := fun t => ‖r t‖
  continuous_value := (innerSL ℝ (E := BoxH1ZeroSigma I)).continuous.comp hr
  continuous_rep := hr
  value_apply := fun t w => rfl
  aestronglyMeasurable_value := fun μ => by
    letI : SecondCountableTopology (BoxH1ZeroSigma I) :=
      boxH1ZeroSigma_secondCountableTopology I
    exact (innerSL ℝ (E := BoxH1ZeroSigma I)).continuous.comp_aestronglyMeasurable
      hr.aestronglyMeasurable
  continuous_bound := hr.norm
  bound_nonneg := fun t => norm_nonneg _
  norm_le := by
    intro t w
    show ‖⟪r t, w⟫_ℝ‖ ≤ ‖r t‖ * ‖w‖
    rw [Real.norm_eq_abs]
    exact abs_real_inner_le_norm _ _

/-- The dual majorant is bounded on every compact interval. -/
theorem exists_bound_on (a b : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc a b, Φ.bound t ≤ M := by
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
      Φ.continuous_bound.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t ht => ?_⟩
  exact ((le_abs_self _).trans (hC t ht)).trans (le_max_left _ _)

/-- State-independent work majorant supplied by the box Poincaré constant. -/
def workMajorant (t : ℝ) : ℝ :=
  (1 + boxPoincareConstant I ^ 2) * Φ.bound t ^ 2

theorem workMajorant_nonneg (t : ℝ) : 0 ≤ Φ.workMajorant t := by
  unfold workMajorant
  positivity

theorem workMajorant_continuous : Continuous Φ.workMajorant := by
  unfold workMajorant
  exact continuous_const.mul (Φ.continuous_bound.pow 2)

theorem workMajorant_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable Φ.workMajorant volume a b :=
  Φ.workMajorant_continuous.intervalIntegrable a b

theorem workIntegral_nonneg {a b : ℝ} (hab : a ≤ b) :
    0 ≤ ∫ s in a..b, Φ.workMajorant s := by
  apply intervalIntegral.integral_nonneg hab
  intro s _hs
  exact Φ.workMajorant_nonneg s

/-- **Poincaré absorption.**  The work of the forcing at any energy vector is
bounded by a state-independent majorant plus the diffusion form. -/
theorem work_le (t : ℝ) (v : BoxH1ZeroSigma I) :
    2 * Φ.value t v ≤ Φ.workMajorant t + boxGradientDiffusion I v v :=
  boxForcing_work_le I (Φ.value t) (Φ.bound t) (Φ.bound_nonneg t)
    (Φ.norm_le t) v

/-- Uniform pivot-space radius of every forced spectral trajectory. -/
def stateRadius (a b : ℝ) (u₀ : BoxL2Sigma I) : ℝ :=
  Real.sqrt (‖u₀‖ ^ 2 + ∫ s in a..b, Φ.workMajorant s)

theorem stateRadius_nonneg (a b : ℝ) (u₀ : BoxL2Sigma I) :
    0 ≤ Φ.stateRadius a b u₀ :=
  Real.sqrt_nonneg _

theorem stateRadius_sq {a b : ℝ} (hab : a ≤ b) (u₀ : BoxL2Sigma I) :
    Φ.stateRadius a b u₀ ^ 2 =
      ‖u₀‖ ^ 2 + ∫ s in a..b, Φ.workMajorant s := by
  unfold stateRadius
  rw [Real.sq_sqrt]
  have h := Φ.workIntegral_nonneg hab
  positivity

/-- Uniform graph-space radius of the forced spectral family. -/
def energyRadius (a b : ℝ) (u₀ : BoxL2Sigma I) : ℝ :=
  Real.sqrt
    ((measureUnivNNReal
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) ^
        ((2 : ℝ≥0∞).toReal)⁻¹ * Φ.stateRadius a b u₀) ^ 2 +
      Φ.stateRadius a b u₀ ^ 2)

theorem energyRadius_nonneg (a b : ℝ) (u₀ : BoxL2Sigma I) :
    0 ≤ Φ.energyRadius a b u₀ :=
  Real.sqrt_nonneg _

/-- Square root of the accumulated squared dual majorant. -/
def dualRadius (a b : ℝ) : ℝ :=
  Real.sqrt (∫ t in a..b, Φ.bound t ^ 2)

theorem dualRadius_sq {a b : ℝ} (hab : a ≤ b) :
    ∫ t in a..b, ‖Φ.bound t‖ ^ 2 ≤ Φ.dualRadius a b ^ 2 := by
  have hnonneg : 0 ≤ ∫ t in a..b, Φ.bound t ^ 2 := by
    apply intervalIntegral.integral_nonneg hab
    intro t _ht
    positivity
  unfold dualRadius
  rw [Real.sq_sqrt hnonneg]
  apply le_of_eq
  apply intervalIntegral.integral_congr
  intro t _ht
  show ‖Φ.bound t‖ ^ 2 = Φ.bound t ^ 2
  rw [Real.norm_eq_abs, abs_of_nonneg (Φ.bound_nonneg t)]

theorem bound_memLp (a b : ℝ) :
    MemLp Φ.bound 2 (volume.restrict (Icc a b)) := by
  obtain ⟨M₀, _hM₀nonneg, hM₀⟩ := Φ.exists_bound_on a b
  haveI : IsFiniteMeasure (volume.restrict (Icc a b)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact (isCompact_Icc (a := a) (b := b)).measure_lt_top
  apply MemLp.of_bound Φ.continuous_bound.aestronglyMeasurable M₀
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (Φ.bound_nonneg t)]
  exact hM₀ t ht

end BoxDualForcing

namespace BoxCompactSpectralRepresentation

variable (S : BoxCompactSpectralRepresentation I)

local instance forcedBoxL2Complete : CompleteSpace (BoxL2Sigma I) :=
  boxL2Sigma_completeSpace I

local instance forcedBoxH1Complete : CompleteSpace (BoxH1ZeroSigma I) :=
  boxH1ZeroSigma_completeSpace I

/-- The canonical two-dimensional spectral problem at level `m` driven by an
arbitrary energy-dual forcing and the projected initial state. -/
noncomputable def forcedProblem2D (m : ℕ)
    (Φ : BoxDualForcing I) (u₀ : BoxL2Sigma I) :
    VariationalGalerkinProblem (S.CoefficientSpace m) :=
  S.variationalProblem2D m Φ.value (S.stateInitialCoefficient m u₀)

@[simp]
theorem forcedProblem2D_initial (m : ℕ)
    (Φ : BoxDualForcing I) (u₀ : BoxL2Sigma I) :
    (S.forcedProblem2D m Φ u₀).initial = S.stateInitialCoefficient m u₀ :=
  rfl

@[simp]
theorem forcedProblem2D_forcing_apply (m : ℕ)
    (Φ : BoxDualForcing I) (u₀ : BoxL2Sigma I)
    (t : ℝ) (x : S.CoefficientSpace m) :
    (S.forcedProblem2D m Φ u₀).forcing t x =
      Φ.value t (S.energySynthesis m x) :=
  rfl

@[simp]
theorem forcedProblem2D_diffusion_apply (m : ℕ)
    (Φ : BoxDualForcing I) (u₀ : BoxL2Sigma I)
    (x y : S.CoefficientSpace m) :
    (S.forcedProblem2D m Φ u₀).system.diffusion x y =
      boxGradientDiffusion I (S.energySynthesis m x) (S.energySynthesis m y) :=
  rfl

theorem forcedProblem2D_forcing_continuous (m : ℕ)
    (Φ : BoxDualForcing I) (u₀ : BoxL2Sigma I) :
    Continuous (S.forcedProblem2D m Φ u₀).forcing := by
  have hcomp : Continuous
      (fun G : BoxH1ZeroSigma I →L[ℝ] ℝ =>
        G.comp (S.energySynthesis m)) := by
    fun_prop
  exact hcomp.comp Φ.continuous_value

/-- Poincaré absorption transported to the coefficient level. -/
theorem forcedProblem2D_work_le (m : ℕ)
    (Φ : BoxDualForcing I) (u₀ : BoxL2Sigma I)
    (t : ℝ) (x : S.CoefficientSpace m) :
    2 * (S.forcedProblem2D m Φ u₀).forcing t x ≤
      Φ.workMajorant t +
        (S.forcedProblem2D m Φ u₀).system.diffusion x x :=
  Φ.work_le t (S.energySynthesis m x)

/-- The forced energy budget is closed by the definition of the forced state
radius. -/
theorem forcedProblem2D_budget
    {a b : ℝ} (hab : a ≤ b) (m : ℕ)
    (Φ : BoxDualForcing I) (u₀ : BoxL2Sigma I) :
    ‖(S.forcedProblem2D m Φ u₀).initial‖ ^ 2 +
        ∫ s in a..b, Φ.workMajorant s ≤
      Φ.stateRadius a b u₀ ^ 2 := by
  rw [Φ.stateRadius_sq hab u₀, S.forcedProblem2D_initial m Φ u₀]
  have hinit : ‖S.stateInitialCoefficient m u₀‖ ^ 2 ≤ ‖u₀‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg u₀)).2
      (S.norm_stateInitialCoefficient_le m u₀)
  linarith

/-- **Global forced spectral solutions.**  For every finite interval, every
pivot-space initial state, and every continuous energy-dual forcing with a
continuous dual majorant, each spectral level has a solution on the whole
interval. -/
theorem exists_forcedSolution2D
    {a b : ℝ} (hab : a ≤ b) (m : ℕ)
    (Φ : BoxDualForcing I) (u₀ : BoxL2Sigma I) :
    Nonempty (S.CanonicalSolution2D m hab Φ.value
      (S.stateInitialCoefficient m u₀)) := by
  letI : NormedAddCommGroup (S.CoefficientSpace m) :=
    S.coefficientSpaceNormedAddCommGroup m
  letI : InnerProductSpace ℝ (S.CoefficientSpace m) :=
    S.coefficientSpaceInnerProductSpace m
  letI : CompleteSpace (S.CoefficientSpace m) :=
    S.coefficientSpaceCompleteSpace m
  have hFcont := S.forcedProblem2D_forcing_continuous m Φ u₀
  obtain ⟨M₀, hM₀⟩ :=
    (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
      hFcont.continuousOn
  change Nonempty (@VariationalGalerkinProblem.LocalSolutionOn
    (S.CoefficientSpace m)
    (S.coefficientSpaceNormedAddCommGroup m)
    (S.coefficientSpaceInnerProductSpace m)
    (S.coefficientSpaceCompleteSpace m)
    (S.forcedProblem2D m Φ u₀) a b (⟨a, le_rfl, hab⟩ : Icc a b))
  apply @VariationalGalerkinProblem.exists_solutionOn_of_energy_budget
    (S.CoefficientSpace m)
    (S.coefficientSpaceNormedAddCommGroup m)
    (S.coefficientSpaceInnerProductSpace m)
    (S.coefficientSpaceCompleteSpace m)
    (S.forcedProblem2D m Φ u₀) a b hab hFcont
    (max M₀ 0)
    (Φ.stateRadius a b u₀)
    (le_max_right _ _)
    (Φ.stateRadius_nonneg a b u₀)
  · intro t ht
    exact (hM₀ t ht).trans (le_max_left _ _)
  · exact Φ.workMajorant_intervalIntegrable a b
  · intro t _ht
    exact Φ.workMajorant_nonneg t
  · intro t _ht x
    exact S.forcedProblem2D_work_le m Φ u₀ t x
  · exact S.forcedProblem2D_budget hab m Φ u₀

/-- A chosen forced spectral solution on one finite interval. -/
noncomputable def forcedSolution2D
    {a b : ℝ} (hab : a ≤ b) (m : ℕ)
    (Φ : BoxDualForcing I) (u₀ : BoxL2Sigma I) :
    S.CanonicalSolution2D m hab Φ.value (S.stateInitialCoefficient m u₀) :=
  Classical.choice (S.exists_forcedSolution2D hab m Φ u₀)

/-- Abstract consequence of energy-driven continuation: a state-independent
work majorant bounds every trajectory of the variational problem. -/
private theorem norm_le_of_work_majorant
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [CompleteSpace W]
    {P : VariationalGalerkinProblem W} {a b : ℝ} (hab : a ≤ b)
    (u : P.LocalSolutionOn (⟨a, le_rfl, hab⟩ : Icc a b))
    (g : ℝ → ℝ) (hFcont : Continuous P.forcing)
    (hgint : IntervalIntegrable g volume a b)
    (hg_nonneg : ∀ t, 0 ≤ g t)
    (hwork : ∀ t, ∀ x : W, 2 * P.forcing t x ≤ g t + P.system.diffusion x x)
    (R : ℝ) (hR : 0 ≤ R)
    (hbudget : ‖P.initial‖ ^ 2 + ∫ s in a..b, g s ≤ R ^ 2) :
    ∀ t ∈ Icc a b, ‖u.toFun t‖ ≤ R :=
  @VariationalGalerkinProblem.LocalSolutionOn.norm_le_energyRadius
    W _ _ _ P a b hab u g hFcont hgint (fun t _ht => hg_nonneg t)
    (fun t _ht x => hwork t x) R hR hbudget

/-- Abstract consequence of the absorbed energy estimate: the accumulated
diffusion is bounded by the initial energy plus the work majorant. -/
private theorem diffusion_integral_le_of_work_majorant
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [CompleteSpace W]
    {P : VariationalGalerkinProblem W} {a b : ℝ} (hab : a ≤ b)
    (u : P.LocalSolutionOn (⟨a, le_rfl, hab⟩ : Icc a b))
    (g : ℝ → ℝ) (hFcont : Continuous P.forcing)
    (hgint : IntervalIntegrable g volume a b)
    (hwork : ∀ t, ∀ x : W, 2 * P.forcing t x ≤ g t + P.system.diffusion x x) :
    ∫ s in a..b, P.system.diffusion (u.toFun s) (u.toFun s) ≤
      ‖P.initial‖ ^ 2 + ∫ s in a..b, g s := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hAint := u.diffusion_intervalIntegrable ha hb hab
  have hFint := u.forcing_intervalIntegrable hFcont ha hb hab
  have hbound := u.aprioriBoundWithDissipationOn g ha hb hab hAint hFint hgint
    (fun s _hs => hwork s (u.toFun s))
  rw [u.initial] at hbound
  nlinarith [sq_nonneg ‖u.toFun b‖]

/-- Every forced spectral trajectory stays in the forced energy ball. -/
theorem forcedSolution2D_norm_le
    {a b : ℝ} (hab : a ≤ b) (m : ℕ)
    (Φ : BoxDualForcing I) (u₀ : BoxL2Sigma I)
    (u : S.CanonicalSolution2D m hab Φ.value
      (S.stateInitialCoefficient m u₀)) :
    ∀ t ∈ Icc a b,
      ‖S.canonicalSolutionToFun m hab u t‖ ≤ Φ.stateRadius a b u₀ := by
  have h := @norm_le_of_work_majorant
    (S.CoefficientSpace m)
    (S.coefficientSpaceNormedAddCommGroup m)
    (S.coefficientSpaceInnerProductSpace m)
    (S.coefficientSpaceCompleteSpace m)
    (S.forcedProblem2D m Φ u₀) a b hab u
    Φ.workMajorant
    (S.forcedProblem2D_forcing_continuous m Φ u₀)
    (Φ.workMajorant_intervalIntegrable a b)
    (fun t => Φ.workMajorant_nonneg t)
    (fun t x => S.forcedProblem2D_work_le m Φ u₀ t x)
    (Φ.stateRadius a b u₀)
    (Φ.stateRadius_nonneg a b u₀)
    (S.forcedProblem2D_budget hab m Φ u₀)
  exact h

/-- The accumulated diffusion of a forced spectral trajectory is bounded by
the squared forced state radius. -/
theorem forcedSolution2D_diffusion_integral_le
    {a b : ℝ} (hab : a ≤ b) (m : ℕ)
    (Φ : BoxDualForcing I) (u₀ : BoxL2Sigma I)
    (u : S.CanonicalSolution2D m hab Φ.value
      (S.stateInitialCoefficient m u₀)) :
    ∫ t in a..b,
        (S.variationalProblem2D m Φ.value
          (S.stateInitialCoefficient m u₀)).system.diffusion
          (S.canonicalSolutionToFun m hab u t)
          (S.canonicalSolutionToFun m hab u t) ≤
      Φ.stateRadius a b u₀ ^ 2 := by
  have h := @diffusion_integral_le_of_work_majorant
    (S.CoefficientSpace m)
    (S.coefficientSpaceNormedAddCommGroup m)
    (S.coefficientSpaceInnerProductSpace m)
    (S.coefficientSpaceCompleteSpace m)
    (S.forcedProblem2D m Φ u₀) a b hab u
    Φ.workMajorant
    (S.forcedProblem2D_forcing_continuous m Φ u₀)
    (Φ.workMajorant_intervalIntegrable a b)
    (fun t x => S.forcedProblem2D_work_le m Φ u₀ t x)
  have h' :
      ∫ t in a..b,
          (S.variationalProblem2D m Φ.value
            (S.stateInitialCoefficient m u₀)).system.diffusion
            (S.canonicalSolutionToFun m hab u t)
            (S.canonicalSolutionToFun m hab u t) ≤
        ‖(S.forcedProblem2D m Φ u₀).initial‖ ^ 2 +
          ∫ s in a..b, Φ.workMajorant s := h
  exact h'.trans (S.forcedProblem2D_budget hab m Φ u₀)

/-- The physical pivot-space bound of a forced spectral trajectory. -/
theorem forcedSolution2D_state_bound
    {a b : ℝ} (hab : a ≤ b) (m : ℕ)
    (Φ : BoxDualForcing I) (u₀ : BoxL2Sigma I)
    (u : S.CanonicalSolution2D m hab Φ.value
      (S.stateInitialCoefficient m u₀)) :
    ∀ t ∈ Icc a b,
      ‖boxEnergyToState I
        (S.energySynthesis m (S.canonicalSolutionToFun m hab u t))‖ ≤
        Φ.stateRadius a b u₀ := by
  intro t ht
  rw [S.boxEnergyToState_energySynthesis, S.norm_stateSynthesis]
  exact S.forcedSolution2D_norm_le hab m Φ u₀ u t ht

/-- State and diffusion estimates give the uniform graph-space radius of the
forced spectral family. -/
theorem forcedSolution2D_energy_toLp_norm_le
    {a b : ℝ} (hab : a ≤ b) (m : ℕ)
    (Φ : BoxDualForcing I) (u₀ : BoxL2Sigma I)
    (u : S.CanonicalSolution2D m hab Φ.value
      (S.stateInitialCoefficient m u₀)) :
    ‖BoundedContinuousFunction.toLp (2 : ℝ≥0∞)
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) ℝ
        (S.solutionEnergyPath2D m (S.canonicalSolutionToFun m hab u)
          (S.canonicalSolution_continuousOn m hab u))‖ ≤
      Φ.energyRadius a b u₀ := by
  simpa only [BoxDualForcing.energyRadius] using
    S.solutionEnergyPath2D_toLp_norm_le_of_state_diffusion m hab
      Φ.value (S.stateInitialCoefficient m u₀)
      (S.canonicalSolutionToFun m hab u)
      (S.canonicalSolution_continuousOn m hab u)
      (Φ.stateRadius a b u₀) (Φ.stateRadius a b u₀)
      (Φ.stateRadius_nonneg a b u₀)
      (Φ.stateRadius_nonneg a b u₀)
      (S.forcedSolution2D_state_bound hab m Φ u₀ u)
      (S.forcedSolution2D_diffusion_integral_le hab m Φ u₀ u)

/-- Ordered-interval form of the forced graph-energy estimate. -/
theorem forcedSolution2D_energy_integral_le
    {a b : ℝ} (hab : a ≤ b) (m : ℕ)
    (Φ : BoxDualForcing I) (u₀ : BoxL2Sigma I)
    (u : S.CanonicalSolution2D m hab Φ.value
      (S.stateInitialCoefficient m u₀)) :
    ∫ t in a..b,
        ‖S.energySynthesis m (S.canonicalSolutionToFun m hab u t)‖ ^ 2 ≤
      Φ.energyRadius a b u₀ ^ 2 := by
  rw [← S.solutionEnergyPath2D_toLp_norm_sq_eq m hab
    (S.canonicalSolutionToFun m hab u)
    (S.canonicalSolution_continuousOn m hab u)]
  set V := BoundedContinuousFunction.toLp (2 : ℝ≥0∞)
    (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) ℝ
    (S.solutionEnergyPath2D m (S.canonicalSolutionToFun m hab u)
      (S.canonicalSolution_continuousOn m hab u)) with hV
  have hle : ‖V‖ ≤ Φ.energyRadius a b u₀ :=
    S.forcedSolution2D_energy_toLp_norm_le hab m Φ u₀ u
  exact (sq_le_sq₀ (norm_nonneg V) (Φ.energyRadius_nonneg a b u₀)).2 hle

/-- **The forced two-dimensional spectral compactness family.**  Arbitrary
continuous energy-dual forcing, an arbitrary pivot-space initial state, and an
arbitrary finite interval. -/
noncomputable def forcedLeraySpectralCompactFamily2D
    {a b : ℝ} (hab : a ≤ b)
    (Φ : BoxDualForcing I) (u₀ : BoxL2Sigma I) :
    LeraySpectralCompactFamily
      (I := Icc a b) (V := BoxH1ZeroSigma I) (H := BoxL2Sigma I)
      (μ := SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) := by
  apply S.leraySpectralCompactFamily2D hab Φ.value
    (fun m => S.stateInitialCoefficient m u₀)
    (fun m => S.forcedSolution2D hab m Φ u₀)
    Φ.bound
    (Φ.stateRadius a b u₀)
    (Φ.energyRadius a b u₀)
    (Φ.dualRadius a b)
  · exact Φ.stateRadius_nonneg a b u₀
  · exact Φ.energyRadius_nonneg a b u₀
  · intro t _ht
    exact Φ.bound_nonneg t
  · intro t _ht φ
    exact Φ.norm_le t φ
  · exact Φ.aestronglyMeasurable_value _
  · intro m t ht
    exact S.forcedSolution2D_state_bound hab m Φ u₀
      (S.forcedSolution2D hab m Φ u₀) t ht
  · intro m
    exact S.forcedSolution2D_energy_integral_le hab m Φ u₀
      (S.forcedSolution2D hab m Φ u₀)
  · exact Φ.bound_memLp a b
  · exact Φ.dualRadius_sq hab

/-- The forced family has a strict subsequence converging strongly in
`L2((a,b); L2_sigma)`. -/
theorem exists_forced_twoDimensional_strongL2_subsequence
    {a b : ℝ} (hab : a ≤ b)
    (Φ : BoxDualForcing I) (u₀ : BoxL2Sigma I) :
    Nonempty (StrongMetricSubsequence
      (S.forcedLeraySpectralCompactFamily2D hab Φ u₀).stateLp) :=
  exists_boxLeray_strongL2_subsequence
    (S.forcedLeraySpectralCompactFamily2D hab Φ u₀)

/-- The forced family has one strict subsequence with simultaneous strong
pivot convergence and weak energy convergence. -/
theorem exists_forced_twoDimensional_strongWeak_subsequence
    {a b : ℝ} (hab : a ≤ b)
    (Φ : BoxDualForcing I) (u₀ : BoxL2Sigma I) :
    Nonempty
      (S.forcedLeraySpectralCompactFamily2D hab Φ u₀).StrongWeakSubsequence := by
  letI : TopologicalSpace.SeparableSpace
      (Lp (BoxH1ZeroSigma I) (2 : ℝ≥0∞)
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)) :=
    boxEnergyTimeLp_separableSpace I a b
  exact @LeraySpectralCompactFamily.exists_strongWeakSubsequence
    (Icc a b) (BoxH1ZeroSigma I) (BoxL2Sigma I)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance (boxH1ZeroSigma_completeSpace I)
    inferInstance inferInstance (boxL2Sigma_completeSpace I)
    (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)
    inferInstance
    (S.forcedLeraySpectralCompactFamily2D hab Φ u₀)
    (boxEnergyTimeLp_separableSpace I a b)

/-- The forced family has one strict subsequence carrying strong state
convergence, weak energy convergence, and uniform convergence of every finite
projected path. -/
theorem exists_forced_twoDimensional_strongWeakPath_subsequence
    {a b : ℝ} (hab : a ≤ b)
    (Φ : BoxDualForcing I) (u₀ : BoxL2Sigma I) :
    Nonempty
      (S.forcedLeraySpectralCompactFamily2D hab Φ u₀).StrongWeakPathSubsequence := by
  obtain ⟨SW⟩ := S.exists_forced_twoDimensional_strongWeak_subsequence hab Φ u₀
  exact SW.exists_pathwiseRefinement

end BoxCompactSpectralRepresentation

/-- **Forced two-dimensional box Galerkin theorem.**  For every nondegenerate
plane box, every finite interval, every pivot-space initial state, and every
continuous energy-dual forcing with a continuous dual majorant, the canonical
spectral tower has solutions on the whole interval at every level, and the
resulting family has a synchronized strong--weak convergent subsequence with
uniformly convergent finite projected paths. -/
theorem exists_forced_twoDimensional_galerkinCompactness
    {I : BoxIntegral.Box (Fin 2)} {a b : ℝ} (hab : a ≤ b)
    (Φ : BoxDualForcing I) (u₀ : BoxL2Sigma I) :
    Nonempty
      ((boxCompactSpectralRepresentation I).forcedLeraySpectralCompactFamily2D
        hab Φ u₀).StrongWeakPathSubsequence :=
  (boxCompactSpectralRepresentation
    I).exists_forced_twoDimensional_strongWeakPath_subsequence hab Φ u₀

end
