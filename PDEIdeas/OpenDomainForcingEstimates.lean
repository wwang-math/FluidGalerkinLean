import PDEIdeas.OpenDomainSpectral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Energy-dual forcing on an open subdomain

`PDEIdeas.OpenDomainSpectral` equips an open subdomain `Ω ⊆ interior Q` of a
plane rectangle with singular coordinates for its compact energy-to-state
embedding, and inherits the rectangle's Poincaré estimate through the
isometric inclusion `openDomainEnergyToBox`.  This file turns those two
ingredients into the forcing data that the existing Galerkin theory consumes.

A forcing is a time-dependent functional on the *subdomain* energy space,
i.e. a path in `(H¹_{0,σ}(Ω))'`, together with a real majorant of its dual
norm.  Three things are supplied.

* **Pointwise forcing-work absorption.**  `openDomainForcing_work_le` absorbs
  the work of an arbitrary energy-dual functional into the dissipation, with
  the constant `1 + boxPoincareConstant Q ^ 2` and the norms of the ambient
  rectangle — both unchanged from `PDEIdeas.BoxSubspaceEstimates`.  The
  dissipation is measured by `‖openDomainEnergyGradient Ω v‖ ^ 2`, which is
  the diagonal of the inherited diffusion form
  (`openDomainSubspaceDiffusion_self`).

* **Pullback to a Galerkin test space.**
  `OpenDomainEnergyDualForcing.pullback` precomposes the forcing with a
  continuous linear synthesis map `E : W →L[ℝ] H¹_{0,σ}(Ω)`, producing the
  `ℝ → W →L[ℝ] ℝ` field that `VariationalGalerkinProblem.forcing` expects.
  `OpenDomainEnergyDualForcing.head` is the same composition taken against
  `CompactEmbeddingSpectralRepresentation.energySynthesis S m`, i.e. the
  pullback to the finite spectral head `m` of the subdomain tower.

* **Measurability and time integrability.**  Exactly the hypotheses used by
  `VariationalGalerkinProblem.exists_solutionOn_of_energy_budget`
  (continuity of the pulled-back forcing, a uniform operator bound on a
  compact interval, an interval-integrable nonnegative work majorant, and the
  pointwise absorption inequality), by
  `VariationalGalerkinProblem.dualRHS_aestronglyMeasurable` (ae strong
  measurability), and by the compactness assembly (`MemLp _ 2` of the dual
  majorant and the accumulated squared majorant).

## Why the pullback is stated over an abstract test space

Everything that mentions an operator norm on a dual space is stated for an
abstract `W` with `[NormedAddCommGroup W] [NormedSpace ℝ W]`.  This is not a
weakening: `VariationalGalerkinProblem` is itself stated over an abstract
normed `W`, and a concrete spectral head is used through it by supplying the
head's normed-space instances explicitly, exactly as
`BoxForcedSpectralGalerkin.exists_forcedSolution2D` does with
`letI : NormedAddCommGroup (S.CoefficientSpace m) := …`.  Stating the
operator-norm facts over the raw subtype `↥(S.stateSpace m)` instead is not
possible here: `Norm (↥(S.stateSpace m) →L[ℝ] ℝ)` is not reachable by
instance synthesis, because the `TopologicalSpace` carried by a submodule
coercion is `instTopologicalSpaceSubtype`, which is only non-reducibly
defeq to the one induced by `Submodule.seminormedAddCommGroup`.  The
norm-free head statements below are given directly.

## Time-integrability scope

The structure `OpenDomainEnergyDualForcing` separates its hypotheses.  The
majorant `bound` is only assumed ae strongly measurable with locally
square-integrable square; continuity of `bound` is never assumed.  The field
`continuous_value` is used **only** by the six continuity-dependent
statements listed in the closing remark: `continuous_pullback`,
`continuous_head` and their consequences.  It is retained because the
finite-dimensional solvability theorem
`VariationalGalerkinProblem.exists_solutionOn_of_energy_budget` requires
`Continuous P.forcing`.  See the closing remark for the exact gap this
leaves.
-/

open InnerProductSpace MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

/-! ### The subdomain inclusion reads off the ambient state and gradient -/

section Inclusion

variable {n : ℕ} {Q : BoxIntegral.Box (Fin (n + 1))} {Ω : OpenDomainInBox Q}

/-- The inclusion of the subdomain energy space into the rectangle energy
space preserves the graph norm. -/
@[simp]
theorem norm_openDomainEnergyToBox (v : OpenDomainH1ZeroSigma Ω) :
    ‖openDomainEnergyToBox Ω v‖ = ‖v‖ := rfl

/-- The ambient gradient of an included subdomain field is its subdomain
gradient. -/
@[simp]
theorem boxEnergyGradient_openDomainEnergyToBox (v : OpenDomainH1ZeroSigma Ω) :
    boxEnergyGradient Q (openDomainEnergyToBox Ω v) =
      openDomainEnergyGradient Ω v := rfl

/-- The ambient state norm of an included subdomain field is its subdomain
state norm. -/
@[simp]
theorem norm_boxEnergyToState_openDomainEnergyToBox
    (v : OpenDomainH1ZeroSigma Ω) :
    ‖boxEnergyToState Q (openDomainEnergyToBox Ω v)‖ =
      ‖openDomainEnergyToState Ω v‖ := rfl

/-- Exact graph-norm identity on the subdomain energy space: the graph norm
splits into the state and gradient norms of the subdomain maps. -/
theorem openDomainEnergy_norm_sq_eq_state_add_gradient
    (v : OpenDomainH1ZeroSigma Ω) :
    ‖v‖ ^ 2 =
      ‖openDomainEnergyToState Ω v‖ ^ 2 +
        ‖openDomainEnergyGradient Ω v‖ ^ 2 :=
  boxEnergy_norm_sq_eq_state_add_gradient Q (openDomainEnergyToBox Ω v)

end Inclusion

/-! ### The inherited Poincaré estimate in subdomain norms -/

section Poincare

variable {Q : BoxIntegral.Box (Fin 2)} {Ω : OpenDomainInBox Q}

/-- The diffusion form inherited from the rectangle, evaluated on the
diagonal, is the squared subdomain gradient norm. -/
theorem openDomainSubspaceDiffusion_self (v : OpenDomainH1ZeroSigma Ω) :
    boxSubspaceDiffusion Q (openDomainEnergyToBox Ω) v v =
      ‖openDomainEnergyGradient Ω v‖ ^ 2 :=
  boxSubspaceDiffusion_self Q (openDomainEnergyToBox Ω) v

/-- **Poincaré inequality on the open subdomain**, in subdomain norms.  The
constant is the rectangle constant `boxPoincareConstant Q`, unchanged. -/
theorem openDomainPoincare (v : OpenDomainH1ZeroSigma Ω) :
    ‖openDomainEnergyToState Ω v‖ ≤
      boxPoincareConstant Q * ‖openDomainEnergyGradient Ω v‖ :=
  boxSubspace_state_le Q (openDomainEnergyToBox Ω) v

/-- The bundled inherited estimates carry the rectangle Poincaré constant. -/
@[simp]
theorem openDomainEnergyEstimates_poincareConstant (Ω : OpenDomainInBox Q) :
    (openDomainEnergyEstimates Ω).poincareConstant = boxPoincareConstant Q :=
  rfl

/-- The graph norm of a subdomain field is controlled by its gradient alone,
with the rectangle constant `Real.sqrt (1 + boxPoincareConstant Q ^ 2)`. -/
theorem openDomainEnergy_norm_le_gradient (v : OpenDomainH1ZeroSigma Ω) :
    ‖v‖ ≤
      Real.sqrt (1 + boxPoincareConstant Q ^ 2) *
        ‖openDomainEnergyGradient Ω v‖ :=
  boxSubspace_embedding_norm_le_gradient Q (openDomainEnergyToBox Ω) v

/-- **Pointwise forcing-work absorption on the open subdomain.**  The work of
an arbitrary functional on the subdomain energy space, measured by any
majorant `f` of its dual norm relative to the subdomain graph norm, is
absorbed into the dissipation with the rectangle constant
`1 + boxPoincareConstant Q ^ 2`.  This is the hypothesis shape required by
energy-driven continuation of the finite-dimensional Galerkin systems. -/
theorem openDomainForcing_work_le
    (F : OpenDomainH1ZeroSigma Ω →L[ℝ] ℝ) (f : ℝ) (hf : 0 ≤ f)
    (hbound : ∀ w : OpenDomainH1ZeroSigma Ω, ‖F w‖ ≤ f * ‖w‖)
    (v : OpenDomainH1ZeroSigma Ω) :
    2 * F v ≤
      (1 + boxPoincareConstant Q ^ 2) * f ^ 2 +
        ‖openDomainEnergyGradient Ω v‖ ^ 2 := by
  have hK : (0 : ℝ) ≤ 1 + boxPoincareConstant Q ^ 2 := by positivity
  have h1 : F v ≤ f * ‖v‖ := by
    have hnorm : |F v| ≤ f * ‖v‖ := by
      simpa only [Real.norm_eq_abs] using hbound v
    exact (le_abs_self _).trans hnorm
  have hmul : f * ‖v‖ ≤
      f * (Real.sqrt (1 + boxPoincareConstant Q ^ 2) *
        ‖openDomainEnergyGradient Ω v‖) :=
    mul_le_mul_of_nonneg_left (openDomainEnergy_norm_le_gradient v) hf
  have hyoung := two_mul_le_add_sq
    (Real.sqrt (1 + boxPoincareConstant Q ^ 2) * f)
    ‖openDomainEnergyGradient Ω v‖
  have hsq : (Real.sqrt (1 + boxPoincareConstant Q ^ 2) * f) ^ 2 =
      (1 + boxPoincareConstant Q ^ 2) * f ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hK]
  rw [← hsq]
  linarith

/-- The same absorption written against the inherited diffusion form. -/
theorem openDomainForcing_work_le_diffusion
    (F : OpenDomainH1ZeroSigma Ω →L[ℝ] ℝ) (f : ℝ) (hf : 0 ≤ f)
    (hbound : ∀ w : OpenDomainH1ZeroSigma Ω, ‖F w‖ ≤ f * ‖w‖)
    (v : OpenDomainH1ZeroSigma Ω) :
    2 * F v ≤
      (1 + boxPoincareConstant Q ^ 2) * f ^ 2 +
        boxSubspaceDiffusion Q (openDomainEnergyToBox Ω) v v := by
  rw [openDomainSubspaceDiffusion_self]
  exact openDomainForcing_work_le F f hf hbound v

end Poincare

/-! ### Time-dependent energy-dual forcing -/

/-- A time-dependent forcing valued in the dual of the subdomain energy space,
together with a real majorant of its dual norm.

The hypotheses are the ones the existing Galerkin theory consumes.  Continuity
is imposed on `value` only, because
`VariationalGalerkinProblem.exists_solutionOn_of_energy_budget` asks for
`Continuous P.forcing`; the majorant `bound` is only required to be ae
strongly measurable with locally square-integrable square. -/
structure OpenDomainEnergyDualForcing {Q : BoxIntegral.Box (Fin 2)}
    (Ω : OpenDomainInBox Q) where
  /-- The forcing functional on the subdomain energy space at each time. -/
  value : ℝ → OpenDomainH1ZeroSigma Ω →L[ℝ] ℝ
  /-- A majorant of the dual norm of the forcing. -/
  bound : ℝ → ℝ
  /-- Continuity in time, required by finite-dimensional solvability only. -/
  continuous_value : Continuous value
  bound_nonneg : ∀ t, 0 ≤ bound t
  /-- `bound` majorizes the dual norm relative to the subdomain graph norm. -/
  norm_le : ∀ (t : ℝ) (w : OpenDomainH1ZeroSigma Ω),
    ‖value t w‖ ≤ bound t * ‖w‖
  aestronglyMeasurable_bound : AEStronglyMeasurable bound volume
  /-- Local square integrability of the dual majorant. -/
  sq_intervalIntegrable : ∀ a b : ℝ,
    IntervalIntegrable (fun t => bound t ^ 2) volume a b

namespace OpenDomainEnergyDualForcing

variable {Q : BoxIntegral.Box (Fin 2)} {Ω : OpenDomainInBox Q}

/-- **Energy-path forcing.**  A continuous path in the subdomain energy space
acts on that space through its inner product, and its own graph norm is a
majorant of the resulting dual norm.  By the Riesz isomorphism every
continuous path of functionals on `H¹_{0,σ}(Ω)` arises this way. -/
def ofEnergyPath (r : ℝ → OpenDomainH1ZeroSigma Ω) (hr : Continuous r) :
    OpenDomainEnergyDualForcing Ω where
  value := fun t => innerSL ℝ (r t)
  bound := fun t => ‖r t‖
  continuous_value :=
    (innerSL ℝ (E := OpenDomainH1ZeroSigma Ω)).continuous.comp hr
  bound_nonneg := fun _ => norm_nonneg _
  norm_le := by
    intro t w
    show ‖⟪r t, w⟫_ℝ‖ ≤ ‖r t‖ * ‖w‖
    rw [Real.norm_eq_abs]
    exact abs_real_inner_le_norm _ _
  aestronglyMeasurable_bound := hr.norm.aestronglyMeasurable
  sq_intervalIntegrable := fun a b => (hr.norm.pow 2).intervalIntegrable a b

@[simp]
theorem ofEnergyPath_value_apply (r : ℝ → OpenDomainH1ZeroSigma Ω)
    (hr : Continuous r) (t : ℝ) (w : OpenDomainH1ZeroSigma Ω) :
    (ofEnergyPath r hr).value t w = ⟪r t, w⟫_ℝ := rfl

@[simp]
theorem ofEnergyPath_bound (r : ℝ → OpenDomainH1ZeroSigma Ω)
    (hr : Continuous r) (t : ℝ) : (ofEnergyPath r hr).bound t = ‖r t‖ := rfl

instance : Inhabited (OpenDomainEnergyDualForcing Ω) :=
  ⟨ofEnergyPath (fun _ => 0) continuous_const⟩

variable (Φ : OpenDomainEnergyDualForcing Ω)

/-! #### The state-independent work majorant -/

/-- State-independent work majorant supplied by the inherited Poincaré
constant. -/
def workMajorant (t : ℝ) : ℝ :=
  (1 + boxPoincareConstant Q ^ 2) * Φ.bound t ^ 2

theorem workMajorant_nonneg (t : ℝ) : 0 ≤ Φ.workMajorant t := by
  unfold workMajorant
  positivity

/-- Interval integrability of the work majorant, from local square
integrability of the dual majorant alone. -/
theorem workMajorant_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable Φ.workMajorant volume a b :=
  (Φ.sq_intervalIntegrable a b).const_mul (1 + boxPoincareConstant Q ^ 2)

theorem workIntegral_nonneg {a b : ℝ} (hab : a ≤ b) :
    0 ≤ ∫ s in a..b, Φ.workMajorant s :=
  intervalIntegral.integral_nonneg hab fun s _ => Φ.workMajorant_nonneg s

/-- **Poincaré absorption of the forcing work.**  The work of the forcing at
any subdomain energy vector is bounded by a state-independent majorant plus
the dissipation, with the rectangle constant and the subdomain gradient
norm. -/
theorem work_le (t : ℝ) (v : OpenDomainH1ZeroSigma Ω) :
    2 * Φ.value t v ≤
      Φ.workMajorant t + ‖openDomainEnergyGradient Ω v‖ ^ 2 :=
  openDomainForcing_work_le (Φ.value t) (Φ.bound t) (Φ.bound_nonneg t)
    (Φ.norm_le t) v

/-- The absorption written against the inherited diffusion form. -/
theorem work_le_diffusion (t : ℝ) (v : OpenDomainH1ZeroSigma Ω) :
    2 * Φ.value t v ≤
      Φ.workMajorant t +
        boxSubspaceDiffusion Q (openDomainEnergyToBox Ω) v v := by
  rw [openDomainSubspaceDiffusion_self]
  exact Φ.work_le t v

/-! #### Square integrability of the dual majorant -/

/-- The dual majorant is square integrable on every compact interval. -/
theorem memLp_bound {a b : ℝ} (hab : a ≤ b) :
    MemLp Φ.bound 2 (volume.restrict (Icc a b)) := by
  have hmeas : AEStronglyMeasurable Φ.bound (volume.restrict (Icc a b)) :=
    Φ.aestronglyMeasurable_bound.restrict
  rw [memLp_two_iff_integrable_sq hmeas]
  have hIoc : IntegrableOn (fun t => Φ.bound t ^ 2) (Ioc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1
      (Φ.sq_intervalIntegrable a b)
  show IntegrableOn (fun t => Φ.bound t ^ 2) (Icc a b) volume
  rw [integrableOn_Icc_iff_integrableOn_Ioc]
  exact hIoc

/-- Square root of the accumulated squared dual majorant. -/
def dualRadius (a b : ℝ) : ℝ :=
  Real.sqrt (∫ t in a..b, Φ.bound t ^ 2)

theorem dualRadius_nonneg (a b : ℝ) : 0 ≤ Φ.dualRadius a b :=
  Real.sqrt_nonneg _

theorem dualRadius_sq {a b : ℝ} (hab : a ≤ b) :
    ∫ t in a..b, ‖Φ.bound t‖ ^ 2 ≤ Φ.dualRadius a b ^ 2 := by
  have hnonneg : 0 ≤ ∫ t in a..b, Φ.bound t ^ 2 :=
    intervalIntegral.integral_nonneg hab fun t _ => by positivity
  unfold dualRadius
  rw [Real.sq_sqrt hnonneg]
  refine le_of_eq (intervalIntegral.integral_congr fun t _ => ?_)
  show ‖Φ.bound t‖ ^ 2 = Φ.bound t ^ 2
  rw [Real.norm_eq_abs, abs_of_nonneg (Φ.bound_nonneg t)]

/-! ### Pullback along a Galerkin synthesis map -/

section Pullback

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (E : W →L[ℝ] OpenDomainH1ZeroSigma Ω)

/-- **Pullback of the forcing along a synthesis map.**  This is the
`ℝ → W →L[ℝ] ℝ` field that `VariationalGalerkinProblem.forcing` expects on a
Galerkin test space `W` presented by `E : W →L[ℝ] H¹_{0,σ}(Ω)`. -/
def pullback : ℝ → W →L[ℝ] ℝ := fun t => (Φ.value t).comp E

@[simp]
theorem pullback_apply (t : ℝ) (x : W) :
    Φ.pullback E t x = Φ.value t (E x) := rfl

/-- Continuity in time of the pulled-back forcing; this is the `hFcont`
hypothesis of
`VariationalGalerkinProblem.exists_solutionOn_of_energy_budget`. -/
theorem continuous_pullback : Continuous (Φ.pullback E) := by
  have hcomp : Continuous
      (fun G : OpenDomainH1ZeroSigma Ω →L[ℝ] ℝ => G.comp E) := by
    fun_prop
  exact hcomp.comp Φ.continuous_value

/-- Ae strong measurability of the pulled-back forcing; this is the
`hforcing` hypothesis of
`VariationalGalerkinProblem.dualRHS_aestronglyMeasurable`. -/
theorem aestronglyMeasurable_pullback (μ : Measure ℝ) :
    AEStronglyMeasurable (Φ.pullback E) μ :=
  (Φ.continuous_pullback E).aestronglyMeasurable

/-- The dual norm of the pulled-back forcing, against any bound `C` for the
synthesis map. -/
theorem norm_pullback_le (t : ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hEC : ∀ x : W, ‖E x‖ ≤ C * ‖x‖) :
    ‖Φ.pullback E t‖ ≤ Φ.bound t * C := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (Φ.bound_nonneg t) hC) fun x => ?_
  calc
    ‖Φ.pullback E t x‖ ≤ Φ.bound t * ‖E x‖ := Φ.norm_le t (E x)
    _ ≤ Φ.bound t * (C * ‖x‖) :=
      mul_le_mul_of_nonneg_left (hEC x) (Φ.bound_nonneg t)
    _ = Φ.bound t * C * ‖x‖ := by ring

/-- The dual norm of the pulled-back forcing is majorized by the dual
majorant of the forcing, up to a constant depending only on the synthesis
map. -/
theorem exists_norm_pullback_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖Φ.pullback E t‖ ≤ Φ.bound t * C := by
  obtain ⟨C, hCpos, hC⟩ := E.bound
  exact ⟨C, hCpos.le, fun t => Φ.norm_pullback_le E t C hCpos.le hC⟩

/-- Uniform operator bound of the pulled-back forcing on a compact interval;
this is the `hFbound` hypothesis of
`VariationalGalerkinProblem.exists_solutionOn_of_energy_budget`. -/
theorem exists_pullback_opNorm_bound (a b : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc a b, ‖Φ.pullback E t‖ ≤ M := by
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
      (Φ.continuous_pullback E).continuousOn
  exact ⟨max C 0, le_max_right _ _,
    fun t ht => (hC t ht).trans (le_max_left _ _)⟩

/-- **Absorption at the test-space level.**  This is the `hwork` hypothesis of
`VariationalGalerkinProblem.exists_solutionOn_of_energy_budget`, with the
dissipation of the synthesized energy vector on the right. -/
theorem pullback_work_le (t : ℝ) (x : W) :
    2 * Φ.pullback E t x ≤
      Φ.workMajorant t + ‖openDomainEnergyGradient Ω (E x)‖ ^ 2 :=
  Φ.work_le t (E x)

/-- The test-space absorption written against the inherited diffusion
form. -/
theorem pullback_work_le_diffusion (t : ℝ) (x : W) :
    2 * Φ.pullback E t x ≤
      Φ.workMajorant t +
        boxSubspaceDiffusion Q (openDomainEnergyToBox Ω) (E x) (E x) :=
  Φ.work_le_diffusion t (E x)

/-- **The hypothesis package of the finite-dimensional existence theorem.**
Every hypothesis of
`VariationalGalerkinProblem.exists_solutionOn_of_energy_budget` that concerns
the forcing is available on every Galerkin test space and every finite
interval, with the work majorant `Φ.workMajorant` playing the role of `g`. -/
theorem pullback_galerkin_hypotheses (a b : ℝ) :
    Continuous (Φ.pullback E) ∧
      (∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc a b, ‖Φ.pullback E t‖ ≤ M) ∧
      IntervalIntegrable Φ.workMajorant volume a b ∧
      (∀ t ∈ Icc a b, 0 ≤ Φ.workMajorant t) ∧
      (∀ t ∈ Icc a b, ∀ x : W,
        2 * Φ.pullback E t x ≤
          Φ.workMajorant t + ‖openDomainEnergyGradient Ω (E x)‖ ^ 2) :=
  ⟨Φ.continuous_pullback E,
    Φ.exists_pullback_opNorm_bound E a b,
    Φ.workMajorant_intervalIntegrable a b,
    fun t _ => Φ.workMajorant_nonneg t,
    fun t _ x => Φ.pullback_work_le E t x⟩

end Pullback

/-! ### Pullback to a finite spectral head -/

section Head

variable (S : OpenDomainCompactSpectralRepresentation Ω) (m : ℕ)

/-- **Pullback of the forcing to the finite spectral head `m`** of the
subdomain tower: the synthesis map is
`CompactEmbeddingSpectralRepresentation.energySynthesis`.

This repeats `OpenDomainEnergyDualForcing.pullback` rather than instantiating
it.  The synthesis map of the abstract tower is stated over an abstract
energy space, so its instances on `↥(OpenDomainH1ZeroSigma Ω)` are the ones
induced by `Submodule.normedAddCommGroup`, whereas a freshly elaborated
`↥(OpenDomainH1ZeroSigma Ω) →L[ℝ] ℝ` carries `instTopologicalSpaceSubtype`;
the two presentations are defeq but do not unify during elaboration. -/
def head :=
  fun t => (Φ.value t).comp
    (CompactEmbeddingSpectralRepresentation.energySynthesis S m)

@[simp]
theorem head_apply (t : ℝ) (x : S.stateSpace m) :
    Φ.head S m t x =
      Φ.value t
        (CompactEmbeddingSpectralRepresentation.energySynthesis S m x) :=
  rfl

/-- Continuity in time of the head forcing; this is the `hFcont` hypothesis
of `VariationalGalerkinProblem.exists_solutionOn_of_energy_budget` at the
spectral level `m`. -/
theorem continuous_head : Continuous (Φ.head S m) := by
  have hcomp : Continuous
      (fun G : OpenDomainH1ZeroSigma Ω →L[ℝ] ℝ =>
        G.comp (CompactEmbeddingSpectralRepresentation.energySynthesis S m)) := by
    fun_prop
  exact hcomp.comp Φ.continuous_value

/-- Pointwise dual bound at the spectral level `m`, stated without an
operator norm on the head dual. -/
theorem norm_head_apply_le (t : ℝ) (x : S.stateSpace m) :
    ‖Φ.head S m t x‖ ≤
      Φ.bound t *
        ‖CompactEmbeddingSpectralRepresentation.energySynthesis S m x‖ :=
  Φ.norm_le t _

/-- **Absorption at the coefficient level.**  The dissipation on the right is
the squared gradient norm of the synthesized energy vector. -/
theorem head_work_le (t : ℝ) (x : S.stateSpace m) :
    2 * Φ.head S m t x ≤
      Φ.workMajorant t +
        ‖openDomainEnergyGradient Ω
          (CompactEmbeddingSpectralRepresentation.energySynthesis S m x)‖ ^ 2 :=
  Φ.work_le t _

/-- The coefficient-level absorption written against the inherited diffusion
form. -/
theorem head_work_le_diffusion (t : ℝ) (x : S.stateSpace m) :
    2 * Φ.head S m t x ≤
      Φ.workMajorant t +
        boxSubspaceDiffusion Q (openDomainEnergyToBox Ω)
          (CompactEmbeddingSpectralRepresentation.energySynthesis S m x)
          (CompactEmbeddingSpectralRepresentation.energySynthesis S m x) :=
  Φ.work_le_diffusion t _

/-- **The instance-free part of the hypothesis package at the spectral level
`m`.**  The remaining hypothesis of
`VariationalGalerkinProblem.exists_solutionOn_of_energy_budget`, the uniform
operator bound `‖P.forcing t‖ ≤ M`, is `exists_pullback_opNorm_bound` and is
obtained from `continuous_head` once the head's normed-space instances are
fixed, as `BoxForcedSpectralGalerkin.exists_forcedSolution2D` does. -/
theorem head_galerkin_hypotheses (a b : ℝ) :
    Continuous (Φ.head S m) ∧
      IntervalIntegrable Φ.workMajorant volume a b ∧
      (∀ t ∈ Icc a b, 0 ≤ Φ.workMajorant t) ∧
      (∀ t ∈ Icc a b, ∀ x : S.stateSpace m,
        2 * Φ.head S m t x ≤
          Φ.workMajorant t +
            ‖openDomainEnergyGradient Ω
              (CompactEmbeddingSpectralRepresentation.energySynthesis S m
                x)‖ ^ 2) :=
  ⟨Φ.continuous_head S m,
    Φ.workMajorant_intervalIntegrable a b,
    fun t _ => Φ.workMajorant_nonneg t,
    fun t _ x => Φ.head_work_le S m t x⟩

end Head

end OpenDomainEnergyDualForcing

/-!
### Remaining time-integrability gap

Let `Φ : OpenDomainEnergyDualForcing Ω`.  Every statement in this file except
`OpenDomainEnergyDualForcing.continuous_pullback`,
`OpenDomainEnergyDualForcing.aestronglyMeasurable_pullback`,
`OpenDomainEnergyDualForcing.exists_pullback_opNorm_bound`,
`OpenDomainEnergyDualForcing.pullback_galerkin_hypotheses`,
`OpenDomainEnergyDualForcing.continuous_head` and
`OpenDomainEnergyDualForcing.head_galerkin_hypotheses` is proved from

  `bound_nonneg`, `norm_le`, `aestronglyMeasurable_bound`,
  `sq_intervalIntegrable`

alone.  This has been checked by deleting the field `continuous_value` from
the structure together with those six statements: the rest of the file still
compiles.  In particular the absorption chain
`openDomainPoincare → openDomainEnergy_norm_le_gradient →
openDomainForcing_work_le → work_le → pullback_work_le → head_work_le`, the
interval integrability `workMajorant_intervalIntegrable`, the square
integrability `memLp_bound`, and the dual radius estimate `dualRadius_sq` use
no continuity in time whatsoever: `bound ∈ L²_loc(ℝ)` suffices, and the
constants are the rectangle constants `boxPoincareConstant Q` and
`1 + boxPoincareConstant Q ^ 2`.

The gap is exactly one hypothesis, and it concerns the functional and not the
majorant.  `VariationalGalerkinProblem.exists_solutionOn_of_energy_budget`
takes `hFcont : Continuous P.forcing`, because its local step
`VariationalGalerkinProblem.exists_localSolutionOn` runs Picard--Lindelöf on
the coefficient ODE, which in this development requires a time-continuous
vector field.  Therefore `continuous_value : Continuous value` cannot be
dropped from `OpenDomainEnergyDualForcing`, and the class

  `value : ℝ → (H¹_{0,σ}(Ω))'` strongly measurable with
  `∫ₐᵇ ‖value t‖² dt < ∞`,

i.e. the natural Leray--Hopf forcing class `L²(a, b; (H¹_{0,σ}(Ω))')`, is
**not** covered by `OpenDomainEnergyDualForcing` unless the path happens to be
continuous.  Closing that gap requires a Carathéodory existence theorem for
the finite-dimensional coefficient ODE (measurable in `t`, locally Lipschitz
in `x`, with a locally integrable majorant), which this development does not
contain; nothing in this file asserts or assumes one.
-/

end
