import PDEIdeas.OpenDomainGelfandTriple
import PDEIdeas.BoxL4Convection
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The two-dimensional common-dual derivative estimate on an open subdomain

For a path `U` of states of the energy space `H¹₀σ(Ω)` of an open subdomain `Ω` of a plane
rectangle `Q`, the weak Navier--Stokes right-hand side

`φ ↦ -⟪DU, Dφ⟫ - b(U, U, φ) + ⟨forcing, φ⟩`

is a functional on `H¹₀σ(Ω)`, that is an element of the common dual `(H¹₀σ(Ω))'`.  This file
bounds it, pointwise and then in `L²` in time, starting from **explicit uniform state and
energy bounds on the path**.  It is the derivative bound consumed by the Aubin--Lions route
of `PDEIdeas.OpenDomainTimeCompactness`; here it is proved, never assumed.

The two analytic ingredients are the **already proved box estimates**, read through the
canonical isometric inclusion `openDomainEnergyToBox Ω`:

* diffusion — `norm_boxGradientDiffusion_apply_le` of `PDEIdeas.BoxSobolevClosure`;
* convection — `BoxLadyzhenskayaRealization.convectionForm_diagonal_norm_le` of
  `PDEIdeas.BoxL4Convection`, i.e. the two-dimensional Ladyzhenskaya `L4-L2-L4` estimate.

The forcing is an arbitrary envelope `f` with `‖forcing t φ‖ ≤ f t * ‖φ‖`; it may be `0`.

## Main results

Generic layer (arbitrary normed space, so that the estimates are elaborated cheaply):

* `dualRHS` — the functional `φ ↦ -diffusion u φ - convection u u φ + forcing t φ`;
* `norm_dualRHS_le`, `norm_dualRHS_sq_le` — the pointwise and squared estimates;
* `dualRHS_aestronglyMeasurable`;
* `dualRHS_memLp_and_integral_le` — the `L²`-in-time estimate.

Open-subdomain layer:

* `diffusionForm`, `convectionForm` — the two box forms restricted to `Ω`;
* `norm_diffusionForm_apply_le`, `norm_convectionForm_diagonal_le` — their estimates on `Ω`;
* `openDomain_dualRHS_memLp_and_integral_le` — **the two-dimensional common-dual derivative
  estimate on `Ω`**: with `‖state (U t)‖ ≤ H` on `[a,b]`, `∫ ‖U t‖² ≤ R²` and `∫ f² ≤ F²`,
  `t ↦ dualRHS t (U t)` lies in `L²([a,b]; (H¹₀σ(Ω))')` and
  `∫ ‖dualRHS t (U t)‖² ≤ 2 (1 + c H)² R² + 2 F²` with
  `c = boxLpConvectionBound Q * L.constant`;
* `openDomain_dualRHS_memLp_and_integral_le_zeroForcing` — the unforced case.

## Scope and independence

The path `U` is arbitrary: no Galerkin problem, no solution theory and no existence
statement is used, so the file depends only on the `Ω` core (`PDEIdeas.OpenDomainGelfandTriple`)
and the box diffusion/convection layer.  For a finite Galerkin level, apply the results to
the synthesised path `t ↦ energySynthesis (coefficients t)`.  Viscosity is `1`, matching the
unit-viscosity convention of the box development; a constant viscosity only rescales the
diffusion term, which is linear in the energy norm.

Following the implementation note of the surrounding development, every estimate is proved
once for an arbitrary normed space and then instantiated a single time at the concrete
closure space, where elaboration is expensive.
-/

open Filter InnerProductSpace MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace OpenDomainDualDerivative

/-! ## Generic layer -/

section Generic

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The common-dual right-hand side of a weak Navier--Stokes equation:
`φ ↦ -diffusion u φ - convection u u φ + forcing t φ`, an element of the dual `V'`. -/
def dualRHS (diffusion : V →L[ℝ] V →L[ℝ] ℝ)
    (convection : V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ)
    (forcing : ℝ → V →L[ℝ] ℝ) (t : ℝ) (u : V) : V →L[ℝ] ℝ :=
  -diffusion u - convection u u + forcing t

@[simp]
theorem dualRHS_apply (diffusion : V →L[ℝ] V →L[ℝ] ℝ)
    (convection : V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ)
    (forcing : ℝ → V →L[ℝ] ℝ) (t : ℝ) (u φ : V) :
    dualRHS diffusion convection forcing t u φ =
      -diffusion u φ - convection u u φ + forcing t φ := rfl

/-- **Pointwise common-dual estimate.**  Diffusion contributes the energy norm, convection
the Ladyzhenskaya product of the state and energy norms, and the forcing its envelope. -/
theorem norm_dualRHS_le (diffusion : V →L[ℝ] V →L[ℝ] ℝ)
    (convection : V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ)
    (forcing : ℝ → V →L[ℝ] ℝ) (state : V → ℝ) (cB : ℝ) (hcB : 0 ≤ cB)
    (hstate_nonneg : ∀ u, 0 ≤ state u)
    (hdiff : ∀ u φ : V, ‖diffusion u φ‖ ≤ ‖u‖ * ‖φ‖)
    (hconv : ∀ u φ : V, ‖convection u u φ‖ ≤ cB * state u * ‖u‖ * ‖φ‖)
    (t : ℝ) (u : V) (f : ℝ) (hf : 0 ≤ f)
    (hforcing : ∀ φ : V, ‖forcing t φ‖ ≤ f * ‖φ‖) :
    ‖dualRHS diffusion convection forcing t u‖ ≤ ‖u‖ + cB * state u * ‖u‖ + f := by
  have hbound : 0 ≤ ‖u‖ + cB * state u * ‖u‖ + f :=
    add_nonneg
      (add_nonneg (norm_nonneg _)
        (mul_nonneg (mul_nonneg hcB (hstate_nonneg u)) (norm_nonneg _))) hf
  refine (dualRHS diffusion convection forcing t u).opNorm_le_bound hbound fun φ => ?_
  have htri :
      ‖dualRHS diffusion convection forcing t u φ‖ ≤
        ‖diffusion u φ‖ + ‖convection u u φ‖ + ‖forcing t φ‖ := by
    have h := norm_add₃_le (a := -diffusion u φ) (b := -convection u u φ)
      (c := forcing t φ)
    simpa [dualRHS_apply, sub_eq_add_neg] using h
  calc
    ‖dualRHS diffusion convection forcing t u φ‖ ≤
        ‖diffusion u φ‖ + ‖convection u u φ‖ + ‖forcing t φ‖ := htri
    _ ≤ ‖u‖ * ‖φ‖ + cB * state u * ‖u‖ * ‖φ‖ + f * ‖φ‖ :=
      add_le_add (add_le_add (hdiff u φ) (hconv u φ)) (hforcing φ)
    _ = (‖u‖ + cB * state u * ‖u‖ + f) * ‖φ‖ := by ring

/-- **Squared common-dual estimate** under a uniform state bound: the form the `L²`-in-time
integration consumes. -/
theorem norm_dualRHS_sq_le (diffusion : V →L[ℝ] V →L[ℝ] ℝ)
    (convection : V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ)
    (forcing : ℝ → V →L[ℝ] ℝ) (state : V → ℝ) (cB : ℝ) (hcB : 0 ≤ cB)
    (hstate_nonneg : ∀ u, 0 ≤ state u)
    (hdiff : ∀ u φ : V, ‖diffusion u φ‖ ≤ ‖u‖ * ‖φ‖)
    (hconv : ∀ u φ : V, ‖convection u u φ‖ ≤ cB * state u * ‖u‖ * ‖φ‖)
    (t : ℝ) (u : V) (f H : ℝ) (hf : 0 ≤ f) (hH : 0 ≤ H)
    (hforcing : ∀ φ : V, ‖forcing t φ‖ ≤ f * ‖φ‖) (hstate : state u ≤ H) :
    ‖dualRHS diffusion convection forcing t u‖ ^ 2 ≤
      2 * (1 + cB * H) ^ 2 * ‖u‖ ^ 2 + 2 * f ^ 2 := by
  have hbase := norm_dualRHS_le diffusion convection forcing state cB hcB hstate_nonneg
    hdiff hconv t u f hf hforcing
  have hconv' : cB * state u * ‖u‖ ≤ cB * H * ‖u‖ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstate hcB) (norm_nonneg _)
  have hlinear :
      ‖dualRHS diffusion convection forcing t u‖ ≤ (1 + cB * H) * ‖u‖ + f := by
    calc
      ‖dualRHS diffusion convection forcing t u‖ ≤ ‖u‖ + cB * state u * ‖u‖ + f := hbase
      _ ≤ ‖u‖ + cB * H * ‖u‖ + f := by linarith
      _ = (1 + cB * H) * ‖u‖ + f := by ring
  have hcoef : 0 ≤ (1 + cB * H) * ‖u‖ :=
    mul_nonneg (add_nonneg zero_le_one (mul_nonneg hcB hH)) (norm_nonneg _)
  have hsq :
      ‖dualRHS diffusion convection forcing t u‖ ^ 2 ≤ ((1 + cB * H) * ‖u‖ + f) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (add_nonneg hcoef hf)).2 hlinear
  calc
    ‖dualRHS diffusion convection forcing t u‖ ^ 2 ≤
        ((1 + cB * H) * ‖u‖ + f) ^ 2 := hsq
    _ ≤ 2 * ((1 + cB * H) * ‖u‖) ^ 2 + 2 * f ^ 2 := by
      nlinarith [sq_nonneg (((1 + cB * H) * ‖u‖) - f)]
    _ = 2 * (1 + cB * H) ^ 2 * ‖u‖ ^ 2 + 2 * f ^ 2 := by ring

/-- A measurable state path and a measurable forcing path give a measurable common-dual
path. -/
theorem dualRHS_aestronglyMeasurable (diffusion : V →L[ℝ] V →L[ℝ] ℝ)
    (convection : V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ)
    (forcing : ℝ → V →L[ℝ] ℝ) (μ : Measure ℝ) (U : ℝ → V)
    (hU : AEStronglyMeasurable U μ) (hforcing : AEStronglyMeasurable forcing μ) :
    AEStronglyMeasurable (fun t => dualRHS diffusion convection forcing t (U t)) μ := by
  have hdiff : AEStronglyMeasurable (fun t => diffusion (U t)) μ :=
    diffusion.continuous.comp_aestronglyMeasurable hU
  have hconv : AEStronglyMeasurable (fun t => convection (U t) (U t)) μ :=
    convection.aestronglyMeasurable_comp₂ hU hU
  exact (hdiff.neg.sub hconv).add hforcing

/-- **The `L²`-in-time common-dual estimate.**  A uniform state bound `H`, a square
integrable energy path with `∫ ‖U‖² ≤ R²` and a square integrable forcing envelope with
`∫ f² ≤ F²` place the common-dual right-hand side in `L²([a,b]; V')` with an explicit
bound. -/
theorem dualRHS_memLp_and_integral_le {a b : ℝ} (hab : a ≤ b)
    (diffusion : V →L[ℝ] V →L[ℝ] ℝ) (convection : V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ)
    (forcing : ℝ → V →L[ℝ] ℝ) (state : V → ℝ) (cB : ℝ) (hcB : 0 ≤ cB)
    (hstate_nonneg : ∀ u, 0 ≤ state u)
    (hdiff : ∀ u φ : V, ‖diffusion u φ‖ ≤ ‖u‖ * ‖φ‖)
    (hconv : ∀ u φ : V, ‖convection u u φ‖ ≤ cB * state u * ‖u‖ * ‖φ‖)
    (U : ℝ → V) (f : ℝ → ℝ) (H R F : ℝ) (hH : 0 ≤ H)
    (hf_nonneg : ∀ t ∈ Icc a b, 0 ≤ f t)
    (hforcing : ∀ t ∈ Icc a b, ∀ φ : V, ‖forcing t φ‖ ≤ f t * ‖φ‖)
    (hforcing_meas : AEStronglyMeasurable forcing (volume.restrict (Icc a b)))
    (hstate : ∀ t ∈ Icc a b, state (U t) ≤ H)
    (henergy : MemLp U 2 (volume.restrict (Icc a b)))
    (henergy_sq : ∫ t in a..b, ‖U t‖ ^ 2 ≤ R ^ 2)
    (hforce : MemLp f 2 (volume.restrict (Icc a b)))
    (hforce_sq : ∫ t in a..b, ‖f t‖ ^ 2 ≤ F ^ 2) :
    MemLp (fun t => dualRHS diffusion convection forcing t (U t)) 2
        (volume.restrict (Icc a b)) ∧
      ∫ t in a..b, ‖dualRHS diffusion convection forcing t (U t)‖ ^ 2 ≤
        2 * (1 + cB * H) ^ 2 * R ^ 2 + 2 * F ^ 2 := by
  set A : ℝ := 1 + cB * H with hAdef
  set D : ℝ → (V →L[ℝ] ℝ) := fun t => dualRHS diffusion convection forcing t (U t)
    with hDdef
  have hA : 0 ≤ A := add_nonneg zero_le_one (mul_nonneg hcB hH)
  have hmajor : MemLp (fun t => A * ‖U t‖ + f t) 2 (volume.restrict (Icc a b)) :=
    (henergy.norm.const_mul A).add hforce
  have hDmeas : AEStronglyMeasurable D (volume.restrict (Icc a b)) :=
    dualRHS_aestronglyMeasurable diffusion convection forcing
      (volume.restrict (Icc a b)) U henergy.1 hforcing_meas
  have hdual : MemLp D 2 (volume.restrict (Icc a b)) := by
    apply MemLp.of_le (f := D) (g := fun t => A * ‖U t‖ + f t) hmajor hDmeas
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hbase := norm_dualRHS_le diffusion convection forcing state cB hcB
      hstate_nonneg hdiff hconv t (U t) (f t) (hf_nonneg t ht) (hforcing t ht)
    have hconv' : cB * state (U t) * ‖U t‖ ≤ cB * H * ‖U t‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hstate t ht) hcB) (norm_nonneg _)
    have hbound : ‖D t‖ ≤ A * ‖U t‖ + f t := by
      calc
        ‖D t‖ ≤ ‖U t‖ + cB * state (U t) * ‖U t‖ + f t := hbase
        _ ≤ ‖U t‖ + cB * H * ‖U t‖ + f t := by linarith
        _ = A * ‖U t‖ + f t := by rw [hAdef]; ring
    have hmajor_nonneg : 0 ≤ A * ‖U t‖ + f t :=
      add_nonneg (mul_nonneg hA (norm_nonneg _)) (hf_nonneg t ht)
    simpa only [Real.norm_eq_abs, abs_of_nonneg hmajor_nonneg] using hbound
  refine ⟨hdual, ?_⟩
  have hdual_sq_int : IntervalIntegrable (fun t => ‖D t‖ ^ 2) volume a b := by
    rw [intervalIntegrable_iff, uIoc_of_le hab]
    exact ((MemLp.norm (f := D) hdual).mono_measure
      (Measure.restrict_mono_set volume Ioc_subset_Icc_self)).integrable_sq
  have henergy_sq_int : IntervalIntegrable (fun t => ‖U t‖ ^ 2) volume a b := by
    rw [intervalIntegrable_iff, uIoc_of_le hab]
    exact (henergy.norm.mono_measure
      (Measure.restrict_mono_set volume Ioc_subset_Icc_self)).integrable_sq
  have hforce_sq_int : IntervalIntegrable (fun t => ‖f t‖ ^ 2) volume a b := by
    rw [intervalIntegrable_iff, uIoc_of_le hab]
    exact (hforce.norm.mono_measure
      (Measure.restrict_mono_set volume Ioc_subset_Icc_self)).integrable_sq
  have hrhs_int : IntervalIntegrable
      (fun t => 2 * A ^ 2 * ‖U t‖ ^ 2 + 2 * ‖f t‖ ^ 2) volume a b :=
    (henergy_sq_int.const_mul (2 * A ^ 2)).add (hforce_sq_int.const_mul 2)
  calc
    ∫ t in a..b, ‖D t‖ ^ 2 ≤
        ∫ t in a..b, 2 * A ^ 2 * ‖U t‖ ^ 2 + 2 * ‖f t‖ ^ 2 := by
      apply intervalIntegral.integral_mono_on hab hdual_sq_int hrhs_int
      intro t ht
      have hsquare := norm_dualRHS_sq_le diffusion convection forcing state cB hcB
        hstate_nonneg hdiff hconv t (U t) (f t) H (hf_nonneg t ht) hH
        (hforcing t ht) (hstate t ht)
      simpa only [hDdef, hAdef, Real.norm_eq_abs, abs_of_nonneg (hf_nonneg t ht)]
        using hsquare
    _ = 2 * A ^ 2 * (∫ t in a..b, ‖U t‖ ^ 2) + 2 * (∫ t in a..b, ‖f t‖ ^ 2) := by
      rw [intervalIntegral.integral_add (henergy_sq_int.const_mul (2 * A ^ 2))
        (hforce_sq_int.const_mul 2), intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
    _ ≤ 2 * A ^ 2 * R ^ 2 + 2 * F ^ 2 :=
      add_le_add
        (mul_le_mul_of_nonneg_left henergy_sq (mul_nonneg (by norm_num) (sq_nonneg A)))
        (mul_le_mul_of_nonneg_left hforce_sq (by norm_num))

end Generic

/-! ## The two forms of the `Ω` weak equation -/

section OpenDomain

variable {Q : BoxIntegral.Box (Fin 2)} (Ω : OpenDomainInBox Q)

/-- The gradient-pairing diffusion form of `Ω`: the box form restricted through the
canonical isometric inclusion. -/
def diffusionForm : OpenDomainH1ZeroSigma Ω →L[ℝ] OpenDomainH1ZeroSigma Ω →L[ℝ] ℝ :=
  (boxGradientDiffusion Q).bilinearCompSame (openDomainEnergyToBox Ω)

/-- The `L4-L2-L4` convection form of `Ω`: the box form restricted through the canonical
isometric inclusion. -/
def convectionForm (E : BoxEnergyL4Realization Q) :
    OpenDomainH1ZeroSigma Ω →L[ℝ]
      OpenDomainH1ZeroSigma Ω →L[ℝ] OpenDomainH1ZeroSigma Ω →L[ℝ] ℝ :=
  (BoxEnergyL4Realization.convectionForm Q E).trilinearCompSame (openDomainEnergyToBox Ω)

@[simp]
theorem diffusionForm_apply (u v : OpenDomainH1ZeroSigma Ω) :
    diffusionForm Ω u v =
      boxGradientDiffusion Q (openDomainEnergyToBox Ω u) (openDomainEnergyToBox Ω v) :=
  rfl

@[simp]
theorem convectionForm_apply (E : BoxEnergyL4Realization Q)
    (u v w : OpenDomainH1ZeroSigma Ω) :
    convectionForm Ω E u v w =
      BoxEnergyL4Realization.convectionForm Q E (openDomainEnergyToBox Ω u)
        (openDomainEnergyToBox Ω v) (openDomainEnergyToBox Ω w) :=
  rfl

@[simp]
theorem norm_openDomainEnergyToBox (u : OpenDomainH1ZeroSigma Ω) :
    ‖openDomainEnergyToBox Ω u‖ = ‖u‖ := rfl

/-- The `Ω` state norm and the box state norm of an included element agree. -/
theorem norm_boxEnergyToState_openDomainEnergyToBox (u : OpenDomainH1ZeroSigma Ω) :
    ‖boxEnergyToState Q (openDomainEnergyToBox Ω u)‖ = ‖openDomainEnergyToState Ω u‖ := by
  rw [← openDomain_embedding_commutes Ω u]
  rfl

/-- **Diffusion estimate on `Ω`**: the gradient pairing is bounded by the two energy norms.
This is the box estimate read through the isometric inclusion. -/
theorem norm_diffusionForm_apply_le (u v : OpenDomainH1ZeroSigma Ω) :
    ‖diffusionForm Ω u v‖ ≤ ‖u‖ * ‖v‖ := by
  have hbox := norm_boxGradientDiffusion_apply_le Q (openDomainEnergyToBox Ω u)
    (openDomainEnergyToBox Ω v)
  simpa only [diffusionForm_apply, norm_openDomainEnergyToBox] using hbox

/-- **Two-dimensional convection estimate on `Ω`** on the diagonal: the Ladyzhenskaya
`L4-L2-L4` bound of the ambient rectangle, read through the isometric inclusion. -/
theorem norm_convectionForm_diagonal_le (L : BoxLadyzhenskayaRealization Q)
    (u φ : OpenDomainH1ZeroSigma Ω) :
    ‖convectionForm Ω L.toBoxEnergyL4Realization u u φ‖ ≤
      (boxLpConvectionBound Q * L.constant) * ‖openDomainEnergyToState Ω u‖ * ‖u‖ *
        ‖φ‖ := by
  have happ := convectionForm_apply Ω L.toBoxEnergyL4Realization u u φ
  have hbox := BoxLadyzhenskayaRealization.convectionForm_diagonal_norm_le Q L
    (openDomainEnergyToBox Ω u) (openDomainEnergyToBox Ω φ)
  rw [norm_boxEnergyToState_openDomainEnergyToBox Ω u] at hbox
  rw [happ]
  exact hbox

/-! ## The common-dual derivative estimate on `Ω` -/

/-- **The two-dimensional common-dual derivative estimate on an open subdomain.**

For an arbitrary state path `U` on `[a, b]` in the energy space of `Ω`, with a uniform
state bound `H`, a square integrable energy path with `∫ ‖U‖² ≤ R²`, and a forcing envelope
`f` with `∫ f² ≤ F²`, the common-dual right-hand side
`φ ↦ -⟪DU, Dφ⟫ - b(U, U, φ) + ⟨forcing, φ⟩` lies in `L²([a,b]; (H¹₀σ(Ω))')` and

`∫ ‖dualRHS t (U t)‖² ≤ 2 (1 + c H)² R² + 2 F²`,
`c = boxLpConvectionBound Q * L.constant`.

Diffusion contributes the `1`, convection the `c H`, and the forcing the `2 F²`. -/
theorem openDomain_dualRHS_memLp_and_integral_le {a b : ℝ} (hab : a ≤ b)
    (L : BoxLadyzhenskayaRealization Q)
    (forcing : ℝ → OpenDomainH1ZeroSigma Ω →L[ℝ] ℝ)
    (U : ℝ → OpenDomainH1ZeroSigma Ω) (f : ℝ → ℝ) (H R F : ℝ) (hH : 0 ≤ H)
    (hf_nonneg : ∀ t ∈ Icc a b, 0 ≤ f t)
    (hforcing : ∀ t ∈ Icc a b, ∀ φ, ‖forcing t φ‖ ≤ f t * ‖φ‖)
    (hforcing_meas : AEStronglyMeasurable forcing (volume.restrict (Icc a b)))
    (hstate : ∀ t ∈ Icc a b, ‖openDomainEnergyToState Ω (U t)‖ ≤ H)
    (henergy : MemLp U 2 (volume.restrict (Icc a b)))
    (henergy_sq : ∫ t in a..b, ‖U t‖ ^ 2 ≤ R ^ 2)
    (hforce : MemLp f 2 (volume.restrict (Icc a b)))
    (hforce_sq : ∫ t in a..b, ‖f t‖ ^ 2 ≤ F ^ 2) :
    MemLp (fun t => dualRHS (diffusionForm Ω) (convectionForm Ω L.toBoxEnergyL4Realization)
        forcing t (U t)) 2 (volume.restrict (Icc a b)) ∧
      ∫ t in a..b, ‖dualRHS (diffusionForm Ω)
          (convectionForm Ω L.toBoxEnergyL4Realization) forcing t (U t)‖ ^ 2 ≤
        2 * (1 + (boxLpConvectionBound Q * L.constant) * H) ^ 2 * R ^ 2 + 2 * F ^ 2 :=
  dualRHS_memLp_and_integral_le hab (diffusionForm Ω)
    (convectionForm Ω L.toBoxEnergyL4Realization) forcing
    (fun u => ‖openDomainEnergyToState Ω u‖) (boxLpConvectionBound Q * L.constant)
    (mul_nonneg (boxLpConvectionBound_pos Q).le L.constant_nonneg)
    (fun _ => norm_nonneg _) (norm_diffusionForm_apply_le Ω)
    (fun u φ => norm_convectionForm_diagonal_le Ω L u φ)
    U f H R F hH hf_nonneg hforcing hforcing_meas hstate henergy henergy_sq hforce
    hforce_sq

/-- **The unforced case.**  Without forcing the common-dual derivative is controlled by the
state and energy bounds alone. -/
theorem openDomain_dualRHS_memLp_and_integral_le_zeroForcing {a b : ℝ} (hab : a ≤ b)
    (L : BoxLadyzhenskayaRealization Q)
    (U : ℝ → OpenDomainH1ZeroSigma Ω) (H R : ℝ) (hH : 0 ≤ H)
    (hstate : ∀ t ∈ Icc a b, ‖openDomainEnergyToState Ω (U t)‖ ≤ H)
    (henergy : MemLp U 2 (volume.restrict (Icc a b)))
    (henergy_sq : ∫ t in a..b, ‖U t‖ ^ 2 ≤ R ^ 2) :
    MemLp (fun t => dualRHS (diffusionForm Ω)
        (convectionForm Ω L.toBoxEnergyL4Realization)
        (fun _ => (0 : OpenDomainH1ZeroSigma Ω →L[ℝ] ℝ)) t (U t)) 2
        (volume.restrict (Icc a b)) ∧
      ∫ t in a..b, ‖dualRHS (diffusionForm Ω)
          (convectionForm Ω L.toBoxEnergyL4Realization)
          (fun _ => (0 : OpenDomainH1ZeroSigma Ω →L[ℝ] ℝ)) t (U t)‖ ^ 2 ≤
        2 * (1 + (boxLpConvectionBound Q * L.constant) * H) ^ 2 * R ^ 2 := by
  have h := openDomain_dualRHS_memLp_and_integral_le Ω hab L
    (fun _ => (0 : OpenDomainH1ZeroSigma Ω →L[ℝ] ℝ)) U (fun _ => (0 : ℝ)) H R 0 hH
    (fun _ _ => le_rfl) (fun _ _ φ => by simp) aestronglyMeasurable_const hstate
    henergy henergy_sq (memLp_const 0) (by simp)
  exact ⟨h.1, by simpa using h.2⟩

end OpenDomain

end OpenDomainDualDerivative

end
