import PDEIdeas.LeraySpectralWeakContinuity
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Passing the energy identity to the Galerkin limit

The finite Galerkin levels satisfy an exact energy identity.  This file turns
that identity, together with the compactness data already extracted by
`PDEIdeas.LeraySpectralWeakCompactness` and
`PDEIdeas.LeraySpectralWeakContinuity`, into the two energy-side facts a
Leray--Hopf solution record needs: the limiting energy **inequality**, and a
weakly continuous pivot-space representative attaining the initial datum.

## Why it is stated generically

Everything here is phrased over an abstract
`G : LeraySpectralCompactFamily (I := I) (V := V) (H := H) (μ := μ)` and a
`S : G.StrongWeakPathSubsequence`, with the finite-level identity taken as an
explicit hypothesis carrying a *level-dependent* right-hand side `c t k`.  That
is what lets one statement serve both families:

* unforced — `c t k = ‖u₀‖ ^ 2` and `C t = ‖u₀‖ ^ 2`;
* forced — `c t k` the initial energy plus twice the forcing work of level `k`
  up to `t`, and `C t` its limit.

It is also why the file needs none of the `OpenDomain*` or `Box*` modules: the
open-domain and rectangle families are both instances of
`LeraySpectralCompactFamily`, so each applies these results rather than
repeating them.

## The two analytic ideas

The energy inequality cannot be obtained by bounding the state term and the
dissipation term separately — summing two lower bounds is not valid.  Instead
the state at time `t` and `√2` times the accumulated dissipation are packed
into a single vector of `WithLp 2 (H × K)`, whose squared norm is exactly
`‖u(t)‖² + 2 ∫ ‖∇u‖²` (`norm_sqrtTwo_prod_sq`); weak lower semicontinuity is
then applied once, to the pair (`norm_sq_le_of_weak_tendsto`).

The dissipation is kept inside a Hilbert space rather than handled by Fatou:
`restrictedGradientMap` is the continuous linear map `w ↦ (∇w)|_A`, and
`restrictedGradientMap_norm_sq` identifies its squared norm with
`∫ s in A, ‖∇ w s‖² ∂μ`.  This mirrors the existing rectangle argument and
keeps the whole passage inside weak Hilbert-space convergence.

## Main results

* `norm_sq_le_of_weak_tendsto` — weak limits inherit a convergent squared-norm
  majorant.  Generic; the sequence-dependent majorant is what admits forcing.
* `norm_sq_add_dissipation_le` — the limiting energy inequality in abstract
  form, for any continuous linear image `D` of the energy path.
* `restrictedGradientMap` / `restrictedGradientMap_norm_sq` — the dissipation
  over a set of times as a Hilbert-space norm.
* `path_eq_of_statePath_tendsto` — the representative attains the initial value.
* `EnergyLimit` / `energyLimitOfFiniteLevel` — the two packaged together, built
  from the explicit finite-level hypotheses.

## Scope

No Leray--Hopf solution is constructed here, for any domain.  This file
supplies the energy-side fields only; the weak equation, the identification of
the state and energy limits, and the construction of the compact family itself
are all elsewhere and are **not** claimed.  In particular nothing here asserts
an open-domain existence theorem: applying `energyLimitOfFiniteLevel` to the
open-domain family still requires that family, its finite energy identity, and
a separate weak-equation limit passage.
-/

open BoundedContinuousFunction Filter Function InnerProductSpace MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace Topology

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace OpenDomainEnergyLimit

/-! ## Generic Hilbert-space facts -/

section Hilbert

/-- The squared `L²` norm is the integral of the squared pointwise norm. -/
theorem norm_sq_eq_integral_norm_sq {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ν : Measure α}
    (f : Lp E (2 : ℝ≥0∞) ν) :
    ‖f‖ ^ 2 = ∫ a, ‖f a‖ ^ 2 ∂ν := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  exact integral_congr_ae
    (Filter.Eventually.of_forall fun a => real_inner_self_eq_norm_sq _)

/-- **Weak limits inherit a convergent squared-norm majorant.**  If `x j ⇀ ell`
weakly and `‖x j‖² ≤ c j` with `c j → C`, then `‖ell‖² ≤ C`.  Stated with a
sequence-dependent majorant so that a forcing term on the right-hand side is
allowed. -/
theorem norm_sq_le_of_weak_tendsto {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {x : ℕ → E} {ell : E}
    (hweak : ∀ z : E, Tendsto (fun j => ⟪x j, z⟫_ℝ) atTop (𝓝 ⟪ell, z⟫_ℝ))
    {c : ℕ → ℝ} {C : ℝ}
    (hc : ∀ j, ‖x j‖ ^ 2 ≤ c j) (hC : Tendsto c atTop (𝓝 C)) :
    ‖ell‖ ^ 2 ≤ C := by
  have hcnonneg : ∀ j, 0 ≤ c j := fun j => le_trans (sq_nonneg _) (hc j)
  have hCnonneg : 0 ≤ C :=
    ge_of_tendsto hC (Filter.Eventually.of_forall hcnonneg)
  have hbound : ∀ j, ⟪x j, ell⟫_ℝ ≤ Real.sqrt (c j) * ‖ell‖ := by
    intro j
    refine le_trans (real_inner_le_norm _ _) ?_
    have hxj : ‖x j‖ ≤ Real.sqrt (c j) := by
      rw [show ‖x j‖ = Real.sqrt (‖x j‖ ^ 2) by
        rw [Real.sqrt_sq (norm_nonneg _)]]
      exact Real.sqrt_le_sqrt (hc j)
    exact mul_le_mul_of_nonneg_right hxj (norm_nonneg _)
  have hlim : Tendsto (fun j => Real.sqrt (c j) * ‖ell‖) atTop
      (𝓝 (Real.sqrt C * ‖ell‖)) :=
    (hC.sqrt).mul tendsto_const_nhds
  have hkey : ‖ell‖ ^ 2 ≤ Real.sqrt C * ‖ell‖ := by
    rw [← real_inner_self_eq_norm_sq]
    exact le_of_tendsto_of_tendsto' (hweak ell) hlim hbound
  have hsq : Real.sqrt C ^ 2 = C := Real.sq_sqrt hCnonneg
  nlinarith [Real.sqrt_nonneg C, norm_nonneg ell, hkey, hsq]

/-- The squared `L²`-product norm of a state paired with `√2` times a
dissipation vector. -/
theorem norm_sqrtTwo_prod_sq {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (x : E) (y : F) :
    ‖(WithLp.toLp 2 (x, Real.sqrt 2 • y) : WithLp 2 (E × F))‖ ^ 2 =
      ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h2 : ‖Real.sqrt 2 • y‖ ^ 2 = 2 * ‖y‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2), mul_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [WithLp.prod_norm_sq_eq_of_L2, ← h2]
  simp

end Hilbert

/-! ## The limit passage -/

section Limit

variable {I V H : Type*}
    [PseudoMetricSpace I] [MeasurableSpace I] [BorelSpace I]
    [SecondCountableTopology I]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {μ : Measure I} [IsFiniteMeasure μ]
    {G : LeraySpectralCompactFamily (I := I) (V := V) (H := H) (μ := μ)}
    {S : G.StrongWeakPathSubsequence}

/-- **The limiting energy inequality, in abstract form.**

`D` is any continuous linear image of the energy path — in the application it
is the gradient restricted to the times before `t`, so `‖D w‖²` is the
dissipation accumulated up to `t`.  The hypothesis `hfinite` is the finite
Galerkin energy identity, with a level-dependent right-hand side `c k`; the
unforced family takes `c k = ‖u₀‖²` constant, the forced family takes the
initial energy plus the forcing work at level `k`. -/
theorem norm_sq_add_dissipation_le
    (R : G.WeaklyContinuousStateRepresentative S)
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (D : Lp V (2 : ℝ≥0∞) μ →L[ℝ] K) (t : I)
    {c : ℕ → ℝ} {C : ℝ}
    (hfinite : ∀ k : ℕ,
      ‖G.statePath k t‖ ^ 2 + 2 * ‖D (G.energyLp k)‖ ^ 2 ≤ c k)
    (hC : Tendsto c atTop (𝓝 C)) :
    ‖R.path t‖ ^ 2 + 2 * ‖D S.energyLimit‖ ^ 2 ≤ C := by
  obtain ⟨rho, hrho, hweakState⟩ := R.pointwise_weak_subsequence t
  set idx : ℕ → ℕ := fun j => S.subseq.idx (rho j) with hidx
  have hidxTop : Tendsto idx atTop atTop :=
    (S.subseq.strictMono_idx.tendsto_atTop).comp hrho.tendsto_atTop
  set x : ℕ → WithLp 2 (H × K) := fun j =>
    WithLp.toLp 2 (G.statePath (idx j) t, Real.sqrt 2 • D (G.energyLp (idx j)))
    with hx
  set ell : WithLp 2 (H × K) :=
    WithLp.toLp 2 (R.path t, Real.sqrt 2 • D S.energyLimit) with hell
  have hweak : ∀ z : WithLp 2 (H × K),
      Tendsto (fun j => ⟪x j, z⟫_ℝ) atTop (𝓝 ⟪ell, z⟫_ℝ) := by
    intro z
    have hfst : Tendsto
        (fun j => ⟪G.statePath (idx j) t, (WithLp.ofLp z).fst⟫_ℝ) atTop
        (𝓝 ⟪R.path t, (WithLp.ofLp z).fst⟫_ℝ) := hweakState _
    have hcompl : Tendsto
        (fun k => ⟪(WithLp.ofLp z).snd, D (G.energyLp (S.subseq.idx k))⟫_ℝ)
        atTop (𝓝 ⟪(WithLp.ofLp z).snd, D S.energyLimit⟫_ℝ) :=
      S.toStrongWeakSubsequence.energy_clm_tendsto
        ((innerSL ℝ (WithLp.ofLp z).snd).comp D)
    have hsnd : Tendsto
        (fun j => ⟪Real.sqrt 2 • D (G.energyLp (idx j)),
          (WithLp.ofLp z).snd⟫_ℝ) atTop
        (𝓝 ⟪Real.sqrt 2 • D S.energyLimit, (WithLp.ofLp z).snd⟫_ℝ) := by
      simp only [real_inner_smul_left]
      refine tendsto_const_nhds.mul ?_
      have := hcompl.comp hrho.tendsto_atTop
      simpa only [Function.comp_def, real_inner_comm] using this
    simp only [hx, hell, WithLp.prod_inner_apply]
    exact hfst.add hsnd
  have hcbound : ∀ j, ‖x j‖ ^ 2 ≤ c (idx j) := by
    intro j
    rw [hx, norm_sqrtTwo_prod_sq]
    exact hfinite (idx j)
  have hClim : Tendsto (fun j => c (idx j)) atTop (𝓝 C) := hC.comp hidxTop
  have hfinal := norm_sq_le_of_weak_tendsto hweak hcbound hClim
  rwa [hell, norm_sqrtTwo_prod_sq] at hfinal

omit [CompleteSpace V] in
/-- **The weakly continuous representative attains a prescribed initial
value.**  The only hypothesis is that the finite Galerkin states at time `t`
converge to `u₀` in the pivot space. -/
theorem path_eq_of_statePath_tendsto
    (R : G.WeaklyContinuousStateRepresentative S) (t : I) (u₀ : H)
    (h : Tendsto (fun k => G.statePath k t) atTop (𝓝 u₀)) :
    R.path t = u₀ :=
  R.eq_of_statePath_tendsto id tendsto_id t u₀
    (h.comp (S.subseq.strictMono_idx.tendsto_atTop))

/-! ## The dissipation as a time integral -/

section Dissipation

variable {Grad : Type*} [NormedAddCommGroup Grad] [InnerProductSpace ℝ Grad]

/-- The energy path's gradient, restricted to a set of times.  Its squared norm
is the dissipation accumulated over that set. -/
def restrictedGradientMap (grad : V →L[ℝ] Grad) (A : Set I) :
    Lp V (2 : ℝ≥0∞) μ →L[ℝ] Lp Grad (2 : ℝ≥0∞) (μ.restrict A) :=
  (MeasureTheory.LpToLpRestrictCLM I Grad ℝ μ 2 A).comp (grad.compLpL 2 μ)

omit [PseudoMetricSpace I] [BorelSpace I] [SecondCountableTopology I]
  [CompleteSpace V] [IsFiniteMeasure μ] in
theorem restrictedGradientMap_ae (grad : V →L[ℝ] Grad) (A : Set I)
    (w : Lp V (2 : ℝ≥0∞) μ) :
    (restrictedGradientMap grad A w : I → Grad) =ᵐ[μ.restrict A]
      fun s => grad (w s) := by
  refine (MeasureTheory.LpToLpRestrictCLM_coeFn ℝ A
    ((grad.compLpL 2 μ) w)).trans ?_
  exact ae_restrict_of_ae (grad.coeFn_compLpL w)

omit [PseudoMetricSpace I] [BorelSpace I] [SecondCountableTopology I]
  [CompleteSpace V] [IsFiniteMeasure μ] in
/-- **The squared restricted-gradient norm is the accumulated dissipation.** -/
theorem restrictedGradientMap_norm_sq (grad : V →L[ℝ] Grad) (A : Set I)
    (w : Lp V (2 : ℝ≥0∞) μ) :
    ‖restrictedGradientMap grad A w‖ ^ 2 =
      ∫ s in A, ‖grad (w s)‖ ^ 2 ∂μ := by
  rw [norm_sq_eq_integral_norm_sq]
  refine integral_congr_ae ?_
  filter_upwards [restrictedGradientMap_ae grad A w] with s hs
  rw [hs]

end Dissipation

/-! ## The packaged conclusion -/

section Package

variable {Grad : Type*} [NormedAddCommGroup Grad] [InnerProductSpace ℝ Grad]

/-- **The energy-side data of a Galerkin limit.**

This is exactly what a Leray--Hopf solution record needs from the energy
argument: a pivot-space path that is bounded, weakly continuous, a.e. equal to
the strong `L²` limit, attains the initial datum at `t₀`, and satisfies the
energy inequality with accumulated dissipation over `past t`.

`past` is kept abstract rather than fixed to `Set.Iic t` so that the statement
does not require an order on the time type; the intended instantiation on an
interval is `past t = Set.Iic t`. -/
structure EnergyLimit
    (G : LeraySpectralCompactFamily (I := I) (V := V) (H := H) (μ := μ))
    (S : G.StrongWeakPathSubsequence) (grad : V →L[ℝ] Grad)
    (past : I → Set I) (t₀ : I) (u₀ : H) (C : I → ℝ) where
  /-- The pivot-space representative. -/
  path : I → H
  /-- It obeys the family's uniform state bound. -/
  norm_le : ∀ t, ‖path t‖ ≤ G.stateRadius
  /-- It is weakly continuous in time. -/
  inner_continuous : ∀ y : H, Continuous fun t => ⟪path t, y⟫_ℝ
  /-- It represents the strong `L²` state limit. -/
  path_ae_eq_stateLimit : path =ᵐ[μ] (S.stateLimit : I → H)
  /-- It attains the prescribed initial value. -/
  initial : path t₀ = u₀
  /-- The limiting energy inequality. -/
  energy_inequality : ∀ t : I,
    ‖path t‖ ^ 2 + 2 * ∫ s in past t, ‖grad (S.energyLimit s)‖ ^ 2 ∂μ ≤ C t

/-- **Assembling the energy limit from explicit finite-level hypotheses.**

The two inputs are exactly the finite Galerkin facts:

* `hfinite` — the finite energy identity at every level `k` and time `t`, with a
  level-dependent right-hand side `c t k`;
* `hC` — that right-hand side converges as the level grows;
* `hinit` — the finite states at `t₀` converge to the initial datum.

The unforced family instantiates `c t k = ‖u₀‖ ^ 2` with `C t = ‖u₀‖ ^ 2`; the
forced family instantiates `c t k` as the initial energy plus twice the forcing
work of level `k` up to `t`, with `C t` its limit. -/
def energyLimitOfFiniteLevel
    {G : LeraySpectralCompactFamily (I := I) (V := V) (H := H) (μ := μ)}
    {S : G.StrongWeakPathSubsequence}
    (R : G.WeaklyContinuousStateRepresentative S)
    (grad : V →L[ℝ] Grad) (past : I → Set I) (t₀ : I) (u₀ : H)
    (c : I → ℕ → ℝ) (C : I → ℝ)
    (hfinite : ∀ (t : I) (k : ℕ),
      ‖G.statePath k t‖ ^ 2 +
        2 * ∫ s in past t, ‖grad (G.energyLp k s)‖ ^ 2 ∂μ ≤ c t k)
    (hC : ∀ t : I, Tendsto (c t) atTop (𝓝 (C t)))
    (hinit : Tendsto (fun k => G.statePath k t₀) atTop (𝓝 u₀)) :
    EnergyLimit G S grad past t₀ u₀ C where
  path := R.path
  norm_le := R.norm_le
  inner_continuous := R.inner_continuous
  path_ae_eq_stateLimit := R.path_ae_eq_stateLimit
  initial := path_eq_of_statePath_tendsto R t₀ u₀ hinit
  energy_inequality := by
    intro t
    have hrewrite := norm_sq_add_dissipation_le R
      (restrictedGradientMap grad (past t)) t
      (c := c t) (C := C t)
      (fun k => by
        rw [restrictedGradientMap_norm_sq]
        exact hfinite t k)
      (hC t)
    rwa [restrictedGradientMap_norm_sq] at hrewrite

end Package

end Limit

end OpenDomainEnergyLimit
