import PDEIdeas.OpenDomainEnergyLimit
import PDEIdeas.OpenDomainTimeCompactness

/-!
# Real interval time and subtype time

Two incompatible descriptions of the time variable meet in this project.

The Galerkin side works with **real** time: trajectories are functions `ℝ → V`, their
bounds are interval integrals `∫ s in a..b, f s`, and the dissipation accumulated up to a
time `t` is `∫ s in a..t, ‖∇u s‖ ^ 2` (this is the shape produced by
`PDEIdeas.OpenDomainUnforcedUniformBounds` and
`PDEIdeas.OpenDomainGalerkinDerivativeIdentity`).

The compactness side works with **subtype** time: `PDEIdeas.OpenDomainTimeCompactness`
takes paths `u : ℕ → Icc a b →ᵇ V` and a finite measure `μI : Measure (Icc a b)` on the
subtype, and measures the energy by `‖toLp 2 μI ℝ (u k)‖`; `PDEIdeas.OpenDomainEnergyLimit`
measures the dissipation by `∫ s in past t, ‖grad (w s)‖ ^ 2 ∂μ` for a set `past t` of
subtype times, the intended instantiation being `past t = Iic t`.

This file supplies the dictionary, once, with no analysis beyond it.

## The measure

`timeMeasure a b` is Lebesgue measure comapped along the inclusion `Icc a b → ℝ`; it is the
measure the subtype carries anyway (`MeasureTheory.Measure.Subtype.measureSpace`), named
here so that it can be handed to the compactness theorems as their `μI` without a local
instance.  It is finite (`timeMeasure_univ`), its mass is the length of the interval, and
the mass of `Iic t` is `t - a` (`timeMeasure_Iic`).

## Main results

* `timeMeasure_apply`, `timeMeasure_preimage`, `timeMeasure_univ`, `timeMeasure_Iic` — the
  measure identities;
* `map_val_timeMeasure`, `map_val_timeMeasure_restrict_Iic` — the two pushforward
  identities, which say that subtype time up to `t` **is** real time on `Icc a t`;
* `integral_timeMeasure_eq_intervalIntegral` — `∫ x : Icc a b, g x ∂timeMeasure = ∫ x in
  a..b, g x`;
* `setIntegral_Iic_timeMeasure` — `∫ x in Iic t, g x ∂timeMeasure = ∫ x in a..t, g x`: the
  restriction to times up to `t`;
* `timePath`, `timeLp` — a path continuous on `Icc a b` read as a bounded continuous
  function of subtype time and as an element of `L²`;
* `norm_sq_eq_intervalIntegral_of_ae`, `norm_timeLp_sq`, `norm_timeLp_le` — the squared
  `L²` norm of an element with an a.e. real-time representative is the interval integral of
  the squared norm, so a real interval energy bound supplies the `energyRadius`
  hypothesis of `PDEIdeas.OpenDomainTimeCompactness` verbatim;
* `setIntegral_Iic_norm_grad_sq_of_ae`, `norm_restrictedGradientMap_sq_of_ae` and their
  path corollaries — the dissipation over the subtype times up to `t`, in both the shape
  used by `OpenDomainEnergyLimit.EnergyLimit` and the operator shape used by
  `OpenDomainEnergyLimit.restrictedGradientMap`, equals the real interval integral
  `∫ s in a..t, ‖grad (g s)‖ ^ 2`.

Everything is stated for a general compact interval `Icc a b`; the intended instantiation
is `a = 0`, `b = T`.

## Scope

Pure measure theory and integration: no Galerkin object, no compactness statement and no
limit passage occurs here, and nothing is assumed about the paths beyond continuity on the
interval.  The identities are unconditional — no integrability hypothesis is needed,
because the inclusion of the interval is a measurable embedding.
-/

open BoundedContinuousFunction MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace OpenDomainIntervalMeasureBridge

/-! ## The time measure of a compact interval -/

section Measure

variable (a b : ℝ)

/-- **Subtype time.**  Lebesgue measure comapped along the inclusion `Icc a b → ℝ`: the
measure carried by the time subtype, named so that it can be supplied as the `μI` of
`PDEIdeas.OpenDomainTimeCompactness`. -/
def timeMeasure : Measure (Icc a b) :=
  Measure.comap (Subtype.val : Icc a b → ℝ) volume

theorem timeMeasure_eq :
    timeMeasure a b = Measure.comap (Subtype.val : Icc a b → ℝ) volume := rfl

variable {a b}

theorem measurableEmbedding_val :
    MeasurableEmbedding (Subtype.val : Icc a b → ℝ) :=
  MeasurableEmbedding.subtype_coe measurableSet_Icc

/-- The mass of a set of subtype times is the Lebesgue measure of its image. -/
theorem timeMeasure_apply (A : Set (Icc a b)) :
    timeMeasure a b A = volume ((Subtype.val : Icc a b → ℝ) '' A) :=
  measurableEmbedding_val.comap_apply volume A

theorem image_val_preimage (B : Set ℝ) :
    (Subtype.val : Icc a b → ℝ) '' ((Subtype.val : Icc a b → ℝ) ⁻¹' B) = B ∩ Icc a b := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, x.2⟩
  · rintro ⟨hyB, hyI⟩
    exact ⟨⟨y, hyI⟩, hyB, rfl⟩

/-- The mass of the subtype times lying in a real set `B` is the length of `B ∩ [a,b]`. -/
theorem timeMeasure_preimage (B : Set ℝ) :
    timeMeasure a b ((Subtype.val : Icc a b → ℝ) ⁻¹' B) = volume (B ∩ Icc a b) := by
  rw [timeMeasure_apply, image_val_preimage]

@[simp]
theorem timeMeasure_univ : timeMeasure a b univ = ENNReal.ofReal (b - a) := by
  rw [timeMeasure_apply, image_univ, Subtype.range_coe, Real.volume_Icc]

instance isFiniteMeasure_timeMeasure : IsFiniteMeasure (timeMeasure a b) :=
  ⟨by rw [timeMeasure_univ]; exact ENNReal.ofReal_lt_top⟩

/-- Subtype times up to `t` are exactly the times of the real ray `Iic t`. -/
theorem Iic_eq_preimage_Iic (t : Icc a b) :
    (Iic t : Set (Icc a b)) = (Subtype.val : Icc a b → ℝ) ⁻¹' Iic (t : ℝ) := rfl

theorem Iic_inter_Icc (t : Icc a b) :
    Iic (t : ℝ) ∩ Icc a b = Icc a (t : ℝ) := by
  ext y
  simp only [mem_inter_iff, mem_Iic, mem_Icc]
  constructor
  · rintro ⟨hyt, hay, -⟩
    exact ⟨hay, hyt⟩
  · rintro ⟨hay, hyt⟩
    exact ⟨hyt, hay, hyt.trans t.2.2⟩

@[simp]
theorem timeMeasure_Iic (t : Icc a b) :
    timeMeasure a b (Iic t) = ENNReal.ofReal ((t : ℝ) - a) := by
  rw [Iic_eq_preimage_Iic, timeMeasure_preimage, Iic_inter_Icc, Real.volume_Icc]

/-- **Subtype time pushes forward to real time on the interval.** -/
theorem map_val_timeMeasure :
    Measure.map (Subtype.val : Icc a b → ℝ) (timeMeasure a b) = volume.restrict (Icc a b) := by
  rw [timeMeasure_eq, measurableEmbedding_val.map_comap, Subtype.range_coe]

/-- **Subtype time up to `t` pushes forward to real time on `Icc a t`.**  This is the
measure identity behind every "dissipation up to `t`" statement below. -/
theorem map_val_timeMeasure_restrict_Iic (t : Icc a b) :
    Measure.map (Subtype.val : Icc a b → ℝ) ((timeMeasure a b).restrict (Iic t)) =
      volume.restrict (Icc a (t : ℝ)) := by
  rw [Iic_eq_preimage_Iic, ← measurableEmbedding_val.restrict_map, map_val_timeMeasure,
    Measure.restrict_restrict measurableSet_Iic, Iic_inter_Icc]

end Measure

/-! ## The integral identities -/

section Integral

variable {a b : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Integration in subtype time is integration over the interval. -/
theorem integral_timeMeasure (g : ℝ → E) :
    ∫ x : Icc a b, g (x : ℝ) ∂(timeMeasure a b) = ∫ x in Icc a b, g x :=
  integral_subtype_comap measurableSet_Icc g

/-- **Subtype time against real interval integrals.** -/
theorem integral_timeMeasure_eq_intervalIntegral (hab : a ≤ b) (g : ℝ → E) :
    ∫ x : Icc a b, g (x : ℝ) ∂(timeMeasure a b) = ∫ x in a..b, g x := by
  rw [integral_timeMeasure, intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]

/-- Integration over the subtype times lying in a real set `B`. -/
theorem setIntegral_preimage_timeMeasure {B : Set ℝ} (hB : MeasurableSet B) (g : ℝ → E) :
    ∫ x in ((Subtype.val : Icc a b → ℝ) ⁻¹' B), g (x : ℝ) ∂(timeMeasure a b) =
      ∫ y in B ∩ Icc a b, g y := by
  have hmap := measurableEmbedding_val.setIntegral_map (μ := timeMeasure a b) g B
  rw [map_val_timeMeasure] at hmap
  rw [← hmap, Measure.restrict_restrict hB]

/-- **The dissipation window.**  Integration over the subtype times up to `t` is the real
interval integral from `a` to `t`. -/
theorem setIntegral_Iic_timeMeasure (t : Icc a b) (g : ℝ → E) :
    ∫ x in Iic t, g (x : ℝ) ∂(timeMeasure a b) = ∫ x in a..(t : ℝ), g x := by
  rw [Iic_eq_preimage_Iic, setIntegral_preimage_timeMeasure measurableSet_Iic, Iic_inter_Icc,
    intervalIntegral.integral_of_le t.2.1, integral_Icc_eq_integral_Ioc]

end Integral

/-! ## Paths of real time as `L²` elements of subtype time -/

section Path

variable {a b : ℝ} {V Grad : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup Grad] [InnerProductSpace ℝ Grad]

/-- A path continuous on `Icc a b` as a bounded continuous function of subtype time — the
shape `PDEIdeas.OpenDomainTimeCompactness` consumes. -/
def timePath (g : ℝ → V) (hg : ContinuousOn g (Icc a b)) : Icc a b →ᵇ V :=
  BoundedContinuousFunction.mkOfCompact ⟨(Icc a b).restrict g, hg.restrict⟩

omit [InnerProductSpace ℝ V] in
@[simp]
theorem timePath_apply (g : ℝ → V) (hg : ContinuousOn g (Icc a b)) (t : Icc a b) :
    timePath g hg t = g (t : ℝ) := rfl

/-- The `L²`-in-time element of such a path. -/
def timeLp (g : ℝ → V) (hg : ContinuousOn g (Icc a b)) : Lp V 2 (timeMeasure a b) :=
  BoundedContinuousFunction.toLp (2 : ℝ≥0∞) (timeMeasure a b) ℝ (timePath g hg)

theorem timeLp_eq_toLp (g : ℝ → V) (hg : ContinuousOn g (Icc a b)) :
    timeLp g hg =
      BoundedContinuousFunction.toLp (2 : ℝ≥0∞) (timeMeasure a b) ℝ (timePath g hg) := rfl

theorem coeFn_timeLp (g : ℝ → V) (hg : ContinuousOn g (Icc a b)) :
    (timeLp g hg : Icc a b → V) =ᵐ[timeMeasure a b] fun t => g (t : ℝ) :=
  BoundedContinuousFunction.coeFn_toLp (2 : ℝ≥0∞) (timeMeasure a b) ℝ (timePath g hg)

/-- **The `L²` norm of any element represented by a path of real time.**  Stated for an
arbitrary `L²` element with an a.e. real-time representative, because the elements produced
by the compactness machinery — strong limits — are given only up to null sets. -/
theorem norm_sq_eq_intervalIntegral_of_ae (hab : a ≤ b) (w : Lp V 2 (timeMeasure a b))
    (g : ℝ → V) (hw : (w : Icc a b → V) =ᵐ[timeMeasure a b] fun s => g (s : ℝ)) :
    ‖w‖ ^ 2 = ∫ x in a..b, ‖g x‖ ^ 2 := by
  have hae : ∫ x : Icc a b, ‖(w : Icc a b → V) x‖ ^ 2 ∂(timeMeasure a b) =
      ∫ x : Icc a b, ‖g (x : ℝ)‖ ^ 2 ∂(timeMeasure a b) := by
    refine integral_congr_ae ?_
    filter_upwards [hw] with x hx
    rw [hx]
  rw [OpenDomainEnergyLimit.norm_sq_eq_integral_norm_sq, hae]
  exact integral_timeMeasure_eq_intervalIntegral hab fun y => ‖g y‖ ^ 2

/-- **The `L²` energy of a path is its real interval energy.** -/
theorem norm_timeLp_sq (hab : a ≤ b) (g : ℝ → V) (hg : ContinuousOn g (Icc a b)) :
    ‖timeLp g hg‖ ^ 2 = ∫ x in a..b, ‖g x‖ ^ 2 :=
  norm_sq_eq_intervalIntegral_of_ae hab (timeLp g hg) g (coeFn_timeLp g hg)

/-- **A real interval energy bound supplies the `energyRadius` hypothesis.**  This is the
form `PDEIdeas.OpenDomainTimeCompactness` asks for. -/
theorem norm_timeLp_le (hab : a ≤ b) (g : ℝ → V) (hg : ContinuousOn g (Icc a b))
    {R : ℝ} (hR : 0 ≤ R) (h : ∫ x in a..b, ‖g x‖ ^ 2 ≤ R ^ 2) :
    ‖timeLp g hg‖ ≤ R := by
  have hsq := norm_timeLp_sq hab g hg
  nlinarith [norm_nonneg (timeLp g hg)]

/-- **The dissipation up to `t` of any element represented by a path of real time**, in the
integral shape of `OpenDomainEnergyLimit.EnergyLimit` with `past t = Iic t`. -/
theorem setIntegral_Iic_norm_grad_sq_of_ae (grad : V →L[ℝ] Grad)
    (w : Lp V 2 (timeMeasure a b)) (g : ℝ → V)
    (hw : (w : Icc a b → V) =ᵐ[timeMeasure a b] fun s => g (s : ℝ)) (t : Icc a b) :
    ∫ s in Iic t, ‖grad ((w : Icc a b → V) s)‖ ^ 2 ∂(timeMeasure a b) =
      ∫ s in a..(t : ℝ), ‖grad (g s)‖ ^ 2 := by
  have hae : ∫ s in Iic t, ‖grad ((w : Icc a b → V) s)‖ ^ 2 ∂(timeMeasure a b) =
      ∫ s in Iic t, ‖grad (g (s : ℝ))‖ ^ 2 ∂(timeMeasure a b) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae hw] with s hs
    rw [hs]
  rw [hae]
  exact setIntegral_Iic_timeMeasure t fun y => ‖grad (g y)‖ ^ 2

/-- **The dissipation of a path over the subtype times up to `t`.** -/
theorem setIntegral_Iic_norm_grad_timeLp_sq (grad : V →L[ℝ] Grad) (g : ℝ → V)
    (hg : ContinuousOn g (Icc a b)) (t : Icc a b) :
    ∫ s in Iic t, ‖grad ((timeLp g hg : Icc a b → V) s)‖ ^ 2 ∂(timeMeasure a b) =
      ∫ s in a..(t : ℝ), ‖grad (g s)‖ ^ 2 :=
  setIntegral_Iic_norm_grad_sq_of_ae grad (timeLp g hg) g (coeFn_timeLp g hg) t

/-- **The same dissipation in operator shape.**  `OpenDomainEnergyLimit` accumulates the
dissipation as the squared norm of `restrictedGradientMap`; on a path of real time that
squared norm is the real interval integral up to `t`. -/
theorem norm_restrictedGradientMap_sq_of_ae (grad : V →L[ℝ] Grad)
    (w : Lp V 2 (timeMeasure a b)) (g : ℝ → V)
    (hw : (w : Icc a b → V) =ᵐ[timeMeasure a b] fun s => g (s : ℝ)) (t : Icc a b) :
    ‖OpenDomainEnergyLimit.restrictedGradientMap grad (Iic t) w‖ ^ 2 =
      ∫ s in a..(t : ℝ), ‖grad (g s)‖ ^ 2 := by
  rw [OpenDomainEnergyLimit.restrictedGradientMap_norm_sq]
  exact setIntegral_Iic_norm_grad_sq_of_ae grad w g hw t

/-- The same for the `L²` element of a path of real time. -/
theorem norm_restrictedGradientMap_timeLp_sq (grad : V →L[ℝ] Grad) (g : ℝ → V)
    (hg : ContinuousOn g (Icc a b)) (t : Icc a b) :
    ‖OpenDomainEnergyLimit.restrictedGradientMap grad (Iic t) (timeLp g hg)‖ ^ 2 =
      ∫ s in a..(t : ℝ), ‖grad (g s)‖ ^ 2 :=
  norm_restrictedGradientMap_sq_of_ae grad (timeLp g hg) g (coeFn_timeLp g hg) t

end Path

end OpenDomainIntervalMeasureBridge

end
