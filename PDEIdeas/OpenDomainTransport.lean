import PDEIdeas.TransportIBP
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Localization of the box transport identities to `Ω`-supported fields

The transport identities of `PDEIdeas.TransportIBP` are stated on a closed box and
require the fields to vanish on every face hyperplane of that box.  This file
provides the two ingredients needed to transfer them to an arbitrary measurable
domain `Ω` without leaving the box divergence theorem:

* measure-theoretic localization: a function vanishing outside a set `Ω` has the
  same integral over any measurable superset of `Ω` (in particular over a box) as
  over `Ω` itself, and integrability over `Ω` upgrades to integrability over the
  superset;
* support bookkeeping: a field whose closed support lies inside `Ω ⊆ interior (Box.Icc I)`
  vanishes on every face hyperplane of `I`, and a differentiable field has vanishing
  derivative off its closed support, so divergence-freeness on `Ω` propagates to the
  whole box.

Combining the two transfers the scalar cancellation, the vector integration by parts,
the skew-symmetry identity and the diagonal cancellation of `PDEIdeas.TransportIBP`
from a box to `Ω`.

**Scope.** No divergence theorem for a general smooth domain is asserted or used.  The
only integration by parts invoked is the box identity already proved in
`PDEIdeas.TransportIBP`; `Ω` enters exclusively through hypotheses of the form "the
field vanishes outside `Ω`" together with `Ω ⊆ interior (Box.Icc I)`, so no boundary
regularity of `Ω` is ever needed and no boundary term over `∂Ω` is ever claimed.
All integrability and support hypotheses are stated explicitly.
-/

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

namespace OpenDomainTransport

/-! ## Localization of integrals and of integrability -/

section Localize

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Localization of a set integral.**  If `f` vanishes outside `Ω` and `Ω` is contained
in a measurable set `s`, then the integral of `f` over `s` equals the integral of `f`
over `Ω`.  No integrability hypothesis is needed: if `f` is not integrable, both sides
are `0` by convention. -/
theorem setIntegral_localize {f : X → E} {Ω s : Set X} (hs : MeasurableSet s)
    (hsub : Ω ⊆ s) (hf : ∀ x, x ∉ Ω → f x = 0) :
    ∫ x in s, f x ∂μ = ∫ x in Ω, f x ∂μ :=
  setIntegral_eq_of_subset_of_forall_diff_eq_zero hs hsub fun _ hx => hf _ hx.2

/-- **Localization against the ambient space.** -/
theorem integral_localize {f : X → E} {Ω : Set X} (hf : ∀ x, x ∉ Ω → f x = 0) :
    ∫ x, f x ∂μ = ∫ x in Ω, f x ∂μ :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero hf).symm

omit [NormedSpace ℝ E] in
/-- **Localization of integrability.**  A function which is integrable on `Ω` and vanishes
outside `Ω` is integrable on every measurable set. -/
theorem integrableOn_localize {f : X → E} {Ω s : Set X} (hΩ : MeasurableSet Ω)
    (hs : MeasurableSet s) (hf : ∀ x, x ∉ Ω → f x = 0) (hint : IntegrableOn f Ω μ) :
    IntegrableOn f s μ := by
  have hdiff : IntegrableOn f (s \ Ω) μ :=
    integrableOn_zero.congr_fun (fun x hx => (hf x hx.2).symm) (hs.diff hΩ)
  have hinter : IntegrableOn f (s ∩ Ω) μ := hint.mono_set inter_subset_right
  have hunion : IntegrableOn f (s ∩ Ω ∪ s \ Ω) μ := hinter.union hdiff
  rwa [inter_union_diff] at hunion

/-- Two measurable windows containing `Ω` see the same integral. -/
theorem setIntegral_localize_congr {f : X → E} {Ω s t : Set X} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hΩs : Ω ⊆ s) (hΩt : Ω ⊆ t) (hf : ∀ x, x ∉ Ω → f x = 0) :
    ∫ x in s, f x ∂μ = ∫ x in t, f x ∂μ := by
  rw [setIntegral_localize hs hΩs hf, setIntegral_localize ht hΩt hf]

end Localize

/-! ## Boxes, faces and supports -/

section BoxSupport

variable {n : ℕ}

/-- `Box.Icc I` is measurable. -/
theorem measurableSet_boxIcc (I : BoxIntegral.Box (Fin (n + 1))) :
    MeasurableSet (BoxIntegral.Box.Icc I) := by
  rw [BoxIntegral.Box.Icc_def]
  exact measurableSet_Icc

/-- Coordinates of a point of the open box are strictly between the box bounds. -/
theorem mem_Ioo_of_mem_interior_boxIcc {I : BoxIntegral.Box (Fin (n + 1))}
    {p : Fin (n + 1) → ℝ} (hp : p ∈ interior (BoxIntegral.Box.Icc I)) (i : Fin (n + 1)) :
    I.lower i < p i ∧ p i < I.upper i := by
  rw [BoxIntegral.Box.Icc_def, ← Set.pi_univ_Icc,
    interior_pi_set (@Set.finite_univ (Fin (n + 1)) _)] at hp
  have h : p i ∈ interior (Set.Icc (I.lower i) (I.upper i)) := hp i (Set.mem_univ i)
  rw [interior_Icc] at h
  exact ⟨h.1, h.2⟩

/-- A point whose coordinates are strictly between the box bounds lies in the open box. -/
theorem mem_interior_boxIcc {I : BoxIntegral.Box (Fin (n + 1))} {p : Fin (n + 1) → ℝ}
    (hp : ∀ i, I.lower i < p i ∧ p i < I.upper i) :
    p ∈ interior (BoxIntegral.Box.Icc I) := by
  rw [BoxIntegral.Box.Icc_def, ← Set.pi_univ_Icc,
    interior_pi_set (@Set.finite_univ (Fin (n + 1)) _)]
  intro i _
  show p i ∈ interior (Set.Icc (I.lower i) (I.upper i))
  rw [interior_Icc]
  exact ⟨(hp i).1, (hp i).2⟩

/-- **Face vanishing.**  A function vanishing outside `Ω ⊆ interior (Box.Icc I)` vanishes on
both face hyperplanes of `I` in every coordinate direction.  This is exactly the boundary
hypothesis required by the identities of `PDEIdeas.TransportIBP`. -/
theorem face_eq_zero_of_vanishing_outside {E : Type*} [Zero E]
    {I : BoxIntegral.Box (Fin (n + 1))} {Ω : Set (Fin (n + 1) → ℝ)}
    {g : (Fin (n + 1) → ℝ) → E} (hΩ : Ω ⊆ interior (BoxIntegral.Box.Icc I))
    (hg : ∀ x, x ∉ Ω → g x = 0) (i : Fin (n + 1)) (y : Fin n → ℝ) :
    g (i.insertNth (I.upper i) y) = 0 ∧ g (i.insertNth (I.lower i) y) = 0 := by
  constructor
  · refine hg _ fun hmem => ?_
    have h := mem_Ioo_of_mem_interior_boxIcc (hΩ hmem) i
    rw [Fin.insertNth_apply_same] at h
    exact absurd h.2 (lt_irrefl _)
  · refine hg _ fun hmem => ?_
    have h := mem_Ioo_of_mem_interior_boxIcc (hΩ hmem) i
    rw [Fin.insertNth_apply_same] at h
    exact absurd h.1 (lt_irrefl _)

variable {u : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ}
  {u' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] Fin (n + 1) → ℝ}

/-- A field with closed support inside `Ω` vanishes outside `Ω`. -/
theorem eq_zero_of_notMem_of_tsupport_subset {Ω : Set (Fin (n + 1) → ℝ)}
    (hsupp : tsupport u ⊆ Ω) {x : Fin (n + 1) → ℝ} (hx : x ∉ Ω) : u x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hx (hsupp h)

/-- The derivative of a differentiable field vanishes off its closed support. -/
theorem deriv_eq_zero_of_notMem_tsupport (hu : ∀ x, HasFDerivAt u (u' x) x)
    {x : Fin (n + 1) → ℝ} (hx : x ∉ tsupport u) : u' x = 0 := by
  have h : u =ᶠ[𝓝 x] fun _ => (0 : Fin (n + 1) → ℝ) :=
    notMem_tsupport_iff_eventuallyEq.mp hx
  exact (hu x).unique ((hasFDerivAt_const (0 : Fin (n + 1) → ℝ) x).congr_of_eventuallyEq h)

/-- The divergence of a differentiable field vanishes off its closed support. -/
theorem divergence_eq_zero_of_notMem_tsupport (hu : ∀ x, HasFDerivAt u (u' x) x)
    {x : Fin (n + 1) → ℝ} (hx : x ∉ tsupport u) :
    ∑ i : Fin (n + 1), u' x (Pi.single i 1) i = 0 := by
  simp [deriv_eq_zero_of_notMem_tsupport hu hx]

/-- **Propagation of divergence-freeness.**  A differentiable field with closed support inside
`Ω` which is divergence free on `Ω` is divergence free everywhere. -/
theorem divergence_eq_zero_of_divFree_on {Ω : Set (Fin (n + 1) → ℝ)}
    (hu : ∀ x, HasFDerivAt u (u' x) x) (hsupp : tsupport u ⊆ Ω)
    (hdiv : ∀ x ∈ Ω, ∑ i : Fin (n + 1), u' x (Pi.single i 1) i = 0)
    (x : Fin (n + 1) → ℝ) : ∑ i : Fin (n + 1), u' x (Pi.single i 1) i = 0 := by
  by_cases hx : x ∈ Ω
  · exact hdiv x hx
  · exact divergence_eq_zero_of_notMem_tsupport hu fun h => hx (hsupp h)

/-- Every compact set sits inside the interior of a closed box. -/
theorem exists_box_superset_of_isCompact {K : Set (Fin (n + 1) → ℝ)} (hK : IsCompact K) :
    ∃ I : BoxIntegral.Box (Fin (n + 1)), K ⊆ interior (BoxIntegral.Box.Icc I) := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Fin (n + 1) → ℝ)
  have habs : (0 : ℝ) ≤ |R| := abs_nonneg R
  refine ⟨⟨fun _ => -(|R| + 1), fun _ => |R| + 1, fun _ => by linarith⟩, fun x hx => ?_⟩
  refine mem_interior_boxIcc fun i => ?_
  have hxR : ‖x‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hR hx
  have hxi : ‖x i‖ ≤ ‖x‖ := norm_le_pi_norm x i
  rw [Real.norm_eq_abs] at hxi
  have hle : |x i| ≤ |R| := le_trans (le_trans hxi hxR) (le_abs_self R)
  have hbounds := abs_le.mp hle
  exact ⟨by simp only; linarith [hbounds.1], by simp only; linarith [hbounds.2]⟩

/-- Coordinate expansion of a continuous linear functional on `Fin (n+1) → ℝ`.  (This repeats a
private auxiliary lemma of `PDEIdeas.TransportIBP`, which is not exported.) -/
private theorem apply_eq_sum_standardBasis
    (L : (Fin (n + 1) → ℝ) →L[ℝ] ℝ) (x : Fin (n + 1) → ℝ) :
    L x = ∑ i, L (Pi.single i 1) * x i := by
  conv_lhs => rw [← Finset.univ_sum_single x]
  rw [_root_.map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [show Pi.single i (x i) = x i • (Pi.single i 1 : Fin (n + 1) → ℝ) by
    simpa using (Pi.single_smul' i (x i) (1 : ℝ))]
  simp [mul_comm]

end BoxSupport

/-! ## Localized transport identities -/

section Transport

variable {n : ℕ}

/-- **Box integral equals `Ω` integral.**  Specialization of `setIntegral_localize` to a box:
a function vanishing outside `Ω ⊆ Box.Icc I` has the same integral over the box as over `Ω`. -/
theorem boxIntegral_eq_setIntegral_of_vanishing_outside
    (I : BoxIntegral.Box (Fin (n + 1))) (Ω : Set (Fin (n + 1) → ℝ))
    (g : (Fin (n + 1) → ℝ) → ℝ) (hsub : Ω ⊆ BoxIntegral.Box.Icc I)
    (hg : ∀ x, x ∉ Ω → g x = 0) :
    ∫ x in BoxIntegral.Box.Icc I, g x = ∫ x in Ω, g x :=
  setIntegral_localize (measurableSet_boxIcc I) hsub hg

/-- Integrability on `Ω` upgrades to integrability on the box. -/
theorem integrableOn_boxIcc_of_integrableOn_of_vanishing_outside
    (I : BoxIntegral.Box (Fin (n + 1))) (Ω : Set (Fin (n + 1) → ℝ))
    (g : (Fin (n + 1) → ℝ) → ℝ) (hΩ : MeasurableSet Ω)
    (hg : ∀ x, x ∉ Ω → g x = 0) (hint : IntegrableOn g Ω) :
    IntegrableOn g (BoxIntegral.Box.Icc I) :=
  integrableOn_localize hΩ (measurableSet_boxIcc I) hg hint

/-- **Scalar transport cancellation on `Ω`.**  If `u` is differentiable with closed support
inside `Ω`, divergence free on `Ω`, if `f` is differentiable and vanishes outside `Ω`, and if
`Ω` is a measurable subset of the interior of a box, then the transport integral of `f` along
`u` over `Ω` vanishes. -/
theorem scalar_transport_cancel_localized
    (I : BoxIntegral.Box (Fin (n + 1))) (Ω : Set (Fin (n + 1) → ℝ))
    (u : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ) (f : (Fin (n + 1) → ℝ) → ℝ)
    (u' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] Fin (n + 1) → ℝ)
    (f' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] ℝ)
    (hΩ : MeasurableSet Ω) (hΩbox : Ω ⊆ interior (BoxIntegral.Box.Icc I))
    (hu : ∀ x, HasFDerivAt u (u' x) x) (hf : ∀ x, HasFDerivAt f (f' x) x)
    (husupp : tsupport u ⊆ Ω) (hfsupp : ∀ x, x ∉ Ω → f x = 0)
    (hdiv : ∀ x ∈ Ω, ∑ i : Fin (n + 1), u' x (Pi.single i 1) i = 0)
    (hint : IntegrableOn (fun x => f' x (u x)) Ω) :
    ∫ x in Ω, f' x (u x) = 0 := by
  have hbox : MeasurableSet (BoxIntegral.Box.Icc I) := measurableSet_boxIcc I
  have hsub : Ω ⊆ BoxIntegral.Box.Icc I := hΩbox.trans interior_subset
  have hzero : ∀ x, x ∉ Ω → f' x (u x) = 0 := by
    intro x hx
    rw [eq_zero_of_notMem_of_tsupport_subset husupp hx]
    simp
  have hintbox : IntegrableOn (fun x => f' x (u x)) (BoxIntegral.Box.Icc I) :=
    integrableOn_localize hΩ hbox hzero hint
  have hcancel := scalar_transport_cancel I u f u' f'
    (fun x _ => hu x) (fun x _ => (hu x).continuousAt.continuousWithinAt)
    (fun x _ => hf x) (fun x _ => (hf x).continuousAt.continuousWithinAt)
    (fun i y => face_eq_zero_of_vanishing_outside hΩbox hfsupp i y)
    (fun x _ => divergence_eq_zero_of_divFree_on hu husupp hdiv x) hintbox
  rw [← setIntegral_localize hbox hsub hzero]
  exact hcancel

/-- **Vector transport integration by parts on `Ω`.** -/
theorem vector_transport_ibp_localized
    (I : BoxIntegral.Box (Fin (n + 1))) (Ω : Set (Fin (n + 1) → ℝ))
    (u v w : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (u' v' w' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] Fin (n + 1) → ℝ)
    (hΩ : MeasurableSet Ω) (hΩbox : Ω ⊆ interior (BoxIntegral.Box.Icc I))
    (hu : ∀ x, HasFDerivAt u (u' x) x) (hv : ∀ x, HasFDerivAt v (v' x) x)
    (hw : ∀ x, HasFDerivAt w (w' x) x)
    (husupp : tsupport u ⊆ Ω) (hvsupp : ∀ x, x ∉ Ω → v x = 0)
    (hwsupp : ∀ x, x ∉ Ω → w x = 0)
    (hdiv : ∀ x ∈ Ω, ∑ i : Fin (n + 1), u' x (Pi.single i 1) i = 0)
    (hint₁ : IntegrableOn (fun x => ∑ i, v' x (u x) i * w x i) Ω)
    (hint₂ : IntegrableOn (fun x => ∑ i, v x i * w' x (u x) i) Ω) :
    ∫ x in Ω, ∑ i, v' x (u x) i * w x i =
      -∫ x in Ω, ∑ i, v x i * w' x (u x) i := by
  have hbox : MeasurableSet (BoxIntegral.Box.Icc I) := measurableSet_boxIcc I
  have hsub : Ω ⊆ BoxIntegral.Box.Icc I := hΩbox.trans interior_subset
  have hzero₁ : ∀ x, x ∉ Ω → (∑ i, v' x (u x) i * w x i) = 0 := by
    intro x hx
    rw [eq_zero_of_notMem_of_tsupport_subset husupp hx]
    simp
  have hzero₂ : ∀ x, x ∉ Ω → (∑ i, v x i * w' x (u x) i) = 0 := by
    intro x hx
    rw [hvsupp x hx]
    simp
  have hibp := vector_transport_ibp I u v w u' v' w'
    (fun x _ => hu x) (fun x _ => (hu x).continuousAt.continuousWithinAt)
    (fun x _ => hv x) (fun x _ => (hv x).continuousAt.continuousWithinAt)
    (fun x _ => hw x) (fun x _ => (hw x).continuousAt.continuousWithinAt)
    (fun i y => face_eq_zero_of_vanishing_outside hΩbox hvsupp i y)
    (fun i y => face_eq_zero_of_vanishing_outside hΩbox hwsupp i y)
    (fun x _ => divergence_eq_zero_of_divFree_on hu husupp hdiv x)
    (integrableOn_localize hΩ hbox hzero₁ hint₁)
    (integrableOn_localize hΩ hbox hzero₂ hint₂)
  rw [← setIntegral_localize hbox hsub hzero₁, ← setIntegral_localize hbox hsub hzero₂]
  exact hibp

/-- **Skew-symmetry of the trilinear transport form on `Ω`.** -/
theorem trilinear_skew_localized
    (I : BoxIntegral.Box (Fin (n + 1))) (Ω : Set (Fin (n + 1) → ℝ))
    (u v w : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (u' v' w' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] Fin (n + 1) → ℝ)
    (hΩ : MeasurableSet Ω) (hΩbox : Ω ⊆ interior (BoxIntegral.Box.Icc I))
    (hu : ∀ x, HasFDerivAt u (u' x) x) (hv : ∀ x, HasFDerivAt v (v' x) x)
    (hw : ∀ x, HasFDerivAt w (w' x) x)
    (husupp : tsupport u ⊆ Ω) (hvsupp : ∀ x, x ∉ Ω → v x = 0)
    (hwsupp : ∀ x, x ∉ Ω → w x = 0)
    (hdiv : ∀ x ∈ Ω, ∑ i : Fin (n + 1), u' x (Pi.single i 1) i = 0)
    (hint₁ : IntegrableOn (fun x => ∑ i, v' x (u x) i * w x i) Ω)
    (hint₂ : IntegrableOn (fun x => ∑ i, v x i * w' x (u x) i) Ω) :
    (∫ x in Ω, ∑ i, v' x (u x) i * w x i) +
      ∫ x in Ω, ∑ i, w' x (u x) i * v x i = 0 := by
  have hbox : MeasurableSet (BoxIntegral.Box.Icc I) := measurableSet_boxIcc I
  have hsub : Ω ⊆ BoxIntegral.Box.Icc I := hΩbox.trans interior_subset
  have hzero₁ : ∀ x, x ∉ Ω → (∑ i, v' x (u x) i * w x i) = 0 := by
    intro x hx
    rw [eq_zero_of_notMem_of_tsupport_subset husupp hx]
    simp
  have hzero₂ : ∀ x, x ∉ Ω → (∑ i, v x i * w' x (u x) i) = 0 := by
    intro x hx
    rw [hvsupp x hx]
    simp
  have hzero₃ : ∀ x, x ∉ Ω → (∑ i, w' x (u x) i * v x i) = 0 := by
    intro x hx
    rw [eq_zero_of_notMem_of_tsupport_subset husupp hx]
    simp
  have hskew := trilinear_skew I u v w u' v' w'
    (fun x _ => hu x) (fun x _ => (hu x).continuousAt.continuousWithinAt)
    (fun x _ => hv x) (fun x _ => (hv x).continuousAt.continuousWithinAt)
    (fun x _ => hw x) (fun x _ => (hw x).continuousAt.continuousWithinAt)
    (fun i y => face_eq_zero_of_vanishing_outside hΩbox hvsupp i y)
    (fun i y => face_eq_zero_of_vanishing_outside hΩbox hwsupp i y)
    (fun x _ => divergence_eq_zero_of_divFree_on hu husupp hdiv x)
    (integrableOn_localize hΩ hbox hzero₁ hint₁)
    (integrableOn_localize hΩ hbox hzero₂ hint₂)
  rw [← setIntegral_localize hbox hsub hzero₁, ← setIntegral_localize hbox hsub hzero₃]
  exact hskew

/-- **Diagonal transport cancellation on `Ω`.** -/
theorem trilinear_self_cancel_localized
    (I : BoxIntegral.Box (Fin (n + 1))) (Ω : Set (Fin (n + 1) → ℝ))
    (u : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (u' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] Fin (n + 1) → ℝ)
    (hΩ : MeasurableSet Ω) (hΩbox : Ω ⊆ interior (BoxIntegral.Box.Icc I))
    (hu : ∀ x, HasFDerivAt u (u' x) x) (husupp : tsupport u ⊆ Ω)
    (hdiv : ∀ x ∈ Ω, ∑ i : Fin (n + 1), u' x (Pi.single i 1) i = 0)
    (hint : IntegrableOn (fun x => ∑ i, u' x (u x) i * u x i) Ω) :
    ∫ x in Ω, ∑ i, u' x (u x) i * u x i = 0 := by
  have hbox : MeasurableSet (BoxIntegral.Box.Icc I) := measurableSet_boxIcc I
  have hsub : Ω ⊆ BoxIntegral.Box.Icc I := hΩbox.trans interior_subset
  have husupp' : ∀ x, x ∉ Ω → u x = 0 := fun x hx =>
    eq_zero_of_notMem_of_tsupport_subset husupp hx
  have hzero : ∀ x, x ∉ Ω → (∑ i, u' x (u x) i * u x i) = 0 := by
    intro x hx
    rw [husupp' x hx]
    simp
  have hcancel := trilinear_self_cancel I u u'
    (fun x _ => hu x) (fun x _ => (hu x).continuousAt.continuousWithinAt)
    (fun i y => face_eq_zero_of_vanishing_outside hΩbox husupp' i y)
    (fun x _ => divergence_eq_zero_of_divFree_on hu husupp hdiv x)
    (integrableOn_localize hΩ hbox hzero hint)
  rw [← setIntegral_localize hbox hsub hzero]
  exact hcancel

/-- **Scalar transport integration by parts on `Ω`, with support only on the velocity.**
Here the scalar field `f` is an arbitrary differentiable function: no boundary or support
condition is imposed on `f`, because the flux `f • u` already vanishes on the faces of the
box thanks to the closed support of `u`.  This is the form needed for weak formulations,
where `f` plays the role of a test function that need not be supported in `Ω`. -/
theorem scalar_ibp_of_support
    (I : BoxIntegral.Box (Fin (n + 1))) (Ω : Set (Fin (n + 1) → ℝ))
    (u : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ) (f : (Fin (n + 1) → ℝ) → ℝ)
    (u' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] Fin (n + 1) → ℝ)
    (f' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] ℝ)
    (hΩ : MeasurableSet Ω) (hΩbox : Ω ⊆ interior (BoxIntegral.Box.Icc I))
    (hu : ∀ x, HasFDerivAt u (u' x) x) (hf : ∀ x, HasFDerivAt f (f' x) x)
    (husupp : tsupport u ⊆ Ω)
    (hint_transport : IntegrableOn (fun x => f' x (u x)) Ω)
    (hint_div : IntegrableOn
      (fun x => f x * ∑ i, u' x (Pi.single i 1) i) Ω) :
    ∫ x in Ω, f' x (u x) =
      -∫ x in Ω, f x * ∑ i, u' x (Pi.single i 1) i := by
  have hbox : MeasurableSet (BoxIntegral.Box.Icc I) := measurableSet_boxIcc I
  have hsub : Ω ⊆ BoxIntegral.Box.Icc I := hΩbox.trans interior_subset
  have huzero : ∀ x, x ∉ Ω → u x = 0 := fun x hx =>
    eq_zero_of_notMem_of_tsupport_subset husupp hx
  have hu'zero : ∀ x, x ∉ Ω → u' x = 0 := fun x hx =>
    deriv_eq_zero_of_notMem_tsupport hu fun h => hx (husupp h)
  have hzero₁ : ∀ x, x ∉ Ω → f' x (u x) = 0 := by
    intro x hx
    rw [huzero x hx]
    simp
  have hzero₂ : ∀ x, x ∉ Ω → f x * ∑ i, u' x (Pi.single i 1) i = 0 := by
    intro x hx
    rw [hu'zero x hx]
    simp
  have huc : ContinuousOn u (BoxIntegral.Box.Icc I) :=
    fun x _ => (hu x).continuousAt.continuousWithinAt
  have hfc : ContinuousOn f (BoxIntegral.Box.Icc I) :=
    fun x _ => (hf x).continuousAt.continuousWithinAt
  let flux : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ := fun x => f x • u x
  let flux' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] Fin (n + 1) → ℝ :=
    fun x => f x • u' x + (f' x).smulRight (u x)
  have hflux_deriv : ∀ x ∈ interior (BoxIntegral.Box.Icc I),
      HasFDerivAt flux (flux' x) x := by
    intro x _
    simpa [flux, flux'] using (hf x).smul (hu x)
  have hflux_cont : ContinuousOn flux (BoxIntegral.Box.Icc I) := hfc.smul huc
  have hflux_bc : ∀ i : Fin (n + 1), ∀ y : Fin n → ℝ,
      flux (i.insertNth (I.upper i) y) i = 0 ∧
      flux (i.insertNth (I.lower i) y) i = 0 := by
    intro i y
    obtain ⟨h₁, h₂⟩ := face_eq_zero_of_vanishing_outside hΩbox huzero i y
    constructor
    · simp [flux, h₁]
    · simp [flux, h₂]
  have hflux_div : ∀ x, ∑ i, flux' x (Pi.single i 1) i =
      f' x (u x) + f x * ∑ i, u' x (Pi.single i 1) i := by
    intro x
    rw [apply_eq_sum_standardBasis (f' x) (u x)]
    simp only [flux', ContinuousLinearMap.add_apply, Pi.add_apply,
      ContinuousLinearMap.smul_apply, Pi.smul_apply,
      ContinuousLinearMap.smulRight_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    ring
  have hint_transport_box : IntegrableOn (fun x => f' x (u x))
      (BoxIntegral.Box.Icc I) := integrableOn_localize hΩ hbox hzero₁ hint_transport
  have hint_div_box : IntegrableOn
      (fun x => f x * ∑ i, u' x (Pi.single i 1) i)
      (BoxIntegral.Box.Icc I) := integrableOn_localize hΩ hbox hzero₂ hint_div
  have hflux_int : IntegrableOn (fun x => ∑ i, flux' x (Pi.single i 1) i)
      (BoxIntegral.Box.Icc I) :=
    (hint_transport_box.add hint_div_box).congr_fun
      (fun x _ => (hflux_div x).symm) hbox
  have hvanish := integral_divergence_zero_bc I flux flux'
    hflux_cont hflux_deriv hflux_int hflux_bc
  have hsum : ∫ x in BoxIntegral.Box.Icc I,
      (f' x (u x) + f x * ∑ i, u' x (Pi.single i 1) i) = 0 := by
    rw [setIntegral_congr_fun hbox (fun x _ => (hflux_div x).symm)]
    exact hvanish
  rw [integral_add hint_transport_box hint_div_box] at hsum
  rw [← setIntegral_localize hbox hsub hzero₁, ← setIntegral_localize hbox hsub hzero₂]
  linarith

/-- **Scalar transport cancellation against an arbitrary test function.**  If `u` is
differentiable with closed support inside `Ω` and divergence free on `Ω`, then the transport
integral of any differentiable `f` along `u` over `Ω` vanishes. -/
theorem scalar_transport_cancel_of_support
    (I : BoxIntegral.Box (Fin (n + 1))) (Ω : Set (Fin (n + 1) → ℝ))
    (u : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ) (f : (Fin (n + 1) → ℝ) → ℝ)
    (u' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] Fin (n + 1) → ℝ)
    (f' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] ℝ)
    (hΩ : MeasurableSet Ω) (hΩbox : Ω ⊆ interior (BoxIntegral.Box.Icc I))
    (hu : ∀ x, HasFDerivAt u (u' x) x) (hf : ∀ x, HasFDerivAt f (f' x) x)
    (husupp : tsupport u ⊆ Ω)
    (hdiv : ∀ x ∈ Ω, ∑ i : Fin (n + 1), u' x (Pi.single i 1) i = 0)
    (hint : IntegrableOn (fun x => f' x (u x)) Ω) :
    ∫ x in Ω, f' x (u x) = 0 := by
  have hdivzero : ∀ x, ∑ i : Fin (n + 1), u' x (Pi.single i 1) i = 0 :=
    divergence_eq_zero_of_divFree_on hu husupp hdiv
  have hint_div : IntegrableOn
      (fun x => f x * ∑ i, u' x (Pi.single i 1) i) Ω :=
    integrableOn_zero.congr_fun (fun x _ => by simp [hdivzero x]) hΩ
  have hibp := scalar_ibp_of_support I Ω u f u' f' hΩ hΩbox hu hf husupp hint hint_div
  have hdiv_integral : ∫ x in Ω, f x * ∑ i, u' x (Pi.single i 1) i = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun x _ => by simp [hdivzero x]
  rw [hibp, hdiv_integral, neg_zero]

end Transport

/-! ## Box-free statements for compactly supported fields -/

section CompactSupport

variable {n : ℕ}

/-- **Diagonal transport cancellation on an arbitrary measurable domain.**  For a
differentiable field with compact closed support inside a measurable set `Ω`, divergence free
on `Ω`, with integrable transport density, the diagonal transport integral over `Ω` vanishes.
No regularity whatsoever is assumed of `Ω`: the box is produced from the compact support. -/
theorem trilinear_self_cancel_on_domain
    (Ω : Set (Fin (n + 1) → ℝ))
    (u : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (u' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] Fin (n + 1) → ℝ)
    (hΩ : MeasurableSet Ω) (hu : ∀ x, HasFDerivAt u (u' x) x)
    (hcomp : IsCompact (tsupport u)) (hsupp : tsupport u ⊆ Ω)
    (hdiv : ∀ x ∈ Ω, ∑ i : Fin (n + 1), u' x (Pi.single i 1) i = 0)
    (hint : IntegrableOn (fun x => ∑ i, u' x (u x) i * u x i) Ω) :
    ∫ x in Ω, ∑ i, u' x (u x) i * u x i = 0 := by
  obtain ⟨I, hI⟩ := exists_box_superset_of_isCompact hcomp
  have hzero : ∀ x, x ∉ tsupport u → (∑ i, u' x (u x) i * u x i) = 0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx]
    simp
  have key := trilinear_self_cancel_localized I (tsupport u) u u'
    isClosed_closure.measurableSet hI hu subset_rfl
    (fun x hx => hdiv x (hsupp hx)) (hint.mono_set hsupp)
  rw [setIntegral_localize hΩ hsupp hzero]
  exact key

/-- **Diagonal transport cancellation on the whole space.**  For a differentiable,
compactly supported, divergence-free field with integrable transport density,
`∫ ⟪(u ⬝ ∇) u, u⟫ = 0` over all of `Fin (n+1) → ℝ`. -/
theorem trilinear_self_cancel_of_compactSupport
    (u : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (u' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] Fin (n + 1) → ℝ)
    (hu : ∀ x, HasFDerivAt u (u' x) x) (hcomp : IsCompact (tsupport u))
    (hdiv : ∀ x, ∑ i : Fin (n + 1), u' x (Pi.single i 1) i = 0)
    (hint : Integrable (fun x => ∑ i, u' x (u x) i * u x i)) :
    ∫ x, ∑ i, u' x (u x) i * u x i = 0 := by
  have h := trilinear_self_cancel_on_domain Set.univ u u' MeasurableSet.univ hu hcomp
    (Set.subset_univ _) (fun x _ => hdiv x) hint.integrableOn
  rwa [setIntegral_univ] at h

/-- **Skew-symmetry on an arbitrary measurable domain** for compactly supported fields. -/
theorem trilinear_skew_on_domain
    (Ω : Set (Fin (n + 1) → ℝ))
    (u v w : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (u' v' w' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] Fin (n + 1) → ℝ)
    (hΩ : MeasurableSet Ω)
    (hu : ∀ x, HasFDerivAt u (u' x) x) (hv : ∀ x, HasFDerivAt v (v' x) x)
    (hw : ∀ x, HasFDerivAt w (w' x) x)
    (hcompu : IsCompact (tsupport u)) (hcompv : IsCompact (tsupport v))
    (hcompw : IsCompact (tsupport w))
    (hsuppu : tsupport u ⊆ Ω) (hsuppv : tsupport v ⊆ Ω) (hsuppw : tsupport w ⊆ Ω)
    (hdiv : ∀ x ∈ Ω, ∑ i : Fin (n + 1), u' x (Pi.single i 1) i = 0)
    (hint₁ : IntegrableOn (fun x => ∑ i, v' x (u x) i * w x i) Ω)
    (hint₂ : IntegrableOn (fun x => ∑ i, v x i * w' x (u x) i) Ω) :
    (∫ x in Ω, ∑ i, v' x (u x) i * w x i) +
      ∫ x in Ω, ∑ i, w' x (u x) i * v x i = 0 := by
  set K : Set (Fin (n + 1) → ℝ) := tsupport u ∪ tsupport v ∪ tsupport w with hK
  have hKcomp : IsCompact K := (hcompu.union hcompv).union hcompw
  have hKmeas : MeasurableSet K :=
    ((isClosed_closure.union isClosed_closure).union isClosed_closure).measurableSet
  have hKsub : K ⊆ Ω := Set.union_subset (Set.union_subset hsuppu hsuppv) hsuppw
  obtain ⟨I, hI⟩ := exists_box_superset_of_isCompact hKcomp
  have huK : tsupport u ⊆ K := (Set.subset_union_left).trans Set.subset_union_left
  have hvK : ∀ x, x ∉ K → v x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h =>
      hx (Set.subset_union_left (Set.subset_union_right h))
  have hwK : ∀ x, x ∉ K → w x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (Set.subset_union_right h)
  have hzero₁ : ∀ x, x ∉ K → (∑ i, v' x (u x) i * w x i) = 0 := by
    intro x hx
    rw [eq_zero_of_notMem_of_tsupport_subset huK hx]
    simp
  have hzero₃ : ∀ x, x ∉ K → (∑ i, w' x (u x) i * v x i) = 0 := by
    intro x hx
    rw [eq_zero_of_notMem_of_tsupport_subset huK hx]
    simp
  have key := trilinear_skew_localized I K u v w u' v' w' hKmeas hI hu hv hw huK hvK hwK
    (fun x hx => hdiv x (hKsub hx)) (hint₁.mono_set hKsub) (hint₂.mono_set hKsub)
  rw [setIntegral_localize hΩ hKsub hzero₁, setIntegral_localize hΩ hKsub hzero₃]
  exact key

/-- **Diagonal transport cancellation for `C¹` compactly supported divergence-free fields.**
Integrability is derived here rather than assumed: the transport density is continuous with
compact support, hence integrable. -/
theorem trilinear_self_cancel_of_contDiff
    (u : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (hu : ContDiff ℝ 1 u) (hcomp : HasCompactSupport u)
    (hdiv : ∀ x, ∑ i : Fin (n + 1), fderiv ℝ u x (Pi.single i 1) i = 0) :
    ∫ x, ∑ i, fderiv ℝ u x (u x) i * u x i = 0 := by
  have hu' : ∀ x, HasFDerivAt u (fderiv ℝ u x) x := fun x =>
    (hu.differentiable one_ne_zero x).hasFDerivAt
  have hcu : Continuous u := hu.continuous
  have hcd : Continuous (fderiv ℝ u) := hu.continuous_fderiv one_ne_zero
  have happ : Continuous fun x => fderiv ℝ u x (u x) := hcd.clm_apply hcu
  have hcont : Continuous fun x => ∑ i, fderiv ℝ u x (u x) i * u x i := by
    refine continuous_finset_sum Finset.univ fun i _ => ?_
    exact ((continuous_apply i).comp happ).mul ((continuous_apply i).comp hcu)
  have hsupp : Function.support (fun x => ∑ i, fderiv ℝ u x (u x) i * u x i) ⊆
      Function.support u := by
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro h
    exact hx (by simp [h])
  have hcs : HasCompactSupport fun x => ∑ i, fderiv ℝ u x (u x) i * u x i :=
    hcomp.mono hsupp
  exact trilinear_self_cancel_of_compactSupport u (fderiv ℝ u) hu' hcomp.isCompact hdiv
    (hcont.integrable_of_hasCompactSupport hcs)

end CompactSupport

end OpenDomainTransport

end
