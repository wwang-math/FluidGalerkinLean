import PDEIdeas.OpenDomainPhysicalConvection
import PDEIdeas.BoxLadyzhenskayaLimit

/-!
# The tested convection limit on an open subdomain

`PDEIdeas.OpenDomainPhysicalConvection` realizes the transport integral of an open
subdomain `Ω ⊆ interior (Box.Icc Q)` of a plane rectangle as the continuous trilinear
form `OpenDomainPhysicalConvection.convectionForm Ω E` on the closed energy space
`OpenDomainH1ZeroSigma Ω`, together with its skewness.
`PDEIdeas.QuadraticTensorLimit` and `PDEIdeas.QuadraticWeakFormLimit` supply the
projective-tensor limit of a quadratic observable along a strongly `L²`-in-time
convergent sequence, and `PDEIdeas.BoxLadyzhenskayaLimit` supplies the space-time
interpolation that converts strong pivot convergence plus a uniform energy bound into
strong `L²_t L⁴_x` convergence.  This file runs the three together for `Ω`.

## What is proved

For a sequence of energy paths `w : ℕ → L²_t(H¹_{0,σ}(Ω))` that

* is **uniformly bounded in `L²_t V`**: `∀ k, ‖w k‖ ≤ R` — the two-dimensional a priori
  energy bound; and
* **converges strongly in `L²_t H`**: the pivot paths
  `(energyToBoxState Ω).compLpL 2 μ (w k)` converge to
  `(energyToBoxState Ω).compLpL 2 μ wLim` in `L²_t(L²_σ)`,

the tested convection term converges:

`∫ b_Ω(w k t, w k t, φ) η t dμ → ∫ b_Ω(wLim t, wLim t, φ) η t dμ`

for every test field `φ ∈ H¹_{0,σ}(Ω)` and every bounded scalar time weight
`η ∈ L^∞_t`.  This is `OpenDomainConvectionLimit.tested_convection_tendsto`.  The
convergence is **derived**, not assumed: no hypothesis of this file mentions the
convection term of the limit.

## Hypotheses that are actually used

* `L : BoxLadyzhenskayaRealization Q` — the two-dimensional Ladyzhenskaya realization of
  the ambient rectangle.  Only `L.constant`, `L.constant_nonneg` and `L.l4_sq_le` are
  used, and the subdomain inherits them with the same constant
  (`OpenDomainConvectionLimit.l4_sq_le`) through the isometric inclusion
  `OpenDomainPhysicalConvection.energyInclusion`.
* `w k, wLim : Lp (OpenDomainH1ZeroSigma Ω) 2 μ` — the integrability of the paths: each
  is square integrable in time with values in the subdomain energy space.  This is the
  `L²_t V` regularity of a Galerkin family.
* `R : ℝ` with `∀ k, ‖w k‖ ≤ R` — the uniform `L²_t V` bound.
* `hstate` — strong `L²_t H` convergence of the pivot paths.
* `φ : OpenDomainH1ZeroSigma Ω` — the **test field**.  No smoothness is required: the
  form is continuous on the energy closure, and only `boxEnergyGradient Q` of its
  inclusion enters.
* `η : Lp ℝ ∞ μ` — the **bounded scalar time weight** of the test.

No integrability of the convection integrand is assumed.  It is *proved*:
`OpenDomainConvectionLimit.integrable_convection_integrand` shows that
`t ↦ b_Ω(v t, v t, φ) * η t` is integrable for every `v : Lp (OpenDomainH1ZeroSigma Ω) 2 μ`,
from the `L¹`–`L^∞` Hölder pairing of the projective tensor square against the gradient
test, so the limit statement is not an artefact of the junk value of a divergent
Bochner integral.

**Scope.**  Nothing here is asserted about pointwise representatives of closure
elements, and no divergence or boundary theorem on `∂Ω` is used: the subdomain enters
only through `energyInclusion` and the already-proved skewness of the box form.
-/

open Filter MeasureTheory
open scoped ENNReal NNReal

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 1000000

local instance openDomainConvectionLimitFactFour : Fact (1 ≤ (4 : ℝ≥0∞)) :=
  ⟨by norm_num⟩

/-! ### Strong interpolated limits for sequences -/

section Interpolation

variable {Time : Type*} [MeasurableSpace Time] {μ : Measure Time}
variable {V H X : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- **Sequence form of the interpolation argument.**  A pointwise interpolation
inequality `‖A v‖² ≤ C ‖J v‖ ‖v‖`, a uniform `L²_t V` bound and strong `L²_t H`
convergence of the `J`-images give strong `L²_t X` convergence of the `A`-images.  This
is the sequence analogue of
`LeraySpectralCompactFamily.StrongWeakSubsequence.interpolatedTimeMap_tendsto`, stated
without any extraction structure. -/
theorem tendsto_compLpL_of_pointwise_interpolation
    (A : V →L[ℝ] X) (J : V →L[ℝ] H) (C : ℝ) (hC : 0 ≤ C)
    (hpointwise : ∀ v, ‖A v‖ ^ 2 ≤ C * ‖J v‖ * ‖v‖)
    (w : ℕ → Lp V (2 : ℝ≥0∞) μ) (wLim : Lp V (2 : ℝ≥0∞) μ)
    (R : ℝ) (hbound : ∀ k, ‖w k‖ ≤ R)
    (hstate : Tendsto (fun k => J.compLpL 2 μ (w k)) atTop
      (nhds (J.compLpL 2 μ wLim))) :
    Tendsto (fun k => A.compLpL 2 μ (w k)) atTop
      (nhds (A.compLpL 2 μ wLim)) := by
  have hR0 : (0 : ℝ) ≤ R := (norm_nonneg (w 0)).trans (hbound 0)
  have hB0 : (0 : ℝ) ≤ R + ‖wLim‖ := by positivity
  set d : ℕ → Lp V (2 : ℝ≥0∞) μ := fun k => w k - wLim with hd
  have hdBound : ∀ k, ‖d k‖ ≤ R + ‖wLim‖ := by
    intro k
    exact (norm_sub_le _ _).trans (add_le_add (hbound k) le_rfl)
  have hJd : ∀ k, J.compLpL 2 μ (d k) =
      J.compLpL 2 μ (w k) - J.compLpL 2 μ wLim := by
    intro k
    simpa only [hd] using (J.compLpL 2 μ).map_sub (w k) wLim
  set upper : ℕ → ℝ := fun k =>
    C * ‖J.compLpL 2 μ (w k) - J.compLpL 2 μ wLim‖ * (R + ‖wLim‖) with hupperdef
  have hupper_nonneg : ∀ k, 0 ≤ upper k := by
    intro k
    exact mul_nonneg (mul_nonneg hC (norm_nonneg _)) hB0
  have hsq : ∀ k, ‖A.compLpL 2 μ (d k)‖ ^ 2 ≤ upper k := by
    intro k
    have h := norm_compLpL_sq_le_of_pointwise_interpolation
      A J C hC hpointwise (d k)
    rw [hJd k] at h
    exact h.trans
      (mul_le_mul_of_nonneg_left (hdBound k) (mul_nonneg hC (norm_nonneg _)))
  have hnormBound : ∀ k, ‖A.compLpL 2 μ (d k)‖ ≤ Real.sqrt (upper k) := by
    intro k
    rw [← sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _),
      Real.sq_sqrt (hupper_nonneg k)]
    exact hsq k
  have hstateNorm : Tendsto
      (fun k => ‖J.compLpL 2 μ (w k) - J.compLpL 2 μ wLim‖) atTop (nhds 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hstate
  have hupper : Tendsto upper atTop (nhds 0) := by
    rw [hupperdef]
    simpa using ((tendsto_const_nhds.mul hstateNorm).mul tendsto_const_nhds)
  have hsqrt : Tendsto (fun k => Real.sqrt (upper k)) atTop (nhds 0) := by
    have hsqrtAt : Tendsto Real.sqrt (nhds 0) (nhds (Real.sqrt 0)) :=
      Real.continuous_sqrt.continuousAt
    simpa using hsqrtAt.comp hupper
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have hnorm : Tendsto (fun k => ‖A.compLpL 2 μ (d k)‖) atTop (nhds 0) :=
    squeeze_zero (fun _ => norm_nonneg _) hnormBound hsqrt
  simpa only [hd, map_sub] using hnorm

end Interpolation

/-! ### A convergent sequence as a strong metric subsequence -/

/-- A convergent sequence is a strong metric subsequence for the identity
extraction.  This is what feeds a plain sequence into the projective tensor
machinery of `PDEIdeas.QuadraticTensorLimit`. -/
def strongMetricSubsequenceOfTendsto {X : Type*} [TopologicalSpace X]
    {x : ℕ → X} {limit : X} (h : Tendsto x atTop (nhds limit)) :
    StrongMetricSubsequence x where
  subseq := ExtractedSubsequence.identity
  limit := limit
  converges := h

@[simp]
theorem strongMetricSubsequenceOfTendsto_idx {X : Type*} [TopologicalSpace X]
    {x : ℕ → X} {limit : X} (h : Tendsto x atTop (nhds limit)) (k : ℕ) :
    (strongMetricSubsequenceOfTendsto h).subseq.idx k = k := rfl

@[simp]
theorem strongMetricSubsequenceOfTendsto_limit {X : Type*} [TopologicalSpace X]
    {x : ℕ → X} {limit : X} (h : Tendsto x atTop (nhds limit)) :
    (strongMetricSubsequenceOfTendsto h).limit = limit := rfl

/-! ### Integrability of a tested quadratic trilinear integrand -/

/-- **The tested quadratic integrand of a continuous trilinear form is integrable.**
The projective tensor square of an `L²` path is a tensor-valued `L¹` path, and the
`L¹`–`L^∞` Hölder pairing against a bounded test path lands in `L¹`.  No integrability
hypothesis is needed. -/
theorem integrable_trilinear_tensorSquare
    {α H Test : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup Test] [NormedSpace ℝ Test]
    (T : H →L[ℝ] H →L[ℝ] Test →L[ℝ] ℝ)
    (x : Lp H (2 : ℝ≥0∞) μ) (ψ : Lp Test (∞ : ℝ≥0∞) μ) :
    Integrable (fun t => T (x t) (x t) (ψ t)) μ := by
  have hmem :
      MemLp (fun t =>
        trilinearProjectiveTensorPairing T ((projectiveTensorSquareLp x) t) (ψ t))
        (1 : ℝ≥0∞) μ :=
    (trilinearProjectiveTensorPairing T).memLp_of_bilin (r := (1 : ℝ≥0∞))
      (Lp.memLp (projectiveTensorSquareLp x)) (Lp.memLp ψ)
  have hae :
      (fun t =>
        trilinearProjectiveTensorPairing T ((projectiveTensorSquareLp x) t) (ψ t))
        =ᵐ[μ] fun t => T (x t) (x t) (ψ t) := by
    filter_upwards [(projectiveTensorBilinear H).coeFn_holder
      (r := (1 : ℝ≥0∞)) x x] with t ht
    change
      trilinearProjectiveTensorPairing T
        (((projectiveTensorBilinear H).holder (1 : ℝ≥0∞) x x) t) (ψ t) = _
    rw [ht]
    exact trilinearProjectiveTensorPairing_tmul T (x t) (x t) (ψ t)
  exact (memLp_one_iff_integrable.1 hmem).congr hae

/-! ### The subdomain convection limit -/

namespace OpenDomainConvectionLimit

open OpenDomainPhysicalConvection

variable {Q : BoxIntegral.Box (Fin 2)} {Ω : OpenDomainInBox Q}

/-- The `L⁴` velocity representative of a subdomain energy vector, read in the ambient
rectangle. -/
def energyToLp4 (Ω : OpenDomainInBox Q) (E : BoxEnergyL4Realization Q) :
    OpenDomainH1ZeroSigma Ω →L[ℝ] BoxVelocityL4 Q :=
  E.toLp4.comp (energyInclusion Ω)

@[simp]
theorem energyToLp4_apply (E : BoxEnergyL4Realization Q)
    (v : OpenDomainH1ZeroSigma Ω) :
    energyToLp4 Ω E v = E.toLp4 (energyInclusion Ω v) := rfl

/-- The subdomain state map, read in the ambient rectangle pivot space.  Its norm is the
subdomain state norm, so strong convergence of these paths is exactly strong
`L²_t(L²_σ(Ω))` convergence. -/
def energyToBoxState (Ω : OpenDomainInBox Q) :
    OpenDomainH1ZeroSigma Ω →L[ℝ] BoxL2Sigma Q :=
  (boxEnergyToState Q).comp (energyInclusion Ω)

@[simp]
theorem energyToBoxState_apply (v : OpenDomainH1ZeroSigma Ω) :
    energyToBoxState Ω v = boxEnergyToState Q (energyInclusion Ω v) := rfl

@[simp]
theorem norm_energyToBoxState (v : OpenDomainH1ZeroSigma Ω) :
    ‖energyToBoxState Ω v‖ = ‖openDomainEnergyToState Ω v‖ := rfl

/-- **The two-dimensional Ladyzhenskaya interpolation on the subdomain**, with the
rectangle constant unchanged.  The gradient norm is dominated by the subdomain graph
norm through the isometric inclusion. -/
theorem l4_sq_le (L : BoxLadyzhenskayaRealization Q)
    (v : OpenDomainH1ZeroSigma Ω) :
    ‖energyToLp4 Ω L.toBoxEnergyL4Realization v‖ ^ 2 ≤
      L.constant * ‖energyToBoxState Ω v‖ * ‖v‖ := by
  refine (L.l4_sq_le (energyInclusion Ω v)).trans ?_
  refine mul_le_mul_of_nonneg_left ?_
    (mul_nonneg L.constant_nonneg (norm_nonneg _))
  exact (norm_boxEnergyGradient_le Q (energyInclusion Ω v)).trans_eq
    (norm_energyInclusion v)

/-- **The tested `L⁴`–`L²`–`L⁴` form is minus the subdomain convection form.**  This is
the skew conversion that puts the two velocity arguments adjacent and the gradient of
the test field in the last slot. -/
theorem boxLpConvectionTested_energyToLp4 (E : BoxEnergyL4Realization Q)
    (u φ : OpenDomainH1ZeroSigma Ω) :
    boxLpConvectionTested (energyToLp4 Ω E u) (energyToLp4 Ω E u)
        (boxEnergyGradient Q (energyInclusion Ω φ)) =
      -convectionForm Ω E u u φ := by
  have hbox :
      boxLpConvectionTested (energyToLp4 Ω E u) (energyToLp4 Ω E u)
          (boxEnergyGradient Q (energyInclusion Ω φ)) =
        convectionForm Ω E u φ u := by
    rw [convectionForm_apply, BoxEnergyL4Realization.convectionForm_apply,
      boxLpConvectionTested_apply, energyToLp4_apply]
  rw [hbox]
  have hskew := convectionForm_skew Ω E u u φ
  linarith

/-- The scaled form of the skew conversion: a scalar weight on the gradient test
factors out of the tested form. -/
theorem boxLpConvectionTested_energyToLp4_smul (E : BoxEnergyL4Realization Q)
    (u φ : OpenDomainH1ZeroSigma Ω) (c : ℝ) :
    boxLpConvectionTested (energyToLp4 Ω E u) (energyToLp4 Ω E u)
        (c • boxEnergyGradient Q (energyInclusion Ω φ)) =
      -(convectionForm Ω E u u φ * c) := by
  rw [map_smul, boxLpConvectionTested_energyToLp4 E u φ]
  simp [mul_comm]

/-- The bounded gradient test path determined by a test field `φ` in the subdomain
energy space and a bounded scalar time weight `η`. -/
def gradientTestLp {Time : Type*} [MeasurableSpace Time] {μ : Measure Time}
    (Ω : OpenDomainInBox Q) (φ : OpenDomainH1ZeroSigma Ω)
    (η : Lp ℝ (∞ : ℝ≥0∞) μ) : Lp (BoxGradientL2 Q) (∞ : ℝ≥0∞) μ :=
  (ContinuousLinearMap.toSpanSingleton ℝ
    (boxEnergyGradient Q (energyInclusion Ω φ))).compLpL (∞ : ℝ≥0∞) μ η

theorem gradientTestLp_apply_ae {Time : Type*} [MeasurableSpace Time]
    {μ : Measure Time} (φ : OpenDomainH1ZeroSigma Ω) (η : Lp ℝ (∞ : ℝ≥0∞) μ) :
    gradientTestLp Ω φ η =ᵐ[μ]
      fun t => η t • boxEnergyGradient Q (energyInclusion Ω φ) := by
  unfold gradientTestLp
  filter_upwards [(ContinuousLinearMap.toSpanSingleton ℝ
    (boxEnergyGradient Q (energyInclusion Ω φ))).coeFn_compLpL η] with t ht
  rw [ht]
  rfl

/-- **The tested integrand is minus the physical convection integrand.**  Almost
everywhere in time, for canonical `Lp` representatives. -/
theorem tested_integrand_ae {Time : Type*} [MeasurableSpace Time]
    {μ : Measure Time} (E : BoxEnergyL4Realization Q)
    (φ : OpenDomainH1ZeroSigma Ω) (η : Lp ℝ (∞ : ℝ≥0∞) μ)
    (v : Lp (OpenDomainH1ZeroSigma Ω) (2 : ℝ≥0∞) μ) :
    (fun t => boxLpConvectionTested
        (((energyToLp4 Ω E).compLpL 2 μ v) t)
        (((energyToLp4 Ω E).compLpL 2 μ v) t)
        ((gradientTestLp Ω φ η) t))
      =ᵐ[μ] fun t => -(convectionForm Ω E (v t) (v t) φ * η t) := by
  filter_upwards [(energyToLp4 Ω E).coeFn_compLpL v,
    gradientTestLp_apply_ae (Ω := Ω) φ η] with t hA hψ
  conv_lhs => rw [hA, hψ]
  exact boxLpConvectionTested_energyToLp4_smul E (v t) φ (η t)

/-- **Integrability of the physical convection integrand.**  No hypothesis: the tested
quadratic integrand is `L¹` by the Hölder pairing, and it differs from the physical one
only by a sign. -/
theorem integrable_convection_integrand {Time : Type*} [MeasurableSpace Time]
    {μ : Measure Time} (E : BoxEnergyL4Realization Q)
    (φ : OpenDomainH1ZeroSigma Ω) (η : Lp ℝ (∞ : ℝ≥0∞) μ)
    (v : Lp (OpenDomainH1ZeroSigma Ω) (2 : ℝ≥0∞) μ) :
    Integrable (fun t => convectionForm Ω E (v t) (v t) φ * η t) μ := by
  have hbase := integrable_trilinear_tensorSquare (boxLpConvectionTested (I := Q))
    ((energyToLp4 Ω E).compLpL 2 μ v) (gradientTestLp Ω φ η)
  have hneg : Integrable
      (fun t => -(convectionForm Ω E (v t) (v t) φ * η t)) μ :=
    hbase.congr (tested_integrand_ae E φ η v)
  simpa using hneg.neg

/-- The tested integral is minus the physical convection integral. -/
theorem integral_tested_eq_neg {Time : Type*} [MeasurableSpace Time]
    {μ : Measure Time} (E : BoxEnergyL4Realization Q)
    (φ : OpenDomainH1ZeroSigma Ω) (η : Lp ℝ (∞ : ℝ≥0∞) μ)
    (v : Lp (OpenDomainH1ZeroSigma Ω) (2 : ℝ≥0∞) μ) :
    (∫ t, boxLpConvectionTested
        (((energyToLp4 Ω E).compLpL 2 μ v) t)
        (((energyToLp4 Ω E).compLpL 2 μ v) t)
        ((gradientTestLp Ω φ η) t) ∂μ) =
      -∫ t, convectionForm Ω E (v t) (v t) φ * η t ∂μ := by
  rw [integral_congr_ae (tested_integrand_ae E φ η v)]
  exact integral_neg _

/-- **Strong `L²_t L⁴_x` convergence on the subdomain** from strong pivot convergence
and the uniform `L²_t V` bound, by two-dimensional Ladyzhenskaya interpolation. -/
theorem tendsto_energyToLp4_compLpL {Time : Type*} [MeasurableSpace Time]
    {μ : Measure Time} (L : BoxLadyzhenskayaRealization Q)
    (w : ℕ → Lp (OpenDomainH1ZeroSigma Ω) (2 : ℝ≥0∞) μ)
    (wLim : Lp (OpenDomainH1ZeroSigma Ω) (2 : ℝ≥0∞) μ)
    (R : ℝ) (hbound : ∀ k, ‖w k‖ ≤ R)
    (hstate : Tendsto (fun k => (energyToBoxState Ω).compLpL 2 μ (w k)) atTop
      (nhds ((energyToBoxState Ω).compLpL 2 μ wLim))) :
    Tendsto
      (fun k => (energyToLp4 Ω L.toBoxEnergyL4Realization).compLpL 2 μ (w k))
      atTop
      (nhds ((energyToLp4 Ω L.toBoxEnergyL4Realization).compLpL 2 μ wLim)) :=
  tendsto_compLpL_of_pointwise_interpolation
    (energyToLp4 Ω L.toBoxEnergyL4Realization) (energyToBoxState Ω)
    L.constant L.constant_nonneg (l4_sq_le L) w wLim R hbound hstate

/-- **Convergence of the tested subdomain convection term.**

Hypotheses: `L` is the two-dimensional Ladyzhenskaya realization of the ambient
rectangle; `w k` and `wLim` are square integrable in time with values in the subdomain
energy space; `R` bounds every `‖w k‖` in `L²_t V`; `hstate` is strong `L²_t H`
convergence of the pivot paths; `φ` is an arbitrary test field in the subdomain energy
space; `η` is an arbitrary bounded scalar time weight.  Nothing is assumed about the
convection term itself. -/
theorem tested_convection_tendsto {Time : Type*} [MeasurableSpace Time]
    {μ : Measure Time} (L : BoxLadyzhenskayaRealization Q)
    (w : ℕ → Lp (OpenDomainH1ZeroSigma Ω) (2 : ℝ≥0∞) μ)
    (wLim : Lp (OpenDomainH1ZeroSigma Ω) (2 : ℝ≥0∞) μ)
    (R : ℝ) (hbound : ∀ k, ‖w k‖ ≤ R)
    (hstate : Tendsto (fun k => (energyToBoxState Ω).compLpL 2 μ (w k)) atTop
      (nhds ((energyToBoxState Ω).compLpL 2 μ wLim)))
    (φ : OpenDomainH1ZeroSigma Ω) (η : Lp ℝ (∞ : ℝ≥0∞) μ) :
    Tendsto
      (fun k => ∫ t,
        convectionForm Ω L.toBoxEnergyL4Realization
          (w k t) (w k t) φ * η t ∂μ)
      atTop
      (nhds (∫ t,
        convectionForm Ω L.toBoxEnergyL4Realization
          (wLim t) (wLim t) φ * η t ∂μ)) := by
  have hA := tendsto_energyToLp4_compLpL L w wLim R hbound hstate
  have hbase := (strongMetricSubsequenceOfTendsto hA).projectiveTrilinearIntegral_tendsto
    (boxLpConvectionTested (I := Q)) (gradientTestLp Ω φ η)
  simp only [strongMetricSubsequenceOfTendsto_idx,
    strongMetricSubsequenceOfTendsto_limit] at hbase
  have hneg : Tendsto
      (fun k => -∫ t,
        convectionForm Ω L.toBoxEnergyL4Realization
          (w k t) (w k t) φ * η t ∂μ)
      atTop
      (nhds (-∫ t,
        convectionForm Ω L.toBoxEnergyL4Realization
          (wLim t) (wLim t) φ * η t ∂μ)) := by
    simpa only [integral_tested_eq_neg] using hbase
  simpa using hneg.neg

end OpenDomainConvectionLimit

end
