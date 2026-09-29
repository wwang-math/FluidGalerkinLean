import PDEIdeas.OpenDomainConvectionLimit
import PDEIdeas.LerayTimeTest

/-!
# Passing the tested Ω Galerkin equation to the limit (zero forcing)

`PDEIdeas.OpenDomainConvectionLimit` proves that the tested convection term of an
open subdomain `Ω ⊆ interior Q` of a plane rectangle converges along a sequence of
energy paths with a uniform `L²_t V` bound and strong `L²_t H` pivot convergence.
`PDEIdeas.LerayTimeTest` supplies the smooth time weights: an `IntervalTimeTest a b`
carries a value and a derivative on `[a, b]`, and a `LerayIntervalTimeTest a b`
additionally puts that derivative in `L²` of the interval measure.  This file runs
the two together and passes the whole tested Galerkin equation to the limit.

## The equation

For a test field `ψ` in the subdomain energy space and a smooth time weight `eta`,
the tested zero-forcing equation of a path `w` with initial state `u₀` reads

`-∫ ⟪J w(t), J ψ⟫ eta'(t) dt + ∫ D(w(t), ψ) eta(t) dt + ∫ b(w(t), w(t), ψ) eta(t) dt
    = ⟪u₀, J ψ⟫ eta(a)`

where `J` is the energy-to-state embedding of `Ω` read in the rectangle pivot space
(`OpenDomainConvectionLimit.energyToBoxState`), `D` is the gradient diffusion form of
the rectangle restricted to `Ω` (`diffusionForm`), and `b` is the physical convection
form of `Ω` (`OpenDomainPhysicalConvection.convectionForm`).  The three integrals are
`stateTestIntegral`, `diffusionTestIntegral` and `convectionTestIntegral`.

## What is proved

`tested_weak_equation_limit` takes the equation **at every level** of an `Ω` spectral
sequence, together with

* a uniform `L²_t V` bound `R` and a uniform `L²_t H` bound `Rs`;
* **strong `L²`-in-time pivot convergence** of the embedded state paths;
* **weak `L²`-in-time energy convergence** of the energy paths;
* convergence `ψ k → ψLim` of the level-admissible test fields to an arbitrary
  energy-space test field, and `u₀ k → u₀Lim` of the reconstructed initial states,

and concludes the same equation for the limit.  Nothing about the limit is assumed:
the four term limits are proved separately as `stateTestIntegral_tendsto`,
`diffusionTestIntegral_tendsto`, `convectionTestIntegral_tendsto` and
`initialPairing_tendsto`, and the assembly is uniqueness of limits.

## How each term is passed

* **time-derivative term** — strong pivot convergence, through the generic
  `bilinearIntegral_tendsto_of_weak` with the pivot inner product as the bilinear
  form and the time-derivative weight `eta.derivVectorLp` as the test path;
* **diffusion term** — weak energy convergence, through the same generic lemma with
  the restricted gradient diffusion form and the value weight `eta.valueLpCLM`;
* **convection term** — `OpenDomainConvectionLimit`: its Ladyzhenskaya interpolation
  `tendsto_energyToLp4_compLpL` upgrades strong pivot convergence plus the uniform
  energy bound to strong `L²_t L⁴_x` convergence, and its skew conversion
  `boxLpConvectionTested_energyToLp4_smul` identifies the tested `L⁴`–`L²`–`L⁴` form
  with minus the subdomain convection form; the projective tensor machinery of
  `PDEIdeas.QuadraticWeakFormLimit` then passes the quadratic integral with a
  simultaneously converging gradient test;
* **initial term** — joint continuity of the pivot inner product.

The varying test field is handled in every term: the generic lemma splits off
`A(e k, psi k - psiLim)` and bounds it by the uniform bound, and the convection term
uses the converging-test form of the tensor limit.

## Scope

Forcing is absent: the equation is the zero-forcing one.  A forcing term is **not**
included, because its limit is not proved here; `PDEIdeas.OpenDomainForcingEstimates`
supplies the pointwise absorption bound but no convergence statement for the forcing
integral, so adding a forcing term would amount to assuming what is to be proved.
Nothing here constructs Galerkin solutions, asserts their existence, or claims
anything about pointwise representatives of closure elements.
-/

open BoundedContinuousFunction Filter InnerProductSpace MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000


section ConstWeight

variable {Time : Type*} [MeasurableSpace Time] {μ : Measure Time}
    {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem toSpanSingleton_add {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (x y : E) :
    ContinuousLinearMap.toSpanSingleton ℝ (x + y) =
      ContinuousLinearMap.toSpanSingleton ℝ x +
        ContinuousLinearMap.toSpanSingleton ℝ y := by
  ext
  simp [ContinuousLinearMap.toSpanSingleton_apply, smul_add]

theorem toSpanSingleton_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (c : ℝ) (x : E) :
    ContinuousLinearMap.toSpanSingleton ℝ (c • x) =
      c • ContinuousLinearMap.toSpanSingleton ℝ x := by
  ext
  simp [ContinuousLinearMap.toSpanSingleton_apply, smul_comm]

/-- Multiplication of a fixed vector by a scalar `Lp` time path. -/
def constWeightCLM (η : Lp ℝ p μ) (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] : E →L[ℝ] Lp E p μ :=
  LinearMap.mkContinuous
    { toFun := fun x =>
        (ContinuousLinearMap.toSpanSingleton ℝ x).compLpL p μ η
      map_add' := by
        intro x y
        rw [toSpanSingleton_add, ContinuousLinearMap.add_compLpL]
        rfl
      map_smul' := by
        intro c x
        rw [toSpanSingleton_smul, ContinuousLinearMap.smul_compLpL]
        rfl }
    ‖η‖
    (by
      intro x
      change ‖(ContinuousLinearMap.toSpanSingleton ℝ x).compLpL p μ η‖ ≤ _
      calc
        ‖(ContinuousLinearMap.toSpanSingleton ℝ x).compLpL p μ η‖ ≤
            ‖(ContinuousLinearMap.toSpanSingleton ℝ x).compLpL p μ‖ * ‖η‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖ContinuousLinearMap.toSpanSingleton ℝ x‖ * ‖η‖ :=
          mul_le_mul_of_nonneg_right
            (ContinuousLinearMap.norm_compLpL_le _) (norm_nonneg _)
        _ = ‖η‖ * ‖x‖ := by
          rw [ContinuousLinearMap.norm_toSpanSingleton]
          ring)

@[simp]
theorem constWeightCLM_apply (η : Lp ℝ p μ) (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] (x : E) :
    constWeightCLM η E x =
      (ContinuousLinearMap.toSpanSingleton ℝ x).compLpL p μ η := rfl

theorem constWeightCLM_apply_ae (η : Lp ℝ p μ) (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] (x : E) :
    constWeightCLM η E x =ᵐ[μ] fun t => η t • x := by
  filter_upwards [(ContinuousLinearMap.toSpanSingleton ℝ x).coeFn_compLpL η]
    with t ht
  rw [constWeightCLM_apply, ht]
  rfl

end ConstWeight

section BilinearLimit

variable {Time : Type*} [MeasurableSpace Time] {μ : Measure Time}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem norm_lpPairing_le (A : V →L[ℝ] V →L[ℝ] ℝ)
    (f g : Lp V (2 : ℝ≥0∞) μ) :
    ‖A.lpPairing μ 2 2 f g‖ ≤ ‖A‖ * ‖f‖ * ‖g‖ := by
  let h : Lp ℝ (1 : ℝ≥0∞) μ := A.holder 1 f g
  calc
    ‖A.lpPairing μ 2 2 f g‖ = ‖∫ t, A (f t) (g t) ∂μ‖ := by
      rw [A.lpPairing_eq_integral]
    _ = ‖∫ t, h t ∂μ‖ := by
      congr 1
      exact integral_congr_ae (A.coeFn_holder f g).symm
    _ = ‖L1.integral h‖ := congrArg norm (L1.integral_eq_integral h).symm
    _ ≤ ‖h‖ := L1.norm_integral_le h
    _ ≤ ‖A‖ * ‖f‖ * ‖g‖ := A.norm_holder_apply_apply_le f g

theorem bilinearIntegral_tendsto_of_weak
    (A : V →L[ℝ] V →L[ℝ] ℝ)
    (e : ℕ → Lp V (2 : ℝ≥0∞) μ) (eLim : Lp V (2 : ℝ≥0∞) μ)
    (R : ℝ) (hR : ∀ k, ‖e k‖ ≤ R)
    (hweak : ∀ Λ : Lp V (2 : ℝ≥0∞) μ →L[ℝ] ℝ,
      Tendsto (fun k => Λ (e k)) atTop (nhds (Λ eLim)))
    (psi : ℕ → Lp V (2 : ℝ≥0∞) μ) (psiLim : Lp V (2 : ℝ≥0∞) μ)
    (hpsi : Tendsto psi atTop (nhds psiLim)) :
    Tendsto (fun k => ∫ t, A (e k t) (psi k t) ∂μ) atTop
      (nhds (∫ t, A (eLim t) (psiLim t) ∂μ)) := by
  set P := A.lpPairing μ 2 2 with hP
  have hmain : Tendsto (fun k => P (e k) psiLim) atTop
      (nhds (P eLim psiLim)) := hweak (P.flip psiLim)
  have hpsiNorm : Tendsto (fun k => ‖psi k - psiLim‖) atTop (nhds 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hpsi
  have herrorNorm : Tendsto
      (fun k => ‖P (e k) (psi k - psiLim)‖) atTop (nhds 0) := by
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun k => by
        calc
          ‖P (e k) (psi k - psiLim)‖ ≤ (‖A‖ * ‖e k‖) * ‖psi k - psiLim‖ :=
            norm_lpPairing_le A (e k) (psi k - psiLim)
          _ ≤ (‖A‖ * R) * ‖psi k - psiLim‖ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hR k) (norm_nonneg A))
              (norm_nonneg _))
    simpa using (tendsto_const_nhds.mul hpsiNorm)
  have herror : Tendsto (fun k => P (e k) (psi k - psiLim)) atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr herrorNorm
  have hsum := hmain.add herror
  have hpaired : Tendsto (fun k => P (e k) (psi k)) atTop
      (nhds (P eLim psiLim)) := by
    convert hsum using 1
    · funext k
      rw [map_sub]
      ring
    · simp
  simpa only [hP, A.lpPairing_eq_integral] using hpaired

theorem weak_of_tendsto
    {e : ℕ → Lp V (2 : ℝ≥0∞) μ} {eLim : Lp V (2 : ℝ≥0∞) μ}
    (he : Tendsto e atTop (nhds eLim)) :
    ∀ Λ : Lp V (2 : ℝ≥0∞) μ →L[ℝ] ℝ,
      Tendsto (fun k => Λ (e k)) atTop (nhds (Λ eLim)) :=
  fun Λ => (Λ.continuous.tendsto eLim).comp he

end BilinearLimit

/-! ### The open-domain weak-equation terms -/

namespace OpenDomainWeakEquationLimit

open OpenDomainPhysicalConvection

variable {Q : BoxIntegral.Box (Fin 2)} {Ω : OpenDomainInBox Q}

/-- The gradient of an embedded subdomain field. -/
def energyGradient (Ω : OpenDomainInBox Q) :
    OpenDomainH1ZeroSigma Ω →L[ℝ] BoxGradientL2 Q :=
  (boxEnergyGradient Q).comp (energyInclusion Ω)

@[simp]
theorem energyGradient_apply (v : OpenDomainH1ZeroSigma Ω) :
    energyGradient Ω v = boxEnergyGradient Q (energyInclusion Ω v) := rfl

/-- The gradient diffusion form of the rectangle restricted to the
subdomain energy space. -/
def diffusionForm (Ω : OpenDomainInBox Q) :
    OpenDomainH1ZeroSigma Ω →L[ℝ] OpenDomainH1ZeroSigma Ω →L[ℝ] ℝ :=
  (boxGradientDiffusion Q).bilinearCompSame (energyInclusion Ω)

@[simp]
theorem diffusionForm_apply (u v : OpenDomainH1ZeroSigma Ω) :
    diffusionForm Ω u v =
      boxGradientDiffusion Q (energyInclusion Ω u) (energyInclusion Ω v) := rfl

/-- The pivot-space inner product as a bounded bilinear form. -/
def stateInner (Q : BoxIntegral.Box (Fin 2)) :
    BoxL2Sigma Q →L[ℝ] BoxL2Sigma Q →L[ℝ] ℝ :=
  (isBoundedBilinearMap_inner (𝕜 := ℝ)).toContinuousLinearMap

@[simp]
theorem stateInner_apply (x y : BoxL2Sigma Q) :
    stateInner Q x y = ⟪x, y⟫_ℝ := rfl

variable {a b : ℝ}

/-- The time-derivative term of the tested equation. -/
def stateTestIntegral (eta : LerayIntervalTimeTest a b)
    (x : Lp (BoxL2Sigma Q) (2 : ℝ≥0∞)
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b))
    (g : BoxL2Sigma Q) : ℝ :=
  ∫ t, ⟪x t, g⟫_ℝ * eta.deriv t
    ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b

/-- The diffusion term of the tested equation. -/
def diffusionTestIntegral (Ω : OpenDomainInBox Q) (eta : IntervalTimeTest a b)
    (w : Lp (OpenDomainH1ZeroSigma Ω) (2 : ℝ≥0∞)
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b))
    (ψ : OpenDomainH1ZeroSigma Ω) : ℝ :=
  ∫ t, diffusionForm Ω (w t) ψ * eta.value t
    ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b

/-- The convection term of the tested equation. -/
def convectionTestIntegral (Ω : OpenDomainInBox Q) (E : BoxEnergyL4Realization Q)
    (eta : IntervalTimeTest a b)
    (w : Lp (OpenDomainH1ZeroSigma Ω) (2 : ℝ≥0∞)
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b))
    (ψ : OpenDomainH1ZeroSigma Ω) : ℝ :=
  ∫ t, convectionForm Ω E (w t) (w t) ψ * eta.value t
    ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b

/-! #### The three terms as bilinear space-time pairings -/

theorem stateTestIntegral_eq_pairing (eta : LerayIntervalTimeTest a b)
    (x : Lp (BoxL2Sigma Q) (2 : ℝ≥0∞)
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b))
    (g : BoxL2Sigma Q) :
    stateTestIntegral eta x g =
      ∫ t, stateInner Q (x t) ((eta.derivVectorLp (BoxL2Sigma Q) g) t)
        ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b := by
  refine (integral_congr_ae ?_).symm
  filter_upwards [eta.derivVectorLp_apply_ae (BoxL2Sigma Q) g] with t ht
  rw [stateInner_apply, ht]
  exact (real_inner_smul_right (x t) g (eta.deriv t)).trans (mul_comm _ _)

theorem diffusionTestIntegral_eq_pairing (eta : IntervalTimeTest a b)
    (w : Lp (OpenDomainH1ZeroSigma Ω) (2 : ℝ≥0∞)
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b))
    (ψ : OpenDomainH1ZeroSigma Ω) :
    diffusionTestIntegral Ω eta w ψ =
      ∫ t, diffusionForm Ω (w t)
          ((eta.valueLpCLM (OpenDomainH1ZeroSigma Ω) 2 ψ) t)
        ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b := by
  refine (integral_congr_ae ?_).symm
  filter_upwards [eta.valueLpCLM_apply_ae (OpenDomainH1ZeroSigma Ω) 2 ψ]
    with t ht
  rw [ht, map_smul]
  exact mul_comm _ _


/-! #### The state, diffusion and initial terms -/

theorem stateTestIntegral_tendsto (eta : LerayIntervalTimeTest a b)
    (x : ℕ → Lp (BoxL2Sigma Q) (2 : ℝ≥0∞)
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b))
    (xLim : Lp (BoxL2Sigma Q) (2 : ℝ≥0∞)
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b))
    (R : ℝ) (hR : ∀ k, ‖x k‖ ≤ R)
    (hx : Tendsto x atTop (nhds xLim))
    (g : ℕ → BoxL2Sigma Q) (gLim : BoxL2Sigma Q)
    (hg : Tendsto g atTop (nhds gLim)) :
    Tendsto (fun k => stateTestIntegral eta (x k) (g k)) atTop
      (nhds (stateTestIntegral eta xLim gLim)) := by
  have hpsi : Tendsto (fun k => eta.derivVectorLp (BoxL2Sigma Q) (g k)) atTop
      (nhds (eta.derivVectorLp (BoxL2Sigma Q) gLim)) :=
    ((constWeightCLM eta.derivLp (BoxL2Sigma Q)).continuous.tendsto gLim).comp hg
  have hbase := bilinearIntegral_tendsto_of_weak (stateInner Q) x xLim R hR
    (weak_of_tendsto hx) _ _ hpsi
  rw [stateTestIntegral_eq_pairing eta xLim gLim]
  exact hbase.congr fun k => (stateTestIntegral_eq_pairing eta (x k) (g k)).symm

theorem diffusionTestIntegral_tendsto (eta : IntervalTimeTest a b)
    (w : ℕ → Lp (OpenDomainH1ZeroSigma Ω) (2 : ℝ≥0∞)
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b))
    (wLim : Lp (OpenDomainH1ZeroSigma Ω) (2 : ℝ≥0∞)
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b))
    (R : ℝ) (hR : ∀ k, ‖w k‖ ≤ R)
    (hweak : ∀ Λ : Lp (OpenDomainH1ZeroSigma Ω) (2 : ℝ≥0∞)
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) →L[ℝ] ℝ,
      Tendsto (fun k => Λ (w k)) atTop (nhds (Λ wLim)))
    (ψ : ℕ → OpenDomainH1ZeroSigma Ω) (ψLim : OpenDomainH1ZeroSigma Ω)
    (hψ : Tendsto ψ atTop (nhds ψLim)) :
    Tendsto (fun k => diffusionTestIntegral Ω eta (w k) (ψ k)) atTop
      (nhds (diffusionTestIntegral Ω eta wLim ψLim)) := by
  have hpsi : Tendsto
      (fun k => eta.valueLpCLM (OpenDomainH1ZeroSigma Ω) 2 (ψ k)) atTop
      (nhds (eta.valueLpCLM (OpenDomainH1ZeroSigma Ω) 2 ψLim)) :=
    ((eta.valueLpCLM (OpenDomainH1ZeroSigma Ω) 2).continuous.tendsto ψLim).comp hψ
  have hbase := bilinearIntegral_tendsto_of_weak (diffusionForm Ω) w wLim R hR
    hweak _ _ hpsi
  rw [diffusionTestIntegral_eq_pairing eta wLim ψLim]
  exact hbase.congr fun k => (diffusionTestIntegral_eq_pairing eta (w k) (ψ k)).symm

theorem initialPairing_tendsto (eta : IntervalTimeTest a b)
    (u : ℕ → BoxL2Sigma Q) (uLim : BoxL2Sigma Q)
    (hu : Tendsto u atTop (nhds uLim))
    (g : ℕ → BoxL2Sigma Q) (gLim : BoxL2Sigma Q)
    (hg : Tendsto g atTop (nhds gLim)) :
    Tendsto (fun k => ⟪u k, g k⟫_ℝ * eta.value a) atTop
      (nhds (⟪uLim, gLim⟫_ℝ * eta.value a)) := by
  exact (hu.inner hg).mul tendsto_const_nhds

/-! #### The convection term through `OpenDomainConvectionLimit` -/

section Convection

local instance openDomainWeakEquationFactFour : Fact (1 ≤ (4 : ℝ≥0∞)) :=
  ⟨by norm_num⟩

theorem convection_tested_integral_eq (E : BoxEnergyL4Realization Q)
    (eta : IntervalTimeTest a b)
    (w : Lp (OpenDomainH1ZeroSigma Ω) (2 : ℝ≥0∞)
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b))
    (ψ : OpenDomainH1ZeroSigma Ω) :
    (∫ t, boxLpConvectionTested
        (((OpenDomainConvectionLimit.energyToLp4 Ω E).compLpL 2
          (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) w) t)
        (((OpenDomainConvectionLimit.energyToLp4 Ω E).compLpL 2
          (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) w) t)
        ((eta.valueLpCLM (BoxGradientL2 Q) ∞ (energyGradient Ω ψ)) t)
        ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) =
      -convectionTestIntegral Ω E eta w ψ := by
  have hae : (fun t => boxLpConvectionTested
        (((OpenDomainConvectionLimit.energyToLp4 Ω E).compLpL 2
          (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) w) t)
        (((OpenDomainConvectionLimit.energyToLp4 Ω E).compLpL 2
          (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) w) t)
        ((eta.valueLpCLM (BoxGradientL2 Q) ∞ (energyGradient Ω ψ)) t))
      =ᵐ[SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b]
        fun t => -(convectionForm Ω E (w t) (w t) ψ * eta.value t) := by
    filter_upwards
      [(OpenDomainConvectionLimit.energyToLp4 Ω E).coeFn_compLpL w,
        eta.valueLpCLM_apply_ae (BoxGradientL2 Q) ∞ (energyGradient Ω ψ)]
      with t hA hpsi
    conv_lhs => rw [hA, hpsi]
    exact OpenDomainConvectionLimit.boxLpConvectionTested_energyToLp4_smul
      E (w t) ψ (eta.value t)
  calc
    (∫ t, boxLpConvectionTested
        (((OpenDomainConvectionLimit.energyToLp4 Ω E).compLpL 2
          (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) w) t)
        (((OpenDomainConvectionLimit.energyToLp4 Ω E).compLpL 2
          (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) w) t)
        ((eta.valueLpCLM (BoxGradientL2 Q) ∞ (energyGradient Ω ψ)) t)
        ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) =
        ∫ t, -(convectionForm Ω E (w t) (w t) ψ * eta.value t)
          ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b :=
      integral_congr_ae hae
    _ = -∫ t, convectionForm Ω E (w t) (w t) ψ * eta.value t
          ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b :=
      integral_neg _
    _ = -convectionTestIntegral Ω E eta w ψ := rfl

theorem convectionTestIntegral_tendsto (L : BoxLadyzhenskayaRealization Q)
    (eta : IntervalTimeTest a b)
    (w : ℕ → Lp (OpenDomainH1ZeroSigma Ω) (2 : ℝ≥0∞)
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b))
    (wLim : Lp (OpenDomainH1ZeroSigma Ω) (2 : ℝ≥0∞)
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b))
    (R : ℝ) (hbound : ∀ k, ‖w k‖ ≤ R)
    (hstate : Tendsto
      (fun k => (OpenDomainConvectionLimit.energyToBoxState Ω).compLpL 2
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) (w k))
      atTop
      (nhds ((OpenDomainConvectionLimit.energyToBoxState Ω).compLpL 2
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) wLim)))
    (ψ : ℕ → OpenDomainH1ZeroSigma Ω) (ψLim : OpenDomainH1ZeroSigma Ω)
    (hψ : Tendsto ψ atTop (nhds ψLim)) :
    Tendsto
      (fun k => convectionTestIntegral Ω L.toBoxEnergyL4Realization eta
        (w k) (ψ k))
      atTop
      (nhds (convectionTestIntegral Ω L.toBoxEnergyL4Realization eta
        wLim ψLim)) := by
  have hA := OpenDomainConvectionLimit.tendsto_energyToLp4_compLpL L w wLim R
    hbound hstate
  have hpsi : Tendsto
      (fun k => eta.valueLpCLM (BoxGradientL2 Q) ∞ (energyGradient Ω (ψ k)))
      atTop
      (nhds (eta.valueLpCLM (BoxGradientL2 Q) ∞ (energyGradient Ω ψLim))) :=
    (((eta.valueLpCLM (BoxGradientL2 Q) ∞).comp
      (energyGradient Ω)).continuous.tendsto ψLim).comp hψ
  have hbase :=
    (strongMetricSubsequenceOfTendsto hA).projectiveTrilinearIntegral_tendsto_of_test_tendsto
      (boxLpConvectionTested (I := Q)) _ _ hpsi
  simp only [strongMetricSubsequenceOfTendsto_idx,
    strongMetricSubsequenceOfTendsto_limit] at hbase
  have hneg : Tendsto
      (fun k => -convectionTestIntegral Ω L.toBoxEnergyL4Realization eta
        (w k) (ψ k))
      atTop
      (nhds (-convectionTestIntegral Ω L.toBoxEnergyL4Realization eta
        wLim ψLim)) := by
    rw [← convection_tested_integral_eq
      L.toBoxEnergyL4Realization eta wLim ψLim]
    exact hbase.congr fun k => convection_tested_integral_eq
      L.toBoxEnergyL4Realization eta (w k) (ψ k)
  simpa using hneg.neg

end Convection


/-! ### The tested weak equation in the limit -/

set_option maxHeartbeats 8000000 in
/-- **The tested zero-forcing Galerkin equation passes to the limit.**

The hypotheses are the data of an `Ω` spectral sequence and nothing else:

* `w k` and `wLim` are square integrable in time with values in the subdomain
  energy space `H¹₀σ(Ω)`, `R` bounds every `‖w k‖` in `L²_t V`, and `Rs` bounds
  every embedded state path in `L²_t H`;
* `hstate` is **strong `L²`-in-time pivot convergence** of the embedded state
  paths;
* `hweak` is **weak `L²`-in-time energy convergence**: every continuous linear
  functional on `L²(I; H¹₀σ(Ω))` converges along the sequence;
* `ψ k → ψLim` in the energy space — the test fields admissible at each level,
  converging to an arbitrary energy-space test field;
* `u₀ k → u₀Lim` in the pivot space — the reconstructed initial states;
* `eta` is a smooth time weight (`LerayIntervalTimeTest`), so its value is
  continuous on `[a, b]` and its derivative is square integrable there;
* `hGalerkin` is the **tested Galerkin equation at each level**.

The conclusion is the same identity for the limit, with the limiting test
field and the limiting initial state.  No part of the conclusion is assumed:
`hGalerkin` is the finite-level equation, and every term limit is proved
(`stateTestIntegral_tendsto`, `diffusionTestIntegral_tendsto`,
`convectionTestIntegral_tendsto`, `initialPairing_tendsto`).

Forcing is absent: the equation is the zero-forcing one.  A forcing term is
not included because its limit is not proved here. -/
theorem tested_weak_equation_limit (L : BoxLadyzhenskayaRealization Q)
    (eta : LerayIntervalTimeTest a b)
    (w : ℕ → Lp (OpenDomainH1ZeroSigma Ω) (2 : ℝ≥0∞)
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b))
    (wLim : Lp (OpenDomainH1ZeroSigma Ω) (2 : ℝ≥0∞)
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b))
    (R : ℝ) (hbound : ∀ k, ‖w k‖ ≤ R)
    (Rs : ℝ) (hRs : ∀ k,
      ‖(OpenDomainConvectionLimit.energyToBoxState Ω).compLpL 2
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)
        (w k)‖ ≤ Rs)
    (hstate : Tendsto
      (fun k => (OpenDomainConvectionLimit.energyToBoxState Ω).compLpL 2
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) (w k))
      atTop
      (nhds ((OpenDomainConvectionLimit.energyToBoxState Ω).compLpL 2
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) wLim)))
    (hweak : ∀ Λ : Lp (OpenDomainH1ZeroSigma Ω) (2 : ℝ≥0∞)
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) →L[ℝ] ℝ,
      Tendsto (fun k => Λ (w k)) atTop (nhds (Λ wLim)))
    (ψ : ℕ → OpenDomainH1ZeroSigma Ω) (ψLim : OpenDomainH1ZeroSigma Ω)
    (hψ : Tendsto ψ atTop (nhds ψLim))
    (u₀ : ℕ → BoxL2Sigma Q) (u₀Lim : BoxL2Sigma Q)
    (hu₀ : Tendsto u₀ atTop (nhds u₀Lim))
    (hGalerkin : ∀ k,
      -stateTestIntegral eta
          ((OpenDomainConvectionLimit.energyToBoxState Ω).compLpL 2
            (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)
            (w k))
          (OpenDomainConvectionLimit.energyToBoxState Ω (ψ k)) +
        diffusionTestIntegral Ω eta.toIntervalTimeTest (w k) (ψ k) +
        convectionTestIntegral Ω L.toBoxEnergyL4Realization
          eta.toIntervalTimeTest (w k) (ψ k) =
      ⟪u₀ k, OpenDomainConvectionLimit.energyToBoxState Ω (ψ k)⟫_ℝ *
        eta.value a) :
    -stateTestIntegral eta
        ((OpenDomainConvectionLimit.energyToBoxState Ω).compLpL 2
          (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) wLim)
        (OpenDomainConvectionLimit.energyToBoxState Ω ψLim) +
      diffusionTestIntegral Ω eta.toIntervalTimeTest wLim ψLim +
      convectionTestIntegral Ω L.toBoxEnergyL4Realization
        eta.toIntervalTimeTest wLim ψLim =
    ⟪u₀Lim, OpenDomainConvectionLimit.energyToBoxState Ω ψLim⟫_ℝ *
      eta.value a := by
  have hg : Tendsto
      (fun k => OpenDomainConvectionLimit.energyToBoxState Ω (ψ k)) atTop
      (nhds (OpenDomainConvectionLimit.energyToBoxState Ω ψLim)) :=
    ((OpenDomainConvectionLimit.energyToBoxState Ω).continuous.tendsto
      ψLim).comp hψ
  have hstateTerm := stateTestIntegral_tendsto eta
    (fun k => (OpenDomainConvectionLimit.energyToBoxState Ω).compLpL 2
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) (w k))
    ((OpenDomainConvectionLimit.energyToBoxState Ω).compLpL 2
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) wLim)
    Rs hRs hstate
    (fun k => OpenDomainConvectionLimit.energyToBoxState Ω (ψ k))
    (OpenDomainConvectionLimit.energyToBoxState Ω ψLim) hg
  have hdiffTerm := diffusionTestIntegral_tendsto eta.toIntervalTimeTest
    w wLim R hbound hweak ψ ψLim hψ
  have hconvTerm := convectionTestIntegral_tendsto L eta.toIntervalTimeTest
    w wLim R hbound hstate ψ ψLim hψ
  have hinitTerm := initialPairing_tendsto eta.toIntervalTimeTest
    u₀ u₀Lim hu₀
    (fun k => OpenDomainConvectionLimit.energyToBoxState Ω (ψ k))
    (OpenDomainConvectionLimit.energyToBoxState Ω ψLim) hg
  have hLHS := (hstateTerm.neg.add hdiffTerm).add hconvTerm
  exact tendsto_nhds_unique (hLHS.congr hGalerkin) hinitTerm

end OpenDomainWeakEquationLimit
