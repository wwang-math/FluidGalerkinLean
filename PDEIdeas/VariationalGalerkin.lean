import PDEIdeas.GalerkinScalarAbsorption
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Real MeasureTheory intervalIntegral InnerProductSpace Set Metric Filter
open scoped BigOperators ENNReal NNReal

noncomputable section

/-!
# Finite-dimensional variational Galerkin systems

The diffusion and transport terms are forms on the Galerkin space itself.
Riesz representation turns their sum into the coefficient ODE vector field.
This avoids treating the unbounded Stokes operator or NSE convection as
bounded operators on the ambient energy Hilbert space.
-/

/-- Variational forms restricted to one finite-dimensional Galerkin space. -/
structure VariationalGalerkinSystem
    (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℝ W] where
  diffusion : W →L[ℝ] W →L[ℝ] ℝ
  convection : W →L[ℝ] W →L[ℝ] W →L[ℝ] ℝ
  convectionBound : ℝ
  convectionBound_nonneg : 0 ≤ convectionBound
  convection_norm_le :
    ∀ u v : W, ‖convection u v‖ ≤ convectionBound * ‖u‖ * ‖v‖
  diffusion_nonneg : ∀ u : W, 0 ≤ diffusion u u
  convection_skew :
    ∀ u v w : W, convection u v w = -convection u w v

namespace VariationalGalerkinSystem

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

theorem convection_cancel (S : VariationalGalerkinSystem W) (u : W) :
    S.convection u u u = 0 := by
  have h := S.convection_skew u u u
  linarith

end VariationalGalerkinSystem

/-- A finite-dimensional variational Galerkin initial-value problem. -/
structure VariationalGalerkinProblem
    (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℝ W] where
  system : VariationalGalerkinSystem W
  forcing : ℝ → W →L[ℝ] ℝ
  initial : W

namespace VariationalGalerkinProblem

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [CompleteSpace W]

/-- The weak right-hand side as a functional on the Galerkin test space. -/
def weakRHS (P : VariationalGalerkinProblem W) (t : ℝ) (u : W) :
    W →L[ℝ] ℝ :=
  -P.system.diffusion u - P.system.convection u u + P.forcing t

/-- Riesz representative of the variational right-hand side. -/
def rhs (P : VariationalGalerkinProblem W) (t : ℝ) (u : W) : W :=
  (InnerProductSpace.toDual ℝ W).symm (P.weakRHS t u)

/-- The coefficient vector field represents the variational equation against
every Galerkin test vector. -/
theorem inner_rhs (P : VariationalGalerkinProblem W) (t : ℝ) (u v : W) :
    ⟪P.rhs t u, v⟫_ℝ =
      -P.system.diffusion u v - P.system.convection u u v + P.forcing t v := by
  rw [rhs, InnerProductSpace.toDual_symm_apply]
  rfl

omit [CompleteSpace W] in
/-- The forcing cancels from state differences of the weak right-hand side. -/
theorem weakRHS_sub (P : VariationalGalerkinProblem W) (t : ℝ) (u v : W) :
    P.weakRHS t u - P.weakRHS t v =
      -P.system.diffusion (u - v)
        - (P.system.convection (u - v) u + P.system.convection v (u - v)) := by
  ext w
  simp [weakRHS, map_sub]
  ring

/-- Riesz representation preserves the norm of the weak right-hand side. -/
theorem norm_rhs (P : VariationalGalerkinProblem W) (t : ℝ) (u : W) :
    ‖P.rhs t u‖ = ‖P.weakRHS t u‖ := by
  exact (InnerProductSpace.toDual ℝ W).symm.norm_map (P.weakRHS t u)

theorem norm_rhs_sub (P : VariationalGalerkinProblem W) (t : ℝ) (u v : W) :
    ‖P.rhs t u - P.rhs t v‖ = ‖P.weakRHS t u - P.weakRHS t v‖ := by
  change ‖(InnerProductSpace.toDual ℝ W).symm (P.weakRHS t u) -
      (InnerProductSpace.toDual ℝ W).symm (P.weakRHS t v)‖ = _
  rw [← map_sub]
  exact (InnerProductSpace.toDual ℝ W).symm.norm_map
    (P.weakRHS t u - P.weakRHS t v)

/-- Pointwise norm bound for the Riesz-represented variational vector field. -/
theorem rhs_norm_le (P : VariationalGalerkinProblem W) (t : ℝ) (u : W) :
    ‖P.rhs t u‖ ≤
      ‖P.system.diffusion‖ * ‖u‖
        + P.system.convectionBound * ‖u‖ ^ 2
        + ‖P.forcing t‖ := by
  rw [P.norm_rhs]
  calc
    ‖P.weakRHS t u‖
        ≤ ‖P.system.diffusion u‖ + ‖P.system.convection u u‖
            + ‖P.forcing t‖ := by
          have htri :
              ‖(-P.system.diffusion u) + (-P.system.convection u u) + P.forcing t‖
                ≤ ‖P.system.diffusion u‖ + ‖P.system.convection u u‖
                    + ‖P.forcing t‖ := by
            simpa using (norm_add₃_le :
              ‖(-P.system.diffusion u) + (-P.system.convection u u) + P.forcing t‖
                ≤ ‖-P.system.diffusion u‖ + ‖-P.system.convection u u‖
                    + ‖P.forcing t‖)
          simpa [weakRHS, sub_eq_add_neg] using htri
    _ ≤ (‖P.system.diffusion‖ * ‖u‖)
          + (P.system.convectionBound * ‖u‖ * ‖u‖)
          + ‖P.forcing t‖ := by
          gcongr
          · exact P.system.diffusion.le_opNorm u
          · exact P.system.convection_norm_le u u
    _ = ‖P.system.diffusion‖ * ‖u‖
          + P.system.convectionBound * ‖u‖ ^ 2
          + ‖P.forcing t‖ := by ring

/-- Bounded-set local Lipschitz estimate for the finite-dimensional
variational coefficient field. -/
theorem rhs_lipschitz_on_norm_ball
    (P : VariationalGalerkinProblem W)
    (R : ℝ)
    (t : ℝ) {u v : W} (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R) :
    ‖P.rhs t u - P.rhs t v‖ ≤
      (‖P.system.diffusion‖ + 2 * P.system.convectionBound * R) * ‖u - v‖ := by
  rw [P.norm_rhs_sub, P.weakRHS_sub]
  calc
    ‖-P.system.diffusion (u - v) -
          (P.system.convection (u - v) u + P.system.convection v (u - v))‖
        ≤ ‖P.system.diffusion (u - v)‖
          + ‖P.system.convection (u - v) u‖
          + ‖P.system.convection v (u - v)‖ := by
            calc
              ‖-P.system.diffusion (u - v) -
                    (P.system.convection (u - v) u +
                      P.system.convection v (u - v))‖
                  ≤ ‖-P.system.diffusion (u - v)‖
                    + ‖P.system.convection (u - v) u +
                        P.system.convection v (u - v)‖ := norm_sub_le _ _
              _ ≤ ‖-P.system.diffusion (u - v)‖
                    + (‖P.system.convection (u - v) u‖
                      + ‖P.system.convection v (u - v)‖) := by
                    gcongr
                    exact norm_add_le _ _
              _ = ‖P.system.diffusion (u - v)‖
                    + ‖P.system.convection (u - v) u‖
                    + ‖P.system.convection v (u - v)‖ := by
                    rw [norm_neg]
                    ring
    _ ≤ ‖P.system.diffusion‖ * ‖u - v‖
          + (P.system.convectionBound * ‖u - v‖) * ‖u‖
          + (P.system.convectionBound * ‖v‖) * ‖u - v‖ := by
            gcongr
            · exact P.system.diffusion.le_opNorm (u - v)
            · exact P.system.convection_norm_le (u - v) u
            · exact P.system.convection_norm_le v (u - v)
    _ ≤ ‖P.system.diffusion‖ * ‖u - v‖
          + (P.system.convectionBound * ‖u - v‖) * R
          + (P.system.convectionBound * R) * ‖u - v‖ := by
            gcongr
            · exact mul_nonneg P.system.convectionBound_nonneg (norm_nonneg _)
            · exact P.system.convectionBound_nonneg
    _ = (‖P.system.diffusion‖ + 2 * P.system.convectionBound * R) * ‖u - v‖ := by
          ring

/-- Canonical norm radius containing a Picard ball around the initial state. -/
def stateNormRadius (P : VariationalGalerkinProblem W) (a : ℝ≥0) : ℝ :=
  ‖P.initial‖ + a

omit [CompleteSpace W] in
theorem norm_le_stateNormRadius_of_mem_closedBall
    (P : VariationalGalerkinProblem W) (a : ℝ≥0) {u : W}
    (hu : u ∈ closedBall P.initial a) :
    ‖u‖ ≤ P.stateNormRadius a := by
  have hdist : ‖u - P.initial‖ ≤ (a : ℝ) := by
    simpa [dist_eq_norm] using (mem_closedBall.mp hu)
  have hbase := norm_le_norm_add_norm_sub' u P.initial
  change ‖u‖ ≤ ‖P.initial‖ + (a : ℝ)
  linarith

omit [CompleteSpace W] in
theorem stateNormRadius_nonneg
    (P : VariationalGalerkinProblem W) (a : ℝ≥0) :
    0 ≤ P.stateNormRadius a := by
  exact add_nonneg (norm_nonneg _) a.property

/-- Lipschitz constant on the norm ball used by Picard--Lindelöf. -/
def rhsLipschitzConstant
    (P : VariationalGalerkinProblem W) (R : ℝ) (hR : 0 ≤ R) : ℝ≥0 :=
  ⟨‖P.system.diffusion‖ + 2 * P.system.convectionBound * R,
    add_nonneg P.system.diffusion.opNorm_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) P.system.convectionBound_nonneg) hR)⟩

/-- Uniform RHS bound on a state norm ball and a forcing norm ball. -/
def rhsNormBound
    (P : VariationalGalerkinProblem W)
    (M R : ℝ) (hM : 0 ≤ M) (hR : 0 ≤ R) : ℝ≥0 :=
  ⟨‖P.system.diffusion‖ * R + P.system.convectionBound * R ^ 2 + M,
    add_nonneg
      (add_nonneg
        (mul_nonneg P.system.diffusion.opNorm_nonneg hR)
        (mul_nonneg P.system.convectionBound_nonneg (sq_nonneg R))) hM⟩

theorem rhs_norm_le_rhsNormBound
    (P : VariationalGalerkinProblem W)
    (M R : ℝ) (hM : 0 ≤ M) (hR : 0 ≤ R)
    {u : W} (hu : ‖u‖ ≤ R) (t : ℝ)
    (hFt : ‖P.forcing t‖ ≤ M) :
    ‖P.rhs t u‖ ≤ P.rhsNormBound M R hM hR := by
  calc
    ‖P.rhs t u‖
        ≤ ‖P.system.diffusion‖ * ‖u‖
          + P.system.convectionBound * ‖u‖ ^ 2
          + ‖P.forcing t‖ := P.rhs_norm_le t u
    _ ≤ ‖P.system.diffusion‖ * R
          + P.system.convectionBound * R ^ 2 + M := by
          have hdiff :
              ‖P.system.diffusion‖ * ‖u‖ ≤ ‖P.system.diffusion‖ * R :=
            mul_le_mul_of_nonneg_left hu P.system.diffusion.opNorm_nonneg
          have hsq : ‖u‖ ^ 2 ≤ R ^ 2 :=
            (sq_le_sq₀ (norm_nonneg u) hR).2 hu
          have hconv :
              P.system.convectionBound * ‖u‖ ^ 2
                ≤ P.system.convectionBound * R ^ 2 :=
            mul_le_mul_of_nonneg_left hsq P.system.convectionBound_nonneg
          exact add_le_add (add_le_add hdiff hconv) hFt
    _ = P.rhsNormBound M R hM hR := rfl

/-- Continuity in time of the variational coefficient field follows from
continuity of the forcing in the finite-space dual norm. -/
theorem continuous_rhs_time
    (P : VariationalGalerkinProblem W)
    (hF : Continuous P.forcing) (u : W) :
    Continuous (fun t => P.rhs t u) := by
  unfold rhs weakRHS
  fun_prop

/-- Picard--Lindelöf data for the variational coefficient field. -/
def IsPicardLindelofAt
    (P : VariationalGalerkinProblem W)
    {tmin tmax : ℝ}
    (t₀ : Icc tmin tmax)
    (a L K : ℝ≥0) : Prop :=
  IsPicardLindelof (fun (t : ℝ) (u : W) => P.rhs t u) t₀
    P.initial a 0 L K

/-- Continuous forcing and explicit interval bounds discharge every analytic
Picard--Lindelöf field for the finite variational system. -/
theorem isPicardLindelofAt
    (P : VariationalGalerkinProblem W)
    {tmin tmax : ℝ}
    (t₀ : Icc tmin tmax)
    (hFcont : Continuous P.forcing)
    (M : ℝ) (hM : 0 ≤ M)
    (hFbound : ∀ t ∈ Icc tmin tmax, ‖P.forcing t‖ ≤ M)
    (a : ℝ≥0)
    (hSmall :
      (P.rhsNormBound M (P.stateNormRadius a) hM
          (P.stateNormRadius_nonneg a) : ℝ) *
          max (tmax - (t₀ : ℝ)) ((t₀ : ℝ) - tmin) ≤ (a : ℝ)) :
    P.IsPicardLindelofAt t₀ a
      (P.rhsNormBound M (P.stateNormRadius a) hM
        (P.stateNormRadius_nonneg a))
      (P.rhsLipschitzConstant (P.stateNormRadius a)
        (P.stateNormRadius_nonneg a)) := by
  let R := P.stateNormRadius a
  let L := P.rhsNormBound M R hM (P.stateNormRadius_nonneg a)
  let K := P.rhsLipschitzConstant R (P.stateNormRadius_nonneg a)
  refine {
    lipschitzOnWith := ?_
    continuousOn := ?_
    norm_le := ?_
    mul_max_le := ?_
  }
  · intro t _ht
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro u hu v hv
    have huR : ‖u‖ ≤ R := P.norm_le_stateNormRadius_of_mem_closedBall a hu
    have hvR : ‖v‖ ≤ R := P.norm_le_stateNormRadius_of_mem_closedBall a hv
    simpa [K, rhsLipschitzConstant, dist_eq_norm] using
      P.rhs_lipschitz_on_norm_ball R t huR hvR
  · intro u _hu
    exact (P.continuous_rhs_time hFcont u).continuousOn
  · intro t ht u hu
    have huR : ‖u‖ ≤ R := P.norm_le_stateNormRadius_of_mem_closedBall a hu
    simpa [L] using
      P.rhs_norm_le_rhsNormBound M R hM (P.stateNormRadius_nonneg a)
        huR t (hFbound t ht)
  · simpa [L] using hSmall

/-- A coefficient trajectory solving the variational Galerkin ODE on a closed
time interval. -/
structure LocalSolutionOn
    (P : VariationalGalerkinProblem W)
    {tmin tmax : ℝ}
    (t₀ : Icc tmin tmax) where
  toFun : ℝ → W
  initial : toFun t₀ = P.initial
  hasDerivWithinAt :
    ∀ t ∈ Icc tmin tmax,
      HasDerivWithinAt toFun (P.rhs t (toFun t)) (Icc tmin tmax) t

/-- Local existence for the finite variational coefficient system. -/
theorem exists_localSolutionOn_of_isPicardLindelof
    (P : VariationalGalerkinProblem W)
    {tmin tmax : ℝ}
    (t₀ : Icc tmin tmax)
    {a L K : ℝ≥0}
    (hPL : P.IsPicardLindelofAt t₀ a L K) :
    Nonempty (P.LocalSolutionOn t₀) := by
  obtain ⟨u, hu0, huderiv⟩ :=
    hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨{
    toFun := u
    initial := hu0
    hasDerivWithinAt := huderiv
  }⟩

/-- Direct local-existence constructor from continuous bounded forcing and
the explicit Picard interval inequality. -/
theorem exists_localSolutionOn
    (P : VariationalGalerkinProblem W)
    {tmin tmax : ℝ}
    (t₀ : Icc tmin tmax)
    (hFcont : Continuous P.forcing)
    (M : ℝ) (hM : 0 ≤ M)
    (hFbound : ∀ t ∈ Icc tmin tmax, ‖P.forcing t‖ ≤ M)
    (a : ℝ≥0)
    (hSmall :
      (P.rhsNormBound M (P.stateNormRadius a) hM
          (P.stateNormRadius_nonneg a) : ℝ) *
          max (tmax - (t₀ : ℝ)) ((t₀ : ℝ) - tmin) ≤ (a : ℝ)) :
    Nonempty (P.LocalSolutionOn t₀) :=
  P.exists_localSolutionOn_of_isPicardLindelof t₀
    (P.isPicardLindelofAt t₀ hFcont M hM hFbound a hSmall)

/-- The same variational problem restarted from a new coefficient state. -/
def withInitial (P : VariationalGalerkinProblem W) (x : W) :
    VariationalGalerkinProblem W where
  system := P.system
  forcing := P.forcing
  initial := x

omit [CompleteSpace W] in
@[simp] theorem withInitial_system
    (P : VariationalGalerkinProblem W) (x : W) :
    (P.withInitial x).system = P.system := rfl

omit [CompleteSpace W] in
@[simp] theorem withInitial_forcing
    (P : VariationalGalerkinProblem W) (x : W) :
    (P.withInitial x).forcing = P.forcing := rfl

omit [CompleteSpace W] in
@[simp] theorem withInitial_initial
    (P : VariationalGalerkinProblem W) (x : W) :
    (P.withInitial x).initial = x := rfl

@[simp] theorem withInitial_rhs
    (P : VariationalGalerkinProblem W) (x : W) (t : ℝ) (u : W) :
    (P.withInitial x).rhs t u = P.rhs t u := rfl

/-- Uniform local extension from every state in a fixed energy ball.  The
Picard time depends only on the common state and forcing bounds, not on the
particular restart state. -/
theorem exists_restartSolutionOn_of_state_bound
    (P : VariationalGalerkinProblem W)
    {tmin tmax : ℝ}
    (t₀ : Icc tmin tmax)
    (hFcont : Continuous P.forcing)
    (M R₀ : ℝ) (hM : 0 ≤ M) (hR₀ : 0 ≤ R₀)
    (hFbound : ∀ t ∈ Icc tmin tmax, ‖P.forcing t‖ ≤ M)
    (a : ℝ≥0)
    (hSmall :
      (‖P.system.diffusion‖ * (R₀ + (a : ℝ))
          + P.system.convectionBound * (R₀ + (a : ℝ)) ^ 2 + M) *
          max (tmax - (t₀ : ℝ)) ((t₀ : ℝ) - tmin) ≤ (a : ℝ))
    {x : W} (hx : ‖x‖ ≤ R₀) :
    Nonempty ((P.withInitial x).LocalSolutionOn t₀) := by
  let R : ℝ := R₀ + (a : ℝ)
  have hR : 0 ≤ R := add_nonneg hR₀ a.property
  have hxRadius : (P.withInitial x).stateNormRadius a ≤ R := by
    simp only [stateNormRadius, withInitial_initial, R]
    linarith
  have hxRadius_nonneg : 0 ≤ (P.withInitial x).stateNormRadius a :=
    (P.withInitial x).stateNormRadius_nonneg a
  have hsq : ((P.withInitial x).stateNormRadius a) ^ 2 ≤ R ^ 2 :=
    (sq_le_sq₀ hxRadius_nonneg hR).2 hxRadius
  have hBound :
      ((P.withInitial x).rhsNormBound M
          ((P.withInitial x).stateNormRadius a) hM hxRadius_nonneg : ℝ)
        ≤ ‖P.system.diffusion‖ * R
          + P.system.convectionBound * R ^ 2 + M := by
    change
      ‖P.system.diffusion‖ * (P.withInitial x).stateNormRadius a
          + P.system.convectionBound * ((P.withInitial x).stateNormRadius a) ^ 2 + M
        ≤ ‖P.system.diffusion‖ * R
          + P.system.convectionBound * R ^ 2 + M
    have hbase :=
      add_le_add
        (mul_le_mul_of_nonneg_left hxRadius P.system.diffusion.opNorm_nonneg)
        (mul_le_mul_of_nonneg_left hsq P.system.convectionBound_nonneg)
    linarith
  have htime :
      0 ≤ max (tmax - (t₀ : ℝ)) ((t₀ : ℝ) - tmin) := by
    exact le_max_of_le_left (sub_nonneg.mpr t₀.property.2)
  have hSmall' :
      ((P.withInitial x).rhsNormBound M
          ((P.withInitial x).stateNormRadius a) hM hxRadius_nonneg : ℝ) *
          max (tmax - (t₀ : ℝ)) ((t₀ : ℝ) - tmin) ≤ (a : ℝ) := by
    exact (mul_le_mul_of_nonneg_right hBound htime).trans (by simpa [R] using hSmall)
  exact (P.withInitial x).exists_localSolutionOn t₀
    (by simpa using hFcont) M hM (by simpa using hFbound) a hSmall'

/-- Adjacent coefficient solutions with the same junction value concatenate
to a solution on the union interval.  At the junction, the matching left and
right derivatives combine by differentiability within a union. -/
theorem LocalSolutionOn.concat
    {P : VariationalGalerkinProblem W}
    {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c)
    (u : P.LocalSolutionOn (⟨a, le_rfl, hab⟩ : Icc a b))
    (v : (P.withInitial (u.toFun b)).LocalSolutionOn
      (⟨b, le_rfl, hbc⟩ : Icc b c)) :
    Nonempty (P.LocalSolutionOn
      (⟨a, le_rfl, hab.trans hbc⟩ : Icc a c)) := by
  let w : ℝ → W := fun t => if t ≤ b then u.toFun t else v.toFun t
  have hv_initial : v.toFun b = u.toFun b := by
    simpa using v.initial
  refine ⟨{
    toFun := w
    initial := ?_
    hasDerivWithinAt := ?_
  }⟩
  · simpa [w, hab] using u.initial
  · intro t ht
    rcases lt_trichotomy t b with htb | htb | hbt
    · have hut := u.hasDerivWithinAt t ⟨ht.1, htb.le⟩
      have hsets : Icc a b =ᶠ[nhds t] Icc a c := by
        filter_upwards [Iic_mem_nhds htb] with x hxb
        apply propext
        change (a ≤ x ∧ x ≤ b) ↔ (a ≤ x ∧ x ≤ c)
        constructor
        · intro hx
          exact ⟨hx.1, hx.2.trans hbc⟩
        · intro hx
          exact ⟨hx.1, hxb⟩
      have hut' :
          HasDerivWithinAt u.toFun (P.rhs t (u.toFun t)) (Icc a c) t :=
        hut.congr_set hsets
      have hwu : w =ᶠ[nhds t] u.toFun := by
        filter_upwards [Iic_mem_nhds htb] with x hxb
        have hxb' : x ≤ b := hxb
        simp [w, hxb']
      simpa [w, htb.le] using
        hut'.congr_of_eventuallyEq (hwu.filter_mono inf_le_left)
          (by simp [w, htb.le])
    · subst t
      have hu := u.hasDerivWithinAt b ⟨hab, le_rfl⟩
      have hv := v.hasDerivWithinAt b ⟨le_rfl, hbc⟩
      have hwu : w =ᶠ[nhdsWithin b (Icc a b)] u.toFun := by
        filter_upwards [self_mem_nhdsWithin] with x hx
        simp [w, hx.2]
      have hwv : w =ᶠ[nhdsWithin b (Icc b c)] v.toFun := by
        filter_upwards [self_mem_nhdsWithin] with x hx
        by_cases hxb : x ≤ b
        · have hxeq : x = b := le_antisymm hxb hx.1
          subst x
          simp [w, hv_initial]
        · simp [w, hxb]
      have hleft :
          HasDerivWithinAt w (P.rhs b (w b)) (Icc a b) b := by
        simpa [w] using hu.congr_of_eventuallyEq hwu (by simp [w])
      have hright :
          HasDerivWithinAt w (P.rhs b (w b)) (Icc b c) b := by
        have hv' :
            HasDerivWithinAt v.toFun (P.rhs b (v.toFun b)) (Icc b c) b := by
          simpa using hv
        simpa [w, hv_initial] using
          hv'.congr_of_eventuallyEq hwv (by simp [w, hv_initial])
      rw [← Icc_union_Icc_eq_Icc hab hbc]
      exact hleft.union hright
    · have hvt := v.hasDerivWithinAt t ⟨hbt.le, ht.2⟩
      have hvt' :
          HasDerivWithinAt v.toFun (P.rhs t (v.toFun t)) (Icc b c) t := by
        simpa using hvt
      have hsets : Icc b c =ᶠ[nhds t] Icc a c := by
        filter_upwards [Ici_mem_nhds hbt] with x hbx
        apply propext
        change (b ≤ x ∧ x ≤ c) ↔ (a ≤ x ∧ x ≤ c)
        constructor
        · intro hx
          exact ⟨hab.trans hx.1, hx.2⟩
        · intro hx
          exact ⟨hbx, hx.2⟩
      have hvt'' :
          HasDerivWithinAt v.toFun (P.rhs t (v.toFun t)) (Icc a c) t :=
        hvt'.congr_set hsets
      have hwv : w =ᶠ[nhds t] v.toFun := by
        filter_upwards [Ici_mem_nhds hbt] with x hbx
        have hbx' : b ≤ x := hbx
        by_cases hxb : x ≤ b
        · have hxeq : x = b := le_antisymm hxb hbx'
          subst x
          simp [w, hv_initial]
        · simp [w, hxb]
      simpa [w, not_le.mpr hbt] using
        hvt''.congr_of_eventuallyEq (hwv.filter_mono inf_le_left)
          (by simp [w, not_le.mpr hbt])

/-- Every coefficient solution is continuous on its defining interval. -/
theorem LocalSolutionOn.continuousOn
    {P : VariationalGalerkinProblem W}
    {tmin tmax : ℝ}
    {t₀ : Icc tmin tmax}
    (u : P.LocalSolutionOn t₀) :
    ContinuousOn u.toFun (Icc tmin tmax) :=
  HasDerivWithinAt.continuousOn u.hasDerivWithinAt

/-- Diffusion energy is automatically integrable on each ordered subinterval
of a coefficient solution. -/
theorem LocalSolutionOn.diffusion_intervalIntegrable
    {P : VariationalGalerkinProblem W}
    {tmin tmax : ℝ}
    {t₀ : Icc tmin tmax}
    (u : P.LocalSolutionOn t₀)
    {a b : ℝ}
    (ha : a ∈ Icc tmin tmax)
    (hb : b ∈ Icc tmin tmax)
    (hab : a ≤ b) :
    IntervalIntegrable
      (fun s => P.system.diffusion (u.toFun s) (u.toFun s)) volume a b := by
  have hsub : Icc a b ⊆ Icc tmin tmax := by
    intro s hs
    exact ⟨le_trans ha.1 hs.1, le_trans hs.2 hb.2⟩
  have hu : ContinuousOn u.toFun (Icc a b) := u.continuousOn.mono hsub
  have hdiff : ContinuousOn
      (fun s => P.system.diffusion (u.toFun s) (u.toFun s)) (Icc a b) :=
    P.system.diffusion.continuous₂.comp_continuousOn (hu.prodMk hu)
  exact ContinuousOn.intervalIntegrable_of_Icc hab hdiff

/-- Dual forcing work is automatically integrable when the forcing is
continuous in the finite-space dual norm. -/
theorem LocalSolutionOn.forcing_intervalIntegrable
    {P : VariationalGalerkinProblem W}
    {tmin tmax : ℝ}
    {t₀ : Icc tmin tmax}
    (u : P.LocalSolutionOn t₀)
    (hFcont : Continuous P.forcing)
    {a b : ℝ}
    (ha : a ∈ Icc tmin tmax)
    (hb : b ∈ Icc tmin tmax)
    (hab : a ≤ b) :
    IntervalIntegrable (fun s => P.forcing s (u.toFun s)) volume a b := by
  have hsub : Icc a b ⊆ Icc tmin tmax := by
    intro s hs
    exact ⟨le_trans ha.1 hs.1, le_trans hs.2 hb.2⟩
  have hu : ContinuousOn u.toFun (Icc a b) := u.continuousOn.mono hsub
  have hforce : ContinuousOn P.forcing (Icc a b) := hFcont.continuousOn
  have hwork : ContinuousOn (fun s => P.forcing s (u.toFun s)) (Icc a b) :=
    hforce.clm_apply hu
  exact ContinuousOn.intervalIntegrable_of_Icc hab hwork

/-- Fundamental-theorem-of-calculus identity obtained by testing the
coefficient ODE with the state itself. -/
theorem LocalSolutionOn.integral_inner_rhs_eq_sub_norm_sq
    {P : VariationalGalerkinProblem W}
    {tmin tmax : ℝ}
    {t₀ : Icc tmin tmax}
    (u : P.LocalSolutionOn t₀)
    {a b : ℝ}
    (ha : a ∈ Icc tmin tmax)
    (hb : b ∈ Icc tmin tmax)
    (hab : a ≤ b)
    (hint : IntervalIntegrable
      (fun s => 2 * ⟪P.rhs s (u.toFun s), u.toFun s⟫_ℝ) volume a b) :
    ∫ s in a..b, 2 * ⟪P.rhs s (u.toFun s), u.toFun s⟫_ℝ
      = ‖u.toFun b‖ ^ 2 - ‖u.toFun a‖ ^ 2 := by
  let f : ℝ → ℝ := fun s => ‖u.toFun s‖ ^ 2
  let f' : ℝ → ℝ := fun s => 2 * ⟪P.rhs s (u.toFun s), u.toFun s⟫_ℝ
  have hsub : Icc a b ⊆ Icc tmin tmax := by
    intro x hx
    exact ⟨le_trans ha.1 hx.1, le_trans hx.2 hb.2⟩
  have hu_within :
      ∀ x ∈ Icc a b,
        HasDerivWithinAt u.toFun (P.rhs x (u.toFun x)) (Icc a b) x := by
    intro x hx
    exact (u.hasDerivWithinAt x (hsub hx)).mono hsub
  have hf_within :
      ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x := by
    intro x hx
    simpa [f, f', real_inner_comm, mul_comm] using (hu_within x hx).norm_sq
  have hcont : ContinuousOn f (Icc a b) :=
    HasDerivWithinAt.continuousOn hf_within
  have hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x := by
    intro x hx
    have hwithin := hf_within x (mem_Icc_of_Ioo hx)
    have hnhds : Icc a b ∈ nhds x := by
      refine mem_of_superset (Ioo_mem_nhds hx.1 hx.2) ?_
      intro y hy
      exact ⟨le_of_lt hy.1, le_of_lt hy.2⟩
    exact hwithin.hasDerivAt hnhds
  simpa [f, f'] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv hint

/-- Variational Galerkin energy identity.  Only the weak forms restricted to
the finite-dimensional space enter the calculation. -/
theorem LocalSolutionOn.energyIdentityOn
    {P : VariationalGalerkinProblem W}
    {tmin tmax : ℝ}
    {t₀ : Icc tmin tmax}
    (u : P.LocalSolutionOn t₀)
    {a b : ℝ}
    (ha : a ∈ Icc tmin tmax)
    (hb : b ∈ Icc tmin tmax)
    (hab : a ≤ b)
    (hAint : IntervalIntegrable
      (fun s => P.system.diffusion (u.toFun s) (u.toFun s)) volume a b)
    (hFint : IntervalIntegrable
      (fun s => P.forcing s (u.toFun s)) volume a b) :
    ‖u.toFun b‖ ^ 2
      + 2 * ∫ s in a..b, P.system.diffusion (u.toFun s) (u.toFun s)
      = ‖u.toFun a‖ ^ 2
        + 2 * ∫ s in a..b, P.forcing s (u.toFun s) := by
  let A : ℝ → ℝ := fun s => P.system.diffusion (u.toFun s) (u.toFun s)
  let F : ℝ → ℝ := fun s => P.forcing s (u.toFun s)
  have hpoint :
      (fun s => 2 * ⟪P.rhs s (u.toFun s), u.toFun s⟫_ℝ) =
        (fun s => 2 * (-A s + F s)) := by
    funext s
    rw [P.inner_rhs]
    rw [P.system.convection_cancel]
    simp [A, F]
  have hint : IntervalIntegrable
      (fun s => 2 * ⟪P.rhs s (u.toFun s), u.toFun s⟫_ℝ) volume a b := by
    rw [hpoint]
    simpa [A, F, sub_eq_add_neg, mul_add, mul_neg] using
      (hAint.const_mul (-2)).add (hFint.const_mul 2)
  have hFTC := u.integral_inner_rhs_eq_sub_norm_sq ha hb hab hint
  have hraw :
      ∫ s in a..b, 2 * (-A s + F s)
        = ‖u.toFun b‖ ^ 2 - ‖u.toFun a‖ ^ 2 := by
    rw [← hpoint]
    exact hFTC
  have hsplit :
      ∫ s in a..b, 2 * (-A s + F s)
        = -2 * (∫ s in a..b, A s) + 2 * (∫ s in a..b, F s) := by
    calc
      ∫ s in a..b, 2 * (-A s + F s)
          = ∫ s in a..b, (-2) * A s + 2 * F s := by
              apply intervalIntegral.integral_congr_ae
              filter_upwards
              intro s _
              ring
      _ = (∫ s in a..b, (-2) * A s) + ∫ s in a..b, 2 * F s := by
              rw [intervalIntegral.integral_add]
              · exact hAint.const_mul (-2)
              · exact hFint.const_mul 2
      _ = -2 * (∫ s in a..b, A s) + 2 * (∫ s in a..b, F s) := by
              rw [intervalIntegral.integral_const_mul,
                intervalIntegral.integral_const_mul]
  rw [hsplit] at hraw
  change ‖u.toFun b‖ ^ 2 + 2 * (∫ s in a..b, A s) =
    ‖u.toFun a‖ ^ 2 + 2 * (∫ s in a..b, F s)
  linear_combination -hraw

/-- Energy and dissipation bound on an arbitrary ordered subinterval under a
pointwise Young-type estimate for the dual forcing work. -/
theorem LocalSolutionOn.aprioriBoundWithDissipationOn
    {P : VariationalGalerkinProblem W}
    {tmin tmax : ℝ}
    {t₀ : Icc tmin tmax}
    (u : P.LocalSolutionOn t₀)
    (g : ℝ → ℝ)
    {a b : ℝ}
    (ha : a ∈ Icc tmin tmax)
    (hb : b ∈ Icc tmin tmax)
    (hab : a ≤ b)
    (hAint : IntervalIntegrable
      (fun s => P.system.diffusion (u.toFun s) (u.toFun s)) volume a b)
    (hFint : IntervalIntegrable
      (fun s => P.forcing s (u.toFun s)) volume a b)
    (hgint : IntervalIntegrable g volume a b)
    (hwork : ∀ s ∈ Icc a b,
      2 * P.forcing s (u.toFun s)
        ≤ g s + P.system.diffusion (u.toFun s) (u.toFun s)) :
    ‖u.toFun b‖ ^ 2
      + ∫ s in a..b, P.system.diffusion (u.toFun s) (u.toFun s)
      ≤ ‖u.toFun a‖ ^ 2 + ∫ s in a..b, g s := by
  have hEnergy := u.energyIdentityOn ha hb hab hAint hFint
  let A : ℝ → ℝ := fun s => P.system.diffusion (u.toFun s) (u.toFun s)
  let F : ℝ → ℝ := fun s => P.forcing s (u.toFun s)
  have hYoung :
      2 * (∫ s in a..b, F s)
        ≤ (∫ s in a..b, g s) + ∫ s in a..b, A s := by
    calc
      2 * (∫ s in a..b, F s)
          = ∫ s in a..b, 2 * F s := by
              rw [intervalIntegral.integral_const_mul]
      _ ≤ ∫ s in a..b, (g s + A s) := by
              apply intervalIntegral.integral_mono_on hab
              · exact hFint.const_mul 2
              · exact hgint.add hAint
              · intro s hs
                simpa [F, A] using hwork s hs
      _ = (∫ s in a..b, g s) + ∫ s in a..b, A s := by
              rw [intervalIntegral.integral_add hgint hAint]
  exact apriori_scalar_bound_with_dissipation
    (u := ‖u.toFun b‖ ^ 2)
    (u0 := ‖u.toFun a‖ ^ 2)
    (work := ∫ s in a..b, F s)
    (forcing := ∫ s in a..b, g s)
    (diss := ∫ s in a..b, A s)
    (by simpa [F, A] using hEnergy)
    hYoung

/-- The global energy budget controls every state of a coefficient solution.
The majorant is nonnegative, so its integral on a partial interval is bounded
by its integral on the full interval. -/
theorem LocalSolutionOn.norm_le_energyRadius
    {P : VariationalGalerkinProblem W}
    {a b : ℝ} (hab : a ≤ b)
    (u : P.LocalSolutionOn (⟨a, le_rfl, hab⟩ : Icc a b))
    (g : ℝ → ℝ)
    (hFcont : Continuous P.forcing)
    (hgint : IntervalIntegrable g volume a b)
    (hg_nonneg : ∀ t ∈ Icc a b, 0 ≤ g t)
    (hwork : ∀ t ∈ Icc a b, ∀ x : W,
      2 * P.forcing t x ≤ g t + P.system.diffusion x x)
    (R : ℝ) (hR : 0 ≤ R)
    (hbudget : ‖P.initial‖ ^ 2 + ∫ s in a..b, g s ≤ R ^ 2) :
    ∀ t ∈ Icc a b, ‖u.toFun t‖ ≤ R := by
  intro t ht
  obtain ⟨hgt_int, htb_int⟩ :
      IntervalIntegrable g volume a t ∧ IntervalIntegrable g volume t b :=
    (IntervalIntegrable.trans_iff
      (by simpa [uIcc_of_le hab] using ht)).mp hgint
  have hbound := u.aprioriBoundWithDissipationOn g
    (ha := (⟨le_rfl, hab⟩ : a ∈ Icc a b)) (hb := ht) ht.1
    (u.diffusion_intervalIntegrable
      (⟨le_rfl, hab⟩ : a ∈ Icc a b) ht ht.1)
    (u.forcing_intervalIntegrable hFcont
      (⟨le_rfl, hab⟩ : a ∈ Icc a b) ht ht.1)
    hgt_int (fun s hs => hwork s ⟨hs.1, hs.2.trans ht.2⟩ (u.toFun s))
  have hA_nonneg :
      0 ≤ ∫ s in a..t,
        P.system.diffusion (u.toFun s) (u.toFun s) := by
    apply intervalIntegral.integral_nonneg ht.1
    intro s _hs
    exact P.system.diffusion_nonneg _
  have hpartial :
      ‖u.toFun t‖ ^ 2 ≤ ‖P.initial‖ ^ 2 + ∫ s in a..t, g s := by
    rw [u.initial] at hbound
    exact (le_add_of_nonneg_right hA_nonneg).trans hbound
  have hg_mono : (∫ s in a..t, g s) ≤ ∫ s in a..b, g s := by
    calc
      (∫ s in a..t, g s)
          ≤ (∫ s in a..t, g s) + ∫ s in t..b, g s := by
            apply le_add_of_nonneg_right
            apply intervalIntegral.integral_nonneg ht.2
            intro s hs
            exact hg_nonneg s ⟨ht.1.trans hs.1, hs.2⟩
      _ = ∫ s in a..b, g s :=
        intervalIntegral.integral_add_adjacent_intervals hgt_int htb_int
  have hsum :
      ‖P.initial‖ ^ 2 + ∫ s in a..t, g s
        ≤ ‖P.initial‖ ^ 2 + ∫ s in a..b, g s := by
    gcongr
  have hsq : ‖u.toFun t‖ ^ 2 ≤ R ^ 2 :=
    hpartial.trans (hsum.trans hbudget)
  exact (sq_le_sq₀ (norm_nonneg _) hR).mp hsq

/-- Energy-controlled continuation on an arbitrary finite interval.  Local
Picard solutions have a common positive restart time inside the energy ball;
concatenation and a supremum argument extend them to the prescribed endpoint. -/
theorem exists_solutionOn_of_energy_budget
    (P : VariationalGalerkinProblem W)
    {tmin tmax : ℝ} (hT : tmin ≤ tmax)
    (hFcont : Continuous P.forcing)
    (M R : ℝ) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hFbound : ∀ t ∈ Icc tmin tmax, ‖P.forcing t‖ ≤ M)
    (g : ℝ → ℝ)
    (hgint : IntervalIntegrable g volume tmin tmax)
    (hg_nonneg : ∀ t ∈ Icc tmin tmax, 0 ≤ g t)
    (hwork : ∀ t ∈ Icc tmin tmax, ∀ x : W,
      2 * P.forcing t x ≤ g t + P.system.diffusion x x)
    (hbudget : ‖P.initial‖ ^ 2 + ∫ s in tmin..tmax, g s ≤ R ^ 2) :
    Nonempty (P.LocalSolutionOn
      (⟨tmin, le_rfl, hT⟩ : Icc tmin tmax)) := by
  let C : ℝ := ‖P.system.diffusion‖ * (R + 1)
    + P.system.convectionBound * (R + 1) ^ 2 + M
  have hC : 0 ≤ C := by
    dsimp [C]
    have hR1 : 0 ≤ R + 1 := by linarith
    exact add_nonneg
      (add_nonneg
        (mul_nonneg P.system.diffusion.opNorm_nonneg hR1)
        (mul_nonneg P.system.convectionBound_nonneg (sq_nonneg (R + 1))))
      hM
  let δ : ℝ := 1 / (C + 1)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hCδ : C * δ ≤ 1 := by
    calc
      C * δ = C / (C + 1) := by simp [δ, div_eq_mul_inv]
      _ ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
  let S : Set ℝ := {b : ℝ | ∃ htb : tmin ≤ b, b ≤ tmax ∧
    Nonempty (P.LocalSolutionOn
      (⟨tmin, le_rfl, htb⟩ : Icc tmin b))}
  have hzero : Nonempty (P.LocalSolutionOn
      (⟨tmin, le_rfl, le_rfl⟩ : Icc tmin tmin)) := by
    apply P.exists_localSolutionOn
      (⟨tmin, le_rfl, le_rfl⟩ : Icc tmin tmin) hFcont M hM
      (a := (1 : ℝ≥0))
    · intro t ht
      apply hFbound t
      constructor <;> linarith [ht.1, ht.2]
    · norm_num
  have htminS : tmin ∈ S := by
    change ∃ htb : tmin ≤ tmin, tmin ≤ tmax ∧
      Nonempty (P.LocalSolutionOn
        (⟨tmin, le_rfl, htb⟩ : Icc tmin tmin))
    exact ⟨le_rfl, hT, hzero⟩
  have hSne : S.Nonempty := ⟨tmin, htminS⟩
  have hSbdd : BddAbove S := by
    refine ⟨tmax, ?_⟩
    intro b hb
    change ∃ htb : tmin ≤ b, b ≤ tmax ∧
      Nonempty (P.LocalSolutionOn
        (⟨tmin, le_rfl, htb⟩ : Icc tmin b)) at hb
    exact hb.choose_spec.1
  have hExtend : ∀ {b c : ℝ}, b ∈ S → b ≤ c → c ≤ tmax → c - b ≤ δ → c ∈ S := by
    intro b c hbS hbc hcmax hlen
    change ∃ htb : tmin ≤ b, b ≤ tmax ∧
      Nonempty (P.LocalSolutionOn
        (⟨tmin, le_rfl, htb⟩ : Icc tmin b)) at hbS
    obtain ⟨hbmin, hbmax, u⟩ := hbS
    obtain ⟨u⟩ := u
    have hb_uIcc : b ∈ uIcc tmin tmax := by
      simpa [uIcc_of_le hT] using
        (⟨hbmin, hbmax⟩ : b ∈ Icc tmin tmax)
    obtain ⟨hg_left, hg_right⟩ :
        IntervalIntegrable g volume tmin b ∧
          IntervalIntegrable g volume b tmax :=
      (IntervalIntegrable.trans_iff hb_uIcc).mp hgint
    have hg_tail_nonneg : 0 ≤ ∫ s in b..tmax, g s := by
      apply intervalIntegral.integral_nonneg hbmax
      intro s hs
      exact hg_nonneg s ⟨hbmin.trans hs.1, hs.2⟩
    have hg_mono :
        (∫ s in tmin..b, g s) ≤ ∫ s in tmin..tmax, g s := by
      calc
        (∫ s in tmin..b, g s)
            ≤ (∫ s in tmin..b, g s) + ∫ s in b..tmax, g s :=
          le_add_of_nonneg_right hg_tail_nonneg
        _ = ∫ s in tmin..tmax, g s :=
          intervalIntegral.integral_add_adjacent_intervals hg_left hg_right
    have hbudget_b :
        ‖P.initial‖ ^ 2 + ∫ s in tmin..b, g s ≤ R ^ 2 := by
      calc
        ‖P.initial‖ ^ 2 + ∫ s in tmin..b, g s
            ≤ ‖P.initial‖ ^ 2 + ∫ s in tmin..tmax, g s := by gcongr
        _ ≤ R ^ 2 := hbudget
    have huR : ‖u.toFun b‖ ≤ R :=
      u.norm_le_energyRadius hbmin g hFcont hg_left
        (fun t ht => hg_nonneg t ⟨ht.1, ht.2.trans hbmax⟩)
        (fun t ht x => hwork t ⟨ht.1, ht.2.trans hbmax⟩ x)
        R hR hbudget_b b ⟨hbmin, le_rfl⟩
    have hsmall :
        (‖P.system.diffusion‖ * (R + (1 : ℝ))
            + P.system.convectionBound * (R + (1 : ℝ)) ^ 2 + M) *
            max (c - b) (b - b) ≤ (1 : ℝ) := by
      change C * max (c - b) (b - b) ≤ 1
      rw [sub_self, max_eq_left (sub_nonneg.mpr hbc)]
      exact (mul_le_mul_of_nonneg_left hlen hC).trans hCδ
    have hFbound_bc : ∀ t ∈ Icc b c, ‖P.forcing t‖ ≤ M := by
      intro t ht
      exact hFbound t ⟨hbmin.trans ht.1, ht.2.trans hcmax⟩
    obtain ⟨v⟩ := P.exists_restartSolutionOn_of_state_bound
      (⟨b, le_rfl, hbc⟩ : Icc b c) hFcont M R hM hR hFbound_bc
      (1 : ℝ≥0) hsmall huR
    obtain ⟨w⟩ := LocalSolutionOn.concat hbmin hbc u v
    change ∃ htc : tmin ≤ c, c ≤ tmax ∧
      Nonempty (P.LocalSolutionOn
        (⟨tmin, le_rfl, htc⟩ : Icc tmin c))
    exact ⟨hbmin.trans hbc, hcmax, ⟨w⟩⟩
  let B : ℝ := sSup S
  have hBle : B ≤ tmax := by
    exact csSup_le hSne (by
      intro b hb
      change ∃ htb : tmin ≤ b, b ≤ tmax ∧
        Nonempty (P.LocalSolutionOn
          (⟨tmin, le_rfl, htb⟩ : Icc tmin b)) at hb
      exact hb.choose_spec.1)
  have hBeq : B = tmax := by
    apply le_antisymm hBle
    by_contra hnot
    have hBlt : B < tmax := lt_of_not_ge hnot
    let η : ℝ := min (δ / 2) ((tmax - B) / 2)
    have hη : 0 < η := by
      dsimp [η]
      exact lt_min (half_pos hδ) (half_pos (sub_pos.mpr hBlt))
    have hnear : B - η < B := sub_lt_self B hη
    obtain ⟨b, hbS, hbclose⟩ := exists_lt_of_lt_csSup hSne hnear
    have hbB : b ≤ B := le_csSup hSbdd hbS
    let c : ℝ := b + η
    have hbc : b ≤ c := by dsimp [c]; linarith
    have hcmax : c ≤ tmax := by
      have hηmax : η ≤ (tmax - B) / 2 := min_le_right _ _
      dsimp [c]
      linarith
    have hlen : c - b ≤ δ := by
      have hηδ : η ≤ δ / 2 := min_le_left _ _
      dsimp [c]
      linarith
    have hcS : c ∈ S := hExtend hbS hbc hcmax hlen
    have hcB : c ≤ B := le_csSup hSbdd hcS
    dsimp [c] at hcB
    linarith
  have hnear : tmax - δ < B := by rw [hBeq]; linarith
  obtain ⟨b, hbS, hbclose⟩ := exists_lt_of_lt_csSup hSne hnear
  have hbmax : b ≤ tmax := hBeq ▸ le_csSup hSbdd hbS
  have hlen : tmax - b ≤ δ := by linarith
  have htmaxS : tmax ∈ S := hExtend hbS hbmax le_rfl hlen
  change ∃ htb : tmin ≤ tmax, tmax ≤ tmax ∧
    Nonempty (P.LocalSolutionOn
      (⟨tmin, le_rfl, htb⟩ : Icc tmin tmax)) at htmaxS
  obtain ⟨_, _, hsol⟩ := htmaxS
  simpa using hsol

/-- Initial-time form of the variational energy identity. -/
theorem LocalSolutionOn.energyIdentityAtTime
    {P : VariationalGalerkinProblem W}
    {tmax : ℝ}
    (t₀ : Icc (0 : ℝ) tmax)
    (hzero : (t₀ : ℝ) = 0)
    (u : P.LocalSolutionOn t₀)
    {T : ℝ}
    (hT : T ∈ Icc (0 : ℝ) tmax)
    (hAint : IntervalIntegrable
      (fun s => P.system.diffusion (u.toFun s) (u.toFun s)) volume 0 T)
    (hFint : IntervalIntegrable
      (fun s => P.forcing s (u.toFun s)) volume 0 T) :
    ‖u.toFun T‖ ^ 2
      + 2 * ∫ s in (0 : ℝ)..T,
          P.system.diffusion (u.toFun s) (u.toFun s)
      = ‖P.initial‖ ^ 2
        + 2 * ∫ s in (0 : ℝ)..T, P.forcing s (u.toFun s) := by
  have h := u.energyIdentityOn
    (a := (t₀ : ℝ)) (b := T) t₀.property hT
    (by simpa [hzero] using hT.1)
    (by simpa [hzero] using hAint)
    (by simpa [hzero] using hFint)
  rw [u.initial] at h
  simpa [hzero] using h

/-- Energy and dissipation bound under a pointwise Young-type estimate for
the dual forcing work.  The majorant `g` can come from a genuine `V'` norm;
no ambient `H`-valued forcing is required. -/
theorem LocalSolutionOn.aprioriBoundWithDissipationAtTime
    {P : VariationalGalerkinProblem W}
    {tmax : ℝ}
    (t₀ : Icc (0 : ℝ) tmax)
    (hzero : (t₀ : ℝ) = 0)
    (u : P.LocalSolutionOn t₀)
    (g : ℝ → ℝ)
    {T : ℝ}
    (hT : T ∈ Icc (0 : ℝ) tmax)
    (hAint : IntervalIntegrable
      (fun s => P.system.diffusion (u.toFun s) (u.toFun s)) volume 0 T)
    (hFint : IntervalIntegrable
      (fun s => P.forcing s (u.toFun s)) volume 0 T)
    (hgint : IntervalIntegrable g volume 0 T)
    (hwork : ∀ s ∈ Icc (0 : ℝ) T,
      2 * P.forcing s (u.toFun s)
        ≤ g s + P.system.diffusion (u.toFun s) (u.toFun s)) :
    ‖u.toFun T‖ ^ 2
      + ∫ s in (0 : ℝ)..T,
          P.system.diffusion (u.toFun s) (u.toFun s)
      ≤ ‖P.initial‖ ^ 2 + ∫ s in (0 : ℝ)..T, g s := by
  have hEnergy := u.energyIdentityAtTime t₀ hzero hT hAint hFint
  let A : ℝ → ℝ := fun s => P.system.diffusion (u.toFun s) (u.toFun s)
  let F : ℝ → ℝ := fun s => P.forcing s (u.toFun s)
  have hYoung :
      2 * (∫ s in (0 : ℝ)..T, F s)
        ≤ (∫ s in (0 : ℝ)..T, g s) + ∫ s in (0 : ℝ)..T, A s := by
    calc
      2 * (∫ s in (0 : ℝ)..T, F s)
          = ∫ s in (0 : ℝ)..T, 2 * F s := by
              rw [intervalIntegral.integral_const_mul]
      _ ≤ ∫ s in (0 : ℝ)..T, (g s + A s) := by
              apply intervalIntegral.integral_mono_on hT.1
              · exact hFint.const_mul 2
              · exact hgint.add hAint
              · intro s hs
                simpa [F, A] using hwork s hs
      _ = (∫ s in (0 : ℝ)..T, g s) + ∫ s in (0 : ℝ)..T, A s := by
              rw [intervalIntegral.integral_add hgint hAint]
  exact apriori_scalar_bound_with_dissipation
    (u := ‖u.toFun T‖ ^ 2)
    (u0 := ‖P.initial‖ ^ 2)
    (work := ∫ s in (0 : ℝ)..T, F s)
    (forcing := ∫ s in (0 : ℝ)..T, g s)
    (diss := ∫ s in (0 : ℝ)..T, A s)
    (by simpa [F, A] using hEnergy)
    hYoung

section DualDerivative

variable {Test : Type*} [NormedAddCommGroup Test] [NormedSpace ℝ Test]

/-- The variational right-hand side interpreted as a functional on a common
test space through a Galerkin test projection. -/
def dualRHS
    (P : VariationalGalerkinProblem W)
    (Q : Test →L[ℝ] W) (t : ℝ) (u : W) : Test →L[ℝ] ℝ :=
  (P.weakRHS t u).comp Q

omit [CompleteSpace W] in
@[simp] theorem dualRHS_apply
    (P : VariationalGalerkinProblem W)
    (Q : Test →L[ℝ] W) (t : ℝ) (u : W) (φ : Test) :
    P.dualRHS Q t u φ =
      -P.system.diffusion u (Q φ)
      - P.system.convection u u (Q φ) + P.forcing t (Q φ) :=
  rfl

omit [CompleteSpace W] in
/-- Measurable coefficient and forcing paths produce a measurable common-dual
right-hand side. -/
theorem dualRHS_aestronglyMeasurable
    (P : VariationalGalerkinProblem W)
    (Q : Test →L[ℝ] W) (μ : Measure ℝ)
    (U : ℝ → W)
    (hU : AEStronglyMeasurable U μ)
    (hforcing : AEStronglyMeasurable P.forcing μ) :
    AEStronglyMeasurable (fun t => P.dualRHS Q t (U t)) μ := by
  have hdiff : AEStronglyMeasurable
      (fun t => P.system.diffusion (U t)) μ :=
    P.system.diffusion.continuous.comp_aestronglyMeasurable hU
  have hconv : AEStronglyMeasurable
      (fun t => P.system.convection (U t) (U t)) μ :=
    P.system.convection.aestronglyMeasurable_comp₂ hU hU
  have hweak : AEStronglyMeasurable
      (fun t => -P.system.diffusion (U t) -
        P.system.convection (U t) (U t) + P.forcing t) μ :=
    (hdiff.neg.sub hconv).add hforcing
  have hcomp : Continuous
      (fun F : W →L[ℝ] ℝ => F.comp Q) := by
    fun_prop
  simpa only [dualRHS, weakRHS] using
    hcomp.comp_aestronglyMeasurable hweak

omit [CompleteSpace W] in
/-- A termwise variational estimate controls the common-test-space dual norm
of the coefficient derivative. -/
theorem dualRHS_norm_le
    (P : VariationalGalerkinProblem W)
    (Q : Test →L[ℝ] W) (t : ℝ) (u : W)
    (A B F : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hF : 0 ≤ F)
    (hdiff : ∀ φ : Test,
      ‖P.system.diffusion u (Q φ)‖ ≤ A * ‖φ‖)
    (hconv : ∀ φ : Test,
      ‖P.system.convection u u (Q φ)‖ ≤ B * ‖φ‖)
    (hforce : ∀ φ : Test,
      ‖P.forcing t (Q φ)‖ ≤ F * ‖φ‖) :
    ‖P.dualRHS Q t u‖ ≤ A + B + F := by
  apply (P.dualRHS Q t u).opNorm_le_bound
    (add_nonneg (add_nonneg hA hB) hF)
  intro φ
  calc
    ‖P.dualRHS Q t u φ‖
        ≤ ‖P.system.diffusion u (Q φ)‖
          + ‖P.system.convection u u (Q φ)‖
          + ‖P.forcing t (Q φ)‖ := by
            have htri :
                ‖(-P.system.diffusion u (Q φ))
                    + (-P.system.convection u u (Q φ))
                    + P.forcing t (Q φ)‖
                  ≤ ‖P.system.diffusion u (Q φ)‖
                    + ‖P.system.convection u u (Q φ)‖
                    + ‖P.forcing t (Q φ)‖ := by
              simpa using (norm_add₃_le :
                ‖(-P.system.diffusion u (Q φ))
                    + (-P.system.convection u u (Q φ))
                    + P.forcing t (Q φ)‖
                  ≤ ‖-P.system.diffusion u (Q φ)‖
                    + ‖-P.system.convection u u (Q φ)‖
                    + ‖P.forcing t (Q φ)‖)
            simpa [dualRHS_apply, sub_eq_add_neg] using htri
    _ ≤ A * ‖φ‖ + B * ‖φ‖ + F * ‖φ‖ := by
          exact add_le_add (add_le_add (hdiff φ) (hconv φ)) (hforce φ)
    _ = (A + B + F) * ‖φ‖ := by ring

omit [CompleteSpace W] in
/-- Standard NSE-shaped `V'` estimate: diffusion is linear in the energy
size, while convection is bilinear in the state and energy sizes. -/
theorem dualRHS_nse_norm_le
    (P : VariationalGalerkinProblem W)
    (Q : Test →L[ℝ] W) (t : ℝ) (u : W)
    (cA cB h d f : ℝ)
    (hcA : 0 ≤ cA) (hcB : 0 ≤ cB)
    (hh : 0 ≤ h) (hd : 0 ≤ d) (hf : 0 ≤ f)
    (hdiff : ∀ φ : Test,
      ‖P.system.diffusion u (Q φ)‖ ≤ cA * d * ‖φ‖)
    (hconv : ∀ φ : Test,
      ‖P.system.convection u u (Q φ)‖ ≤ cB * h * d * ‖φ‖)
    (hforce : ∀ φ : Test,
      ‖P.forcing t (Q φ)‖ ≤ f * ‖φ‖) :
    ‖P.dualRHS Q t u‖ ≤ cA * d + cB * h * d + f := by
  exact P.dualRHS_norm_le Q t u (cA * d) (cB * h * d) f
    (mul_nonneg hcA hd) (mul_nonneg (mul_nonneg hcB hh) hd) hf
    hdiff hconv hforce

omit [CompleteSpace W] in
/-- A uniform state bound turns the NSE-shaped pointwise dual estimate into
the square-integrable majorant used in the Aubin--Lions route. -/
theorem dualRHS_nse_norm_sq_le
    (P : VariationalGalerkinProblem W)
    (Q : Test →L[ℝ] W) (t : ℝ) (u : W)
    (cA cB h d f H : ℝ)
    (hcA : 0 ≤ cA) (hcB : 0 ≤ cB)
    (hh : 0 ≤ h) (hd : 0 ≤ d) (hf : 0 ≤ f)
    (hH : 0 ≤ H) (hhH : h ≤ H)
    (hdiff : ∀ φ : Test,
      ‖P.system.diffusion u (Q φ)‖ ≤ cA * d * ‖φ‖)
    (hconv : ∀ φ : Test,
      ‖P.system.convection u u (Q φ)‖ ≤ cB * h * d * ‖φ‖)
    (hforce : ∀ φ : Test,
      ‖P.forcing t (Q φ)‖ ≤ f * ‖φ‖) :
    ‖P.dualRHS Q t u‖ ^ 2
      ≤ 2 * (cA + cB * H) ^ 2 * d ^ 2 + 2 * f ^ 2 := by
  have hbase := P.dualRHS_nse_norm_le Q t u cA cB h d f
    hcA hcB hh hd hf hdiff hconv hforce
  have hconvCoeff : cB * h * d ≤ cB * H * d := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hhH hcB) hd
  have hlinear :
      ‖P.dualRHS Q t u‖ ≤ (cA + cB * H) * d + f := by
    calc
      ‖P.dualRHS Q t u‖ ≤ cA * d + cB * h * d + f := hbase
      _ ≤ cA * d + cB * H * d + f := by linarith
      _ = (cA + cB * H) * d + f := by ring
  have hcoef : 0 ≤ (cA + cB * H) * d := by
    exact mul_nonneg
      (add_nonneg hcA (mul_nonneg hcB hH)) hd
  have hsq :
      ‖P.dualRHS Q t u‖ ^ 2
        ≤ ((cA + cB * H) * d + f) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (add_nonneg hcoef hf)).2 hlinear
  calc
    ‖P.dualRHS Q t u‖ ^ 2
        ≤ ((cA + cB * H) * d + f) ^ 2 := hsq
    _ ≤ 2 * ((cA + cB * H) * d) ^ 2 + 2 * f ^ 2 := by
          nlinarith [sq_nonneg (((cA + cB * H) * d) - f)]
    _ = 2 * (cA + cB * H) ^ 2 * d ^ 2 + 2 * f ^ 2 := by ring

/-- The coefficient ODE yields the tested derivative identity on the common
test space. -/
theorem LocalSolutionOn.hasDerivWithinAt_test
    {P : VariationalGalerkinProblem W}
    {tmin tmax : ℝ}
    {t₀ : Icc tmin tmax}
    (u : P.LocalSolutionOn t₀)
    (Q : Test →L[ℝ] W) (φ : Test)
    (t : ℝ) (ht : t ∈ Icc tmin tmax) :
    HasDerivWithinAt
      (fun s => ⟪u.toFun s, Q φ⟫_ℝ)
      (P.dualRHS Q t (u.toFun t) φ)
      (Icc tmin tmax) t := by
  let ell : W →L[ℝ] ℝ := innerSLFlip ℝ (Q φ)
  have h := ell.hasFDerivAt.comp_hasDerivWithinAt
    (x := t) (hf := u.hasDerivWithinAt t ht)
  convert h using 1
  change
    -P.system.diffusion (u.toFun t) (Q φ)
        - P.system.convection (u.toFun t) (u.toFun t) (Q φ)
        + P.forcing t (Q φ) = ⟪P.rhs t (u.toFun t), Q φ⟫_ℝ
  exact (P.inner_rhs t (u.toFun t) (Q φ)).symm

section FiniteModeReconstruction

variable {Y ι : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Synthesis of finitely many tested dual coordinates in a normed target
space. -/
def finiteModeSynthesis
    (modes : ι → Test) (vectors : ι → Y) (s : Finset ι)
    (D : Test →L[ℝ] ℝ) : Y :=
  ∑ i ∈ s, D (modes i) • vectors i

/-- The finite-dimensional norm constant for `finiteModeSynthesis`. -/
def finiteModeSynthesisConstant
    (modes : ι → Test) (vectors : ι → Y) (s : Finset ι) : ℝ≥0 :=
  ∑ i ∈ s, ‖modes i‖₊ * ‖vectors i‖₊

/-- Finite-mode synthesis is bounded by the dual norm times the explicit
sum of mode norms. -/
theorem norm_finiteModeSynthesis_le
    (modes : ι → Test) (vectors : ι → Y) (s : Finset ι)
    (D : Test →L[ℝ] ℝ) :
    ‖finiteModeSynthesis modes vectors s D‖
      ≤ (finiteModeSynthesisConstant modes vectors s : ℝ) * ‖D‖ := by
  calc
    ‖finiteModeSynthesis modes vectors s D‖
        ≤ ∑ i ∈ s, ‖D (modes i) • vectors i‖ := by
          exact norm_sum_le _ _
    _ = ∑ i ∈ s, ‖D (modes i)‖ * ‖vectors i‖ := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [norm_smul]
    _ ≤ ∑ i ∈ s, (‖D‖ * ‖modes i‖) * ‖vectors i‖ := by
          apply Finset.sum_le_sum
          intro i _hi
          exact mul_le_mul_of_nonneg_right
            (D.le_opNorm (modes i)) (norm_nonneg _)
    _ = (∑ i ∈ s, ‖modes i‖ * ‖vectors i‖) * ‖D‖ := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _hi
          ring
    _ = (finiteModeSynthesisConstant modes vectors s : ℝ) * ‖D‖ := by
          simp [finiteModeSynthesisConstant]

/-- An `Lᵖ` path in the common test-space dual remains in `Lᵖ` after any
fixed finite-mode synthesis. -/
theorem finiteModeSynthesis_memLp
    {α : Type*} [MeasurableSpace α]
    (D : α → Test →L[ℝ] ℝ) (p : ℝ≥0∞) (μ : Measure α)
    (modes : ι → Test) (vectors : ι → Y) (s : Finset ι)
    (hD : MemLp D p μ) :
    MemLp (fun x => finiteModeSynthesis modes vectors s (D x)) p μ := by
  apply MemLp.of_le_mul hD
  · have hmeas := Finset.aestronglyMeasurable_sum s fun i _hi =>
      (hD.1.apply_continuousLinearMap (modes i)).smul_const (vectors i)
    have heq :
        (fun x => finiteModeSynthesis modes vectors s (D x)) =
          ∑ i ∈ s, fun x => D x (modes i) • vectors i := by
      funext x
      simp [finiteModeSynthesis]
    rw [heq]
    exact hmeas
  · exact Filter.Eventually.of_forall fun x =>
      norm_finiteModeSynthesis_le modes vectors s (D x)

/-- Squaring the synthesis estimate gives the pointwise estimate used under
the time integral. -/
theorem norm_finiteModeSynthesis_sq_le
    (modes : ι → Test) (vectors : ι → Y) (s : Finset ι)
    (D : Test →L[ℝ] ℝ) :
    ‖finiteModeSynthesis modes vectors s D‖ ^ 2
      ≤ (finiteModeSynthesisConstant modes vectors s : ℝ) ^ 2 * ‖D‖ ^ 2 := by
  have h := norm_finiteModeSynthesis_le modes vectors s D
  have hnonneg :
      0 ≤ (finiteModeSynthesisConstant modes vectors s : ℝ) * ‖D‖ :=
    mul_nonneg (finiteModeSynthesisConstant modes vectors s).coe_nonneg
      (norm_nonneg D)
  have hsq := (sq_le_sq₀ (norm_nonneg _) hnonneg).2 h
  nlinarith

/-- The square integral of a fixed finite-mode synthesis is controlled by
the square integral of the common-test-space dual path. -/
theorem intervalIntegral_norm_finiteModeSynthesis_sq_le
    {a b : ℝ} (hab : a ≤ b)
    (D : ℝ → Test →L[ℝ] ℝ)
    (modes : ι → Test) (vectors : ι → Y) (s : Finset ι)
    (hD : MemLp D 2 (volume.restrict (Icc a b))) :
    ∫ t in a..b, ‖finiteModeSynthesis modes vectors s (D t)‖ ^ 2
      ≤ (finiteModeSynthesisConstant modes vectors s : ℝ) ^ 2 *
          ∫ t in a..b, ‖D t‖ ^ 2 := by
  have hSynth :
      MemLp (fun t => finiteModeSynthesis modes vectors s (D t)) 2
        (volume.restrict (Icc a b)) :=
    finiteModeSynthesis_memLp D 2 (volume.restrict (Icc a b))
      modes vectors s hD
  have hDsq : IntervalIntegrable (fun t => ‖D t‖ ^ 2) volume a b := by
    rw [intervalIntegrable_iff, uIoc_of_le hab]
    exact (hD.norm.mono_measure
      (Measure.restrict_mono_set volume Ioc_subset_Icc_self)).integrable_sq
  have hSynthSq :
      IntervalIntegrable
        (fun t => ‖finiteModeSynthesis modes vectors s (D t)‖ ^ 2)
        volume a b := by
    rw [intervalIntegrable_iff, uIoc_of_le hab]
    exact (hSynth.norm.mono_measure
      (Measure.restrict_mono_set volume Ioc_subset_Icc_self)).integrable_sq
  calc
    ∫ t in a..b, ‖finiteModeSynthesis modes vectors s (D t)‖ ^ 2
        ≤ ∫ t in a..b,
            (finiteModeSynthesisConstant modes vectors s : ℝ) ^ 2 *
              ‖D t‖ ^ 2 := by
          apply intervalIntegral.integral_mono_on hab hSynthSq
            (hDsq.const_mul
              ((finiteModeSynthesisConstant modes vectors s : ℝ) ^ 2))
          intro t _ht
          exact norm_finiteModeSynthesis_sq_le modes vectors s (D t)
    _ = (finiteModeSynthesisConstant modes vectors s : ℝ) ^ 2 *
          ∫ t in a..b, ‖D t‖ ^ 2 := by
          rw [intervalIntegral.integral_const_mul]

/-- The tested variational identities assemble into the derivative identity
for every fixed finite-mode vector reconstruction. -/
theorem LocalSolutionOn.hasDerivWithinAt_finiteModeReconstruction
    {P : VariationalGalerkinProblem W}
    {tmin tmax : ℝ}
    {t₀ : Icc tmin tmax}
    (u : P.LocalSolutionOn t₀)
    (Q : Test →L[ℝ] W)
    (modes : ι → Test) (vectors : ι → Y) (s : Finset ι)
    (t : ℝ) (ht : t ∈ Icc tmin tmax) :
    HasDerivWithinAt
      (fun r => ∑ i ∈ s,
        ⟪u.toFun r, Q (modes i)⟫_ℝ • vectors i)
      (finiteModeSynthesis modes vectors s
        (P.dualRHS Q t (u.toFun t)))
      (Icc tmin tmax) t := by
  apply HasDerivWithinAt.fun_sum
  intro i _hi
  exact (u.hasDerivWithinAt_test Q (modes i) t ht).smul_const (vectors i)

/-- A dual `L²` bound supplies all three analytic facts needed for a fixed
finite-mode compactness block: its derivative identity, derivative
measurability, and its explicit square-integral bound. -/
theorem LocalSolutionOn.finiteModeReconstruction_l2Derivative
    {P : VariationalGalerkinProblem W}
    {a b : ℝ} (hab : a ≤ b)
    (u : P.LocalSolutionOn (⟨a, le_rfl, hab⟩ : Icc a b))
    (Q : Test →L[ℝ] W)
    (modes : ι → Test) (vectors : ι → Y) (s : Finset ι)
    (M : ℝ≥0)
    (hDualLp : MemLp (fun t => P.dualRHS Q t (u.toFun t)) 2
      (volume.restrict (Icc a b)))
    (hDualSq :
      ∫ t in a..b, ‖P.dualRHS Q t (u.toFun t)‖ ^ 2 ≤ (M : ℝ) ^ 2) :
    (∀ t ∈ Icc a b,
      HasDerivWithinAt
        (fun r => ∑ i ∈ s,
          ⟪u.toFun r, Q (modes i)⟫_ℝ • vectors i)
        (finiteModeSynthesis modes vectors s
          (P.dualRHS Q t (u.toFun t)))
        (Icc a b) t) ∧
    MemLp
      (fun t => finiteModeSynthesis modes vectors s
        (P.dualRHS Q t (u.toFun t)))
      2 (volume.restrict (Icc a b)) ∧
    ∫ t in a..b,
        ‖finiteModeSynthesis modes vectors s
          (P.dualRHS Q t (u.toFun t))‖ ^ 2
      ≤ ((finiteModeSynthesisConstant modes vectors s * M : ℝ≥0) : ℝ) ^ 2 := by
  refine ⟨fun t ht =>
      u.hasDerivWithinAt_finiteModeReconstruction Q modes vectors s t ht,
    finiteModeSynthesis_memLp
      (fun t => P.dualRHS Q t (u.toFun t)) 2
      (volume.restrict (Icc a b)) modes vectors s hDualLp, ?_⟩
  calc
    ∫ t in a..b,
        ‖finiteModeSynthesis modes vectors s
          (P.dualRHS Q t (u.toFun t))‖ ^ 2
        ≤ (finiteModeSynthesisConstant modes vectors s : ℝ) ^ 2 *
            ∫ t in a..b, ‖P.dualRHS Q t (u.toFun t)‖ ^ 2 :=
      intervalIntegral_norm_finiteModeSynthesis_sq_le hab
        (fun t => P.dualRHS Q t (u.toFun t)) modes vectors s hDualLp
    _ ≤ (finiteModeSynthesisConstant modes vectors s : ℝ) ^ 2 *
          (M : ℝ) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hDualSq (sq_nonneg _)
    _ = ((finiteModeSynthesisConstant modes vectors s * M : ℝ≥0) : ℝ) ^ 2 := by
      push_cast
      ring

end FiniteModeReconstruction

end DualDerivative

end VariationalGalerkinProblem
