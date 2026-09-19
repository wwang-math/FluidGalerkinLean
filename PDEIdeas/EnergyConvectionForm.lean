import PDEIdeas.VariationalGalerkin
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Bounded skew energy convection forms

A continuous trilinear form with a quantitative bound and skew symmetry
pulls back along any continuous energy lift. Together with a nonnegative
diffusion form it defines a finite-dimensional variational Galerkin system.
-/

open InnerProductSpace

noncomputable section

/-- A bounded energy-space convection form with the skew identity used by
the Galerkin energy method. -/
structure EnergyConvectionForm
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] where
  form : V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  norm_le : ∀ u v, ‖form u v‖ ≤ bound * ‖u‖ * ‖v‖
  skew : ∀ u v w, form u v w = -form u w v

namespace ContinuousLinearMap

/-- Pull the three arguments of a continuous trilinear form back along three
continuous linear maps. -/
def trilinearComp
    {E₁ E₂ E₃ W : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (C : E₁ →L[ℝ] E₂ →L[ℝ] E₃ →L[ℝ] ℝ)
    (A : W →L[ℝ] E₁) (B : W →L[ℝ] E₂) (D : W →L[ℝ] E₃) :
    W →L[ℝ] W →L[ℝ] W →L[ℝ] ℝ :=
  let C12 := C.bilinearComp A B
  let post : (E₃ →L[ℝ] ℝ) →L[ℝ] W →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ W E₃ ℝ).flip D
  (ContinuousLinearMap.compL ℝ W (E₃ →L[ℝ] ℝ) (W →L[ℝ] ℝ) post).comp C12

@[simp]
theorem trilinearComp_apply
    {E₁ E₂ E₃ W : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (C : E₁ →L[ℝ] E₂ →L[ℝ] E₃ →L[ℝ] ℝ)
    (A : W →L[ℝ] E₁) (B : W →L[ℝ] E₂) (D : W →L[ℝ] E₃)
    (u v w : W) :
    C.trilinearComp A B D u v w = C (A u) (B v) (D w) :=
  rfl

/-- Pull both arguments of a continuous bilinear form back along one map. -/
def bilinearCompSame
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (E : W →L[ℝ] V) : W →L[ℝ] W →L[ℝ] ℝ :=
  B.bilinearComp E E

@[simp]
theorem bilinearCompSame_apply
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (E : W →L[ℝ] V) (u v : W) :
    B.bilinearCompSame E u v = B (E u) (E v) :=
  rfl

/-- Pull all three arguments of a continuous trilinear form back along one
map. -/
def trilinearCompSame
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (C : V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ)
    (E : W →L[ℝ] V) : W →L[ℝ] W →L[ℝ] W →L[ℝ] ℝ :=
  let C12 := C.bilinearComp E E
  let post : (V →L[ℝ] ℝ) →L[ℝ] W →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ W V ℝ).flip E
  (ContinuousLinearMap.compL ℝ W (V →L[ℝ] ℝ) (W →L[ℝ] ℝ) post).comp C12

@[simp]
theorem trilinearCompSame_apply
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (C : V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ)
    (E : W →L[ℝ] V) (u v w : W) :
    C.trilinearCompSame E u v w = C (E u) (E v) (E w) :=
  rfl

end ContinuousLinearMap

namespace EnergyConvectionForm

set_option maxHeartbeats 800000 in
/-- A positive continuity constant and its operator estimate for a continuous
trilinear form. -/
noncomputable def continuousTrilinearBoundData
    {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (form : V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ) :
    { C : ℝ // 0 < C ∧ ∀ u : V, ‖form u‖ ≤ C * ‖u‖ } :=
  Classical.choice (by
    apply Exists.elim (ContinuousLinearMap.bound (𝕜 := ℝ) (𝕜₂ := ℝ)
      (σ₁₂ := RingHom.id ℝ) (E := V)
      (F := V →L[ℝ] V →L[ℝ] ℝ) form)
    intro C hC
    exact ⟨⟨C, hC⟩⟩)

/-- The selected positive continuity constant of a trilinear form. -/
noncomputable def continuousTrilinearBound
    {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (form : V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ) : ℝ :=
  (continuousTrilinearBoundData form).1

theorem continuousTrilinearBound_pos
    {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (form : V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ) :
    0 < continuousTrilinearBound form :=
  (continuousTrilinearBoundData form).property.1

theorem norm_le_continuousTrilinearBound
    {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (form : V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ)
    (u : V) :
    ‖form u‖ ≤ continuousTrilinearBound form * ‖u‖ :=
  (continuousTrilinearBoundData form).property.2 u

/-- A continuous trilinear form that is skew in its last two variables carries
a positive continuity constant as an admissible energy-space bound. -/
noncomputable def ofContinuousSkew
    {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (form : V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ)
    (skew : ∀ u v w, form u v w = -form u w v) :
    EnergyConvectionForm V where
  form := form
  bound := continuousTrilinearBound form
  bound_nonneg := (continuousTrilinearBound_pos form).le
  norm_le := by
    intro u v
    calc
      ‖form u v‖ ≤ ‖form u‖ * ‖v‖ := (form u).le_opNorm v
      _ ≤ (continuousTrilinearBound form * ‖u‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right
          (norm_le_continuousTrilinearBound form u) (norm_nonneg v)
  skew := skew

@[simp]
theorem ofContinuousSkew_form
    {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (form : V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ)
    (skew : ∀ u v w, form u v w = -form u w v) :
    (ofContinuousSkew form skew).form = form := by
  rfl

/-- Pullback of energy diffusion and convection to a Hilbert coefficient
space. The convection constant grows by at most the cube of the lift norm. -/
noncomputable def pullbackSystem
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [hW : InnerProductSpace ℝ W]
    (C : EnergyConvectionForm V)
    (E : W →L[ℝ] V)
    (D : V →L[ℝ] V →L[ℝ] ℝ)
    (D_nonneg : ∀ u, 0 ≤ D u u) :
    VariationalGalerkinSystem W := by
  letI : NormedSpace ℝ W := hW.toNormedSpace
  exact {
    diffusion := D.bilinearCompSame E
    convection := C.form.trilinearCompSame E
    convectionBound := C.bound * ‖E‖ ^ 3
    convectionBound_nonneg :=
      mul_nonneg C.bound_nonneg (pow_nonneg (norm_nonneg _) 3)
    convection_norm_le := by
      intro u v
      apply (C.form.trilinearCompSame E u v).opNorm_le_bound
      · exact mul_nonneg
          (mul_nonneg
            (mul_nonneg C.bound_nonneg (pow_nonneg (norm_nonneg _) 3))
            (norm_nonneg _))
          (norm_nonneg _)
      · intro w
        rw [ContinuousLinearMap.trilinearCompSame_apply]
        calc
          ‖C.form (E u) (E v) (E w)‖ ≤
              ‖C.form (E u) (E v)‖ * ‖E w‖ :=
            (C.form (E u) (E v)).le_opNorm (E w)
          _ ≤ (C.bound * ‖E u‖ * ‖E v‖) * (‖E‖ * ‖w‖) := by
            exact mul_le_mul (C.norm_le (E u) (E v)) (E.le_opNorm w)
              (norm_nonneg _)
              (mul_nonneg (mul_nonneg C.bound_nonneg (norm_nonneg _))
                (norm_nonneg _))
          _ ≤ (C.bound * (‖E‖ * ‖u‖) * (‖E‖ * ‖v‖)) *
                (‖E‖ * ‖w‖) := by
            have hu : C.bound * ‖E u‖ ≤ C.bound * (‖E‖ * ‖u‖) :=
              mul_le_mul_of_nonneg_left (E.le_opNorm u) C.bound_nonneg
            have huv : C.bound * ‖E u‖ * ‖E v‖ ≤
                C.bound * (‖E‖ * ‖u‖) * (‖E‖ * ‖v‖) :=
              mul_le_mul hu (E.le_opNorm v) (norm_nonneg _)
                (mul_nonneg C.bound_nonneg
                  (mul_nonneg (norm_nonneg E) (norm_nonneg u)))
            exact mul_le_mul_of_nonneg_right huv
              (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          _ = (C.bound * ‖E‖ ^ 3 * ‖u‖ * ‖v‖) * ‖w‖ := by ring
    diffusion_nonneg := by
      intro u
      rw [ContinuousLinearMap.bilinearCompSame_apply]
      exact D_nonneg (E u)
    convection_skew := by
      intro u v w
      simp only [ContinuousLinearMap.trilinearCompSame_apply]
      exact C.skew _ _ _ }

end EnergyConvectionForm

end
