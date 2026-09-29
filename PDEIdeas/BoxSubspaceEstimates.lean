import PDEIdeas.BoxLadyzhenskayaInequality
import PDEIdeas.BoxPoincare

/-!
# Restriction of the two-dimensional box estimates to an energy subspace

The Ladyzhenskaya inequality of `PDEIdeas.BoxLadyzhenskayaInequality` and the
Poincaré inequality of `PDEIdeas.BoxPoincare` are statements about the closed
energy space `BoxH1ZeroSigma I`.  Every closed subspace of that space — and,
more generally, every topological `ℝ`-module carrying a continuous linear map
into it — inherits both estimates *with the same constants*: all of the
analytic content is already carried by the ambient maps `boxEnergyToState`,
`boxEnergyGradient` and by the `L4` realization
`BoxEnergyL4Realization.toLp4`, and restriction only precomposes with a
continuous linear map.

Nothing here reproves an analytic inequality.  Each estimate below is the
ambient one evaluated at `ι w`, where

  `ι : W →L[ℝ] BoxH1ZeroSigma I`

is the embedding of the subspace.  `W` carries only the structure needed to
state `W →L[ℝ] BoxH1ZeroSigma I`, so the results apply verbatim to

* a submodule `S : Submodule ℝ (BoxH1ZeroSigma I)` through
  `boxEnergySubspaceInclusion` (`Submodule.subtypeL`), which is norm
  preserving; closedness of `S` is not needed for the estimates, it is what
  makes `S` complete (`boxEnergySubspace_completeSpace`);
* a future closure space modelling a subdomain `Ω ⊆ I`, which only has to
  supply its own `ι` — for instance extension by zero of `Ω`-fields to the box
  — in order to obtain every estimate and the bundled
  `BoxSubspaceEnergyEstimates`.  No file constructing such a space is mentioned
  or imported here.

## Main results

* `boxSubspace_l4_sq_le` — Ladyzhenskaya on the subspace, constant
  `L.constant`, unchanged.
* `boxSubspace_state_le` — Poincaré on the subspace, constant
  `boxPoincareConstant I`, unchanged.
* `boxSubspace_l4_sq_le_gradient_sq` — the two combined, constant
  `L.constant * boxPoincareConstant I`.
* `boxSubspace_embedding_norm_le_gradient`, `boxSubspace_norm_le_gradient` —
  graph-norm control, constant `Real.sqrt (1 + boxPoincareConstant I ^ 2)`,
  unchanged.
* `boxSubspace_forcing_work_le` — absorption of a forcing functional, constant
  `1 + boxPoincareConstant I ^ 2`, unchanged.
* `BoxSubspaceEnergyEstimates` and `boxSubspaceEnergyEstimates` — the above
  bundled for downstream reuse.
-/

open MeasureTheory Set Real InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 400000

local instance boxSubspaceFactOneLeFour : Fact (1 ≤ (4 : ℝ≥0∞)) :=
  ⟨by norm_num⟩

variable (I : BoxIntegral.Box (Fin 2))
variable {W : Type*} [AddCommMonoid W] [Module ℝ W] [TopologicalSpace W]

/-! ### The restricted maps

Each map below is the corresponding ambient map precomposed with the
embedding; no new realization is constructed. -/

/-- The state (velocity) component of a subspace element. -/
def boxSubspaceState (ι : W →L[ℝ] BoxH1ZeroSigma I) : W →L[ℝ] BoxL2Sigma I :=
  (boxEnergyToState I).comp ι

/-- The gradient component of a subspace element. -/
def boxSubspaceGradient (ι : W →L[ℝ] BoxH1ZeroSigma I) :
    W →L[ℝ] BoxGradientL2 I :=
  (boxEnergyGradient I).comp ι

/-- The `L4` representative of a subspace element, taken from the existing box
`L4` realization. -/
def boxSubspaceLp4 (E : BoxEnergyL4Realization I)
    (ι : W →L[ℝ] BoxH1ZeroSigma I) : W →L[ℝ] BoxVelocityL4 I :=
  E.toLp4.comp ι

@[simp]
theorem boxSubspaceState_apply (ι : W →L[ℝ] BoxH1ZeroSigma I) (w : W) :
    boxSubspaceState I ι w = boxEnergyToState I (ι w) :=
  rfl

@[simp]
theorem boxSubspaceGradient_apply (ι : W →L[ℝ] BoxH1ZeroSigma I) (w : W) :
    boxSubspaceGradient I ι w = boxEnergyGradient I (ι w) :=
  rfl

@[simp]
theorem boxSubspaceLp4_apply (E : BoxEnergyL4Realization I)
    (ι : W →L[ℝ] BoxH1ZeroSigma I) (w : W) :
    boxSubspaceLp4 I E ι w = E.toLp4 (ι w) :=
  rfl

/-- The restricted `L4` representative still represents the restricted state. -/
theorem coeFn_boxSubspaceLp4_eq_state (E : BoxEnergyL4Realization I)
    (ι : W →L[ℝ] BoxH1ZeroSigma I) (w : W) :
    (boxSubspaceLp4 I E ι w : (Fin 2 → ℝ) → BoxVelocityValue 1) =ᵐ[BoxMeasure I]
      (boxSubspaceState I ι w : (Fin 2 → ℝ) → BoxVelocityValue 1) :=
  E.coeFn_toLp4_eq_state (ι w)

/-- The diffusion form restricted to the subspace. -/
def boxSubspaceDiffusion (ι : W →L[ℝ] BoxH1ZeroSigma I) (v w : W) : ℝ :=
  boxGradientDiffusion I (ι v) (ι w)

@[simp]
theorem boxSubspaceDiffusion_apply (ι : W →L[ℝ] BoxH1ZeroSigma I) (v w : W) :
    boxSubspaceDiffusion I ι v w = boxGradientDiffusion I (ι v) (ι w) :=
  rfl

theorem boxSubspaceDiffusion_self (ι : W →L[ℝ] BoxH1ZeroSigma I) (w : W) :
    boxSubspaceDiffusion I ι w w = ‖boxSubspaceGradient I ι w‖ ^ 2 :=
  boxGradientDiffusion_self I (ι w)

theorem boxSubspaceDiffusion_nonneg (ι : W →L[ℝ] BoxH1ZeroSigma I) (w : W) :
    0 ≤ boxSubspaceDiffusion I ι w w :=
  boxGradientDiffusion_nonneg I (ι w)

/-! ### The inherited estimates -/

/-- **Ladyzhenskaya inequality on an energy subspace.**  The constant is the
constant `L.constant` of the ambient realization, unchanged. -/
theorem boxSubspace_l4_sq_le (L : BoxLadyzhenskayaRealization I)
    (ι : W →L[ℝ] BoxH1ZeroSigma I) (w : W) :
    ‖boxSubspaceLp4 I L.toBoxEnergyL4Realization ι w‖ ^ 2 ≤
      L.constant * ‖boxSubspaceState I ι w‖ * ‖boxSubspaceGradient I ι w‖ :=
  L.l4_sq_le (ι w)

/-- **Poincaré inequality on an energy subspace.**  The constant is the box
constant `boxPoincareConstant I`, unchanged. -/
theorem boxSubspace_state_le (ι : W →L[ℝ] BoxH1ZeroSigma I) (w : W) :
    ‖boxSubspaceState I ι w‖ ≤
      boxPoincareConstant I * ‖boxSubspaceGradient I ι w‖ :=
  boxPoincare I (ι w)

/-- Ladyzhenskaya and Poincaré combined on the subspace: the `L4` norm is
controlled by the gradient alone, with constant
`L.constant * boxPoincareConstant I`. -/
theorem boxSubspace_l4_sq_le_gradient_sq (L : BoxLadyzhenskayaRealization I)
    (ι : W →L[ℝ] BoxH1ZeroSigma I) (w : W) :
    ‖boxSubspaceLp4 I L.toBoxEnergyL4Realization ι w‖ ^ 2 ≤
      (L.constant * boxPoincareConstant I) *
        ‖boxSubspaceGradient I ι w‖ ^ 2 := by
  have hC := L.constant_nonneg
  have hg : (0 : ℝ) ≤ ‖boxSubspaceGradient I ι w‖ := norm_nonneg _
  calc
    ‖boxSubspaceLp4 I L.toBoxEnergyL4Realization ι w‖ ^ 2 ≤
        L.constant * ‖boxSubspaceState I ι w‖ *
          ‖boxSubspaceGradient I ι w‖ :=
      boxSubspace_l4_sq_le I L ι w
    _ ≤ L.constant *
          (boxPoincareConstant I * ‖boxSubspaceGradient I ι w‖) *
          ‖boxSubspaceGradient I ι w‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (boxSubspace_state_le I ι w) hC) hg
    _ = (L.constant * boxPoincareConstant I) *
          ‖boxSubspaceGradient I ι w‖ ^ 2 := by ring

/-- The graph norm of the image of a subspace element is controlled by its
gradient, with the ambient constant
`Real.sqrt (1 + boxPoincareConstant I ^ 2)`. -/
theorem boxSubspace_embedding_norm_le_gradient (ι : W →L[ℝ] BoxH1ZeroSigma I)
    (w : W) :
    ‖ι w‖ ≤
      Real.sqrt (1 + boxPoincareConstant I ^ 2) *
        ‖boxSubspaceGradient I ι w‖ :=
  boxEnergy_norm_le_gradient I (ι w)

/-- For a norm-preserving embedding the subspace norm itself is controlled by
the gradient, with the ambient constant. -/
theorem boxSubspace_norm_le_gradient [Norm W] (ι : W →L[ℝ] BoxH1ZeroSigma I)
    (hι : ∀ v : W, ‖ι v‖ = ‖v‖) (w : W) :
    ‖w‖ ≤
      Real.sqrt (1 + boxPoincareConstant I ^ 2) *
        ‖boxSubspaceGradient I ι w‖ := by
  rw [← hι w]
  exact boxSubspace_embedding_norm_le_gradient I ι w

/-- **State-independent absorption of a forcing functional on a subspace.**
The forcing is measured by any real majorant `f` of its dual norm taken
relative to the ambient graph norm.  The constant
`1 + boxPoincareConstant I ^ 2` is the ambient one. -/
theorem boxSubspace_forcing_work_le (ι : W →L[ℝ] BoxH1ZeroSigma I)
    (F : W →L[ℝ] ℝ) (f : ℝ) (hf : 0 ≤ f)
    (hbound : ∀ v : W, ‖F v‖ ≤ f * ‖ι v‖) (w : W) :
    2 * F w ≤
      (1 + boxPoincareConstant I ^ 2) * f ^ 2 +
        boxSubspaceDiffusion I ι w w := by
  have hKnonneg : (0 : ℝ) ≤ 1 + boxPoincareConstant I ^ 2 := by positivity
  have h1 : F w ≤ f * ‖ι w‖ := by
    have hnorm : |F w| ≤ f * ‖ι w‖ := by
      simpa only [Real.norm_eq_abs] using hbound w
    exact (le_abs_self _).trans hnorm
  have h2 := boxSubspace_embedding_norm_le_gradient I ι w
  have hmul : f * ‖ι w‖ ≤
      f * (Real.sqrt (1 + boxPoincareConstant I ^ 2) *
        ‖boxSubspaceGradient I ι w‖) :=
    mul_le_mul_of_nonneg_left h2 hf
  have hyoung := two_mul_le_add_sq
    (Real.sqrt (1 + boxPoincareConstant I ^ 2) * f)
    ‖boxSubspaceGradient I ι w‖
  have hsq : (Real.sqrt (1 + boxPoincareConstant I ^ 2) * f) ^ 2 =
      (1 + boxPoincareConstant I ^ 2) * f ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hKnonneg]
  rw [boxSubspaceDiffusion_self I ι w, ← hsq]
  linarith

/-- The absorption statement for a functional bounded in the subspace norm,
when the embedding is norm preserving. -/
theorem boxSubspace_forcing_work_le_of_isometry [Norm W]
    (ι : W →L[ℝ] BoxH1ZeroSigma I) (hι : ∀ v : W, ‖ι v‖ = ‖v‖)
    (F : W →L[ℝ] ℝ) (f : ℝ) (hf : 0 ≤ f)
    (hbound : ∀ v : W, ‖F v‖ ≤ f * ‖v‖) (w : W) :
    2 * F w ≤
      (1 + boxPoincareConstant I ^ 2) * f ^ 2 +
        boxSubspaceDiffusion I ι w w := by
  refine boxSubspace_forcing_work_le I ι F f hf ?_ w
  intro v
  rw [hι v]
  exact hbound v

/-! ### Bundled data for downstream use -/

/-- The Ladyzhenskaya and Poincaré estimates available on a space `W` mapping
into the box energy space.  A downstream closure space (for a subdomain `Ω`,
say) obtains this structure from `boxSubspaceEnergyEstimates` by supplying only
its own continuous linear map into `BoxH1ZeroSigma I`. -/
structure BoxSubspaceEnergyEstimates (I : BoxIntegral.Box (Fin 2))
    (W : Type*) [AddCommMonoid W] [Module ℝ W] [TopologicalSpace W] where
  /-- `L4` representative of a subspace element. -/
  toLp4 : W →L[ℝ] BoxVelocityL4 I
  /-- State (velocity) component. -/
  state : W →L[ℝ] BoxL2Sigma I
  /-- Gradient component. -/
  gradient : W →L[ℝ] BoxGradientL2 I
  /-- The Ladyzhenskaya constant. -/
  ladyConstant : ℝ
  ladyConstant_nonneg : 0 ≤ ladyConstant
  /-- The `L4-L2-H1` estimate. -/
  l4_sq_le : ∀ w : W,
    ‖toLp4 w‖ ^ 2 ≤ ladyConstant * ‖state w‖ * ‖gradient w‖
  /-- The Poincaré constant. -/
  poincareConstant : ℝ
  poincareConstant_nonneg : 0 ≤ poincareConstant
  /-- The Poincaré estimate. -/
  state_le : ∀ w : W, ‖state w‖ ≤ poincareConstant * ‖gradient w‖

namespace BoxSubspaceEnergyEstimates

variable {I}
variable (E : BoxSubspaceEnergyEstimates I W)

/-- The `L4` norm is controlled by the gradient alone, with constant
`ladyConstant * poincareConstant`. -/
theorem l4_sq_le_gradient_sq (w : W) :
    ‖E.toLp4 w‖ ^ 2 ≤
      (E.ladyConstant * E.poincareConstant) * ‖E.gradient w‖ ^ 2 := by
  have hg : (0 : ℝ) ≤ ‖E.gradient w‖ := norm_nonneg _
  calc
    ‖E.toLp4 w‖ ^ 2 ≤
        E.ladyConstant * ‖E.state w‖ * ‖E.gradient w‖ := E.l4_sq_le w
    _ ≤ E.ladyConstant * (E.poincareConstant * ‖E.gradient w‖) *
          ‖E.gradient w‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (E.state_le w) E.ladyConstant_nonneg) hg
    _ = (E.ladyConstant * E.poincareConstant) * ‖E.gradient w‖ ^ 2 := by ring

/-- The square-root form of `l4_sq_le_gradient_sq`. -/
theorem norm_toLp4_le (w : W) :
    ‖E.toLp4 w‖ ≤
      Real.sqrt (E.ladyConstant * E.poincareConstant) * ‖E.gradient w‖ := by
  have hprod : (0 : ℝ) ≤ E.ladyConstant * E.poincareConstant :=
    mul_nonneg E.ladyConstant_nonneg E.poincareConstant_nonneg
  have hrhs : (0 : ℝ) ≤
      Real.sqrt (E.ladyConstant * E.poincareConstant) * ‖E.gradient w‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  refine (sq_le_sq₀ (norm_nonneg _) hrhs).mp ?_
  calc
    ‖E.toLp4 w‖ ^ 2 ≤
        (E.ladyConstant * E.poincareConstant) * ‖E.gradient w‖ ^ 2 :=
      E.l4_sq_le_gradient_sq w
    _ = (Real.sqrt (E.ladyConstant * E.poincareConstant) *
          ‖E.gradient w‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hprod]

end BoxSubspaceEnergyEstimates

/-- Every continuous linear map into the box energy space inherits the box
Ladyzhenskaya and Poincaré estimates, with the ambient constants. -/
def boxSubspaceEnergyEstimates (L : BoxLadyzhenskayaRealization I)
    (ι : W →L[ℝ] BoxH1ZeroSigma I) : BoxSubspaceEnergyEstimates I W where
  toLp4 := boxSubspaceLp4 I L.toBoxEnergyL4Realization ι
  state := boxSubspaceState I ι
  gradient := boxSubspaceGradient I ι
  ladyConstant := L.constant
  ladyConstant_nonneg := L.constant_nonneg
  l4_sq_le := boxSubspace_l4_sq_le I L ι
  poincareConstant := boxPoincareConstant I
  poincareConstant_nonneg := boxPoincareConstant_nonneg I
  state_le := boxSubspace_state_le I ι

@[simp]
theorem boxSubspaceEnergyEstimates_ladyConstant
    (L : BoxLadyzhenskayaRealization I) (ι : W →L[ℝ] BoxH1ZeroSigma I) :
    (boxSubspaceEnergyEstimates I L ι).ladyConstant = L.constant :=
  rfl

@[simp]
theorem boxSubspaceEnergyEstimates_poincareConstant
    (L : BoxLadyzhenskayaRealization I) (ι : W →L[ℝ] BoxH1ZeroSigma I) :
    (boxSubspaceEnergyEstimates I L ι).poincareConstant =
      boxPoincareConstant I :=
  rfl

/-- The ambient energy space is the special case `ι = id`. -/
def boxEnergyEstimates (L : BoxLadyzhenskayaRealization I) :
    BoxSubspaceEnergyEstimates I (BoxH1ZeroSigma I) :=
  boxSubspaceEnergyEstimates I L (ContinuousLinearMap.id ℝ (BoxH1ZeroSigma I))

/-! ### Subspaces of the energy space -/

section EnergySubmodule

variable (S : Submodule ℝ (BoxH1ZeroSigma I))

/-- The inclusion of an energy subspace into the energy space. -/
def boxEnergySubspaceInclusion : S →L[ℝ] BoxH1ZeroSigma I :=
  S.subtypeL

@[simp]
theorem boxEnergySubspaceInclusion_apply (v : S) :
    boxEnergySubspaceInclusion I S v = (v : BoxH1ZeroSigma I) :=
  rfl

/-- The inclusion of an energy subspace preserves the graph norm. -/
theorem norm_boxEnergySubspaceInclusion (v : S) :
    ‖boxEnergySubspaceInclusion I S v‖ = ‖v‖ :=
  rfl

/-- A closed energy subspace is complete, hence a Hilbert space in the graph
norm.  The estimates below do not use this. -/
theorem boxEnergySubspace_completeSpace
    (hS : IsClosed (S : Set (BoxH1ZeroSigma I))) : CompleteSpace S :=
  hS.completeSpace_coe

/-- **Ladyzhenskaya inequality on an energy subspace**, same constant. -/
theorem boxEnergySubspace_l4_sq_le (L : BoxLadyzhenskayaRealization I) (v : S) :
    ‖boxSubspaceLp4 I L.toBoxEnergyL4Realization
        (boxEnergySubspaceInclusion I S) v‖ ^ 2 ≤
      L.constant *
        ‖boxSubspaceState I (boxEnergySubspaceInclusion I S) v‖ *
        ‖boxSubspaceGradient I (boxEnergySubspaceInclusion I S) v‖ :=
  boxSubspace_l4_sq_le I L (boxEnergySubspaceInclusion I S) v

/-- **Poincaré inequality on an energy subspace**, same constant. -/
theorem boxEnergySubspace_state_le (v : S) :
    ‖boxSubspaceState I (boxEnergySubspaceInclusion I S) v‖ ≤
      boxPoincareConstant I *
        ‖boxSubspaceGradient I (boxEnergySubspaceInclusion I S) v‖ :=
  boxSubspace_state_le I (boxEnergySubspaceInclusion I S) v

/-- The subspace norm is controlled by the gradient, same constant. -/
theorem boxEnergySubspace_norm_le_gradient (v : S) :
    ‖v‖ ≤
      Real.sqrt (1 + boxPoincareConstant I ^ 2) *
        ‖boxSubspaceGradient I (boxEnergySubspaceInclusion I S) v‖ :=
  boxSubspace_norm_le_gradient I (boxEnergySubspaceInclusion I S)
    (norm_boxEnergySubspaceInclusion I S) v

/-- Forcing absorption on an energy subspace, same constant. -/
theorem boxEnergySubspace_forcing_work_le (F : S →L[ℝ] ℝ) (f : ℝ) (hf : 0 ≤ f)
    (hbound : ∀ v : S, ‖F v‖ ≤ f * ‖v‖) (v : S) :
    2 * F v ≤
      (1 + boxPoincareConstant I ^ 2) * f ^ 2 +
        boxSubspaceDiffusion I (boxEnergySubspaceInclusion I S) v v :=
  boxSubspace_forcing_work_le_of_isometry I (boxEnergySubspaceInclusion I S)
    (norm_boxEnergySubspaceInclusion I S) F f hf hbound v

/-- The bundled estimates carried by an energy subspace. -/
def boxEnergySubspaceEstimates (L : BoxLadyzhenskayaRealization I) :
    BoxSubspaceEnergyEstimates I S :=
  boxSubspaceEnergyEstimates I L (boxEnergySubspaceInclusion I S)

end EnergySubmodule

end
