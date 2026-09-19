import PDEIdeas.BoxEnergyClosability

/-!
# Weak Sobolev structure of the box graph closure

The product norm on the graph closure is exactly the sum of the squared state
and gradient norms. The trace of the closed gradient vanishes in scalar L2,
so every element of the closure retains incompressibility at the weak-gradient
level.
-/

open MeasureTheory Real InnerProductSpace Set
open scoped ContDiff ENNReal NNReal RealInnerProductSpace

noncomputable section

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

variable {n : ℕ}

/-- The trace of a full Euclidean gradient matrix. -/
def boxGradientTraceValue :
    BoxGradientValue n →L[ℝ] ℝ :=
  ∑ i : Fin (n + 1), boxGradientCoordinateValue i i

@[simp]
theorem boxGradientTraceValue_apply
    (A : BoxGradientValue n) :
    boxGradientTraceValue A = ∑ i : Fin (n + 1), A (i, i) := by
  simp [boxGradientTraceValue, boxGradientCoordinateValue]

/-- Distributional divergence represented in scalar L2 by taking the trace of
the closed gradient. -/
def boxGradientDivergenceLp
    (I : BoxIntegral.Box (Fin (n + 1))) :
    BoxGradientL2 I →L[ℝ] BoxScalarL2 I :=
  boxGradientTraceValue.compLpL 2 (BoxMeasure I)

theorem boxGradientDivergenceLp_apply_eq_sum
    (I : BoxIntegral.Box (Fin (n + 1)))
    (G : BoxGradientL2 I) :
    boxGradientDivergenceLp I G =
      ∑ i : Fin (n + 1), boxGradientCoordinateLp I i i G := by
  classical
  change
    ((∑ i : Fin (n + 1), boxGradientCoordinateValue i i).compLpL
      2 (BoxMeasure I)) G =
      ∑ i : Fin (n + 1),
        (boxGradientCoordinateValue i i).compLpL 2 (BoxMeasure I) G
  have hsum : ∀ s : Finset (Fin (n + 1)),
      ((∑ i ∈ s, boxGradientCoordinateValue i i).compLpL
        2 (BoxMeasure I)) G =
        ∑ i ∈ s,
          (boxGradientCoordinateValue i i).compLpL 2 (BoxMeasure I) G := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty]
        apply Lp.ext
        filter_upwards [
          (0 : BoxGradientValue n →L[ℝ] ℝ).coeFn_compLpL G,
          Lp.coeFn_zero ℝ 2 (BoxMeasure I)] with x hmap hzero
        rw [hmap, hzero]
        rfl
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi,
          ContinuousLinearMap.add_compLpL,
          ContinuousLinearMap.add_apply, ih]
  simpa using hsum Finset.univ

/-- Divergence on the ambient velocity-gradient graph space. -/
def boxEnergyAmbientDivergence
    (I : BoxIntegral.Box (Fin (n + 1))) :
    BoxEnergyAmbient I →L[ℝ] BoxScalarL2 I :=
  (boxGradientDivergenceLp I).comp (boxEnergyGradientProjection I)

/-- Divergence on the closed energy space. -/
def boxEnergyDivergence
    (I : BoxIntegral.Box (Fin (n + 1))) :
    BoxH1ZeroSigma I →L[ℝ] BoxScalarL2 I :=
  (boxGradientDivergenceLp I).comp (boxEnergyGradient I)

theorem boxGradientDivergenceLp_gradientLp
    {I : BoxIntegral.Box (Fin (n + 1))}
    (u : SmoothBoxEnergyField I) :
    boxGradientDivergenceLp I u.gradientLp = 0 := by
  change boxGradientTraceValue.compLpL 2 (BoxMeasure I) u.gradientLp = 0
  apply Lp.ext
  filter_upwards [
    boxGradientTraceValue.coeFn_compLpL u.gradientLp,
    u.gradient_memLp.coeFn_toLp,
    ae_restrict_mem (BoxIntegral.Box.measurableSet_Icc I),
    Lp.coeFn_zero ℝ 2 (BoxMeasure I)] with x htrace hgradient hx hzero
  rw [hzero, htrace]
  change boxGradientTraceValue
    ((u.gradient_memLp.toLp (boxGradientValue u.derivative)) x) = 0
  rw [hgradient]
  rw [boxGradientTraceValue_apply]
  simpa [boxGradientValue] using u.divergence_field x hx

@[simp]
theorem boxEnergyAmbientDivergence_graphPoint
    {I : BoxIntegral.Box (Fin (n + 1))}
    (u : SmoothBoxEnergyField I) :
    boxEnergyAmbientDivergence I u.graphPoint = 0 := by
  simpa [boxEnergyAmbientDivergence] using
    boxGradientDivergenceLp_gradientLp u

theorem smoothBoxGraphCore_le_boxEnergyAmbientDivergence_ker
    (I : BoxIntegral.Box (Fin (n + 1))) :
    smoothBoxGraphCore I ≤ (boxEnergyAmbientDivergence I).ker := by
  apply Submodule.span_le.mpr
  rintro _ ⟨u, rfl⟩
  exact boxEnergyAmbientDivergence_graphPoint u

/-- The closed gradient of every box energy state has zero trace in L2. -/
theorem boxEnergyDivergence_eq_zero
    (I : BoxIntegral.Box (Fin (n + 1)))
    (u : BoxH1ZeroSigma I) :
    boxEnergyDivergence I u = 0 := by
  have hu :
      (u : BoxEnergyAmbient I) ∈ (boxEnergyAmbientDivergence I).ker :=
    (smoothBoxGraphCore I).topologicalClosure_minimal
      (smoothBoxGraphCore_le_boxEnergyAmbientDivergence_ker I)
      (boxEnergyAmbientDivergence I).isClosed_ker
      u.property
  simpa [boxEnergyDivergence, boxEnergyAmbientDivergence] using hu

theorem boxEnergyGradient_diagonal_inner_sum_eq_zero
    (I : BoxIntegral.Box (Fin (n + 1)))
    (u : BoxH1ZeroSigma I)
    (g : (Fin (n + 1) → ℝ) → ℝ)
    (hg : ContDiff ℝ (∞ : WithTop ℕ∞) g)
    (hgc : HasCompactSupport g) :
    ∑ i : Fin (n + 1),
      ⟪smoothBoxScalarTestLp I g hg hgc,
        boxGradientCoordinateLp I i i (boxEnergyGradient I u)⟫_ℝ = 0 := by
  have hdiv := boxEnergyDivergence_eq_zero I u
  have hinner := congrArg
    (fun z : BoxScalarL2 I =>
      ⟪smoothBoxScalarTestLp I g hg hgc, z⟫_ℝ) hdiv
  simp only [boxEnergyDivergence, ContinuousLinearMap.comp_apply,
    inner_zero_right] at hinner
  rw [boxGradientDivergenceLp_apply_eq_sum] at hinner
  change ∑ i : Fin (n + 1),
    (innerSL ℝ (smoothBoxScalarTestLp I g hg hgc))
      (boxGradientCoordinateLp I i i (boxEnergyGradient I u)) = 0
  rw [← _root_.map_sum]
  exact hinner

/-- The state component is weakly divergence-free against every smooth
compactly supported scalar test. -/
theorem boxEnergyToState_weakDivergence_eq_zero
    (I : BoxIntegral.Box (Fin (n + 1)))
    (u : BoxH1ZeroSigma I)
    (g : (Fin (n + 1) → ℝ) → ℝ)
    (hg : ContDiff ℝ (∞ : WithTop ℕ∞) g)
    (hgc : HasCompactSupport g) :
    ∑ i : Fin (n + 1),
      ⟪smoothBoxScalarDerivativeTestLp I i g hg hgc,
        boxVelocityCoordinateLp I i
          (boxEnergyToState I u : BoxVelocityL2 I)⟫_ℝ = 0 := by
  have hpair :
      ∑ i : Fin (n + 1),
        (⟪smoothBoxScalarTestLp I g hg hgc,
            boxGradientCoordinateLp I i i
              (boxEnergyGradientProjection I
                (u : BoxEnergyAmbient I))⟫_ℝ +
          ⟪smoothBoxScalarDerivativeTestLp I i g hg hgc,
            boxVelocityCoordinateLp I i
              (boxEnergyVelocityProjection I
                (u : BoxEnergyAmbient I))⟫_ℝ) = 0 := by
    apply Finset.sum_eq_zero
    intro i _hi
    exact boxWeakDerivativePairing_eq_zero I i i g hg hgc u
  rw [Finset.sum_add_distrib] at hpair
  have hgradient :
      ∑ i : Fin (n + 1),
        ⟪smoothBoxScalarTestLp I g hg hgc,
          boxGradientCoordinateLp I i i
            (boxEnergyGradientProjection I
              (u : BoxEnergyAmbient I))⟫_ℝ = 0 := by
    simpa [boxEnergyGradient] using
      boxEnergyGradient_diagonal_inner_sum_eq_zero I u g hg hgc
  have hvelocity :
      ∑ i : Fin (n + 1),
        ⟪smoothBoxScalarDerivativeTestLp I i g hg hgc,
          boxVelocityCoordinateLp I i
            (boxEnergyVelocityProjection I
              (u : BoxEnergyAmbient I))⟫_ℝ = 0 := by
    linarith
  simpa [boxEnergyToState] using hvelocity

/-- Exact graph-norm identity for the canonical state and gradient maps. -/
theorem boxEnergy_norm_sq_eq_state_add_gradient
    (I : BoxIntegral.Box (Fin (n + 1)))
    (u : BoxH1ZeroSigma I) :
    ‖u‖ ^ 2 =
      ‖boxEnergyToState I u‖ ^ 2 + ‖boxEnergyGradient I u‖ ^ 2 := by
  simpa [boxEnergyToState, boxEnergyGradient,
    boxEnergyVelocityProjection, boxEnergyGradientProjection] using
      (WithLp.prod_norm_sq_eq_of_L2 (u : BoxEnergyAmbient I))

end
