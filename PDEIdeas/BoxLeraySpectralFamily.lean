import PDEIdeas.BoxGalerkinSolutionBounds
import PDEIdeas.GalerkinL2Compactness

/-!
# Strong `L²` compactness for box Galerkin families

The compact box embedding and the dependent variational compactness theorem
combine here.  Finite coefficient types may vary with the Galerkin level;
the physical lift estimates are supplied by `BoxGalerkinSolutionBounds`.
-/

open BoundedContinuousFunction InnerProductSpace MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

variable {n : ℕ}

/-- Fixed-box specialization of the varying-dimension variational spectral
compactness theorem. -/
noncomputable def boxLeraySpectralCompactFamilyOfVariationalDualL2Family
    {a b : ℝ} (hab : a ≤ b)
    (I : BoxIntegral.Box (Fin (n + 1)))
    {ι : Type*} {W : ℕ → Type*} {Test : Type*}
    [∀ m, NormedAddCommGroup (W m)]
    [∀ m, InnerProductSpace ℝ (W m)]
    [∀ m, CompleteSpace (W m)]
    [NormedAddCommGroup Test] [NormedSpace ℝ Test]
    (basis : HilbertBasis ι ℝ (BoxL2Sigma I))
    (exhaustion : HilbertBasisExhaustion ι)
    (lift : ℕ → Icc a b →ᵇ BoxH1ZeroSigma I)
    (stateRadius : ℝ)
    (state_bound : ∀ m t,
      ‖boxEnergyToState I (lift m t)‖ ≤ stateRadius)
    (liftLpRadius : ℝ) (liftLpRadius_nonneg : 0 ≤ liftLpRadius)
    (liftLp_bound : ∀ m,
      ‖BoundedContinuousFunction.toLp (2 : ℝ≥0∞)
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) ℝ
        (lift m)‖ ≤ liftLpRadius)
    (problem : ∀ m, VariationalGalerkinProblem (W m))
    (solution : ∀ m,
      (problem m).LocalSolutionOn (⟨a, le_rfl, hab⟩ : Icc a b))
    (testProjection : ∀ m, Test →L[ℝ] W m)
    (testMode : ι → Test)
    (coordinate_eq : ∀ m (t : Icc a b) i,
      ⟪(solution m).toFun t, testProjection m (testMode i)⟫_ℝ =
        ⟪boxEnergyToState I (lift m t), basis i⟫_ℝ)
    (dualRadius : ℝ≥0)
    (dual_memLp : ∀ m,
      MemLp
        (fun t =>
          (problem m).dualRHS
            (testProjection m) t ((solution m).toFun t))
        2 (volume.restrict (Icc a b)))
    (dual_sq_integral_bound : ∀ m,
      ∫ t in a..b,
          ‖(problem m).dualRHS
            (testProjection m) t ((solution m).toFun t)‖ ^ 2 ≤
        (dualRadius : ℝ) ^ 2) :
    LeraySpectralCompactFamily
      (I := Icc a b)
      (V := BoxH1ZeroSigma I) (H := BoxL2Sigma I)
      (μ := SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) := by
  letI : CompleteSpace (BoxL2Sigma I) := boxL2Sigma_completeSpace I
  exact
    @LeraySpectralCompactFamily.ofHilbertBasisExhaustionOfVariationalDualL2Family
      (BoxH1ZeroSigma I) (BoxL2Sigma I)
      inferInstance inferInstance inferInstance inferInstance
      (boxL2Sigma_completeSpace I)
      a b hab
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)
      inferInstance
      ι W Test inferInstance inferInstance inferInstance inferInstance inferInstance
      basis exhaustion (boxEnergyToState I)
      (boxEnergyToState_isCompactOperator_fourier I)
      lift stateRadius state_bound
      liftLpRadius liftLpRadius_nonneg liftLp_bound
      problem solution testProjection testMode coordinate_eq
      dualRadius dual_memLp dual_sq_integral_bound

/-- Every assembled box spectral family has a strict subsequence converging
strongly in `L²((a,b); L²_σ)`. -/
theorem exists_boxLeray_strongL2_subsequence
    {a b : ℝ}
    {I : BoxIntegral.Box (Fin (n + 1))}
    (G : LeraySpectralCompactFamily
      (I := Icc a b)
      (V := BoxH1ZeroSigma I) (H := BoxL2Sigma I)
      (μ := SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)) :
    Nonempty (StrongMetricSubsequence G.stateLp) :=
  @LeraySpectralCompactFamily.exists_strongL2_subsequence
    (Icc a b) (BoxH1ZeroSigma I) (BoxL2Sigma I)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    (boxL2Sigma_completeSpace I)
    (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)
    inferInstance G

end
