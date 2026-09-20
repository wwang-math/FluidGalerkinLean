import PDEIdeas.Paper

/-!
# Statement checks

Explicit expected types guard theorem hypotheses and conclusions, not just
declaration names.
-/

open InnerProductSpace MeasureTheory

noncomputable section

example {I : BoxIntegral.Box (Fin 2)} {a b : ℝ}
    (hab : a ≤ b) (u₀ : BoxL2Sigma I) :
    Nonempty
      (BoxCompactSpectralRepresentation.BoxLerayEnergyWeakSolutionOn I a b u₀) :=
  exists_zeroForcing_twoDimensional_lerayHopfSolution hab u₀

example {n : ℕ} (I : BoxIntegral.Box (Fin (n + 1))) :
    IsCompactOperator (boxEnergyToState I) :=
  boxEnergyToState_isCompactOperator_fourier I

example (I : BoxIntegral.Box (Fin 2)) : BoxLadyzhenskayaRealization I :=
  boxLadyzhenskayaRealization I

example {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [TopologicalSpace.SeparableSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (J : V →L[ℝ] H) (hcompact : IsCompactOperator J)
    (hinjective : Function.Injective J) (hdense : DenseRange J)
    (hcontractive : ∀ v, ‖J v‖ ≤ ‖v‖) :
    CompactEmbeddingSpectralRepresentation J :=
  compactEmbeddingSpectralRepresentation J hcompact hinjective hdense hcontractive

example {I : BoxIntegral.Box (Fin 2)}
    (S : BoxCompactSpectralRepresentation I) {a b : ℝ}
    (hab : a ≤ b) (u₀ : BoxL2Sigma I) :
    Nonempty
      (S.zeroForcingLeraySpectralCompactFamily2D hab u₀).StrongWeakPathSubsequence :=
  S.exists_zeroForcing_twoDimensional_strongWeakPath_subsequence hab u₀

open scoped ENNReal RealInnerProductSpace

example {I : BoxIntegral.Box (Fin 2)} {a b : ℝ} {u₀ : BoxL2Sigma I}
    (u : BoxCompactSpectralRepresentation.BoxLerayEnergyWeakSolutionOn I a b u₀)
    (y : BoxL2Sigma I) : Continuous (fun t => ⟪u.weakState t, y⟫_ℝ) :=
  u.weakState_inner_continuous y

example {I : BoxIntegral.Box (Fin 2)} {a b : ℝ} {u₀ : BoxL2Sigma I}
    (u : BoxCompactSpectralRepresentation.BoxLerayEnergyWeakSolutionOn I a b u₀)
    (t : Set.Icc a b) :
    ‖u.weakState t‖ ^ 2 +
        2 * ∫ s : Set.Icc a b in Set.Iic t,
          ‖boxEnergyGradient I (u.energy s)‖ ^ 2
          ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b ≤ ‖u₀‖ ^ 2 :=
  u.energy_inequality t

example {I : BoxIntegral.Box (Fin 2)} {a b : ℝ} {u₀ : BoxL2Sigma I}
    (u : BoxCompactSpectralRepresentation.BoxLerayEnergyWeakSolutionOn I a b u₀)
    (φ : BoxH1ZeroSigma I) (eta : LerayIntervalTimeTest a b)
    (hterminal : eta.value b = 0) :
    -(∫ t : Set.Icc a b,
        ⟪u.state t, boxEnergyToState I φ⟫_ℝ * eta.deriv t
        ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) +
      (∫ t : Set.Icc a b,
        boxGradientDiffusion I (u.energy t) φ * eta.value t
        ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) +
      (∫ t : Set.Icc a b,
        (boxLadyzhenskayaRealization I).toBoxEnergyL4Realization.convectionForm I
          (u.energy t) (u.energy t) φ * eta.value t
        ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) =
      ⟪u₀, boxEnergyToState I φ⟫_ℝ * eta.value a :=
  u.weak_equation φ eta hterminal

example {I : BoxIntegral.Box (Fin 2)} (v : BoxH1ZeroSigma I) :
    ‖boxEnergyToState I v‖ ≤
      boxPoincareConstant I * ‖boxEnergyGradient I v‖ :=
  boxPoincare I v

example {I : BoxIntegral.Box (Fin 2)} (v : BoxH1ZeroSigma I) :
    ‖v‖ ≤
      Real.sqrt (1 + boxPoincareConstant I ^ 2) * ‖boxEnergyGradient I v‖ :=
  boxEnergy_norm_le_gradient I v

example {I : BoxIntegral.Box (Fin 2)}
    (F : BoxH1ZeroSigma I →L[ℝ] ℝ) (f : ℝ) (hf : 0 ≤ f)
    (hbound : ∀ w : BoxH1ZeroSigma I, ‖F w‖ ≤ f * ‖w‖)
    (v : BoxH1ZeroSigma I) :
    2 * F v ≤
      (1 + boxPoincareConstant I ^ 2) * f ^ 2 +
        boxGradientDiffusion I v v :=
  boxForcing_work_le I F f hf hbound v

example {I : BoxIntegral.Box (Fin 2)}
    (r : ℝ → BoxH1ZeroSigma I) (hr : Continuous r) :
    BoxDualForcing I :=
  BoxDualForcing.ofEnergyPath r hr

example {I : BoxIntegral.Box (Fin 2)} (Φ : BoxDualForcing I) :
    Continuous Φ.bound ∧ (∀ t, 0 ≤ Φ.bound t) ∧
      (∀ (t : ℝ) (w : BoxH1ZeroSigma I), ‖Φ.value t w‖ ≤ Φ.bound t * ‖w‖) :=
  ⟨Φ.continuous_bound, Φ.bound_nonneg, Φ.norm_le⟩

example {I : BoxIntegral.Box (Fin 2)}
    (S : BoxCompactSpectralRepresentation I) (m : ℕ) {a b : ℝ} (hab : a ≤ b)
    (Φ : BoxDualForcing I) (u₀ : BoxL2Sigma I) :
    Nonempty
      (S.CanonicalSolution2D m hab Φ.value
        (S.stateInitialCoefficient m u₀)) :=
  S.exists_forcedSolution2D hab m Φ u₀

example {I : BoxIntegral.Box (Fin 2)}
    (S : BoxCompactSpectralRepresentation I) (m : ℕ) {a b : ℝ} (hab : a ≤ b)
    (Φ : BoxDualForcing I) (u₀ : BoxL2Sigma I)
    (u : S.CanonicalSolution2D m hab Φ.value
      (S.stateInitialCoefficient m u₀)) :
    (∀ t ∈ Set.Icc a b,
        ‖S.canonicalSolutionToFun m hab u t‖ ≤ Φ.stateRadius a b u₀) ∧
      ∫ t in a..b,
          ‖S.energySynthesis m (S.canonicalSolutionToFun m hab u t)‖ ^ 2 ≤
        Φ.energyRadius a b u₀ ^ 2 :=
  ⟨S.forcedSolution2D_norm_le hab m Φ u₀ u,
    S.forcedSolution2D_energy_integral_le hab m Φ u₀ u⟩

example {I : BoxIntegral.Box (Fin 2)} {a b : ℝ} (hab : a ≤ b)
    (Φ : BoxDualForcing I) (u₀ : BoxL2Sigma I) :
    Nonempty
      ((boxCompactSpectralRepresentation I).forcedLeraySpectralCompactFamily2D
        hab Φ u₀).StrongWeakPathSubsequence :=
  exists_forced_twoDimensional_galerkinCompactness hab Φ u₀

example {I : BoxIntegral.Box (Fin 2)} {a b : ℝ} (hab : a ≤ b)
    (Φ : BoxDualForcing I) (u₀ : BoxL2Sigma I) :
    Nonempty
      (BoxCompactSpectralRepresentation.BoxForcedLerayHopfSolutionOn
        I a b Φ u₀) :=
  exists_forced_twoDimensional_lerayHopfSolution hab Φ u₀

example {I : BoxIntegral.Box (Fin 2)} {a b : ℝ} {Φ : BoxDualForcing I}
    {u₀ : BoxL2Sigma I}
    (u : BoxCompactSpectralRepresentation.BoxForcedLerayHopfSolutionOn
      I a b Φ u₀)
    (y : BoxL2Sigma I) : Continuous (fun t => ⟪u.weakState t, y⟫_ℝ) :=
  u.weakState_inner_continuous y

example {I : BoxIntegral.Box (Fin 2)} {a b : ℝ} {Φ : BoxDualForcing I}
    {u₀ : BoxL2Sigma I}
    (u : BoxCompactSpectralRepresentation.BoxForcedLerayHopfSolutionOn
      I a b Φ u₀) :
    u.weakState (⟨a, le_rfl, u.interval_nonempty⟩ : Set.Icc a b) = u₀ :=
  u.weakState_initial

example {I : BoxIntegral.Box (Fin 2)} {a b : ℝ} {Φ : BoxDualForcing I}
    {u₀ : BoxL2Sigma I}
    (u : BoxCompactSpectralRepresentation.BoxForcedLerayHopfSolutionOn
      I a b Φ u₀) :
    boxEnergyTimeStateMap (I := I)
        (μ := SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)
        u.energy = u.state :=
  u.state_eq_energy

example {I : BoxIntegral.Box (Fin 2)} {a b : ℝ} {Φ : BoxDualForcing I}
    {u₀ : BoxL2Sigma I}
    (u : BoxCompactSpectralRepresentation.BoxForcedLerayHopfSolutionOn
      I a b Φ u₀)
    (t : Set.Icc a b) :
    ‖u.weakState t‖ ^ 2 +
        2 * ∫ s : Set.Icc a b in Set.Iic t,
          ‖boxEnergyGradient I (u.energy s)‖ ^ 2
          ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b ≤
      ‖u₀‖ ^ 2 +
        2 * ∫ s : Set.Icc a b in Set.Iic t,
          Φ.value (s : ℝ) (u.energy s)
          ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b :=
  u.energy_inequality t

example {I : BoxIntegral.Box (Fin 2)} {a b : ℝ} {Φ : BoxDualForcing I}
    {u₀ : BoxL2Sigma I}
    (u : BoxCompactSpectralRepresentation.BoxForcedLerayHopfSolutionOn
      I a b Φ u₀)
    (φ : BoxH1ZeroSigma I) (eta : LerayIntervalTimeTest a b)
    (hterminal : eta.value b = 0) :
    -(∫ t : Set.Icc a b,
        ⟪u.state t, boxEnergyToState I φ⟫_ℝ * eta.deriv t
        ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) +
      (∫ t : Set.Icc a b,
        boxGradientDiffusion I (u.energy t) φ * eta.value t
        ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) +
      (∫ t : Set.Icc a b,
        (boxLadyzhenskayaRealization I).toBoxEnergyL4Realization.convectionForm I
          (u.energy t) (u.energy t) φ * eta.value t
        ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) =
      ⟪u₀, boxEnergyToState I φ⟫_ℝ * eta.value a +
        ∫ t : Set.Icc a b, Φ.value (t : ℝ) φ * eta.value t
          ∂SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b :=
  u.weak_equation φ eta hterminal
