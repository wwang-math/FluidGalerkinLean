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
