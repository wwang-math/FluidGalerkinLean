import PDEIdeas.BoundaryConditionsBasic
import PDEIdeas.TransportIBP

open MeasureTheory MeasureTheory.Measure Real InnerProductSpace
open scoped NNReal ENNReal

noncomputable section

variable {n : ℕ}

/-- Scalar transport integration by parts under zero Dirichlet data. -/
theorem scalar_ibp_of_zeroDirichlet
    (I : BoxIntegral.Box (Fin (n + 1)))
    (u : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ))
    (f : (Fin (n + 1) → ℝ) → ℝ)
    (u' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ))
    (f' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] ℝ)
    (hu : ∀ x ∈ interior (BoxIntegral.Box.Icc I), HasFDerivAt u (u' x) x)
    (huc : ContinuousOn u (BoxIntegral.Box.Icc I))
    (hf : ∀ x ∈ interior (BoxIntegral.Box.Icc I), HasFDerivAt f (f' x) x)
    (hfc : ContinuousOn f (BoxIntegral.Box.Icc I))
    (hfbc : ZeroDirichletScalarOnBox I f)
    (hint_transport : IntegrableOn (fun x => f' x (u x)) (BoxIntegral.Box.Icc I))
    (hint_div : IntegrableOn
        (fun x => f x * ∑ i, u' x (Pi.single i 1) i)
        (BoxIntegral.Box.Icc I)) :
    ∫ x in BoxIntegral.Box.Icc I, f' x (u x) =
      -∫ x in BoxIntegral.Box.Icc I, f x * ∑ i, u' x (Pi.single i 1) i := by
  exact scalar_ibp I u f u' f' hu huc hf hfc hfbc hint_transport hint_div

/-- Vector transport integration by parts under zero Dirichlet data. -/
theorem vector_transport_ibp_of_zeroDirichlet
    (I : BoxIntegral.Box (Fin (n + 1)))
    (u v w : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ))
    (u' v' w' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ))
    (hu  : ∀ x ∈ interior (BoxIntegral.Box.Icc I), HasFDerivAt u (u' x) x)
    (huc : ContinuousOn u (BoxIntegral.Box.Icc I))
    (hv  : ∀ x ∈ interior (BoxIntegral.Box.Icc I), HasFDerivAt v (v' x) x)
    (hvc : ContinuousOn v (BoxIntegral.Box.Icc I))
    (hw  : ∀ x ∈ interior (BoxIntegral.Box.Icc I), HasFDerivAt w (w' x) x)
    (hwc : ContinuousOn w (BoxIntegral.Box.Icc I))
    (hvbc : ZeroDirichletVectorOnBox I v)
    (hwbc : ZeroDirichletVectorOnBox I w)
    (hdiv : ∀ x ∈ BoxIntegral.Box.Icc I,
        ∑ i : Fin (n + 1), u' x (Pi.single i 1) i = 0)
    (hint_tuv : IntegrableOn
        (fun x => ∑ i, v' x (u x) i * w x i) (BoxIntegral.Box.Icc I))
    (hint_tuw : IntegrableOn
        (fun x => ∑ i, v x i * w' x (u x) i) (BoxIntegral.Box.Icc I)) :
    ∫ x in BoxIntegral.Box.Icc I, ∑ i, v' x (u x) i * w x i =
      -∫ x in BoxIntegral.Box.Icc I, ∑ i, v x i * w' x (u x) i := by
  exact vector_transport_ibp I u v w u' v' w'
    hu huc hv hvc hw hwc hvbc hwbc hdiv hint_tuv hint_tuw

/-- Cubic transport cancellation under zero Dirichlet data. -/
theorem trilinear_self_cancel_of_zeroDirichlet
    (I : BoxIntegral.Box (Fin (n + 1)))
    (u : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ))
    (u' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ))
    (hu   : ∀ x ∈ interior (BoxIntegral.Box.Icc I), HasFDerivAt u (u' x) x)
    (huc  : ContinuousOn u (BoxIntegral.Box.Icc I))
    (hubc : ZeroDirichletVectorOnBox I u)
    (hdiv : ∀ x ∈ BoxIntegral.Box.Icc I,
        ∑ i : Fin (n + 1), u' x (Pi.single i 1) i = 0)
    (hint : IntegrableOn (fun x => ∑ i, u' x (u x) i * u x i)
        (BoxIntegral.Box.Icc I)) :
    ∫ x in BoxIntegral.Box.Icc I, ∑ i, u' x (u x) i * u x i = 0 := by
  exact trilinear_self_cancel I u u' hu huc hubc hdiv hint
