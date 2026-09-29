import PDEIdeas.OpenDomainCore
import PDEIdeas.OpenDomainTransport

/-!
# Transport identities for the open-domain smooth core

The topological-support condition in `SmoothOpenDomainField` supplies the
support hypothesis of the localized box transport identities.
-/

open MeasureTheory

noncomputable section

variable {n : ℕ} {Q : BoxIntegral.Box (Fin (n + 1))}
    {Ω : OpenDomainInBox Q}

/-- Diagonal convection cancellation on an open domain. -/
theorem SmoothOpenDomainField.transport_self_cancel
    (u : SmoothOpenDomainField Ω)
    (hint : IntegrableOn
      (fun x => ∑ i, u.derivative x (u.field x) i * u.field x i)
      Ω.carrier) :
    ∫ x in Ω.carrier,
      ∑ i, u.derivative x (u.field x) i * u.field x i = 0 :=
  OpenDomainTransport.trilinear_self_cancel_localized
    Q Ω.carrier u.field u.derivative Ω.isOpen_carrier.measurableSet
    Ω.carrier_subset_interior u.hasFDerivAt_field u.tsupport_subset
    (fun x _ => u.divergence_field x) hint

/-- The trilinear convection form is skew in its last two arguments on the
open-domain smooth core. -/
theorem SmoothOpenDomainField.transport_skew
    (u v w : SmoothOpenDomainField Ω)
    (hint₁ : IntegrableOn
      (fun x => ∑ i, v.derivative x (u.field x) i * w.field x i)
      Ω.carrier)
    (hint₂ : IntegrableOn
      (fun x => ∑ i, v.field x i * w.derivative x (u.field x) i)
      Ω.carrier) :
    (∫ x in Ω.carrier,
      ∑ i, v.derivative x (u.field x) i * w.field x i) +
      ∫ x in Ω.carrier,
        ∑ i, w.derivative x (u.field x) i * v.field x i = 0 := by
  apply OpenDomainTransport.trilinear_skew_localized
    Q Ω.carrier u.field v.field w.field
    u.derivative v.derivative w.derivative
    Ω.isOpen_carrier.measurableSet Ω.carrier_subset_interior
    u.hasFDerivAt_field v.hasFDerivAt_field w.hasFDerivAt_field
    u.tsupport_subset
  · intro x hx
    exact OpenDomainTransport.eq_zero_of_notMem_of_tsupport_subset
      v.tsupport_subset hx
  · intro x hx
    exact OpenDomainTransport.eq_zero_of_notMem_of_tsupport_subset
      w.tsupport_subset hx
  · intro x _
    exact u.divergence_field x
  · exact hint₁
  · exact hint₂

end
