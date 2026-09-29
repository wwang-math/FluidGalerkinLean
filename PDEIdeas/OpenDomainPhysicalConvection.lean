import PDEIdeas.OpenDomainSmoothTransport
import PDEIdeas.BoxL4Convection

/-!
# The physical convection integral of an open subdomain

`PDEIdeas.BoxL4Convection` realizes the transport integral of a rectangle `Q` as a
continuous trilinear form `BoxEnergyL4Realization.convectionForm Q E` on the closed
energy space `BoxH1ZeroSigma Q`, using the `L4-L2-L4` Hölder triple and the closed
`L2` gradient.  `PDEIdeas.OpenDomainCore` builds the smooth core
`SmoothOpenDomainField Ω` of an open subdomain `Ω ⊆ interior (Box.Icc Q)`, and
`PDEIdeas.OpenDomainSmoothTransport` states the transport identities of that core as
integrals over `Ω`.  This file connects the three.

Main results:

* `convectionDensity_eq_zero_of_notMem` — the convection density of `Ω`-supported
  fields vanishes off `Ω`;
* `isCompact_tsupport_field`, `hasCompactSupport_field` — fields of the smooth core of `Ω`
  are automatically compactly supported;
* `boxIntegral_convectionDensity_eq_setIntegral`,
  `integral_convectionDensity_eq_setIntegral` — the **box** (and the ambient-space)
  convection integral of three smooth `Ω`-supported fields **is** their convection
  integral over `Ω`;
* `integrable_boxMeasure_iff_integrableOn_carrier`,
  `integrable_boxMeasure_of_integrableOn_carrier` — the explicit integrability transfer
  between the two windows;
* `convectionForm_toBoxEnergy_eq_setIntegral` — the `L4-L2-L4` box form evaluated at the
  embedded smooth core is exactly that `Ω` integral;
* `setIntegral_convectionDensity_skew`, `setIntegral_convectionDensity_self_eq_zero` —
  the skew identity and the diagonal cancellation of the `Ω` integral, with the
  integrability hypotheses of `PDEIdeas.OpenDomainSmoothTransport` discharged by the
  Hölder integrability of the `L4` realization;
* `convectionForm`, `convectionForm_skew`, `convectionForm_diagonal_eq_zero`,
  `norm_convectionForm_le`, `energyConvectionForm` — the restriction of the box form to
  the energy closure `OpenDomainH1ZeroSigma Ω` of the subdomain, together with the
  identities that the existing `Lp` machinery justifies on the closure.

**Scope.**  Nothing here asserts a divergence or boundary theorem on `∂Ω`: the
subdomain enters only through the topological-support condition of
`SmoothOpenDomainField`, and every boundary term that is used is a face term of the
ambient rectangle `Q`, supplied by `PDEIdeas.TransportIBP`.  No nonlinear limit is
taken either: the identification of the convection form with a physical integral is
proved on the smooth core only.  On the closure the file claims exactly what
continuity and the already-proved skew symmetry of the box form give — skewness, the
diagonal cancellation and the Hölder bounds — and nothing about pointwise
representatives of closure elements.
-/

open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace OpenDomainPhysicalConvection

variable {n : ℕ} {Q : BoxIntegral.Box (Fin (n + 1))} {Ω : OpenDomainInBox Q}

/-! ## The convection density of `Ω`-supported smooth fields -/

@[simp]
theorem toBoxField_field (u : SmoothOpenDomainField Ω) :
    u.toBoxField.field = u.field := rfl

@[simp]
theorem toBoxField_derivative (u : SmoothOpenDomainField Ω) :
    u.toBoxField.derivative = u.derivative := rfl

/-- The convection density `⟪(u ⬝ ∇) v, w⟫` of fields of the smooth core of `Ω`
vanishes at every point outside `Ω`, because the transporting velocity does. -/
theorem convectionDensity_eq_zero_of_notMem (u v w : SmoothOpenDomainField Ω)
    {x : Fin (n + 1) → ℝ} (hx : x ∉ Ω.carrier) :
    ∑ i, v.derivative x (u.field x) i * w.field x i = 0 := by
  rw [OpenDomainTransport.eq_zero_of_notMem_of_tsupport_subset u.tsupport_subset hx]
  simp

/-- A field of the smooth core of `Ω` is compactly supported: its topological support is
closed and contained in the compact box `Box.Icc Q`. -/
theorem isCompact_tsupport_field (u : SmoothOpenDomainField Ω) :
    IsCompact (tsupport u.field) :=
  Q.isCompact_Icc.of_isClosed_subset isClosed_closure
    (u.tsupport_subset.trans Ω.carrier_subset_Icc)

/-- Restatement of `isCompact_tsupport_field` in the `HasCompactSupport` interface. -/
theorem hasCompactSupport_field (u : SmoothOpenDomainField Ω) :
    HasCompactSupport u.field :=
  isCompact_tsupport_field u

/-- **The box convection integral of `Ω`-supported smooth fields is the `Ω` integral.**
No integrability hypothesis enters: the two integrals of the same function over the two
windows agree because the integrand vanishes off `Ω`, and if the function fails to be
integrable both sides are `0`. -/
theorem boxIntegral_convectionDensity_eq_setIntegral
    (u v w : SmoothOpenDomainField Ω) :
    ∫ x in BoxIntegral.Box.Icc Q, ∑ i, v.derivative x (u.field x) i * w.field x i =
      ∫ x in Ω.carrier, ∑ i, v.derivative x (u.field x) i * w.field x i :=
  OpenDomainTransport.setIntegral_localize
    (OpenDomainTransport.measurableSet_boxIcc Q) Ω.carrier_subset_Icc
    fun _ hx => convectionDensity_eq_zero_of_notMem u v w hx

/-- The same statement written against the reference measure `BoxMeasure Q` used by
`PDEIdeas.BoxL4Convection`. -/
theorem boxMeasure_integral_convectionDensity_eq_setIntegral
    (u v w : SmoothOpenDomainField Ω) :
    ∫ x, (∑ i, v.derivative x (u.field x) i * w.field x i) ∂BoxMeasure Q =
      ∫ x in Ω.carrier, ∑ i, v.derivative x (u.field x) i * w.field x i :=
  boxIntegral_convectionDensity_eq_setIntegral u v w

/-- The ambient-space convection integral of `Ω`-supported smooth fields is the same
`Ω` integral: the box is only a bookkeeping window. -/
theorem integral_convectionDensity_eq_setIntegral
    (u v w : SmoothOpenDomainField Ω) :
    ∫ x, (∑ i, v.derivative x (u.field x) i * w.field x i) =
      ∫ x in Ω.carrier, ∑ i, v.derivative x (u.field x) i * w.field x i :=
  OpenDomainTransport.integral_localize
    fun _ hx => convectionDensity_eq_zero_of_notMem u v w hx

/-! ## Explicit integrability transfer -/

/-- **Integrability on `Ω` upgrades to integrability on the box**, and the two integrals
then agree.  This is the form in which the hypothesis is stated explicitly. -/
theorem integrable_boxMeasure_of_integrableOn_carrier
    (u v w : SmoothOpenDomainField Ω)
    (hint : IntegrableOn
      (fun x => ∑ i, v.derivative x (u.field x) i * w.field x i) Ω.carrier) :
    Integrable
      (fun x => ∑ i, v.derivative x (u.field x) i * w.field x i) (BoxMeasure Q) :=
  OpenDomainTransport.integrableOn_localize Ω.isOpen_carrier.measurableSet
    (OpenDomainTransport.measurableSet_boxIcc Q)
    (fun _ hx => convectionDensity_eq_zero_of_notMem u v w hx) hint

/-- Integrability of the convection density over the box and over `Ω` are equivalent for
fields of the smooth core of `Ω`. -/
theorem integrable_boxMeasure_iff_integrableOn_carrier
    (u v w : SmoothOpenDomainField Ω) :
    Integrable
        (fun x => ∑ i, v.derivative x (u.field x) i * w.field x i) (BoxMeasure Q) ↔
      IntegrableOn
        (fun x => ∑ i, v.derivative x (u.field x) i * w.field x i) Ω.carrier :=
  ⟨fun h => IntegrableOn.mono_set h Ω.carrier_subset_Icc,
    integrable_boxMeasure_of_integrableOn_carrier u v w⟩

/-- **The explicit-hypothesis package.**  Given integrability of the convection density
on `Ω`, it is integrable on the ambient box and the box convection integral equals the
integral over `Ω`. -/
theorem integrable_and_boxIntegral_eq_setIntegral
    (u v w : SmoothOpenDomainField Ω)
    (hint : IntegrableOn
      (fun x => ∑ i, v.derivative x (u.field x) i * w.field x i) Ω.carrier) :
    Integrable
        (fun x => ∑ i, v.derivative x (u.field x) i * w.field x i) (BoxMeasure Q) ∧
      ∫ x in BoxIntegral.Box.Icc Q, ∑ i, v.derivative x (u.field x) i * w.field x i =
        ∫ x in Ω.carrier, ∑ i, v.derivative x (u.field x) i * w.field x i :=
  ⟨integrable_boxMeasure_of_integrableOn_carrier u v w hint,
    boxIntegral_convectionDensity_eq_setIntegral u v w⟩

/-! ## The `L4-L2-L4` box form on the smooth core of `Ω` -/

/-- Hölder integrability of the convection density on `Ω`, inherited from the `L4`
realization of the ambient rectangle.  This is what discharges the integrability
hypotheses of `PDEIdeas.OpenDomainSmoothTransport`. -/
theorem integrableOn_convectionDensity (E : BoxEnergyL4Realization Q) (u v w : SmoothOpenDomainField Ω) :
    IntegrableOn
      (fun x => ∑ i, v.derivative x (u.field x) i * w.field x i) Ω.carrier :=
  IntegrableOn.mono_set
    (BoxEnergyL4Realization.transportIntegrable Q E
      u.toBoxField v.toBoxField w.toBoxField) Ω.carrier_subset_Icc

/-- The commuted convection density is integrable on `Ω` as well. -/
theorem integrableOn_convectionDensity_comm (E : BoxEnergyL4Realization Q) (u v w : SmoothOpenDomainField Ω) :
    IntegrableOn
      (fun x => ∑ i, v.field x i * w.derivative x (u.field x) i) Ω.carrier := by
  apply (integrableOn_convectionDensity E u w v).congr
  filter_upwards with x
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- **The box `L4-L2-L4` convection form of embedded smooth `Ω`-fields is the physical
convection integral over `Ω`.** -/
theorem convectionForm_toBoxEnergy_eq_setIntegral (E : BoxEnergyL4Realization Q) (u v w : SmoothOpenDomainField Ω) :
    BoxEnergyL4Realization.convectionForm Q E
        u.toBoxField.toEnergy v.toBoxField.toEnergy w.toBoxField.toEnergy =
      ∫ x in Ω.carrier, ∑ i, v.derivative x (u.field x) i * w.field x i := by
  rw [BoxEnergyL4Realization.convectionForm_toEnergy_eq_integral Q E
    u.toBoxField v.toBoxField w.toBoxField]
  exact boxMeasure_integral_convectionDensity_eq_setIntegral u v w

/-! ## The skew identity of the `Ω` convection integral -/

/-- **Skew identity.**  The convection integral over `Ω` is skew in its last two
arguments.  This is `SmoothOpenDomainField.transport_skew` with its integrability
hypotheses supplied by the Hölder integrability of the `L4` realization. -/
theorem setIntegral_convectionDensity_skew (E : BoxEnergyL4Realization Q) (u v w : SmoothOpenDomainField Ω) :
    (∫ x in Ω.carrier, ∑ i, v.derivative x (u.field x) i * w.field x i) +
      ∫ x in Ω.carrier, ∑ i, w.derivative x (u.field x) i * v.field x i = 0 :=
  SmoothOpenDomainField.transport_skew u v w
    (integrableOn_convectionDensity E u v w)
    (integrableOn_convectionDensity_comm E u v w)

/-- **Diagonal cancellation.**  The convection integral over `Ω` vanishes on the
diagonal: this is the energy neutrality of the convection term. -/
theorem setIntegral_convectionDensity_self_eq_zero (E : BoxEnergyL4Realization Q) (u : SmoothOpenDomainField Ω) :
    ∫ x in Ω.carrier, ∑ i, u.derivative x (u.field x) i * u.field x i = 0 :=
  SmoothOpenDomainField.transport_self_cancel u
    (integrableOn_convectionDensity E u u u)

/-- The skew identity read on the box form: the `L4-L2-L4` convection form of embedded
smooth `Ω`-fields is skew in its last two arguments, and the identity is exactly the
`Ω`-integral identity above. -/
theorem convectionForm_toBoxEnergy_skew (E : BoxEnergyL4Realization Q) (u v w : SmoothOpenDomainField Ω) :
    BoxEnergyL4Realization.convectionForm Q E
        u.toBoxField.toEnergy v.toBoxField.toEnergy w.toBoxField.toEnergy =
      -BoxEnergyL4Realization.convectionForm Q E
        u.toBoxField.toEnergy w.toBoxField.toEnergy v.toBoxField.toEnergy := by
  have h₁ := convectionForm_toBoxEnergy_eq_setIntegral E u v w
  have h₂ := convectionForm_toBoxEnergy_eq_setIntegral E u w v
  have h₃ := setIntegral_convectionDensity_skew E u v w
  linarith

/-- The diagonal of the box form on embedded smooth `Ω`-fields vanishes. -/
theorem convectionForm_toBoxEnergy_self_eq_zero (E : BoxEnergyL4Realization Q) (u : SmoothOpenDomainField Ω) :
    BoxEnergyL4Realization.convectionForm Q E
      u.toBoxField.toEnergy u.toBoxField.toEnergy u.toBoxField.toEnergy = 0 := by
  have h₁ := convectionForm_toBoxEnergy_eq_setIntegral E u u u
  have h₂ := setIntegral_convectionDensity_self_eq_zero E u
  linarith

/-! ## Restriction to the energy closure of `Ω` -/

/-- The energy closure of `Ω` includes continuously and isometrically into the energy
closure of the ambient rectangle. -/
def energyInclusion (Ω : OpenDomainInBox Q) :
    OpenDomainH1ZeroSigma Ω →L[ℝ] BoxH1ZeroSigma Q :=
  (OpenDomainH1ZeroSigma Ω).subtypeL.codRestrict (BoxH1ZeroSigma Q)
    fun u => openDomainH1ZeroSigma_le Ω u.property

@[simp]
theorem energyInclusion_coe (u : OpenDomainH1ZeroSigma Ω) :
    ((energyInclusion Ω u : BoxH1ZeroSigma Q) : BoxEnergyAmbient Q) =
      (u : BoxEnergyAmbient Q) := rfl

@[simp]
theorem norm_energyInclusion (u : OpenDomainH1ZeroSigma Ω) :
    ‖energyInclusion Ω u‖ = ‖u‖ := rfl

@[simp]
theorem energyInclusion_toEnergy (u : SmoothOpenDomainField Ω) :
    energyInclusion Ω u.toEnergy = u.toBoxField.toEnergy :=
  Subtype.ext (SmoothOpenDomainField.toBoxField_graphPoint u).symm

/-- **The convection form of the subdomain**: the `L4-L2-L4` box form restricted to the
energy closure of `Ω`.  Only the restriction is new; its continuity and its skewness are
those of the ambient box form. -/
def convectionForm (Ω : OpenDomainInBox Q) (E : BoxEnergyL4Realization Q) :
    OpenDomainH1ZeroSigma Ω →L[ℝ]
      OpenDomainH1ZeroSigma Ω →L[ℝ] OpenDomainH1ZeroSigma Ω →L[ℝ] ℝ :=
  (BoxEnergyL4Realization.convectionForm Q E).trilinearCompSame (energyInclusion Ω)

@[simp]
theorem convectionForm_apply (E : BoxEnergyL4Realization Q) (u v w : OpenDomainH1ZeroSigma Ω) :
    convectionForm Ω E u v w =
      BoxEnergyL4Realization.convectionForm Q E
        (energyInclusion Ω u) (energyInclusion Ω v) (energyInclusion Ω w) := rfl

/-- On the smooth core, the restricted form and the ambient box form agree. -/
theorem convectionForm_toEnergy_eq_box (E : BoxEnergyL4Realization Q)
    (u v w : SmoothOpenDomainField Ω) :
    convectionForm Ω E u.toEnergy v.toEnergy w.toEnergy =
      BoxEnergyL4Realization.convectionForm Q E
        u.toBoxField.toEnergy v.toBoxField.toEnergy w.toBoxField.toEnergy := by
  simp only [convectionForm_apply, energyInclusion_toEnergy]

/-- On the smooth core the restricted form is the physical convection integral over
`Ω`. -/
theorem convectionForm_toEnergy_eq_setIntegral (E : BoxEnergyL4Realization Q)
    (u v w : SmoothOpenDomainField Ω) :
    convectionForm Ω E u.toEnergy v.toEnergy w.toEnergy =
      ∫ x in Ω.carrier, ∑ i, v.derivative x (u.field x) i * w.field x i := by
  rw [convectionForm_toEnergy_eq_box E u v w]
  exact convectionForm_toBoxEnergy_eq_setIntegral E u v w

/-- **Skewness on the closure.**  Justified by the already-proved skewness of the box
form on `BoxH1ZeroSigma Q`, which is a continuity/density statement about a fixed
bounded trilinear map; no limit of nonlinear quantities is taken here. -/
theorem convectionForm_skew (Ω : OpenDomainInBox Q) (E : BoxEnergyL4Realization Q) :
    ∀ u v w : OpenDomainH1ZeroSigma Ω,
      convectionForm Ω E u v w = -convectionForm Ω E u w v :=
  fun u v w => BoxEnergyL4Realization.convectionForm_skew Q E
    (energyInclusion Ω u) (energyInclusion Ω v) (energyInclusion Ω w)

/-- **Diagonal cancellation on the closure.**  A purely algebraic consequence of
skewness, hence available for every element of the energy closure of `Ω`. -/
theorem convectionForm_diagonal_eq_zero (E : BoxEnergyL4Realization Q) (u v : OpenDomainH1ZeroSigma Ω) :
    convectionForm Ω E u v v = 0 := by
  have h := convectionForm_skew Ω E u v v
  linarith

/-- Hölder bound of the restricted form, inherited from the box form. -/
theorem norm_convectionForm_le (E : BoxEnergyL4Realization Q) (u v w : OpenDomainH1ZeroSigma Ω) :
    ‖convectionForm Ω E u v w‖ ≤
      boxLpConvectionBound Q * ‖E.toLp4 (energyInclusion Ω u)‖ *
        ‖boxEnergyGradient Q (energyInclusion Ω v)‖ *
        ‖E.toLp4 (energyInclusion Ω w)‖ :=
  BoxEnergyL4Realization.norm_convectionForm_le Q E
    (energyInclusion Ω u) (energyInclusion Ω v) (energyInclusion Ω w)

/-- The convection form of `Ω` as a bounded skew energy convection form, the interface
consumed by the abstract Galerkin development. -/
def energyConvectionForm (Ω : OpenDomainInBox Q) (E : BoxEnergyL4Realization Q) :
    EnergyConvectionForm (OpenDomainH1ZeroSigma Ω) :=
  EnergyConvectionForm.ofContinuousSkew (convectionForm Ω E) (convectionForm_skew Ω E)

@[simp]
theorem energyConvectionForm_form (Ω : OpenDomainInBox Q)
    (E : BoxEnergyL4Realization Q) :
    (energyConvectionForm Ω E).form = convectionForm Ω E := rfl

/-- The two-dimensional Ladyzhenskaya bound of the ambient rectangle, restricted to the
energy closure of `Ω`: the diagonal convection term is controlled by the state norm
times the energy norm. -/
theorem norm_convectionForm_diagonal_le (L : BoxLadyzhenskayaRealization Q)
    (u φ : OpenDomainH1ZeroSigma Ω) :
    ‖convectionForm Ω L.toBoxEnergyL4Realization u u φ‖ ≤
      (boxLpConvectionBound Q * L.constant) *
        ‖boxEnergyToState Q (energyInclusion Ω u)‖ * ‖u‖ * ‖φ‖ :=
  BoxLadyzhenskayaRealization.convectionForm_diagonal_norm_le Q L
    (energyInclusion Ω u) (energyInclusion Ω φ)

end OpenDomainPhysicalConvection

end
