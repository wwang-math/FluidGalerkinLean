import PDEIdeas.BoxSobolevClosure
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Smooth divergence-free core on an open subdomain of a rectangle

`PDEIdeas.BoxSobolevClosure` builds the zero-trace energy space of a rectangle
`Q` as the closure of the graphs `(u, Du)` of smooth divergence-free fields that
vanish on the faces of `Q`.  This file repeats that construction for an
arbitrary **open** set `Ω` sitting inside the interior of `Q`: the smooth core
now consists of the `C¹` divergence-free fields whose topological support is contained in
`Ω`, so the ambient rectangle only supplies the reference measure and the
ambient `L²` spaces.

Main definitions:

* `OpenDomainInBox Q` — an open set `Ω ⊆ interior (Box.Icc Q)`; the largest
  one, `OpenDomainInBox.self Q`, is nonempty by
  `OpenDomainInBox.self_carrier_nonempty`.
* `SmoothOpenDomainField Ω` — a `C¹`, divergence-free field with topological support in `Ω`
  with square-integrable velocity and derivative on `Q`.
* `openDomainGraphCore Ω`, `openDomainVelocityCore Ω` — the linear spans of the
  graph points `(u, Du)` and of the velocities `u`.
* `OpenDomainH1ZeroSigma Ω`, `OpenDomainL2Sigma Ω` — their closures, the models
  of `H¹_{0,σ}(Ω)` and `L²_σ(Ω)`.
* `openDomainEnergyToState Ω` — the canonical `V → H` map, and
  `openDomainEnergyGradient Ω` — the derivative component.

Main results:

* `interior_boxIcc`, `mem_interior_boxIcc_iff` — the interior of a closed box.
* `zeroDirichletVectorOnBox_of_support_subset` — a field supported in `Ω`
  automatically satisfies the homogeneous Dirichlet condition on `∂Q`, so
  `SmoothOpenDomainField.toBoxField` embeds the open-domain core into the
  rectangle core of `PDEIdeas.BoxSobolevClosure`.
* `norm_openDomainEnergyToState_le`, `opNorm_openDomainEnergyToState_le_one`,
  `lipschitzWith_openDomainEnergyToState` — continuity of the energy-to-state
  map.
* `openDomainEnergyToState_denseRange` — its range is dense in `L²_σ(Ω)`.
-/

open MeasureTheory Real InnerProductSpace Set
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

variable {n : ℕ}

/-! ### The interior of a closed rectangle -/

/-- The interior of the closed box `Box.Icc Q` is the open coordinate rectangle. -/
theorem interior_boxIcc (Q : BoxIntegral.Box (Fin (n + 1))) :
    interior (BoxIntegral.Box.Icc Q) =
      Set.pi Set.univ fun i => Set.Ioo (Q.lower i) (Q.upper i) := by
  rw [BoxIntegral.Box.Icc_eq_pi,
    interior_pi_set (@Set.finite_univ (Fin (n + 1)) _)]
  simp only [interior_Icc]

/-- Membership in the interior of a closed box, coordinatewise. -/
theorem mem_interior_boxIcc_iff {Q : BoxIntegral.Box (Fin (n + 1))}
    {x : Fin (n + 1) → ℝ} :
    x ∈ interior (BoxIntegral.Box.Icc Q) ↔
      ∀ i, Q.lower i < x i ∧ x i < Q.upper i := by
  rw [interior_boxIcc]
  simp only [Set.mem_univ_pi, Set.mem_Ioo]

/-! ### Open subdomains of a rectangle -/

/-- An open set `Ω` contained in the interior of the rectangle `Q`. -/
structure OpenDomainInBox (Q : BoxIntegral.Box (Fin (n + 1))) where
  /-- The underlying set of the subdomain. -/
  carrier : Set (Fin (n + 1) → ℝ)
  /-- The subdomain is open. -/
  isOpen_carrier : IsOpen carrier
  /-- The subdomain stays away from the faces of `Q`. -/
  carrier_subset_interior : carrier ⊆ interior (BoxIntegral.Box.Icc Q)

namespace OpenDomainInBox

variable {Q : BoxIntegral.Box (Fin (n + 1))}

theorem carrier_subset_Icc (Ω : OpenDomainInBox Q) :
    Ω.carrier ⊆ BoxIntegral.Box.Icc Q :=
  Ω.carrier_subset_interior.trans interior_subset

theorem lower_lt_of_mem (Ω : OpenDomainInBox Q) {x : Fin (n + 1) → ℝ}
    (hx : x ∈ Ω.carrier) (i : Fin (n + 1)) : Q.lower i < x i :=
  (mem_interior_boxIcc_iff.1 (Ω.carrier_subset_interior hx) i).1

theorem lt_upper_of_mem (Ω : OpenDomainInBox Q) {x : Fin (n + 1) → ℝ}
    (hx : x ∈ Ω.carrier) (i : Fin (n + 1)) : x i < Q.upper i :=
  (mem_interior_boxIcc_iff.1 (Ω.carrier_subset_interior hx) i).2

/-- The interior of `Q` is itself the largest open subdomain of `Q`. -/
def self (Q : BoxIntegral.Box (Fin (n + 1))) : OpenDomainInBox Q where
  carrier := interior (BoxIntegral.Box.Icc Q)
  isOpen_carrier := isOpen_interior
  carrier_subset_interior := Set.Subset.rfl

/-- The largest open subdomain of `Q` is nonempty: it contains the centre of
`Q`.  In particular `OpenDomainInBox Q` is never an empty type and the
subdomains considered here are not vacuous. -/
theorem self_carrier_nonempty (Q : BoxIntegral.Box (Fin (n + 1))) :
    (OpenDomainInBox.self Q).carrier.Nonempty := by
  have hmem : (fun i => (Q.lower i + Q.upper i) / 2) ∈
      interior (BoxIntegral.Box.Icc Q) := by
    rw [mem_interior_boxIcc_iff]
    intro i
    have h := Q.lower_lt_upper i
    show Q.lower i < (Q.lower i + Q.upper i) / 2 ∧
      (Q.lower i + Q.upper i) / 2 < Q.upper i
    constructor <;> linarith
  exact ⟨_, hmem⟩

instance : Inhabited (OpenDomainInBox Q) := ⟨OpenDomainInBox.self Q⟩

end OpenDomainInBox

/-- A field supported in an open subdomain of `Q` vanishes identically on every
coordinate face of `Q`, hence satisfies the homogeneous Dirichlet condition. -/
theorem zeroDirichletVectorOnBox_of_support_subset
    {Q : BoxIntegral.Box (Fin (n + 1))} (Ω : OpenDomainInBox Q)
    {v : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ}
    (hv : Function.support v ⊆ Ω.carrier) :
    ZeroDirichletVectorOnBox Q v := by
  have key : ∀ (i : Fin (n + 1)) (c : ℝ) (y : Fin n → ℝ),
      c = Q.upper i ∨ c = Q.lower i → v (i.insertNth c y) = 0 := by
    intro i c y hc
    by_contra hne
    have hmem : i.insertNth c y ∈ Ω.carrier := hv (Function.mem_support.2 hne)
    have hlt := Ω.lt_upper_of_mem hmem i
    have hgt := Ω.lower_lt_of_mem hmem i
    rw [Fin.insertNth_apply_same] at hlt hgt
    rcases hc with rfl | rfl
    · exact lt_irrefl _ hlt
    · exact lt_irrefl _ hgt
  intro i y
  exact ⟨key i _ y (Or.inl rfl), key i _ y (Or.inr rfl)⟩

/-! ### The smooth divergence-free core supported in `Ω` -/

/-- `C¹`, divergence-free vector fields whose support lies in the open
subdomain `Ω ⊆ interior Q`, with square-integrable velocity and derivative for
the reference measure of `Q`.  This is the smooth core of the zero-trace energy
space of `Ω`. -/
structure SmoothOpenDomainField {Q : BoxIntegral.Box (Fin (n + 1))}
    (Ω : OpenDomainInBox Q) where
  /-- The velocity field, defined on all of the ambient space. -/
  field : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ
  /-- The Fréchet derivative of the velocity field. -/
  derivative : (Fin (n + 1) → ℝ) →
    (Fin (n + 1) → ℝ) →L[ℝ] Fin (n + 1) → ℝ
  /-- The velocity is continuously differentiable. -/
  contDiff_field : ContDiff ℝ 1 field
  /-- `derivative` really is the derivative of `field`. -/
  hasFDerivAt_field : ∀ x, HasFDerivAt field (derivative x) x
  /-- The topological support of the velocity is contained in `Ω`. -/
  tsupport_subset : tsupport field ⊆ Ω.carrier
  /-- The velocity is divergence free. -/
  divergence_field :
    ∀ x, ∑ i : Fin (n + 1), derivative x (Pi.single i 1) i = 0
  /-- The velocity is square integrable on `Q`. -/
  velocity_memLp : MemLp (boxVelocityValue field) 2 (BoxMeasure Q)
  /-- The derivative is square integrable on `Q`. -/
  gradient_memLp : MemLp (boxGradientValue derivative) 2 (BoxMeasure Q)

namespace SmoothOpenDomainField

variable {Q : BoxIntegral.Box (Fin (n + 1))} {Ω : OpenDomainInBox Q}

/-- A field of the open-domain core is in particular a smooth zero-face field of
the ambient rectangle: the Dirichlet condition on `∂Q` is automatic. -/
def toBoxField (u : SmoothOpenDomainField Ω) : SmoothBoxEnergyField Q where
  field := u.field
  derivative := u.derivative
  contDiff_field := u.contDiff_field
  support_field := (subset_tsupport u.field).trans
    (u.tsupport_subset.trans Ω.carrier_subset_Icc)
  hasFDerivAt_field := fun x _ => u.hasFDerivAt_field x
  continuousOn_field := u.contDiff_field.continuous.continuousOn
  zeroDirichlet_field :=
    zeroDirichletVectorOnBox_of_support_subset Ω
      ((subset_tsupport u.field).trans u.tsupport_subset)
  divergence_field := fun x _ => u.divergence_field x
  velocity_memLp := u.velocity_memLp
  gradient_memLp := u.gradient_memLp

/-- The velocity represented in the ambient vector-valued `L²` space of `Q`. -/
def velocityLp (u : SmoothOpenDomainField Ω) : BoxVelocityL2 Q :=
  u.velocity_memLp.toLp (boxVelocityValue u.field)

/-- The derivative represented in the ambient matrix-valued `L²` space of `Q`. -/
def gradientLp (u : SmoothOpenDomainField Ω) : BoxGradientL2 Q :=
  u.gradient_memLp.toLp (boxGradientValue u.derivative)

/-- Graph point `(u, Du)` in the product `L²` space of `Q`. -/
def graphPoint (u : SmoothOpenDomainField Ω) : BoxEnergyAmbient Q :=
  WithLp.toLp 2 (u.velocityLp, u.gradientLp)

@[simp]
theorem toBoxField_velocityLp (u : SmoothOpenDomainField Ω) :
    u.toBoxField.velocityLp = u.velocityLp := rfl

@[simp]
theorem toBoxField_gradientLp (u : SmoothOpenDomainField Ω) :
    u.toBoxField.gradientLp = u.gradientLp := rfl

@[simp]
theorem toBoxField_graphPoint (u : SmoothOpenDomainField Ω) :
    u.toBoxField.graphPoint = u.graphPoint := rfl

/-- The zero field belongs to the smooth core of every open subdomain. -/
def zero (Ω : OpenDomainInBox Q) : SmoothOpenDomainField Ω where
  field := fun _ => 0
  derivative := fun _ => 0
  contDiff_field := contDiff_const
  hasFDerivAt_field := fun x => hasFDerivAt_const 0 x
  tsupport_subset := by simp
  divergence_field := by intro x; simp
  velocity_memLp := by
    have h : boxVelocityValue (fun _ : Fin (n + 1) → ℝ => (0 : Fin (n + 1) → ℝ))
        = fun _ => (0 : BoxVelocityValue n) := by
      funext x
      simp [boxVelocityValue]
    rw [h]
    simp
  gradient_memLp := by
    have h : boxGradientValue
          (fun _ : Fin (n + 1) → ℝ =>
            (0 : (Fin (n + 1) → ℝ) →L[ℝ] Fin (n + 1) → ℝ))
        = fun _ => (0 : BoxGradientValue n) := by
      funext x
      simp only [boxGradientValue, ContinuousLinearMap.zero_apply, Pi.zero_apply]
      rfl
    rw [h]
    simp

instance : Inhabited (SmoothOpenDomainField Ω) := ⟨zero Ω⟩

/-- Enlarging the subdomain enlarges the smooth core. -/
def mono {Ω₁ Ω₂ : OpenDomainInBox Q} (h : Ω₁.carrier ⊆ Ω₂.carrier)
    (u : SmoothOpenDomainField Ω₁) : SmoothOpenDomainField Ω₂ where
  field := u.field
  derivative := u.derivative
  contDiff_field := u.contDiff_field
  hasFDerivAt_field := u.hasFDerivAt_field
  tsupport_subset := u.tsupport_subset.trans h
  divergence_field := u.divergence_field
  velocity_memLp := u.velocity_memLp
  gradient_memLp := u.gradient_memLp

@[simp]
theorem mono_velocityLp {Ω₁ Ω₂ : OpenDomainInBox Q} (h : Ω₁.carrier ⊆ Ω₂.carrier)
    (u : SmoothOpenDomainField Ω₁) : (u.mono h).velocityLp = u.velocityLp := rfl

@[simp]
theorem mono_graphPoint {Ω₁ Ω₂ : OpenDomainInBox Q} (h : Ω₁.carrier ⊆ Ω₂.carrier)
    (u : SmoothOpenDomainField Ω₁) : (u.mono h).graphPoint = u.graphPoint := rfl

end SmoothOpenDomainField

/-! ### The graph and velocity closure spaces of `Ω` -/

/-- Graph points `(u, Du)` of smooth divergence-free fields supported in `Ω`. -/
def openDomainGraphSet {Q : BoxIntegral.Box (Fin (n + 1))}
    (Ω : OpenDomainInBox Q) : Set (BoxEnergyAmbient Q) :=
  Set.range fun u : SmoothOpenDomainField Ω => u.graphPoint

/-- Velocities of smooth divergence-free fields supported in `Ω`. -/
def openDomainVelocitySet {Q : BoxIntegral.Box (Fin (n + 1))}
    (Ω : OpenDomainInBox Q) : Set (BoxVelocityL2 Q) :=
  Set.range fun u : SmoothOpenDomainField Ω => u.velocityLp

/-- Linear span of the smooth graph core of `Ω`. -/
def openDomainGraphCore {Q : BoxIntegral.Box (Fin (n + 1))}
    (Ω : OpenDomainInBox Q) : Submodule ℝ (BoxEnergyAmbient Q) :=
  Submodule.span ℝ (openDomainGraphSet Ω)

/-- Linear span of the smooth velocity core of `Ω`. -/
def openDomainVelocityCore {Q : BoxIntegral.Box (Fin (n + 1))}
    (Ω : OpenDomainInBox Q) : Submodule ℝ (BoxVelocityL2 Q) :=
  Submodule.span ℝ (openDomainVelocitySet Ω)

/-- `H¹_{0,σ}(Ω)` closure model: closure of the smooth `(u, Du)` graph of fields
supported in `Ω`, in the product `L²` norm of `Q`. -/
abbrev OpenDomainH1ZeroSigma {Q : BoxIntegral.Box (Fin (n + 1))}
    (Ω : OpenDomainInBox Q) :=
  (openDomainGraphCore Ω).topologicalClosure

/-- `L²_σ(Ω)` closure model: closure of the smooth divergence-free velocities
supported in `Ω`, in the vector-valued `L²` norm of `Q`. -/
abbrev OpenDomainL2Sigma {Q : BoxIntegral.Box (Fin (n + 1))}
    (Ω : OpenDomainInBox Q) :=
  (openDomainVelocityCore Ω).topologicalClosure

variable {Q : BoxIntegral.Box (Fin (n + 1))}

@[simp]
theorem openDomain_velocityProjection_graphPoint {Ω : OpenDomainInBox Q}
    (u : SmoothOpenDomainField Ω) :
    boxEnergyVelocityProjection Q u.graphPoint = u.velocityLp := rfl

@[simp]
theorem openDomain_gradientProjection_graphPoint {Ω : OpenDomainInBox Q}
    (u : SmoothOpenDomainField Ω) :
    boxEnergyGradientProjection Q u.graphPoint = u.gradientLp := rfl

theorem image_openDomainGraphSet_velocity (Ω : OpenDomainInBox Q) :
    boxEnergyVelocityProjection Q '' openDomainGraphSet Ω =
      openDomainVelocitySet Ω := by
  ext v
  constructor
  · rintro ⟨x, ⟨u, rfl⟩, rfl⟩
    exact ⟨u, by simp⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u.graphPoint, ⟨u, rfl⟩, by simp⟩

theorem openDomainGraphCore_map_velocity (Ω : OpenDomainInBox Q) :
    (openDomainGraphCore Ω).map
        (boxEnergyVelocityProjection Q).toLinearMap =
      openDomainVelocityCore Ω := by
  rw [openDomainGraphCore, openDomainVelocityCore, Submodule.map_span]
  congr 1
  simpa only [ContinuousLinearMap.coe_coe] using
    image_openDomainGraphSet_velocity Ω

/-! ### Comparison with the rectangle core -/

theorem openDomainGraphSet_subset_smoothBoxGraphSet (Ω : OpenDomainInBox Q) :
    openDomainGraphSet Ω ⊆ smoothBoxGraphSet Q := by
  rintro _ ⟨u, rfl⟩
  exact ⟨u.toBoxField, rfl⟩

theorem openDomainVelocitySet_subset_smoothBoxVelocitySet
    (Ω : OpenDomainInBox Q) :
    openDomainVelocitySet Ω ⊆ smoothBoxVelocitySet Q := by
  rintro _ ⟨u, rfl⟩
  exact ⟨u.toBoxField, rfl⟩

theorem openDomainGraphCore_le_smoothBoxGraphCore (Ω : OpenDomainInBox Q) :
    openDomainGraphCore Ω ≤ smoothBoxGraphCore Q :=
  Submodule.span_mono (openDomainGraphSet_subset_smoothBoxGraphSet Ω)

theorem openDomainVelocityCore_le_smoothBoxVelocityCore
    (Ω : OpenDomainInBox Q) :
    openDomainVelocityCore Ω ≤ smoothBoxVelocityCore Q :=
  Submodule.span_mono (openDomainVelocitySet_subset_smoothBoxVelocitySet Ω)

theorem openDomainH1ZeroSigma_le (Ω : OpenDomainInBox Q) :
    OpenDomainH1ZeroSigma Ω ≤ BoxH1ZeroSigma Q :=
  Submodule.topologicalClosure_mono
    (openDomainGraphCore_le_smoothBoxGraphCore Ω)

theorem openDomainL2Sigma_le (Ω : OpenDomainInBox Q) :
    OpenDomainL2Sigma Ω ≤ BoxL2Sigma Q :=
  Submodule.topologicalClosure_mono
    (openDomainVelocityCore_le_smoothBoxVelocityCore Ω)

/-! ### Monotonicity in the subdomain -/

theorem openDomainGraphSet_mono {Ω₁ Ω₂ : OpenDomainInBox Q}
    (h : Ω₁.carrier ⊆ Ω₂.carrier) :
    openDomainGraphSet Ω₁ ⊆ openDomainGraphSet Ω₂ := by
  rintro _ ⟨u, rfl⟩
  exact ⟨u.mono h, rfl⟩

theorem openDomainGraphCore_mono {Ω₁ Ω₂ : OpenDomainInBox Q}
    (h : Ω₁.carrier ⊆ Ω₂.carrier) :
    openDomainGraphCore Ω₁ ≤ openDomainGraphCore Ω₂ :=
  Submodule.span_mono (openDomainGraphSet_mono h)

/-! ### The canonical energy-to-state map -/

/-- Canonical continuous map from the graph closure of `Ω` to its velocity
closure, sending `(u, Du)` to `u`. -/
def openDomainEnergyToState (Ω : OpenDomainInBox Q) :
    OpenDomainH1ZeroSigma Ω →L[ℝ] OpenDomainL2Sigma Ω :=
  ((boxEnergyVelocityProjection Q).comp
      (openDomainGraphCore Ω).topologicalClosure.subtypeL).codRestrict
    (openDomainVelocityCore Ω).topologicalClosure fun u => by
      have huMap :
          boxEnergyVelocityProjection Q (u : BoxEnergyAmbient Q) ∈
            (openDomainGraphCore Ω).topologicalClosure.map
              (boxEnergyVelocityProjection Q).toLinearMap :=
        ⟨u, u.property, rfl⟩
      have huClosure :=
        (openDomainGraphCore Ω).topologicalClosure_map
          (boxEnergyVelocityProjection Q) huMap
      simpa [openDomainGraphCore_map_velocity] using huClosure

/-- Canonical derivative component of an element of the graph closure of `Ω`. -/
def openDomainEnergyGradient (Ω : OpenDomainInBox Q) :
    OpenDomainH1ZeroSigma Ω →L[ℝ] BoxGradientL2 Q :=
  (boxEnergyGradientProjection Q).comp
    (openDomainGraphCore Ω).topologicalClosure.subtypeL

theorem openDomainEnergyToState_coe (Ω : OpenDomainInBox Q)
    (u : OpenDomainH1ZeroSigma Ω) :
    ((openDomainEnergyToState Ω u : OpenDomainL2Sigma Ω) : BoxVelocityL2 Q) =
      boxEnergyVelocityProjection Q (u : BoxEnergyAmbient Q) := rfl

/-! ### Continuity -/

theorem norm_openDomainEnergyToState_le (Ω : OpenDomainInBox Q)
    (u : OpenDomainH1ZeroSigma Ω) :
    ‖openDomainEnergyToState Ω u‖ ≤ ‖u‖ :=
  WithLp.norm_fst_le (x := (u : BoxEnergyAmbient Q))

theorem norm_openDomainEnergyGradient_le (Ω : OpenDomainInBox Q)
    (u : OpenDomainH1ZeroSigma Ω) :
    ‖openDomainEnergyGradient Ω u‖ ≤ ‖u‖ :=
  WithLp.norm_snd_le (x := (u : BoxEnergyAmbient Q))

theorem continuous_openDomainEnergyToState (Ω : OpenDomainInBox Q) :
    Continuous (openDomainEnergyToState Ω) :=
  (openDomainEnergyToState Ω).continuous

theorem lipschitzWith_openDomainEnergyToState (Ω : OpenDomainInBox Q) :
    LipschitzWith 1 (openDomainEnergyToState Ω) :=
  LipschitzWith.of_dist_le_mul fun u v => by
    have h := norm_openDomainEnergyToState_le Ω (u - v)
    rw [map_sub] at h
    calc dist (openDomainEnergyToState Ω u) (openDomainEnergyToState Ω v)
        = ‖openDomainEnergyToState Ω u - openDomainEnergyToState Ω v‖ :=
          dist_eq_norm_sub _ _
      _ ≤ ‖u - v‖ := h
      _ = dist u v := (dist_eq_norm_sub u v).symm
      _ = (1 : ℝ≥0) * dist u v := by norm_num

/-! ### Smooth core elements inside the closures -/

/-- A smooth core field as an element of the `H¹_{0,σ}(Ω)` closure. -/
def SmoothOpenDomainField.toEnergy {Ω : OpenDomainInBox Q}
    (u : SmoothOpenDomainField Ω) : OpenDomainH1ZeroSigma Ω :=
  ⟨u.graphPoint,
    (openDomainGraphCore Ω).le_topologicalClosure
      (Submodule.subset_span ⟨u, rfl⟩)⟩

/-- A smooth core field as an element of the `L²_σ(Ω)` closure. -/
def SmoothOpenDomainField.toState {Ω : OpenDomainInBox Q}
    (u : SmoothOpenDomainField Ω) : OpenDomainL2Sigma Ω :=
  ⟨u.velocityLp,
    (openDomainVelocityCore Ω).le_topologicalClosure
      (Submodule.subset_span ⟨u, rfl⟩)⟩

@[simp]
theorem openDomainEnergyToState_toEnergy {Ω : OpenDomainInBox Q}
    (u : SmoothOpenDomainField Ω) :
    openDomainEnergyToState Ω u.toEnergy = u.toState := rfl

@[simp]
theorem openDomainEnergyGradient_toEnergy {Ω : OpenDomainInBox Q}
    (u : SmoothOpenDomainField Ω) :
    openDomainEnergyGradient Ω u.toEnergy = u.gradientLp := rfl

/-! ### Dense range -/

/-- The canonical energy-to-state map of `Ω` has dense range: its range contains
the smooth velocity core whose closure defines the state space. -/
theorem openDomainEnergyToState_denseRange (Ω : OpenDomainInBox Q) :
    DenseRange (openDomainEnergyToState Ω) := by
  have hcore :
      DenseRange
        (Set.inclusion
          ((openDomainVelocityCore Ω).le_topologicalClosure)) := by
    apply (denseRange_inclusion_iff _).2
    simpa only [Submodule.topologicalClosure_coe] using
      (Set.Subset.rfl :
        closure (openDomainVelocityCore Ω : Set (BoxVelocityL2 Q)) ⊆
          closure (openDomainVelocityCore Ω : Set (BoxVelocityL2 Q)))
  apply hcore.mono
  rintro _ ⟨u, rfl⟩
  have huMap :
      (u : BoxVelocityL2 Q) ∈
        (openDomainGraphCore Ω).map
          (boxEnergyVelocityProjection Q).toLinearMap := by
    rw [openDomainGraphCore_map_velocity]
    exact u.property
  rcases huMap with ⟨v, hv, hvu⟩
  refine ⟨⟨v, (openDomainGraphCore Ω).le_topologicalClosure hv⟩, ?_⟩
  apply Subtype.ext
  exact hvu

/-- The closure of the range of the energy-to-state map is the whole state
space. -/
theorem closure_range_openDomainEnergyToState (Ω : OpenDomainInBox Q) :
    closure (Set.range (openDomainEnergyToState Ω)) = Set.univ :=
  (openDomainEnergyToState_denseRange Ω).closure_range

end
