import PDEIdeas.BoundaryConditions
import PDEIdeas.BoxSobolevClosure
import PDEIdeas.VariationalGalerkin

open MeasureTheory Real InnerProductSpace
open scoped NNReal ENNReal

noncomputable section

variable {n : ℕ}

/-- A finite Galerkin space synthesized as regular, divergence-free,
zero-Dirichlet vector fields on a rectangular box. -/
structure SmoothBoxGalerkinTransport
    (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℝ W] where
  box : BoxIntegral.Box (Fin (n + 1))
  field : W →ₗ[ℝ]
    ((Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
  fieldDerivative : W →ₗ[ℝ]
    ((Fin (n + 1) → ℝ) →
      (Fin (n + 1) → ℝ) →L[ℝ] Fin (n + 1) → ℝ)
  contDiff_field :
    ∀ u : W, ContDiff ℝ 1 (field u)
  support_field :
    ∀ u : W, Function.support (field u) ⊆ BoxIntegral.Box.Icc box
  hasFDerivAt_field :
    ∀ u : W, ∀ x ∈ interior (BoxIntegral.Box.Icc box),
      HasFDerivAt (field u) (fieldDerivative u x) x
  continuousOn_field :
    ∀ u : W, ContinuousOn (field u) (BoxIntegral.Box.Icc box)
  zeroDirichlet_field :
    ∀ u : W, ZeroDirichletVectorOnBox box (field u)
  divergence_field :
    ∀ u : W, ∀ x ∈ BoxIntegral.Box.Icc box,
      ∑ i : Fin (n + 1), fieldDerivative u x (Pi.single i 1) i = 0
  transportIntegrable :
    ∀ u v w : W,
      IntegrableOn
        (fun x => ∑ i,
          fieldDerivative v x (field u x) i * field w x i)
        (BoxIntegral.Box.Icc box)
  convection : W →L[ℝ] W →L[ℝ] W →L[ℝ] ℝ
  convectionBound : ℝ
  convectionBound_nonneg : 0 ≤ convectionBound
  convection_norm_le :
    ∀ u v : W,
      ‖convection u v‖ ≤ convectionBound * ‖u‖ * ‖v‖
  convection_eq_integral :
    ∀ u v w : W,
      convection u v w =
        ∫ x in BoxIntegral.Box.Icc box,
          ∑ i, fieldDerivative v x (field u x) i * field w x i

namespace SmoothBoxGalerkinTransport

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

private theorem measurableSet_box
    (S : SmoothBoxGalerkinTransport (n := n) W) :
    MeasurableSet (BoxIntegral.Box.Icc S.box) := by
  rw [BoxIntegral.Box.Icc_def]
  exact measurableSet_Icc

/-- Integrability of the second transport term, obtained by commuting its
scalar factors. -/
theorem transportIntegrable_right
    (S : SmoothBoxGalerkinTransport (n := n) W) (u v w : W) :
    IntegrableOn
      (fun x => ∑ i,
        S.field v x i * S.fieldDerivative w x (S.field u x) i)
      (BoxIntegral.Box.Icc S.box) := by
  apply (S.transportIntegrable u w v).congr_fun
  · intro x _hx
    apply Finset.sum_congr rfl
    intro i _hi
    exact mul_comm _ _
  · exact S.measurableSet_box

/-- The synthesized box-domain convection form is skew in its transported and
test arguments. -/
theorem convection_skew
    (S : SmoothBoxGalerkinTransport (n := n) W) (u v w : W) :
    S.convection u v w = -S.convection u w v := by
  rw [S.convection_eq_integral, S.convection_eq_integral]
  have hibp := vector_transport_ibp S.box
    (S.field u) (S.field v) (S.field w)
    (S.fieldDerivative u) (S.fieldDerivative v) (S.fieldDerivative w)
    (S.hasFDerivAt_field u) (S.continuousOn_field u)
    (S.hasFDerivAt_field v) (S.continuousOn_field v)
    (S.hasFDerivAt_field w) (S.continuousOn_field w)
    (S.zeroDirichlet_field v) (S.zeroDirichlet_field w)
    (S.divergence_field u)
    (S.transportIntegrable u v w) (S.transportIntegrable_right u v w)
  have hcomm :
      ∫ x in BoxIntegral.Box.Icc S.box,
          ∑ i, S.field v x i * S.fieldDerivative w x (S.field u x) i =
        ∫ x in BoxIntegral.Box.Icc S.box,
          ∑ i, S.fieldDerivative w x (S.field u x) i * S.field v x i := by
    apply setIntegral_congr_fun S.measurableSet_box
    intro x _hx
    apply Finset.sum_congr rfl
    intro i _hi
    exact mul_comm _ _
  calc
    _ = -∫ x in BoxIntegral.Box.Icc S.box,
        ∑ i, S.field v x i * S.fieldDerivative w x (S.field u x) i := hibp
    _ = -∫ x in BoxIntegral.Box.Icc S.box,
        ∑ i, S.fieldDerivative w x (S.field u x) i * S.field v x i := by
          rw [hcomm]

/-- Diagonal cancellation for the synthesized convection form. -/
theorem convection_cancel
    (S : SmoothBoxGalerkinTransport (n := n) W) (u : W) :
    S.convection u u u = 0 := by
  have h := S.convection_skew u u u
  linarith

/-- The smooth box realization supplies the skew field of a finite-level
variational Galerkin system. -/
def toVariationalGalerkinSystem
    (S : SmoothBoxGalerkinTransport (n := n) W)
    (diffusion : W →L[ℝ] W →L[ℝ] ℝ)
    (diffusion_nonneg : ∀ u : W, 0 ≤ diffusion u u) :
    VariationalGalerkinSystem W where
  diffusion := diffusion
  convection := S.convection
  convectionBound := S.convectionBound
  convectionBound_nonneg := S.convectionBound_nonneg
  convection_norm_le := S.convection_norm_le
  diffusion_nonneg := diffusion_nonneg
  convection_skew := S.convection_skew

@[simp]
theorem toVariationalGalerkinSystem_convection
    (S : SmoothBoxGalerkinTransport (n := n) W)
    (diffusion : W →L[ℝ] W →L[ℝ] ℝ)
    (diffusion_nonneg : ∀ u : W, 0 ≤ diffusion u u) :
    (S.toVariationalGalerkinSystem diffusion diffusion_nonneg).convection =
      S.convection :=
  rfl

/-- Square-integrability data placing every synthesized field in the smooth
core of the box energy closure. -/
structure EnergyData
    (S : SmoothBoxGalerkinTransport (n := n) W) where
  velocity_memLp :
    ∀ u : W,
      MemLp (boxVelocityValue (S.field u)) 2 (BoxMeasure S.box)
  gradient_memLp :
    ∀ u : W,
      MemLp (boxGradientValue (S.fieldDerivative u)) 2 (BoxMeasure S.box)

namespace EnergyData

variable {S : SmoothBoxGalerkinTransport (n := n) W}
variable (E : EnergyData (n := n) S)

/-- The synthesized field with its box regularity and `L²` data bundled as a
smooth energy-core field. -/
def smoothField (u : W) : SmoothBoxEnergyField S.box where
  field := S.field u
  derivative := S.fieldDerivative u
  contDiff_field := S.contDiff_field u
  support_field := S.support_field u
  hasFDerivAt_field := S.hasFDerivAt_field u
  continuousOn_field := S.continuousOn_field u
  zeroDirichlet_field := S.zeroDirichlet_field u
  divergence_field := S.divergence_field u
  velocity_memLp := E.velocity_memLp u
  gradient_memLp := E.gradient_memLp u

private theorem velocityLp_add (u v : W) :
    (E.smoothField (u + v)).velocityLp =
      (E.smoothField u).velocityLp + (E.smoothField v).velocityLp := by
  calc
    (E.smoothField (u + v)).velocityLp =
        ((E.velocity_memLp u).add (E.velocity_memLp v)).toLp
          (boxVelocityValue (S.field u) +
            boxVelocityValue (S.field v)) := by
      apply MemLp.toLp_congr
      exact Filter.Eventually.of_forall fun x => by
        simp [smoothField, boxVelocityValue]
    _ = _ := MemLp.toLp_add (E.velocity_memLp u) (E.velocity_memLp v)

private theorem velocityLp_smul (c : ℝ) (u : W) :
    (E.smoothField (c • u)).velocityLp =
      c • (E.smoothField u).velocityLp := by
  calc
    (E.smoothField (c • u)).velocityLp =
        ((E.velocity_memLp u).const_smul c).toLp
          (c • boxVelocityValue (S.field u)) := by
      apply MemLp.toLp_congr
      exact Filter.Eventually.of_forall fun x => by
        simp [smoothField, boxVelocityValue]
    _ = _ := MemLp.toLp_const_smul c (E.velocity_memLp u)

private theorem gradientLp_add (u v : W) :
    (E.smoothField (u + v)).gradientLp =
      (E.smoothField u).gradientLp + (E.smoothField v).gradientLp := by
  calc
    (E.smoothField (u + v)).gradientLp =
        ((E.gradient_memLp u).add (E.gradient_memLp v)).toLp
          (boxGradientValue (S.fieldDerivative u) +
            boxGradientValue (S.fieldDerivative v)) := by
      apply MemLp.toLp_congr
      exact Filter.Eventually.of_forall fun x => by
        ext ij
        simp [smoothField, boxGradientValue]
    _ = _ := MemLp.toLp_add (E.gradient_memLp u) (E.gradient_memLp v)

private theorem gradientLp_smul (c : ℝ) (u : W) :
    (E.smoothField (c • u)).gradientLp =
      c • (E.smoothField u).gradientLp := by
  calc
    (E.smoothField (c • u)).gradientLp =
        ((E.gradient_memLp u).const_smul c).toLp
          (c • boxGradientValue (S.fieldDerivative u)) := by
      apply MemLp.toLp_congr
      exact Filter.Eventually.of_forall fun x => by
        ext ij
        simp [smoothField, boxGradientValue]
    _ = _ := MemLp.toLp_const_smul c (E.gradient_memLp u)

/-- Linear graph realization of the finite Galerkin space in the ambient
velocity-gradient product. -/
def graphLinearMap : W →ₗ[ℝ] BoxEnergyAmbient S.box where
  toFun u := (E.smoothField u).graphPoint
  map_add' u v := by
    simp only [SmoothBoxEnergyField.graphPoint, E.velocityLp_add,
      E.gradientLp_add]
    rw [← WithLp.toLp_add]
    simp only [Prod.mk_add_mk]
  map_smul' c u := by
    simp only [SmoothBoxEnergyField.graphPoint, E.velocityLp_smul,
      E.gradientLp_smul]
    rw [← WithLp.toLp_smul]
    simp only [RingHom.id_apply, Prod.smul_mk]

/-- Continuous graph realization; continuity follows from finite
dimensionality of the Galerkin space. -/
noncomputable def graphContinuousLinearMap
    [FiniteDimensional ℝ W] :
    W →L[ℝ] BoxEnergyAmbient S.box :=
  LinearMap.toContinuousLinearMap (E.graphLinearMap)

/-- Canonical finite-level lift into the `H¹_{0,σ}` graph closure. -/
noncomputable def energyLift
    [FiniteDimensional ℝ W] :
    W →L[ℝ] BoxH1ZeroSigma S.box :=
  E.graphContinuousLinearMap.codRestrict
    (smoothBoxGraphCore S.box).topologicalClosure fun u => by
      change (E.smoothField u).graphPoint ∈
        (smoothBoxGraphCore S.box).topologicalClosure
      exact (smoothBoxGraphCore S.box).le_topologicalClosure
        (Submodule.subset_span ⟨E.smoothField u, rfl⟩)

/-- Canonical finite-level lift into the `L²_σ` velocity closure. -/
noncomputable def stateLift
    [FiniteDimensional ℝ W] :
    W →L[ℝ] BoxL2Sigma S.box :=
  (boxEnergyToState S.box).comp E.energyLift

/-- Derivative component of the finite-level graph lift. -/
noncomputable def gradientLift
    [FiniteDimensional ℝ W] :
    W →L[ℝ] BoxGradientL2 S.box :=
  (boxEnergyGradient S.box).comp E.energyLift

@[simp]
theorem energyLift_apply_coe
    [FiniteDimensional ℝ W] (u : W) :
    ((E.energyLift u : BoxH1ZeroSigma S.box) : BoxEnergyAmbient S.box) =
      (E.smoothField u).graphPoint :=
  rfl

@[simp]
theorem stateLift_apply
    [FiniteDimensional ℝ W] (u : W) :
    E.stateLift u = (E.smoothField u).toState := by
  apply Subtype.ext
  rfl

@[simp]
theorem gradientLift_apply
    [FiniteDimensional ℝ W] (u : W) :
    E.gradientLift u = (E.smoothField u).gradientLp := by
  rfl

/-- Pullback of the concrete gradient pairing to the finite Galerkin space. -/
noncomputable def diffusion
    [FiniteDimensional ℝ W] :
    W →L[ℝ] W →L[ℝ] ℝ :=
  ContinuousLinearMap.bilinearComp
    (isBoundedBilinearMap_inner (𝕜 := ℝ)).toContinuousLinearMap
    E.gradientLift E.gradientLift

@[simp]
theorem diffusion_apply
    [FiniteDimensional ℝ W] (u v : W) :
    E.diffusion u v = ⟪E.gradientLift u, E.gradientLift v⟫_ℝ :=
  rfl

theorem diffusion_nonneg
    [FiniteDimensional ℝ W] (u : W) :
    0 ≤ E.diffusion u u := by
  rw [E.diffusion_apply]
  exact real_inner_self_nonneg

/-- Finite-level variational system with the concrete gradient diffusion form
and box-domain convection cancellation. -/
noncomputable def toBoxVariationalGalerkinSystem
    [FiniteDimensional ℝ W] :
    VariationalGalerkinSystem W :=
  S.toVariationalGalerkinSystem E.diffusion E.diffusion_nonneg

@[simp]
theorem toBoxVariationalGalerkinSystem_diffusion
    [FiniteDimensional ℝ W] :
    E.toBoxVariationalGalerkinSystem.diffusion = E.diffusion :=
  rfl

@[simp]
theorem toBoxVariationalGalerkinSystem_convection
    [FiniteDimensional ℝ W] :
    E.toBoxVariationalGalerkinSystem.convection = S.convection :=
  rfl

end EnergyData

end SmoothBoxGalerkinTransport

end
