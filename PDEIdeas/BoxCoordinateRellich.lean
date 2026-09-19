import PDEIdeas.BoxRellichReduction

/-!
# Coordinate reduction for the full box Rellich map

Compactness of the full vector-valued velocity projection is equivalent to
compactness of its finitely many scalar coordinate projections. This removes
the finite-dimensional target bookkeeping from the scalar Rellich theorem.
-/

open MeasureTheory Real InnerProductSpace Set
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

variable {n : ℕ}

/-- Insert a scalar into one coordinate of a Euclidean velocity value. -/
def boxVelocitySingleValue
    (i : Fin (n + 1)) :
    ℝ →L[ℝ] BoxVelocityValue n :=
  (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℝ (fun _ : Fin (n + 1) => ℝ) i)

@[simp]
theorem boxVelocitySingleValue_apply
    (i j : Fin (n + 1))
    (c : ℝ) :
    boxVelocitySingleValue i c j = if i = j then c else 0 := by
  classical
  simp [boxVelocitySingleValue, eq_comm]

/-- Insert a scalar L2 function into one coordinate of a velocity field. -/
def boxVelocitySingleLp
    (I : BoxIntegral.Box (Fin (n + 1)))
    (i : Fin (n + 1)) :
    BoxScalarL2 I →L[ℝ] BoxVelocityL2 I :=
  (boxVelocitySingleValue i).compLpL 2 (BoxMeasure I)

private theorem compLpL_comp
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (A : F →L[ℝ] G)
    (B : E →L[ℝ] F) :
    (A.compLpL 2 μ).comp (B.compLpL 2 μ) =
      (A.comp B).compLpL 2 μ := by
  ext f
  filter_upwards [
    A.coeFn_compLpL ((B.compLpL 2 μ) f),
    B.coeFn_compLpL f,
    (A.comp B).coeFn_compLpL f] with x hA hB hAB
  simp only [ContinuousLinearMap.comp_apply]
  rw [hA, hB, hAB]
  rfl

private theorem sum_compLpL
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    {ι : Type*}
    (s : Finset ι)
    (A : ι → E →L[ℝ] F) :
    (∑ i ∈ s, A i).compLpL 2 μ =
      ∑ i ∈ s, (A i).compLpL 2 μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      ext f
      filter_upwards [
        (0 : E →L[ℝ] F).coeFn_compLpL f,
        Lp.coeFn_zero F 2 μ] with x hmap hzero
      change
        ((0 : E →L[ℝ] F).compLpL 2 μ f : α → F) x =
          (0 : Lp F 2 μ) x
      rw [hmap]
      simpa using hzero.symm
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [ContinuousLinearMap.add_compLpL, ih]

theorem sum_boxVelocitySingleValue_comp_coordinate :
    ∑ i : Fin (n + 1),
        (boxVelocitySingleValue i).comp
          (boxVelocityCoordinateValue i) =
      ContinuousLinearMap.id ℝ (BoxVelocityValue n) := by
  classical
  ext v j
  simp [boxVelocityCoordinateValue]

/-- A Euclidean-valued L2 field is the sum of its inserted scalar
coordinates. -/
theorem sum_boxVelocitySingleLp_comp_coordinateLp
    (I : BoxIntegral.Box (Fin (n + 1))) :
    ∑ i : Fin (n + 1),
        (boxVelocitySingleLp I i).comp
          (boxVelocityCoordinateLp I i) =
      ContinuousLinearMap.id ℝ (BoxVelocityL2 I) := by
  classical
  have hcomp :
      ∀ i : Fin (n + 1),
        (boxVelocitySingleLp I i).comp
            (boxVelocityCoordinateLp I i) =
          ((boxVelocitySingleValue i).comp
            (boxVelocityCoordinateValue i)).compLpL
              2 (BoxMeasure I) := by
    intro i
    exact compLpL_comp (BoxMeasure I)
      (boxVelocitySingleValue i) (boxVelocityCoordinateValue i)
  rw [Finset.sum_congr rfl fun i _ => hcomp i]
  rw [← sum_compLpL (BoxMeasure I) Finset.univ
    (fun i => (boxVelocitySingleValue i).comp
      (boxVelocityCoordinateValue i))]
  rw [sum_boxVelocitySingleValue_comp_coordinate]
  ext f
  filter_upwards [
    (ContinuousLinearMap.id ℝ (BoxVelocityValue n)).coeFn_compLpL f] with x hx
  rw [hx]
  rfl

/-- One scalar coordinate of the full zero-face velocity projection. -/
def boxFullEnergyToVelocityCoordinate
    (I : BoxIntegral.Box (Fin (n + 1)))
    (i : Fin (n + 1)) :
    BoxH1ZeroFull I →L[ℝ] BoxScalarL2 I :=
  (boxVelocityCoordinateLp I i).comp (boxFullEnergyToVelocity I)

theorem boxFullEnergyToVelocity_eq_sum_coordinates
    (I : BoxIntegral.Box (Fin (n + 1))) :
    boxFullEnergyToVelocity I =
      ∑ i : Fin (n + 1),
        (boxVelocitySingleLp I i).comp
          (boxFullEnergyToVelocityCoordinate I i) := by
  classical
  apply ContinuousLinearMap.ext
  intro u
  have h := congrArg
    (fun T : BoxVelocityL2 I →L[ℝ] BoxVelocityL2 I =>
      T (boxFullEnergyToVelocity I u))
    (sum_boxVelocitySingleLp_comp_coordinateLp I)
  simpa [boxFullEnergyToVelocityCoordinate] using h.symm

private theorem isCompactOperator_finset_sum
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ι : Type*}
    (s : Finset ι)
    (T : ι → E →L[ℝ] F)
    (hT : ∀ i ∈ s, IsCompactOperator (T i)) :
    IsCompactOperator ⇑(∑ i ∈ s, T i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (isCompactOperator_zero :
        IsCompactOperator (0 : E → F))
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      simpa only [ContinuousLinearMap.add_apply] using
        (hT i (Finset.mem_insert_self i s)).add
          (ih fun j hj => hT j (Finset.mem_insert_of_mem hj))

/-- Compactness of a finite-dimensional vector-valued map is equivalent to
compactness of all scalar coordinate maps. -/
theorem boxFullEnergyToVelocity_isCompactOperator_iff_coordinates
    (I : BoxIntegral.Box (Fin (n + 1))) :
    IsCompactOperator (boxFullEnergyToVelocity I) ↔
      ∀ i : Fin (n + 1),
        IsCompactOperator (boxFullEnergyToVelocityCoordinate I i) := by
  constructor
  · intro h i
    exact h.clm_comp (boxVelocityCoordinateLp I i)
  · intro h
    rw [boxFullEnergyToVelocity_eq_sum_coordinates]
    apply isCompactOperator_finset_sum Finset.univ
    intro i _hi
    exact (h i).clm_comp (boxVelocitySingleLp I i)

/-- Scalar coordinate Rellich compactness implies compactness of the
divergence-free canonical box map. -/
theorem boxEnergyToState_isCompactOperator_of_coordinateRellich
    (I : BoxIntegral.Box (Fin (n + 1)))
    (hRellich :
      ∀ i : Fin (n + 1),
        IsCompactOperator (boxFullEnergyToVelocityCoordinate I i)) :
    IsCompactOperator (boxEnergyToState I) :=
  boxEnergyToState_isCompactOperator_of_fullRellich I
    ((boxFullEnergyToVelocity_isCompactOperator_iff_coordinates I).2 hRellich)

end
