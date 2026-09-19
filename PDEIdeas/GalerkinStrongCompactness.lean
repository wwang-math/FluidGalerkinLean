import PDEIdeas.AubinLionsInterface
import PDEIdeas.GalerkinProjection
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Logic.Denumerable
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.UniformConvergence

open Filter Function Metric Set InnerProductSpace
open BoundedContinuousFunction
open scoped BigOperators NNReal

noncomputable section

/-!
# Strong compactness for Galerkin sequences

This file supplies an actual subsequence-extraction theorem for a sequence of
finite-dimensional Galerkin spaces.  Compactness follows from a compact
embedding, a uniform bound in the source space, and uniform time regularity.
The resulting strong path convergence drives both nonlinear convergence and
passage to the tested limiting equation.
-/

/-- Increasing finite subsets exhausting an arbitrary countable basis index.
This lets finite-dimensional Galerkin heads be defined without assuming that
the Hilbert basis itself is indexed by `ℕ`. -/
structure HilbertBasisExhaustion (ι : Type*) where
  head : ℕ → Finset ι
  monotone : Monotone head
  mem_head : ∀ i, ∃ n, i ∈ head n

namespace HilbertBasisExhaustion

variable {ι : Type*}

/-- Canonical finite exhaustion of a countable type, obtained from an
`Encodable` enumeration. -/
noncomputable def ofCountable [Countable ι] : HilbertBasisExhaustion ι := by
  classical
  letI : Encodable ι := Classical.choice (nonempty_encodable ι)
  let head : ℕ → Finset ι := fun n =>
    (Finset.range n).biUnion fun k => (Encodable.decode k : Option ι).toFinset
  refine
    { head := head
      monotone := ?_
      mem_head := ?_ }
  · intro m n hmn i hi
    simp only [head, Finset.mem_biUnion] at hi ⊢
    obtain ⟨k, hk, hki⟩ := hi
    exact ⟨k, Finset.mem_range.mpr ((Finset.mem_range.mp hk).trans_le hmn), hki⟩
  · intro i
    refine ⟨Encodable.encode i + 1, ?_⟩
    simp only [head, Finset.mem_biUnion]
    exact ⟨Encodable.encode i,
      Finset.mem_range.mpr (Nat.lt_succ_self _), by simp⟩

end HilbertBasisExhaustion

/-- A sequence of finite-dimensional Galerkin projectors on a common ambient
space.  The spaces are nested and the projectors converge strongly to the
identity, so the approximation index represents a genuine dense Galerkin
scheme rather than repeated copies of one fixed truncation. -/
structure GalerkinProjectorSequence
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] where
  space : ℕ → Submodule ℝ H
  proj : ℕ → H →L[ℝ] H
  finiteDimensional : ∀ n, FiniteDimensional ℝ (space n)
  range_proj : ∀ n, LinearMap.range (proj n : H →ₗ[ℝ] H) = space n
  proj_fixed : ∀ n, ∀ x ∈ space n, proj n x = x
  nested : Monotone space
  proj_tendsto : ∀ x : H, Tendsto (fun n => proj n x) atTop (nhds x)

namespace GalerkinProjectorSequence

/-- The `n`-th member of a projector sequence as the finite-dimensional
projector used by the coefficient-ODE layer. -/
noncomputable def galerkinProjectionAt
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : GalerkinProjectorSequence H) (n : ℕ) : GalerkinProjection H where
  space := P.space n
  proj := P.proj n
  finiteDimensional_space := P.finiteDimensional n
  mem_space := fun x => by
    rw [← P.range_proj n]
    exact ⟨x, rfl⟩
  fix_space := P.proj_fixed n

theorem proj_mem
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (P : GalerkinProjectorSequence H) (n : ℕ) (x : H) :
    P.proj n x ∈ P.space n := by
  rw [← P.range_proj n]
  exact ⟨x, rfl⟩

theorem proj_idempotent
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (P : GalerkinProjectorSequence H) (n : ℕ) (x : H) :
    P.proj n (P.proj n x) = P.proj n x :=
  P.proj_fixed n _ (P.proj_mem n x)

section HilbertBasis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Span of the first `n` vectors of a countable Hilbert basis. -/
def partialSpace (b : HilbertBasis ℕ ℝ H) (n : ℕ) : Submodule ℝ H :=
  Submodule.span ℝ (b '' Set.Iio n)

theorem partialSpace_finiteDimensional
    (b : HilbertBasis ℕ ℝ H) (n : ℕ) :
    FiniteDimensional ℝ (partialSpace b n) := by
  apply FiniteDimensional.span_of_finite ℝ
  exact (Set.finite_Iio n).image b

theorem partialSpace_monotone
    (b : HilbertBasis ℕ ℝ H) : Monotone (partialSpace b) := by
  intro m n hmn
  apply Submodule.span_mono
  exact Set.image_mono (fun _ hi => lt_of_lt_of_le hi hmn)

theorem partialSpace_dense
    (b : HilbertBasis ℕ ℝ H) :
    ⊤ ≤ (⨆ n, partialSpace b n).topologicalClosure := by
  rw [← b.dense_span]
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_le.mpr
  rintro x ⟨i, rfl⟩
  apply (le_iSup (partialSpace b) (i + 1))
  apply Submodule.subset_span
  exact ⟨i, by simp, rfl⟩

/-- Orthogonal projection onto the first `n` Hilbert-basis modes. -/
noncomputable def partialProjection
    (b : HilbertBasis ℕ ℝ H) (n : ℕ) : H →L[ℝ] H := by
  letI : FiniteDimensional ℝ (partialSpace b n) :=
    partialSpace_finiteDimensional b n
  letI : IsUniformAddGroup (partialSpace b n) :=
    (partialSpace b n).toAddSubgroup.isUniformAddGroup
  letI : CompleteSpace (partialSpace b n) :=
    FiniteDimensional.complete ℝ _
  exact (partialSpace b n).starProjection

/-- The first `n` vectors of a Hilbert basis form an orthonormal basis of
the corresponding partial Galerkin space. -/
noncomputable def partialOrthonormalBasis
    (b : HilbertBasis ℕ ℝ H) (n : ℕ) :
    OrthonormalBasis (Finset.range n) ℝ (partialSpace b n) := by
  classical
  let e := OrthonormalBasis.span b.orthonormal (Finset.range n)
  have hset :
      ((Finset.range n).image b : Set H) = b '' Set.Iio n := by
    ext x
    constructor
    · intro hx
      rw [Finset.coe_image] at hx
      rcases hx with ⟨i, hi, rfl⟩
      exact ⟨i, by simpa using hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      rw [Finset.coe_image]
      exact ⟨i, by simpa using hi, rfl⟩
  have hspace :
      Submodule.span ℝ ((Finset.range n).image b : Set H) =
        partialSpace b n := by
    rw [partialSpace, hset]
  exact e.map (LinearIsometryEquiv.ofEq _ _ hspace)

@[simp] theorem partialOrthonormalBasis_apply
    (b : HilbertBasis ℕ ℝ H) (n : ℕ) (i : Finset.range n) :
    ((partialOrthonormalBasis b n i : partialSpace b n) : H) = b i := by
  classical
  simp [partialOrthonormalBasis]

/-- The canonical partial projector is the finite reconstruction from the
first Hilbert-basis coordinates. -/
theorem partialProjection_apply_eq_sum
    (b : HilbertBasis ℕ ℝ H) (n : ℕ) (x : H) :
    partialProjection b n x =
      ∑ i ∈ Finset.range n, ⟪x, b i⟫_ℝ • b i := by
  classical
  letI : FiniteDimensional ℝ (partialSpace b n) :=
    partialSpace_finiteDimensional b n
  letI : IsUniformAddGroup (partialSpace b n) :=
    (partialSpace b n).toAddSubgroup.isUniformAddGroup
  letI : CompleteSpace (partialSpace b n) :=
    FiniteDimensional.complete ℝ _
  have hproj :=
    (partialOrthonormalBasis b n).orthogonalProjection_apply_eq_sum x
  change (partialSpace b n).starProjection x = _
  rw [Submodule.starProjection_apply, hproj]
  simpa [partialOrthonormalBasis_apply, real_inner_comm] using
    (Finset.sum_attach (Finset.range n)
      (fun i => ⟪x, b i⟫_ℝ • b i))

/-- Orthogonal projection onto the first `n` Hilbert-basis modes is a
contraction. -/
theorem partialProjection_norm_le
    (b : HilbertBasis ℕ ℝ H) (n : ℕ) :
    ‖partialProjection b n‖ ≤ 1 := by
  letI : FiniteDimensional ℝ (partialSpace b n) :=
    partialSpace_finiteDimensional b n
  letI : IsUniformAddGroup (partialSpace b n) :=
    (partialSpace b n).toAddSubgroup.isUniformAddGroup
  letI : CompleteSpace (partialSpace b n) :=
    FiniteDimensional.complete ℝ _
  exact Submodule.starProjection_norm_le (partialSpace b n)

/-- Hilbert-basis partial projection is self-adjoint. -/
theorem inner_partialProjection_left_eq_right
    (b : HilbertBasis ℕ ℝ H) (n : ℕ) (x y : H) :
    ⟪partialProjection b n x, y⟫_ℝ =
      ⟪x, partialProjection b n y⟫_ℝ := by
  letI : FiniteDimensional ℝ (partialSpace b n) :=
    partialSpace_finiteDimensional b n
  letI : IsUniformAddGroup (partialSpace b n) :=
    (partialSpace b n).toAddSubgroup.isUniformAddGroup
  letI : CompleteSpace (partialSpace b n) :=
    FiniteDimensional.complete ℝ _
  exact (partialSpace b n).inner_starProjection_left_eq_right x y

/-- Every Hilbert-basis partial projection has finite-dimensional range and
is therefore a compact operator. -/
theorem partialProjection_isCompactOperator
    (b : HilbertBasis ℕ ℝ H) (n : ℕ) :
    IsCompactOperator (partialProjection b n) := by
  letI : FiniteDimensional ℝ (partialSpace b n) :=
    partialSpace_finiteDimensional b n
  letI : IsUniformAddGroup (partialSpace b n) :=
    (partialSpace b n).toAddSubgroup.isUniformAddGroup
  letI : CompleteSpace (partialSpace b n) :=
    FiniteDimensional.complete ℝ _
  let Q : H →L[ℝ] partialSpace b n :=
    LinearMap.mkContinuous
      (LinearMap.codRestrict
        (partialSpace b n)
        (partialProjection b n : H →ₗ[ℝ] H)
        (fun x => by
          change (partialSpace b n).starProjection x ∈ partialSpace b n
          exact Submodule.starProjection_apply_mem (partialSpace b n) x))
      1
      (fun x => by
        change ‖(partialSpace b n).starProjection x‖ ≤ 1 * ‖x‖
        simpa using
          Submodule.norm_starProjection_apply_le (partialSpace b n) x)
  have hQ : IsCompactOperator Q :=
    isCompactOperator_of_locallyCompactSpace_dom Q
  have hcomp := hQ.clm_comp (partialSpace b n).subtypeL
  simpa [Q, Function.comp_def] using hcomp

@[simp] theorem range_partialProjection
    (b : HilbertBasis ℕ ℝ H) (n : ℕ) :
    LinearMap.range (partialProjection b n : H →ₗ[ℝ] H) = partialSpace b n := by
  letI : FiniteDimensional ℝ (partialSpace b n) :=
    partialSpace_finiteDimensional b n
  letI : IsUniformAddGroup (partialSpace b n) :=
    (partialSpace b n).toAddSubgroup.isUniformAddGroup
  letI : CompleteSpace (partialSpace b n) :=
    FiniteDimensional.complete ℝ _
  exact Submodule.range_starProjection (partialSpace b n)

theorem partialProjection_fixed
    (b : HilbertBasis ℕ ℝ H) (n : ℕ) (x : H)
    (hx : x ∈ partialSpace b n) :
    partialProjection b n x = x := by
  letI : FiniteDimensional ℝ (partialSpace b n) :=
    partialSpace_finiteDimensional b n
  letI : IsUniformAddGroup (partialSpace b n) :=
    (partialSpace b n).toAddSubgroup.isUniformAddGroup
  letI : CompleteSpace (partialSpace b n) :=
    FiniteDimensional.complete ℝ _
  exact Submodule.starProjection_eq_self_iff.mpr hx

theorem partialProjection_tendsto
    (b : HilbertBasis ℕ ℝ H) (x : H) :
    Tendsto (fun n => partialProjection b n x) atTop (nhds x) := by
  let hFinite : ∀ n, FiniteDimensional ℝ (partialSpace b n) :=
    partialSpace_finiteDimensional b
  letI (n : ℕ) : FiniteDimensional ℝ (partialSpace b n) := hFinite n
  letI (n : ℕ) : IsUniformAddGroup (partialSpace b n) :=
    (partialSpace b n).toAddSubgroup.isUniformAddGroup
  letI (n : ℕ) : CompleteSpace (partialSpace b n) :=
    FiniteDimensional.complete ℝ _
  exact Submodule.starProjection_tendsto_self
    (partialSpace b) (partialSpace_monotone b) x (partialSpace_dense b)

/-- The canonical genuine Galerkin projector sequence generated by a
countable Hilbert basis. -/
noncomputable def ofHilbertBasis
    (b : HilbertBasis ℕ ℝ H) : GalerkinProjectorSequence H where
  space := partialSpace b
  proj := partialProjection b
  finiteDimensional := partialSpace_finiteDimensional b
  range_proj := range_partialProjection b
  proj_fixed := partialProjection_fixed b
  nested := partialSpace_monotone b
  proj_tendsto := partialProjection_tendsto b

/-- Every projector in the Hilbert-basis sequence is orthogonal. -/
theorem ofHilbertBasis_isOrthogonal
    (b : HilbertBasis ℕ ℝ H) (n : ℕ) :
    ((ofHilbertBasis b).galerkinProjectionAt n).IsOrthogonal := by
  letI : FiniteDimensional ℝ (partialSpace b n) :=
    partialSpace_finiteDimensional b n
  letI : IsUniformAddGroup (partialSpace b n) :=
    (partialSpace b n).toAddSubgroup.isUniformAddGroup
  letI : CompleteSpace (partialSpace b n) :=
    FiniteDimensional.complete ℝ _
  intro x y
  change ⟪(partialSpace b n).starProjection x, (y : H)⟫_ℝ =
    ⟪x, (y : H)⟫_ℝ
  rw [(partialSpace b n).inner_starProjection_left_eq_right]
  rw [(partialSpace b n).starProjection_eq_self_iff.mpr y.property]

end HilbertBasis

section HilbertBasisExhaustion

variable {ι H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Span of a finite set of vectors from an arbitrarily indexed Hilbert
basis. -/
def finitePartialSpace (b : HilbertBasis ι ℝ H) (s : Finset ι) :
    Submodule ℝ H :=
  Submodule.span ℝ (b '' (s : Set ι))

theorem finitePartialSpace_finiteDimensional
    (b : HilbertBasis ι ℝ H) (s : Finset ι) :
    FiniteDimensional ℝ (finitePartialSpace b s) := by
  apply FiniteDimensional.span_of_finite ℝ
  exact s.finite_toSet.image b

theorem finitePartialSpace_mono
    (b : HilbertBasis ι ℝ H) {s t : Finset ι} (hst : s ⊆ t) :
    finitePartialSpace b s ≤ finitePartialSpace b t := by
  apply Submodule.span_mono
  exact Set.image_mono hst

theorem finitePartialSpace_exhaustion_dense
    (b : HilbertBasis ι ℝ H) (E : HilbertBasisExhaustion ι) :
    ⊤ ≤ (⨆ n, finitePartialSpace b (E.head n)).topologicalClosure := by
  rw [← b.dense_span]
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_le.mpr
  rintro x ⟨i, rfl⟩
  obtain ⟨n, hin⟩ := E.mem_head i
  exact (le_iSup (fun n => finitePartialSpace b (E.head n)) n)
    (Submodule.subset_span ⟨i, hin, rfl⟩)

/-- The selected Hilbert-basis vectors form an orthonormal basis of their
finite span. -/
noncomputable def finitePartialOrthonormalBasis
    (b : HilbertBasis ι ℝ H) (s : Finset ι) :
    OrthonormalBasis s ℝ (finitePartialSpace b s) := by
  classical
  let e := OrthonormalBasis.span b.orthonormal s
  have hset :
      ((s.image b : Finset H) : Set H) = b '' (s : Set ι) := by
    ext x
    constructor
    · intro hx
      rw [Finset.coe_image] at hx
      rcases hx with ⟨i, hi, rfl⟩
      exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      rw [Finset.coe_image]
      exact ⟨i, hi, rfl⟩
  have hspace :
      Submodule.span ℝ ((s.image b : Finset H) : Set H) =
        finitePartialSpace b s := by
    rw [finitePartialSpace, hset]
  exact e.map (LinearIsometryEquiv.ofEq _ _ hspace)

@[simp]
theorem finitePartialOrthonormalBasis_apply
    (b : HilbertBasis ι ℝ H) (s : Finset ι) (i : s) :
    ((finitePartialOrthonormalBasis b s i : finitePartialSpace b s) : H) = b i := by
  classical
  simp [finitePartialOrthonormalBasis]

/-- Orthogonal projection onto a finite set of Hilbert-basis modes. -/
noncomputable def finitePartialProjection
    (b : HilbertBasis ι ℝ H) (s : Finset ι) : H →L[ℝ] H := by
  letI : FiniteDimensional ℝ (finitePartialSpace b s) :=
    finitePartialSpace_finiteDimensional b s
  letI : IsUniformAddGroup (finitePartialSpace b s) :=
    (finitePartialSpace b s).toAddSubgroup.isUniformAddGroup
  letI : CompleteSpace (finitePartialSpace b s) :=
    FiniteDimensional.complete ℝ _
  exact (finitePartialSpace b s).starProjection

/-- Finite projection is the corresponding coordinate sum. -/
theorem finitePartialProjection_apply_eq_sum
    (b : HilbertBasis ι ℝ H) (s : Finset ι) (x : H) :
    finitePartialProjection b s x =
      ∑ i ∈ s, ⟪x, b i⟫_ℝ • b i := by
  classical
  letI : FiniteDimensional ℝ (finitePartialSpace b s) :=
    finitePartialSpace_finiteDimensional b s
  letI : IsUniformAddGroup (finitePartialSpace b s) :=
    (finitePartialSpace b s).toAddSubgroup.isUniformAddGroup
  letI : CompleteSpace (finitePartialSpace b s) :=
    FiniteDimensional.complete ℝ _
  have hproj :=
    (finitePartialOrthonormalBasis b s).orthogonalProjection_apply_eq_sum x
  change (finitePartialSpace b s).starProjection x = _
  rw [Submodule.starProjection_apply, hproj]
  simpa [finitePartialOrthonormalBasis_apply, real_inner_comm] using
    (Finset.sum_attach s (fun i => ⟪x, b i⟫_ℝ • b i))

theorem finitePartialProjection_norm_le
    (b : HilbertBasis ι ℝ H) (s : Finset ι) :
    ‖finitePartialProjection b s‖ ≤ 1 := by
  letI : FiniteDimensional ℝ (finitePartialSpace b s) :=
    finitePartialSpace_finiteDimensional b s
  letI : IsUniformAddGroup (finitePartialSpace b s) :=
    (finitePartialSpace b s).toAddSubgroup.isUniformAddGroup
  letI : CompleteSpace (finitePartialSpace b s) :=
    FiniteDimensional.complete ℝ _
  exact Submodule.starProjection_norm_le (finitePartialSpace b s)

theorem inner_finitePartialProjection_left_eq_right
    (b : HilbertBasis ι ℝ H) (s : Finset ι) (x y : H) :
    ⟪finitePartialProjection b s x, y⟫_ℝ =
      ⟪x, finitePartialProjection b s y⟫_ℝ := by
  letI : FiniteDimensional ℝ (finitePartialSpace b s) :=
    finitePartialSpace_finiteDimensional b s
  letI : IsUniformAddGroup (finitePartialSpace b s) :=
    (finitePartialSpace b s).toAddSubgroup.isUniformAddGroup
  letI : CompleteSpace (finitePartialSpace b s) :=
    FiniteDimensional.complete ℝ _
  exact (finitePartialSpace b s).inner_starProjection_left_eq_right x y

theorem finitePartialProjection_isCompactOperator
    (b : HilbertBasis ι ℝ H) (s : Finset ι) :
    IsCompactOperator (finitePartialProjection b s) := by
  letI : FiniteDimensional ℝ (finitePartialSpace b s) :=
    finitePartialSpace_finiteDimensional b s
  letI : IsUniformAddGroup (finitePartialSpace b s) :=
    (finitePartialSpace b s).toAddSubgroup.isUniformAddGroup
  letI : CompleteSpace (finitePartialSpace b s) :=
    FiniteDimensional.complete ℝ _
  let Q : H →L[ℝ] finitePartialSpace b s :=
    LinearMap.mkContinuous
      (LinearMap.codRestrict
        (finitePartialSpace b s)
        (finitePartialProjection b s : H →ₗ[ℝ] H)
        (fun x => by
          change (finitePartialSpace b s).starProjection x ∈ finitePartialSpace b s
          exact Submodule.starProjection_apply_mem (finitePartialSpace b s) x))
      1
      (fun x => by
        change ‖(finitePartialSpace b s).starProjection x‖ ≤ 1 * ‖x‖
        simpa using
          Submodule.norm_starProjection_apply_le (finitePartialSpace b s) x)
  have hQ : IsCompactOperator Q :=
    isCompactOperator_of_locallyCompactSpace_dom Q
  have hcomp := hQ.clm_comp (finitePartialSpace b s).subtypeL
  simpa [Q, Function.comp_def] using hcomp

@[simp]
theorem range_finitePartialProjection
    (b : HilbertBasis ι ℝ H) (s : Finset ι) :
    LinearMap.range (finitePartialProjection b s : H →ₗ[ℝ] H) =
      finitePartialSpace b s := by
  letI : FiniteDimensional ℝ (finitePartialSpace b s) :=
    finitePartialSpace_finiteDimensional b s
  letI : IsUniformAddGroup (finitePartialSpace b s) :=
    (finitePartialSpace b s).toAddSubgroup.isUniformAddGroup
  letI : CompleteSpace (finitePartialSpace b s) :=
    FiniteDimensional.complete ℝ _
  exact Submodule.range_starProjection (finitePartialSpace b s)

theorem finitePartialProjection_fixed
    (b : HilbertBasis ι ℝ H) (s : Finset ι) (x : H)
    (hx : x ∈ finitePartialSpace b s) :
    finitePartialProjection b s x = x := by
  letI : FiniteDimensional ℝ (finitePartialSpace b s) :=
    finitePartialSpace_finiteDimensional b s
  letI : IsUniformAddGroup (finitePartialSpace b s) :=
    (finitePartialSpace b s).toAddSubgroup.isUniformAddGroup
  letI : CompleteSpace (finitePartialSpace b s) :=
    FiniteDimensional.complete ℝ _
  exact Submodule.starProjection_eq_self_iff.mpr hx

theorem finitePartialProjection_tendsto
    (b : HilbertBasis ι ℝ H) (E : HilbertBasisExhaustion ι) (x : H) :
    Tendsto (fun n => finitePartialProjection b (E.head n) x) atTop (nhds x) := by
  let hFinite : ∀ n,
      FiniteDimensional ℝ (finitePartialSpace b (E.head n)) :=
    fun n => finitePartialSpace_finiteDimensional b (E.head n)
  letI (n : ℕ) : FiniteDimensional ℝ (finitePartialSpace b (E.head n)) :=
    hFinite n
  letI (n : ℕ) : IsUniformAddGroup (finitePartialSpace b (E.head n)) :=
    (finitePartialSpace b (E.head n)).toAddSubgroup.isUniformAddGroup
  letI (n : ℕ) : CompleteSpace (finitePartialSpace b (E.head n)) :=
    FiniteDimensional.complete ℝ _
  exact Submodule.starProjection_tendsto_self
    (fun n => finitePartialSpace b (E.head n))
    (fun _ _ hmn => finitePartialSpace_mono b (E.monotone hmn)) x
    (finitePartialSpace_exhaustion_dense b E)

/-- A genuine projector sequence generated by an arbitrary Hilbert basis and
an increasing finite exhaustion of its index. -/
noncomputable def ofHilbertBasisExhaustion
    (b : HilbertBasis ι ℝ H) (E : HilbertBasisExhaustion ι) :
    GalerkinProjectorSequence H where
  space n := finitePartialSpace b (E.head n)
  proj n := finitePartialProjection b (E.head n)
  finiteDimensional n := finitePartialSpace_finiteDimensional b (E.head n)
  range_proj n := range_finitePartialProjection b (E.head n)
  proj_fixed n := finitePartialProjection_fixed b (E.head n)
  nested _ _ hmn := finitePartialSpace_mono b (E.monotone hmn)
  proj_tendsto := finitePartialProjection_tendsto b E

/-- Every projection in an exhausted Hilbert-basis tower is orthogonal. -/
theorem ofHilbertBasisExhaustion_isOrthogonal
    (b : HilbertBasis ι ℝ H) (E : HilbertBasisExhaustion ι) (n : ℕ) :
    ((ofHilbertBasisExhaustion b E).galerkinProjectionAt n).IsOrthogonal := by
  letI : FiniteDimensional ℝ (finitePartialSpace b (E.head n)) :=
    finitePartialSpace_finiteDimensional b (E.head n)
  letI : IsUniformAddGroup (finitePartialSpace b (E.head n)) :=
    (finitePartialSpace b (E.head n)).toAddSubgroup.isUniformAddGroup
  letI : CompleteSpace (finitePartialSpace b (E.head n)) :=
    FiniteDimensional.complete ℝ _
  intro x y
  change ⟪(finitePartialSpace b (E.head n)).starProjection x, (y : H)⟫_ℝ =
    ⟪x, (y : H)⟫_ℝ
  rw [(finitePartialSpace b (E.head n)).inner_starProjection_left_eq_right]
  rw [(finitePartialSpace b (E.head n)).starProjection_eq_self_iff.mpr y.property]

end HilbertBasisExhaustion

end GalerkinProjectorSequence

/-- Trajectories associated with a genuine Galerkin projector sequence,
together with the uniform compactness estimates.  Each ambient trajectory has
a uniformly bounded lift through a compact embedding.  A common Lipschitz
constant supplies the time equicontinuity used by Arzela--Ascoli. -/
structure StronglyCompactGalerkinFamily
    (I V H : Type*)
    [PseudoMetricSpace I] [CompactSpace I]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup H] [NormedSpace ℝ H] where
  projectors : GalerkinProjectorSequence H
  embed : V →L[ℝ] H
  embed_compact : IsCompactOperator embed
  trajectory : ℕ → I →ᵇ H
  trajectory_mem : ∀ n t, trajectory n t ∈ projectors.space n
  lift : ℕ → I → V
  embed_lift : ∀ n t, embed (lift n t) = trajectory n t
  radius : ℝ
  lift_bound : ∀ n t, ‖lift n t‖ ≤ radius
  timeLipschitz : ℝ≥0
  trajectory_lipschitz : ∀ n, LipschitzWith timeLipschitz (trajectory n)

/-- The output of the checked compactness argument: a strict subsequence and a
strong limit in the uniform topology on bounded continuous paths. -/
structure StrongPathSubsequence
    {I H : Type*}
    [TopologicalSpace I] [PseudoMetricSpace H]
    (U : ℕ → I →ᵇ H) where
  subseq : ExtractedSubsequence
  limit : I →ᵇ H
  converges : Tendsto (U ∘ subseq.idx) atTop (nhds limit)

namespace StronglyCompactGalerkinFamily

variable {I V H : Type*}
    [PseudoMetricSpace I] [CompactSpace I]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup H] [NormedSpace ℝ H]

private theorem trajectory_equicontinuous
    (G : StronglyCompactGalerkinFamily I V H) :
    Equicontinuous
      ((↑) : Set.range G.trajectory → I → H) := by
  apply UniformEquicontinuous.equicontinuous
  apply LipschitzWith.uniformEquicontinuous
      (fun f : Set.range G.trajectory => (f.1 : I → H)) G.timeLipschitz
  rintro ⟨f, n, rfl⟩
  exact G.trajectory_lipschitz n

/-- Compact embedding plus uniform source-space and time-regularity bounds
give a genuinely extracted strongly convergent subsequence of Galerkin paths. -/
theorem exists_stronglyConvergent_subsequence
    (G : StronglyCompactGalerkinFamily I V H) :
    Nonempty (StrongPathSubsequence G.trajectory) := by
  obtain ⟨K, hKcompact, hK⟩ :=
    G.embed_compact.image_closedBall_subset_compact G.radius
  have hRange :
      ∀ (f : I →ᵇ H) (t : I),
        f ∈ Set.range G.trajectory → f t ∈ K := by
    rintro f t ⟨n, rfl⟩
    apply hK
    refine ⟨G.lift n t, ?_, G.embed_lift n t⟩
    exact mem_closedBall_zero_iff.mpr (G.lift_bound n t)
  have hCompactPaths :
      IsCompact (closure (Set.range G.trajectory)) :=
    BoundedContinuousFunction.arzela_ascoli
      K hKcompact (Set.range G.trajectory) hRange G.trajectory_equicontinuous
  obtain ⟨u, _hu, φ, hφ, hconv⟩ :=
    hCompactPaths.tendsto_subseq
      (x := G.trajectory)
      (fun n => subset_closure ⟨n, rfl⟩)
  exact ⟨{
    subseq := ⟨φ, hφ⟩
    limit := u
    converges := hconv
  }⟩

/-- A selected strong limit, obtained only from the checked compactness
theorem above. -/
noncomputable def strongLimit
    (G : StronglyCompactGalerkinFamily I V H) :
    StrongPathSubsequence G.trajectory :=
  Classical.choice G.exists_stronglyConvergent_subsequence

theorem strongLimit_converges
    (G : StronglyCompactGalerkinFamily I V H) :
    Tendsto
      (G.trajectory ∘ G.strongLimit.subseq.idx)
      atTop
      (nhds G.strongLimit.limit) :=
  G.strongLimit.converges

/-- Every continuous observable of the state, including a continuous
quadratic convection map, converges along the extracted subsequence. -/
theorem observable_tendsto
    (G : StronglyCompactGalerkinFamily I V H)
    {Y : Type*} [TopologicalSpace Y]
    (observable : (I →ᵇ H) → Y)
    (hObservable : Continuous observable) :
    Tendsto
      (fun k => observable (G.trajectory (G.strongLimit.subseq.idx k)))
      atTop
      (nhds (observable G.strongLimit.limit)) := by
  exact hObservable.continuousAt.tendsto.comp G.strongLimit_converges

/-- A continuous nonlinear map on strong path space passes to the limit
without a separately postulated nonlinear-convergence field. -/
theorem nonlinear_tendsto
    (G : StronglyCompactGalerkinFamily I V H)
    {N : Type*} [TopologicalSpace N]
    (nonlinear : (I →ᵇ H) → N)
    (hNonlinear : Continuous nonlinear) :
    Tendsto
      (fun k => nonlinear (G.trajectory (G.strongLimit.subseq.idx k)))
      atTop
      (nhds (nonlinear G.strongLimit.limit)) :=
  G.observable_tendsto nonlinear hNonlinear

/-- Passing to the tested limit is a consequence of strong state convergence,
dense Galerkin test projection, continuity of the residual, and the finite
Galerkin equations.  The limiting tested equation is not supplied as input. -/
theorem tested_limit_equation
    (G : StronglyCompactGalerkinFamily I V H)
    {Test : Type*} [TopologicalSpace Test]
    (testProjection : ℕ → Test → Test)
    (testProjection_tendsto :
      ∀ ψ : Test, Tendsto (fun n => testProjection n ψ) atTop (nhds ψ))
    (residual : (I →ᵇ H) → Test → ℝ)
    (residual_continuous :
      Continuous (fun p : (I →ᵇ H) × Test => residual p.1 p.2))
    (galerkin_equation :
      ∀ n ψ, residual (G.trajectory n) (testProjection n ψ) = 0)
    (ψ : Test) :
    residual G.strongLimit.limit ψ = 0 := by
  have hsubseq :
      Tendsto G.strongLimit.subseq.idx atTop atTop :=
    G.strongLimit.subseq.strictMono_idx.tendsto_atTop
  have htest :
      Tendsto
        (fun k => testProjection (G.strongLimit.subseq.idx k) ψ)
        atTop
        (nhds ψ) :=
    (testProjection_tendsto ψ).comp hsubseq
  have hpair :
      Tendsto
        (fun k =>
          (G.trajectory (G.strongLimit.subseq.idx k),
            testProjection (G.strongLimit.subseq.idx k) ψ))
        atTop
        (nhds (G.strongLimit.limit, ψ)) :=
    by
      simpa only [Function.comp_apply, nhds_prod_eq] using
        G.strongLimit_converges.prodMk htest
  have hresidual :
      Tendsto
        (fun k =>
          residual
            (G.trajectory (G.strongLimit.subseq.idx k))
            (testProjection (G.strongLimit.subseq.idx k) ψ))
        atTop
        (nhds (residual G.strongLimit.limit ψ)) :=
    residual_continuous.continuousAt.tendsto.comp hpair
  have hzero :
      Tendsto
        (fun k =>
          residual
            (G.trajectory (G.strongLimit.subseq.idx k))
            (testProjection (G.strongLimit.subseq.idx k) ψ))
        atTop
        (nhds 0) := by
    simpa only [galerkin_equation] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  exact tendsto_nhds_unique hresidual hzero

end StronglyCompactGalerkinFamily

/-- End-to-end output of compactness and limit passage.  All convergence and
the limiting tested equation are derived from a genuine projector sequence and
the finite Galerkin equations. -/
structure GalerkinLimitSolution
    {I H Test N : Type*}
    [TopologicalSpace I] [PseudoMetricSpace H]
    [TopologicalSpace Test] [TopologicalSpace N]
    (U : ℕ → I →ᵇ H)
    (testProjection : ℕ → Test → Test)
    (residual : (I →ᵇ H) → Test → ℝ)
    (nonlinear : (I →ᵇ H) → N) where
  compactness : StrongPathSubsequence U
  nonlinearConverges :
    Tendsto
      (fun k => nonlinear (U (compactness.subseq.idx k)))
      atTop
      (nhds (nonlinear compactness.limit))
  testedEquation : ∀ ψ : Test, residual compactness.limit ψ = 0

namespace StronglyCompactGalerkinFamily

/-- Headline compactness-and-limit theorem.  It constructs a strong limiting
path, proves nonlinear convergence, and proves the limiting tested equation
from the finite-dimensional Galerkin equations. -/
theorem exists_limitSolution
    {I V H : Type*}
    [PseudoMetricSpace I] [CompactSpace I]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (G : StronglyCompactGalerkinFamily I V H)
    {Test N : Type*} [TopologicalSpace Test] [TopologicalSpace N]
    (testProjection : ℕ → Test → Test)
    (testProjection_tendsto :
      ∀ ψ : Test, Tendsto (fun n => testProjection n ψ) atTop (nhds ψ))
    (residual : (I →ᵇ H) → Test → ℝ)
    (residual_continuous :
      Continuous (fun p : (I →ᵇ H) × Test => residual p.1 p.2))
    (galerkin_equation :
      ∀ n ψ, residual (G.trajectory n) (testProjection n ψ) = 0)
    (nonlinear : (I →ᵇ H) → N)
    (nonlinear_continuous : Continuous nonlinear) :
    Nonempty
      (GalerkinLimitSolution
        G.trajectory testProjection residual nonlinear) := by
  let C := G.strongLimit
  refine ⟨{
    compactness := C
    nonlinearConverges := ?_
    testedEquation := ?_
  }⟩
  · exact nonlinear_continuous.continuousAt.tendsto.comp C.converges
  · intro ψ
    exact G.tested_limit_equation
      testProjection testProjection_tendsto residual residual_continuous
      galerkin_equation ψ

end StronglyCompactGalerkinFamily
