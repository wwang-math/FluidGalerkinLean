import Mathlib.Analysis.Normed.Operator.Compact
import PDEIdeas.CompactGelfandTriple

/-!
# Compact embeddings restricted to closed subspaces

A compact continuous linear map `J : V → H` which carries a subspace `V'` of
`V` into a closed subspace `H'` of `H` induces a compact continuous linear map
`V' → H'`.  This file proves that transfer once and abstractly, together with
the matching injectivity, dense-range, and norm transfers.

The intended use is inheritance: a Rellich-type compactness theorem already
proved for one domain, for instance the Fourier proof on a rectangle, is
transported to a subdomain realized as a pair of closed subspaces, without
repeating the original proof.

## Main statements

The commuting square is recorded by `IsSubspaceRestriction J J'`, which says
that `J' : V' →L[k] H'` agrees with `J` after the two inclusions.  The canonical
such `J'` is `ContinuousLinearMap.subspaceRestrict`, and
`isSubspaceRestriction_subspaceRestrict` proves the square for it by `rfl`.
Stating the transfer for an arbitrary `J'` satisfying the square is what allows
an already constructed restriction to be used unchanged.

* `IsSubspaceRestriction.isCompactOperator`: compactness transfers as soon as
  `H'` is closed in `H`.  Closedness of `V'` is not needed.  The converse
  direction is `IsSubspaceRestriction.isCompactOperator_comp_subtypeL`.
* `IsSubspaceRestriction.injective`: injectivity is inherited from `J`, and
  `IsSubspaceRestriction.injective_iff` gives the sharp criterion
  `Disjoint V' (LinearMap.ker J)`.
* `IsSubspaceRestriction.denseRange_iff`: dense range of `J'` is equivalent to
  `H' ⊆ closure (J '' V')`.  This is the one property that is not inherited
  from `J` and has to be supplied; `denseRange_of_le_topologicalClosure` and
  `denseRange_of_approx` are the two convenient sufficient forms.
* `IsSubspaceRestriction.norm_apply` and `IsSubspaceRestriction.norm_apply_le`:
  the restriction has the same pointwise norms as `J`, so contractivity is
  inherited.
* `CompactGelfandTriple.subspaceRestrict`: the packaged consequence.  A compact
  Gelfand triple `V → H` restricts to a compact Gelfand triple `V' → H'` given
  a closed `H'`, the mapping hypothesis, and the density hypothesis.

## Hypotheses that are genuinely used

* `IsClosed (H' : Set H)` is what makes compactness transfer: the inclusion
  `H' → H` is then a closed embedding, so preimages of compact sets stay
  compact.  It is used as a sufficient hypothesis and is not claimed to be
  necessary.  `IsSubspaceRestriction.isCompactOperator_of_complete` accepts
  completeness of `H'` in its place.
* `(H' : Set H) ⊆ closure (J '' V')` is what makes the range dense.  It does
  not follow from `DenseRange J`.
* Nothing here needs `V'` to be closed, nor completeness of `V`, `H`, or the
  subspaces.  Closedness of `V'` matters only downstream, where one wants `V'`
  to be a Banach or Hilbert space in its own right.
* The reverse direction, `IsSubspaceRestriction.isCompactOperator_comp_subtypeL`,
  needs no hypothesis on `H'` at all.
-/

open Function Set Topology

noncomputable section

section ClosedEmbeddingTransfer

variable {V H K : Type*}

/-- Compactness descends through a closed embedding placed after the operator.
This is the mechanism behind the restriction statements below: the inclusion of
a closed subspace is a closed embedding. -/
theorem isCompactOperator_of_isClosedEmbedding_comp
    [Zero V] [TopologicalSpace V] [TopologicalSpace H] [TopologicalSpace K]
    {R : H → K} (hR : IsClosedEmbedding R) {T : V → H}
    (hcompact : IsCompactOperator (R ∘ T)) :
    IsCompactOperator T := by
  obtain ⟨C, hC, hpre⟩ := hcompact
  refine ⟨R ⁻¹' C, hR.isCompact_preimage hC, ?_⟩
  simpa only [Set.preimage_comp] using hpre

/-- Compactness descends through an isometry on a complete target. -/
theorem isCompactOperator_of_isometry_comp
    [Zero V] [TopologicalSpace V] [MetricSpace H] [CompleteSpace H]
    [MetricSpace K]
    {R : H → K} (hR : Isometry R) {T : V → H}
    (hcompact : IsCompactOperator (R ∘ T)) :
    IsCompactOperator T :=
  isCompactOperator_of_isClosedEmbedding_comp hR.isClosedEmbedding hcompact

end ClosedEmbeddingTransfer

section SubspaceRestriction

variable {k : Type*} [Ring k]
variable {V H : Type*}
variable [AddCommGroup V] [TopologicalSpace V] [Module k V]
variable [AddCommGroup H] [TopologicalSpace H] [Module k H]
variable {V' : Submodule k V} {H' : Submodule k H}
variable {J : V →L[k] H} {J' : V' →L[k] H'}

/-- `J'` realizes `J` on the subspaces `V'` and `H'`: the square formed by `J`,
`J'`, and the two inclusions commutes.  A concretely constructed restriction
satisfies this by `rfl`, which is what makes the transfer lemmas below usable
without rewriting an existing construction. -/
structure IsSubspaceRestriction (J : V →L[k] H) (J' : V' →L[k] H') : Prop where
  /-- The restriction agrees with the original map after the two inclusions. -/
  coe_apply : ∀ v : V', (J' v : H) = J (v : V)

/-- The continuous linear map induced by `J` on the subspaces `V'` and `H'`,
under the hypothesis that `J` maps `V'` into `H'`. -/
def ContinuousLinearMap.subspaceRestrict
    (J : V →L[k] H) (V' : Submodule k V) (H' : Submodule k H)
    (hmaps : ∀ v ∈ V', J v ∈ H') :
    V' →L[k] H' :=
  (J.comp V'.subtypeL).codRestrict H' (SetLike.forall.2 hmaps)

@[simp]
theorem ContinuousLinearMap.coe_subspaceRestrict_apply
    (J : V →L[k] H) (V' : Submodule k V) (H' : Submodule k H)
    (hmaps : ∀ v ∈ V', J v ∈ H') (v : V') :
    ((J.subspaceRestrict V' H' hmaps v : H') : H) = J (v : V) :=
  rfl

/-- The canonical restriction is a subspace restriction. -/
theorem isSubspaceRestriction_subspaceRestrict
    (J : V →L[k] H) (V' : Submodule k V) (H' : Submodule k H)
    (hmaps : ∀ v ∈ V', J v ∈ H') :
    IsSubspaceRestriction J (J.subspaceRestrict V' H' hmaps) :=
  ⟨fun _ => rfl⟩

namespace IsSubspaceRestriction

/-- A subspace restriction forces `J` to map `V'` into `H'`. -/
theorem mapsTo (h : IsSubspaceRestriction J J') :
    ∀ v ∈ V', J v ∈ H' := by
  intro v hv
  have hmem := (J' ⟨v, hv⟩).2
  rwa [h.coe_apply ⟨v, hv⟩] at hmem

/-- A subspace restriction is the canonical restriction. -/
theorem eq_subspaceRestrict (h : IsSubspaceRestriction J J') :
    J' = J.subspaceRestrict V' H' h.mapsTo :=
  ContinuousLinearMap.ext fun v => Subtype.ext (h.coe_apply v)

/-- **Compactness transfer.**  If `J` is a compact operator, `H'` is closed in
`H`, and `J'` restricts `J` to the subspaces `V'` and `H'`, then `J'` is a
compact operator.  No hypothesis on `V'` beyond being a submodule is used. -/
theorem isCompactOperator
    (h : IsSubspaceRestriction J J')
    (hJ : IsCompactOperator J)
    (hH' : IsClosed (H' : Set H)) :
    IsCompactOperator J' := by
  rw [h.eq_subspaceRestrict]
  exact (hJ.comp_clm V'.subtypeL).codRestrict (SetLike.forall.2 h.mapsTo) hH'

/-- Compactness of the restriction gives back compactness of `J` on `V'`.  This
direction needs no hypothesis on `H'`. -/
theorem isCompactOperator_comp_subtypeL
    (h : IsSubspaceRestriction J J')
    (hJ' : IsCompactOperator J') :
    IsCompactOperator ((J : V → H) ∘ (V'.subtypeL : V' → V)) := by
  have hcomp := hJ'.clm_comp H'.subtypeL
  have hfun :
      ((H'.subtypeL : H' → H) ∘ (J' : V' → H')) =
        ((J : V → H) ∘ (V'.subtypeL : V' → V)) :=
    funext h.coe_apply
  rwa [hfun] at hcomp

/-- **Injectivity transfer.**  An injective `J` restricts to an injective map,
with no further hypothesis. -/
theorem injective (h : IsSubspaceRestriction J J') (hJ : Function.Injective J) :
    Function.Injective J' := by
  intro a b hab
  refine Subtype.ext (hJ ?_)
  rw [← h.coe_apply a, ← h.coe_apply b, hab]

/-- **Injectivity transfer, sharp form.**  The restriction is injective exactly
when `V'` meets the kernel of `J` trivially. -/
theorem injective_iff (h : IsSubspaceRestriction J J') :
    Function.Injective J' ↔ Disjoint V' (LinearMap.ker (J : V →ₗ[k] H)) := by
  constructor
  · intro hinj
    rw [Submodule.disjoint_def]
    intro x hx hker
    have hJx : J x = 0 := LinearMap.mem_ker.mp hker
    have hzero : J' ⟨x, hx⟩ = 0 := by
      refine Subtype.ext ?_
      rw [h.coe_apply ⟨x, hx⟩, ZeroMemClass.coe_zero]
      exact hJx
    have hv0 : (⟨x, hx⟩ : V') = 0 := hinj (by rw [hzero, map_zero])
    have hcoe := congrArg Subtype.val hv0
    simpa only [ZeroMemClass.coe_zero] using hcoe
  · intro hdisj a b hab
    have hJab : J (a : V) = J (b : V) := by
      rw [← h.coe_apply a, ← h.coe_apply b, hab]
    have hmem : (a : V) - (b : V) ∈ V' ⊓ LinearMap.ker (J : V →ₗ[k] H) := by
      refine Submodule.mem_inf.mpr ⟨V'.sub_mem a.2 b.2, ?_⟩
      refine LinearMap.mem_ker.mpr ?_
      show J ((a : V) - (b : V)) = 0
      rw [map_sub, hJab, sub_self]
    have hbot := hdisj.le_bot hmem
    rw [Submodule.mem_bot, sub_eq_zero] at hbot
    exact Subtype.ext hbot

/-- **Dense-range transfer, sharp form.**  The restriction has dense range
exactly when every element of `H'` is a limit of images of elements of `V'`.
Dense range of `J` itself is neither sufficient nor necessary. -/
theorem denseRange_iff (h : IsSubspaceRestriction J J') :
    DenseRange J' ↔ (H' : Set H) ⊆ closure ((J : V → H) '' (V' : Set V)) := by
  have himg :
      (Subtype.val : H' → H) '' Set.range (J' : V' → H') =
        (J : V → H) '' (V' : Set V) := by
    ext y
    constructor
    · rintro ⟨z, ⟨v, rfl⟩, rfl⟩
      exact ⟨(v : V), v.2, (h.coe_apply v).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨J' ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, h.coe_apply ⟨x, hx⟩⟩
  constructor
  · intro hdense y hy
    have hmem : (⟨y, hy⟩ : H') ∈ closure (Set.range (J' : V' → H')) :=
      hdense ⟨y, hy⟩
    rw [closure_subtype, himg] at hmem
    exact hmem
  · intro hsub y
    have hmem : (y : H) ∈ closure ((J : V → H) '' (V' : Set V)) := hsub y.2
    rw [closure_subtype, himg]
    exact hmem

/-- **Dense-range transfer, sufficient form.** -/
theorem denseRange (h : IsSubspaceRestriction J J')
    (hsub : (H' : Set H) ⊆ closure ((J : V → H) '' (V' : Set V))) :
    DenseRange J' :=
  h.denseRange_iff.2 hsub

/-- **Dense-range transfer, submodule form.**  It suffices that `H'` lies in the
topological closure of the image submodule `V'.map J`. -/
theorem denseRange_of_le_topologicalClosure
    [ContinuousAdd H] [ContinuousConstSMul k H]
    (h : IsSubspaceRestriction J J')
    (hle : H' ≤ (V'.map (J : V →ₗ[k] H)).topologicalClosure) :
    DenseRange J' := by
  refine h.denseRange fun y hy => ?_
  have hmem : y ∈ (V'.map (J : V →ₗ[k] H)).topologicalClosure :=
    hle (SetLike.mem_coe.mp hy)
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Submodule.map_coe,
    ContinuousLinearMap.coe_coe] at hmem
  exact hmem

end IsSubspaceRestriction

end SubspaceRestriction

section NormedSubspaceRestriction

variable {k : Type*} [NontriviallyNormedField k]
variable {V H : Type*}
variable [SeminormedAddCommGroup V] [NormedSpace k V]
variable [SeminormedAddCommGroup H] [NormedSpace k H]
variable {V' : Submodule k V} {H' : Submodule k H}
variable {J : V →L[k] H} {J' : V' →L[k] H'}

namespace IsSubspaceRestriction

/-- **Compactness transfer, completeness form.**  Completeness of `H'` may be
used in place of closedness. -/
theorem isCompactOperator_of_complete
    {H : Type*} [NormedAddCommGroup H] [NormedSpace k H]
    {H' : Submodule k H} {J : V →L[k] H} {J' : V' →L[k] H'}
    (h : IsSubspaceRestriction J J')
    (hJ : IsCompactOperator J)
    [hcomplete : CompleteSpace H'] :
    IsCompactOperator J' :=
  h.isCompactOperator hJ
    (completeSpace_coe_iff_isComplete.mp hcomplete).isClosed

/-- A subspace restriction has the same pointwise norms as the original map. -/
theorem norm_apply (h : IsSubspaceRestriction J J') (v : V') :
    ‖J' v‖ = ‖J (v : V)‖ := by
  rw [← Submodule.norm_coe (J' v), h.coe_apply v]

/-- Contractivity is inherited by a subspace restriction. -/
theorem norm_apply_le (h : IsSubspaceRestriction J J')
    (hJ : ∀ v : V, ‖J v‖ ≤ ‖v‖) (v : V') :
    ‖J' v‖ ≤ ‖v‖ := by
  rw [h.norm_apply v, ← Submodule.norm_coe v]
  exact hJ _

/-- A pointwise operator bound is inherited by a subspace restriction. -/
theorem norm_apply_le_mul (h : IsSubspaceRestriction J J')
    {C : ℝ} (hJ : ∀ v : V, ‖J v‖ ≤ C * ‖v‖) (v : V') :
    ‖J' v‖ ≤ C * ‖v‖ := by
  rw [h.norm_apply v, ← Submodule.norm_coe v]
  exact hJ _

/-- **Dense-range transfer, metric form.**  It suffices that every element of
`H'` is approximated in norm by images of elements of `V'`. -/
theorem denseRange_of_approx (h : IsSubspaceRestriction J J')
    (happrox : ∀ y ∈ H', ∀ ε : ℝ, 0 < ε → ∃ v ∈ V', ‖J v - y‖ < ε) :
    DenseRange J' := by
  refine h.denseRange fun y hy => ?_
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨v, hv, hlt⟩ := happrox y (SetLike.mem_coe.mp hy) ε hε
  refine ⟨J v, ⟨v, hv, rfl⟩, ?_⟩
  rw [dist_comm, dist_eq_norm]
  exact hlt

end IsSubspaceRestriction

end NormedSubspaceRestriction

section GelfandRestriction

variable {V H : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **Inheritance of a compact Gelfand triple by closed subspaces.**  Given a
compact Gelfand triple `V → H`, a subspace `V'` of `V`, and a closed subspace
`H'` of `H` such that the embedding maps `V'` into `H'` with image dense in
`H'`, the induced map `V' → H'` is again a compact Gelfand triple.

Compactness, injectivity, and contractivity are inherited; only the density
hypothesis `hdense` has to be supplied, since density of `V` in `H` says
nothing about density of the image of `V'` in `H'`. -/
def CompactGelfandTriple.subspaceRestrict
    (G : CompactGelfandTriple V H)
    (V' : Submodule ℝ V) (H' : Submodule ℝ H)
    (hH' : IsClosed (H' : Set H))
    (hmaps : ∀ v ∈ V', G.embedding v ∈ H')
    (hdense :
      (H' : Set H) ⊆ closure ((G.embedding : V → H) '' (V' : Set V))) :
    CompactGelfandTriple V' H' where
  embedding := G.embedding.subspaceRestrict V' H' hmaps
  embedding_injective :=
    (isSubspaceRestriction_subspaceRestrict G.embedding V' H' hmaps).injective
      G.embedding_injective
  embedding_denseRange :=
    (isSubspaceRestriction_subspaceRestrict G.embedding V' H' hmaps).denseRange
      hdense
  embedding_compact :=
    (isSubspaceRestriction_subspaceRestrict G.embedding V' H'
      hmaps).isCompactOperator G.embedding_compact hH'
  embedding_contractive :=
    (isSubspaceRestriction_subspaceRestrict G.embedding V' H'
      hmaps).norm_apply_le G.embedding_contractive

@[simp]
theorem CompactGelfandTriple.coe_subspaceRestrict_embedding_apply
    (G : CompactGelfandTriple V H)
    (V' : Submodule ℝ V) (H' : Submodule ℝ H)
    (hH' : IsClosed (H' : Set H))
    (hmaps : ∀ v ∈ V', G.embedding v ∈ H')
    (hdense :
      (H' : Set H) ⊆ closure ((G.embedding : V → H) '' (V' : Set V)))
    (v : V') :
    (((G.subspaceRestrict V' H' hH' hmaps hdense).embedding v : H') : H) =
      G.embedding (v : V) :=
  rfl

end GelfandRestriction

end
