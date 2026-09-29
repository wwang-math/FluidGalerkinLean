import PDEIdeas.OpenDomainSpectral
import PDEIdeas.BoxSpectralCompactness

/-!
# Finite spectral heads of the open-domain energy embedding

`PDEIdeas.OpenDomainSpectral` builds singular coordinates
`openDomainCompactSpectralRepresentation Ω` for the compact dense injection
`openDomainEnergyToState Ω : H¹₀σ(Ω) → L²σ(Ω)`.  This file records what those
coordinates give: the finite state heads selected by the exhaustion
approximate the embedding **in operator norm**, and the finite-head quantities
obey bounds that are uniform in the head index.

The mechanism is the abstract compact-embedding theorem
`compactEmbedding_projectorTail_tendsto` of `PDEIdeas.GalerkinL2Compactness`
-- a compact operator is approximated in operator norm by any uniformly
contractive, strongly convergent family of ambient projectors -- applied
exactly as `PDEIdeas.BoxSpectralCompactness` applies it to the box embedding.
No analytic input is added here: compactness, density and injectivity are read
off the representation, never assumed.

Nothing in this file assumes that Galerkin solutions exist.  Every statement
quantifies over arbitrary elements, or over an arbitrary energy-bounded family
of elements, of the energy space; the later time-compactness argument is what
supplies a family.

## Main results

* `compactEmbedding_exists_uniform_tail` — abstract `ε`-form of the
  compact-embedding theorem, proved once in a generic normed setting.
* `OpenDomainCompactSpectralRepresentation.openDomainEnergyToState_projectorTail_tendsto`
  — operator-norm convergence of the finite state projections.
* `OpenDomainCompactSpectralRepresentation.exists_uniform_tail`,
  `…exists_uniform_tail_of_bounded` — uniform tail smallness, on the whole
  space and on an energy-bounded family.
* `OpenDomainCompactSpectralRepresentation.norm_sub_le_head_add_tail`,
  `…exists_head_sub_bound` — the splitting consumed by a time-compactness
  argument: two embedded states differ by at most their finite-head difference
  plus a tail that is uniformly small.
* `OpenDomainCompactSpectralRepresentation.norm_stateProjection_le`,
  `…norm_stateProjection_sub_le`, `…abs_inner_stateBasis_le`,
  `…abs_inner_stateBasis_sub_le` — the uniform finite-head bounds and the
  modewise coefficient bounds.
-/

open Filter Function InnerProductSpace
open scoped Topology RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

/-! ### The abstract tail estimate

Stated for an arbitrary compact embedding of normed spaces, where the operator
norm of a difference of continuous linear maps is available directly. -/

section AbstractTail

variable {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Pointwise form of the projector-tail estimate. -/
theorem compactEmbedding_norm_sub_projector_le
    (embed : V →L[ℝ] H) (P : H →L[ℝ] H) (x : V) :
    ‖embed x - P (embed x)‖ ≤ ‖embed - P.comp embed‖ * ‖x‖ := by
  have h := (embed - P.comp embed).le_opNorm x
  simpa using h

/-- **`ε`-form of the abstract compact-embedding theorem.**  Beyond some head
index the projected embedding approximates the embedding uniformly on the unit
ball, hence with a relative error at most `ε` on the whole space. -/
theorem compactEmbedding_exists_uniform_tail
    (embed : V →L[ℝ] H) (hembed : IsCompactOperator embed)
    (projector : ℕ → H →L[ℝ] H)
    (hcontractive : ∀ n, ‖projector n‖ ≤ 1)
    (hstrong : ∀ x, Tendsto (fun n => projector n x) atTop (𝓝 x))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ x : V,
      ‖embed x - projector m (embed x)‖ ≤ ε * ‖x‖ := by
  have hlim := compactEmbedding_projectorTail_tendsto embed hembed projector
    hcontractive hstrong
  have hev : ∀ᶠ m in atTop, ‖embed - (projector m).comp embed‖ < ε :=
    hlim (Iio_mem_nhds hε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun m hm x => ?_⟩
  exact (compactEmbedding_norm_sub_projector_le embed (projector m) x).trans
    (mul_le_mul_of_nonneg_right (hN m hm).le (norm_nonneg x))

end AbstractTail

variable {n : ℕ} {Q : BoxIntegral.Box (Fin (n + 1))} {Ω : OpenDomainInBox Q}

namespace OpenDomainCompactSpectralRepresentation

/-! ### What the representation records -/

/-- Compactness of the open-domain embedding, recorded by its constructed
spectral representation. -/
theorem openDomainEnergyToState_isCompactOperator
    (S : OpenDomainCompactSpectralRepresentation Ω) :
    IsCompactOperator (openDomainEnergyToState Ω) :=
  S.embedding_compact

/-- Density of the open-domain embedding, recorded by its constructed spectral
representation. -/
theorem openDomainEnergyToState_denseRange
    (S : OpenDomainCompactSpectralRepresentation Ω) :
    DenseRange (openDomainEnergyToState Ω) :=
  S.embedding_denseRange

/-- Injectivity of the open-domain embedding, recorded by its constructed
spectral representation. -/
theorem openDomainEnergyToState_injective
    (S : OpenDomainCompactSpectralRepresentation Ω) :
    Injective (openDomainEnergyToState Ω) :=
  S.embedding_injective

/-! ### The finite head and its tail -/

/-- The operator left after projecting the open-domain embedding onto the
current finite state head. -/
def openDomainEnergyToStateProjectorTail
    (S : OpenDomainCompactSpectralRepresentation Ω) (m : ℕ) :
    OpenDomainH1ZeroSigma Ω →L[ℝ] OpenDomainL2Sigma Ω :=
  (ContinuousLinearMap.sub :
      Sub (OpenDomainH1ZeroSigma Ω →L[ℝ] OpenDomainL2Sigma Ω)).sub
    (openDomainEnergyToState Ω)
    ((S.stateProjection m).comp (openDomainEnergyToState Ω))

@[simp]
theorem openDomainEnergyToStateProjectorTail_apply
    (S : OpenDomainCompactSpectralRepresentation Ω) (m : ℕ)
    (u : OpenDomainH1ZeroSigma Ω) :
    S.openDomainEnergyToStateProjectorTail m u =
      openDomainEnergyToState Ω u -
        S.stateProjection m (openDomainEnergyToState Ω u) :=
  rfl

/-- The finite head and its tail recompose the embedded state. -/
theorem stateProjection_add_projectorTail
    (S : OpenDomainCompactSpectralRepresentation Ω) (m : ℕ)
    (u : OpenDomainH1ZeroSigma Ω) :
    S.stateProjection m (openDomainEnergyToState Ω u) +
        S.openDomainEnergyToStateProjectorTail m u =
      openDomainEnergyToState Ω u := by
  rw [openDomainEnergyToStateProjectorTail_apply]
  abel

/-- **The finite state projections approximate the open-domain energy-to-state
embedding in operator norm.** -/
theorem openDomainEnergyToState_projectorTail_tendsto
    (S : OpenDomainCompactSpectralRepresentation Ω) :
    Tendsto
      (fun m => ContinuousLinearMap.opNorm
        (S.openDomainEnergyToStateProjectorTail m))
      atTop (𝓝 0) := by
  have htail := compactEmbedding_projectorTail_tendsto
    (openDomainEnergyToState Ω) S.embedding_compact S.stateProjection
    (fun m =>
      GalerkinProjectorSequence.finitePartialProjection_norm_le
        S.stateBasis (S.exhaustion.head m))
    (fun x =>
      GalerkinProjectorSequence.finitePartialProjection_tendsto
        S.stateBasis S.exhaustion x)
  simpa only [openDomainEnergyToStateProjectorTail] using htail

/-- Pointwise form of the operator-norm approximation. -/
theorem norm_sub_stateProjection_le
    (S : OpenDomainCompactSpectralRepresentation Ω) (m : ℕ)
    (u : OpenDomainH1ZeroSigma Ω) :
    ‖openDomainEnergyToState Ω u -
        S.stateProjection m (openDomainEnergyToState Ω u)‖ ≤
      ContinuousLinearMap.opNorm (S.openDomainEnergyToStateProjectorTail m) *
        ‖u‖ :=
  compactEmbedding_norm_sub_projector_le (openDomainEnergyToState Ω)
    (S.stateProjection m) u

/-! ### Uniform finite-head bounds -/

/-- The finite head is a contraction from the energy space, uniformly in the
head index. -/
theorem norm_stateProjection_le
    (S : OpenDomainCompactSpectralRepresentation Ω) (m : ℕ)
    (u : OpenDomainH1ZeroSigma Ω) :
    ‖S.stateProjection m (openDomainEnergyToState Ω u)‖ ≤ ‖u‖ := by
  have h := S.norm_testProjection_le m u
  rwa [show ‖S.testProjection m u‖ =
    ‖S.stateProjection m (openDomainEnergyToState Ω u)‖ from rfl] at h

/-- Finite heads are `1`-Lipschitz in the energy norm, uniformly in the head
index: the equicontinuity input for the head of a time-dependent family. -/
theorem norm_stateProjection_sub_le
    (S : OpenDomainCompactSpectralRepresentation Ω) (m : ℕ)
    (u v : OpenDomainH1ZeroSigma Ω) :
    ‖S.stateProjection m (openDomainEnergyToState Ω u) -
        S.stateProjection m (openDomainEnergyToState Ω v)‖ ≤ ‖u - v‖ := by
  have hlin :
      S.stateProjection m (openDomainEnergyToState Ω (u - v)) =
        S.stateProjection m (openDomainEnergyToState Ω u) -
          S.stateProjection m (openDomainEnergyToState Ω v) := by
    rw [map_sub, map_sub]
  rw [← hlin]
  exact S.norm_stateProjection_le m (u - v)

/-- The energy head is a contraction, uniformly in the head index. -/
theorem norm_energyProjection_le
    (S : OpenDomainCompactSpectralRepresentation Ω) (m : ℕ)
    (u : OpenDomainH1ZeroSigma Ω) :
    ‖S.energyProjection m u‖ ≤ ‖u‖ := by
  have h := S.norm_energySynthesis_testProjection_le m u
  rwa [S.energySynthesis_testProjection_eq_energyProjection m u] at h

/-- The finite state head of an embedded state is the embedding of the
corresponding energy head, so the head never leaves the range of the
embedding. -/
theorem stateProjection_openDomainEnergyToState
    (S : OpenDomainCompactSpectralRepresentation Ω) (m : ℕ)
    (u : OpenDomainH1ZeroSigma Ω) :
    S.stateProjection m (openDomainEnergyToState Ω u) =
      openDomainEnergyToState Ω (S.energyProjection m u) :=
  S.stateProjection_embedding m u

/-- The finite state head is finite dimensional, as the Arzelà--Ascoli step of
a time-compactness argument requires. -/
theorem stateHead_finiteDimensional
    (S : OpenDomainCompactSpectralRepresentation Ω) (m : ℕ) :
    FiniteDimensional ℝ (S.stateSpace m) :=
  S.stateSpace_finiteDimensional m

/-- The finite state head is complete. -/
theorem stateHead_completeSpace
    (S : OpenDomainCompactSpectralRepresentation Ω) (m : ℕ) :
    CompleteSpace (S.stateSpace m) :=
  S.stateSpace_completeSpace m

/-! ### Modewise coefficient bounds -/

/-- Each head coordinate of an embedded state is bounded by its energy norm. -/
theorem abs_inner_stateBasis_le
    (S : OpenDomainCompactSpectralRepresentation Ω) (i : S.Index)
    (u : OpenDomainH1ZeroSigma Ω) :
    |(⟪openDomainEnergyToState Ω u, S.stateBasis i⟫_ℝ)| ≤ ‖u‖ := by
  calc
    |(⟪openDomainEnergyToState Ω u, S.stateBasis i⟫_ℝ)| ≤
        ‖openDomainEnergyToState Ω u‖ * ‖S.stateBasis i‖ :=
      abs_real_inner_le_norm _ _
    _ = ‖openDomainEnergyToState Ω u‖ := by
      rw [S.stateBasis.orthonormal.norm_eq_one i, mul_one]
    _ ≤ ‖u‖ := S.norm_embedding_le u

/-- Each head coordinate is `1`-Lipschitz in the energy norm: the
equicontinuity input for the finitely many coordinates of a fixed head. -/
theorem abs_inner_stateBasis_sub_le
    (S : OpenDomainCompactSpectralRepresentation Ω) (i : S.Index)
    (u v : OpenDomainH1ZeroSigma Ω) :
    |(⟪openDomainEnergyToState Ω u, S.stateBasis i⟫_ℝ -
        ⟪openDomainEnergyToState Ω v, S.stateBasis i⟫_ℝ)| ≤ ‖u - v‖ := by
  have hsub :
      ⟪openDomainEnergyToState Ω (u - v), S.stateBasis i⟫_ℝ =
        ⟪openDomainEnergyToState Ω u, S.stateBasis i⟫_ℝ -
          ⟪openDomainEnergyToState Ω v, S.stateBasis i⟫_ℝ := by
    rw [map_sub]
    exact inner_sub_left _ _ _
  rw [← hsub]
  exact S.abs_inner_stateBasis_le i (u - v)

/-! ### Uniform tail smallness -/

/-- **Uniform tail smallness.**  Beyond some head index the finite head
reproduces every embedded state up to a relative error `ε`. -/
theorem exists_uniform_tail
    (S : OpenDomainCompactSpectralRepresentation Ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ u : OpenDomainH1ZeroSigma Ω,
      ‖openDomainEnergyToState Ω u -
        S.stateProjection m (openDomainEnergyToState Ω u)‖ ≤ ε * ‖u‖ :=
  compactEmbedding_exists_uniform_tail (openDomainEnergyToState Ω)
    S.embedding_compact S.stateProjection
    (fun m =>
      GalerkinProjectorSequence.finitePartialProjection_norm_le
        S.stateBasis (S.exhaustion.head m))
    (fun x =>
      GalerkinProjectorSequence.finitePartialProjection_tendsto
        S.stateBasis S.exhaustion x) hε

/-- **Uniform tail smallness on an energy-bounded family.**  The family is
arbitrary: no Galerkin solution is assumed to exist. -/
theorem exists_uniform_tail_of_bounded
    (S : OpenDomainCompactSpectralRepresentation Ω) {ι : Type*}
    (u : ι → OpenDomainH1ZeroSigma Ω) (R : ℝ) (hR0 : 0 ≤ R)
    (hR : ∀ a, ‖u a‖ ≤ R) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ a : ι,
      ‖openDomainEnergyToState Ω (u a) -
        S.stateProjection m (openDomainEnergyToState Ω (u a))‖ ≤ ε := by
  have hpos : (0 : ℝ) < R + 1 := by linarith
  have hne : (R + 1) ≠ 0 := ne_of_gt hpos
  have hc : (0 : ℝ) < ε / (R + 1) := div_pos hε hpos
  obtain ⟨N, hN⟩ := S.exists_uniform_tail hc
  refine ⟨N, fun m hm a => ?_⟩
  have hid : ε / (R + 1) * (R + 1) = ε := by field_simp
  calc
    ‖openDomainEnergyToState Ω (u a) -
        S.stateProjection m (openDomainEnergyToState Ω (u a))‖ ≤
        ε / (R + 1) * ‖u a‖ := hN m hm (u a)
    _ ≤ ε / (R + 1) * R :=
      mul_le_mul_of_nonneg_left (hR a) hc.le
    _ ≤ ε := by nlinarith [hc.le, hid]

/-! ### The splitting used by a time-compactness argument -/

/-- Two embedded states differ by at most the difference of their finite heads
plus a tail controlled by the tail operator norm. -/
theorem norm_sub_le_head_add_tail
    (S : OpenDomainCompactSpectralRepresentation Ω) (m : ℕ)
    (u v : OpenDomainH1ZeroSigma Ω) :
    ‖openDomainEnergyToState Ω u - openDomainEnergyToState Ω v‖ ≤
      ‖S.stateProjection m (openDomainEnergyToState Ω u) -
          S.stateProjection m (openDomainEnergyToState Ω v)‖ +
        (ContinuousLinearMap.opNorm
            (S.openDomainEnergyToStateProjectorTail m) * ‖u‖ +
          ContinuousLinearMap.opNorm
            (S.openDomainEnergyToStateProjectorTail m) * ‖v‖) := by
  have hsplit :
      openDomainEnergyToState Ω u - openDomainEnergyToState Ω v =
        (S.stateProjection m (openDomainEnergyToState Ω u) -
            S.stateProjection m (openDomainEnergyToState Ω v)) +
          ((openDomainEnergyToState Ω u -
              S.stateProjection m (openDomainEnergyToState Ω u)) -
            (openDomainEnergyToState Ω v -
              S.stateProjection m (openDomainEnergyToState Ω v))) := by
    abel
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  gcongr
  refine (norm_sub_le _ _).trans ?_
  exact add_le_add (S.norm_sub_stateProjection_le m u)
    (S.norm_sub_stateProjection_le m v)

/-- **The estimate a time-compactness argument consumes.**  For every `ε` there
is a head index beyond which any two embedded states differ by at most their
finite-head difference plus `ε` times the sum of their energy norms.  The
finite head is finite dimensional, so its difference is handled by a
finite-dimensional compactness argument, while the remainder is uniformly
small on energy-bounded families. -/
theorem exists_head_sub_bound
    (S : OpenDomainCompactSpectralRepresentation Ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ u v : OpenDomainH1ZeroSigma Ω,
      ‖openDomainEnergyToState Ω u - openDomainEnergyToState Ω v‖ ≤
        ‖S.stateProjection m (openDomainEnergyToState Ω u) -
            S.stateProjection m (openDomainEnergyToState Ω v)‖ +
          ε * (‖u‖ + ‖v‖) := by
  obtain ⟨N, hN⟩ := S.exists_uniform_tail hε
  refine ⟨N, fun m hm u v => ?_⟩
  have hsplit :
      openDomainEnergyToState Ω u - openDomainEnergyToState Ω v =
        (S.stateProjection m (openDomainEnergyToState Ω u) -
            S.stateProjection m (openDomainEnergyToState Ω v)) +
          ((openDomainEnergyToState Ω u -
              S.stateProjection m (openDomainEnergyToState Ω u)) -
            (openDomainEnergyToState Ω v -
              S.stateProjection m (openDomainEnergyToState Ω v))) := by
    abel
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  gcongr
  refine (norm_sub_le _ _).trans ?_
  have hu := hN m hm u
  have hv := hN m hm v
  have hexp : ε * (‖u‖ + ‖v‖) = ε * ‖u‖ + ε * ‖v‖ := by ring
  rw [hexp]
  exact add_le_add hu hv

end OpenDomainCompactSpectralRepresentation

end
