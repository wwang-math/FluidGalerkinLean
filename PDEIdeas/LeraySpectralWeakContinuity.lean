import PDEIdeas.LeraySpectralWeakCompactness
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Weakly continuous representatives of spectral limits

Uniform convergence of every finite spectral projection, together with the
uniform pivot-space bound, reconstructs a weakly continuous pointwise path.
Strong space-time convergence identifies this path almost everywhere with the
previously extracted `L2` state limit.
-/

open BoundedContinuousFunction Filter Function InnerProductSpace MeasureTheory
open scoped ENNReal

noncomputable section

section LeraySpectral

variable {I V H : Type*}
    [PseudoMetricSpace I] [CompactSpace I]
    [MeasurableSpace I] [BorelSpace I] [SecondCountableTopology I]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {μ : Measure I} [IsFiniteMeasure μ]

namespace LeraySpectralCompactFamily

variable {G : LeraySpectralCompactFamily
  (I := I) (V := V) (H := H) (μ := μ)}

/-- A pointwise pivot-space representative of the strong state limit, with
weak continuity expressed through all Hilbert-space pairings. -/
structure WeaklyContinuousStateRepresentative
    (S : G.StrongWeakPathSubsequence) where
  path : I → H
  norm_le : ∀ t, ‖path t‖ ≤ G.stateRadius
  inner_continuous : ∀ y : H, Continuous (fun t => ⟪path t, y⟫_ℝ)
  pointwise_weak_subsequence : ∀ t,
    ∃ rho : ℕ → ℕ, StrictMono rho ∧
      ∀ y : H,
        Tendsto
          (fun j =>
            ⟪G.statePath (S.subseq.idx (rho j)) t, y⟫_ℝ)
          atTop (nhds ⟪path t, y⟫_ℝ)
  path_ae_eq_stateLimit : path =ᵐ[μ] (S.stateLimit : I → H)
  eq_of_statePath_tendsto : ∀ (rho : ℕ → ℕ), Tendsto rho atTop atTop →
    ∀ (t : I) (z : H),
      Tendsto (fun j => G.statePath (S.subseq.idx (rho j)) t)
        atTop (nhds z) →
      path t = z

namespace StrongWeakPathSubsequence

variable (S : G.StrongWeakPathSubsequence)

/-- A pointwise weak cluster extraction of the synchronized state sequence. -/
noncomputable def pointwiseWeakSubsequence (t : I) :
    WeakHilbertSubsequence
      (fun k => G.statePath (S.subseq.idx k) t) :=
  Classical.choice <| exists_weakHilbertSubsequence
    (fun k => G.statePath (S.subseq.idx k) t) G.stateRadius
    (fun k => by
      simpa only [G.statePath_apply] using
        G.state_bound (S.subseq.idx k) t)

/-- Pointwise pivot-space path selected from the weak cluster limits. -/
noncomputable def weakStatePath (t : I) : H :=
  (S.pointwiseWeakSubsequence t).limit

omit [CompactSpace I] [CompleteSpace V] in
/-- At every time, a strict further extraction converges weakly to the
reconstructed pivot-space value. -/
theorem exists_pointwiseWeakSubsequence (t : I) :
    ∃ rho : ℕ → ℕ, StrictMono rho ∧
      ∀ y : H,
        Tendsto
          (fun j =>
            ⟪G.statePath (S.subseq.idx (rho j)) t, y⟫_ℝ)
          atTop (nhds ⟪S.weakStatePath t, y⟫_ℝ) := by
  let W := S.pointwiseWeakSubsequence t
  exact ⟨W.subseq.idx, W.subseq.strictMono_idx, W.inner_tendsto⟩

omit [CompactSpace I] [CompleteSpace V] in
/-- The pointwise weak path retains the uniform pivot-space estimate. -/
theorem weakStatePath_norm_le (t : I) :
    ‖S.weakStatePath t‖ ≤ G.stateRadius := by
  exact (S.pointwiseWeakSubsequence t).limit_norm_le G.stateRadius
    (fun k => by
      simpa only [G.statePath_apply] using
        G.state_bound (S.subseq.idx k) t)

omit [CompactSpace I] [CompleteSpace V] in
/-- Every finite projected path limit records the corresponding coordinates
of the pointwise weak cluster vector. -/
theorem projectedLimit_inner_eq_weakStatePath_projection
    (hself : ∀ m x y,
      ⟪G.projector m x, y⟫_ℝ = ⟪x, G.projector m y⟫_ℝ)
    (m : ℕ) (t : I) (y : H) :
    ⟪S.projectedLimit m t, y⟫_ℝ =
      ⟪S.weakStatePath t, G.projector m y⟫_ℝ := by
  let W := S.pointwiseWeakSubsequence t
  have hpoint : Tendsto
      (fun k => G.projectedPath m (S.subseq.idx k) t)
      atTop (nhds (S.projectedLimit m t)) := by
    simpa only [Function.comp_apply,
      BoundedContinuousFunction.evalCLM_apply] using
      ((BoundedContinuousFunction.evalCLM ℝ t).continuous.tendsto
        (S.projectedLimit m)).comp (S.projected_uniform m)
  have hinner : Tendsto
      (fun k => ⟪G.projectedPath m (S.subseq.idx k) t, y⟫_ℝ)
      atTop (nhds ⟪S.projectedLimit m t, y⟫_ℝ) :=
    ((innerSLFlip ℝ y).continuous.tendsto (S.projectedLimit m t)).comp hpoint
  have hinnerSub := hinner.comp W.subseq.strictMono_idx.tendsto_atTop
  have hprojected : Tendsto
      (fun j =>
        ⟪G.statePath (S.subseq.idx (W.subseq.idx j)) t,
          G.projector m y⟫_ℝ)
      atTop (nhds ⟪S.projectedLimit m t, y⟫_ℝ) := by
    simpa only [G.projectedPath_apply, hself m] using hinnerSub
  exact tendsto_nhds_unique hprojected
    (W.inner_tendsto (G.projector m y))

omit [CompactSpace I] [CompleteSpace V] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] in
/-- A pointwise strong limit of any further extraction determines the stored
finite-mode path limit. -/
theorem projectedLimit_eq_projection_of_statePath_tendsto
    (rho : ℕ → ℕ) (hrho : Tendsto rho atTop atTop)
    (t : I) (z : H)
    (ht : Tendsto
      (fun j => G.statePath (S.subseq.idx (rho j)) t)
        atTop (nhds z)) (m : ℕ) :
    S.projectedLimit m t = G.projector m z := by
  have hlimit : Tendsto
      (fun j => G.projectedPath m (S.subseq.idx (rho j)) t)
      atTop (nhds (S.projectedLimit m t)) := by
    have hpaths := (S.projected_uniform m).comp hrho
    simpa only [Function.comp_apply,
      BoundedContinuousFunction.evalCLM_apply] using
      ((BoundedContinuousFunction.evalCLM ℝ t).continuous.tendsto
        (S.projectedLimit m)).comp hpaths
  have hprojection : Tendsto
      (fun j => G.projectedPath m (S.subseq.idx (rho j)) t)
      atTop (nhds (G.projector m z)) := by
    simpa only [G.projectedPath_apply] using
      ((G.projector m).continuous.tendsto z).comp ht
  exact tendsto_nhds_unique hlimit hprojection

omit [CompactSpace I] [CompleteSpace V] in
/-- Any pointwise strong limit of a further extraction equals the reconstructed
weak path at that time. -/
theorem weakStatePath_eq_of_statePath_tendsto
    (hself : ∀ m x y,
      ⟪G.projector m x, y⟫_ℝ = ⟪x, G.projector m y⟫_ℝ)
    (rho : ℕ → ℕ) (hrho : Tendsto rho atTop atTop)
    (t : I) (z : H)
    (ht : Tendsto
      (fun j => G.statePath (S.subseq.idx (rho j)) t)
      atTop (nhds z)) :
    S.weakStatePath t = z := by
  apply ext_inner_right ℝ
  intro y
  have hcoord (m : ℕ) :
      ⟪S.weakStatePath t, G.projector m y⟫_ℝ =
      ⟪z, G.projector m y⟫_ℝ := by
    calc
      ⟪S.weakStatePath t, G.projector m y⟫_ℝ =
          ⟪S.projectedLimit m t, y⟫_ℝ :=
        (S.projectedLimit_inner_eq_weakStatePath_projection
          hself m t y).symm
      _ = ⟪G.projector m z, y⟫_ℝ := by
        rw [S.projectedLimit_eq_projection_of_statePath_tendsto
          rho hrho t z ht m]
      _ = ⟪z, G.projector m y⟫_ℝ := hself m z y
  have hleft : Tendsto
      (fun m => ⟪S.weakStatePath t, G.projector m y⟫_ℝ)
      atTop (nhds ⟪S.weakStatePath t, y⟫_ℝ) := by
    simpa only [innerSL_apply_apply] using
      ((innerSL ℝ (S.weakStatePath t)).continuous.tendsto y).comp
        (G.projector_tendsto y)
  have hright : Tendsto
      (fun m => ⟪z, G.projector m y⟫_ℝ)
      atTop (nhds ⟪z, y⟫_ℝ) := by
    simpa only [innerSL_apply_apply] using
      ((innerSL ℝ z).continuous.tendsto y).comp
        (G.projector_tendsto y)
  have hleft' : Tendsto
      (fun m => ⟪z, G.projector m y⟫_ℝ)
      atTop (nhds ⟪S.weakStatePath t, y⟫_ℝ) := by
    simpa only [hcoord] using hleft
  exact tendsto_nhds_unique hleft' hright

omit [CompleteSpace V] in
/-- All pivot-space scalar pairings of the reconstructed path are continuous
in time. -/
theorem weakStatePath_inner_continuous
    (hself : ∀ m x y,
      ⟪G.projector m x, y⟫_ℝ = ⟪x, G.projector m y⟫_ℝ)
    (y : H) :
    Continuous (fun t => ⟪S.weakStatePath t, y⟫_ℝ) := by
  let F : ℕ → I → ℝ := fun m t => ⟪S.projectedLimit m t, y⟫_ℝ
  let f : I → ℝ := fun t => ⟪S.weakStatePath t, y⟫_ℝ
  have herror (m : ℕ) (t : I) :
      dist (f t) (F m t) ≤
        G.stateRadius *
          ‖G.projector m y - y‖ := by
    rw [Real.dist_eq]
    change
      |⟪S.weakStatePath t, y⟫_ℝ -
        ⟪S.projectedLimit m t, y⟫_ℝ| ≤ _
    rw [S.projectedLimit_inner_eq_weakStatePath_projection
      hself m t y, ← inner_sub_right]
    calc
      |⟪S.weakStatePath t,
          y - G.projector m y⟫_ℝ| ≤
          ‖S.weakStatePath t‖ *
            ‖y - G.projector m y‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ G.stateRadius *
          ‖y - G.projector m y‖ :=
        mul_le_mul_of_nonneg_right (S.weakStatePath_norm_le t)
          (norm_nonneg _)
      _ = G.stateRadius *
          ‖G.projector m y - y‖ := by
        rw [norm_sub_rev]
  have hnorm : Tendsto
      (fun m => ‖G.projector m y - y‖)
      atTop (nhds 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp
      (G.projector_tendsto y)
  have hscalar : Tendsto
      (fun m => G.stateRadius *
        ‖G.projector m y - y‖)
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hnorm
  have huniform : TendstoUniformly F f atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro epsilon hepsilon
    have hevent : ∀ᶠ m in atTop,
        G.stateRadius *
          ‖G.projector m y - y‖ <
            epsilon :=
      (tendsto_order.1 hscalar).2 epsilon hepsilon
    filter_upwards [hevent] with m hm
    intro t
    exact (herror m t).trans_lt hm
  have hcontinuous (m : ℕ) : Continuous (F m) :=
    (innerSLFlip ℝ y).continuous.comp (S.projectedLimit m).continuous
  have huniformContinuous (m : ℕ) : UniformContinuous (F m) :=
    CompactSpace.uniformContinuous_of_continuous (hcontinuous m)
  exact (huniform.uniformContinuous
    (Frequently.of_forall huniformContinuous)).continuous

omit [CompactSpace I] [CompleteSpace V] in
/-- The reconstructed pointwise path agrees almost everywhere with the strong
space-time state limit. -/
theorem weakStatePath_ae_eq_stateLimit
    (hself : ∀ m x y,
      ⟪G.projector m x, y⟫_ℝ = ⟪x, G.projector m y⟫_ℝ) :
    S.weakStatePath =ᵐ[μ] (S.stateLimit : I → H) := by
  have hmeasure : TendstoInMeasure μ
      (fun k => (G.stateLp (S.subseq.idx k) : I → H)) atTop
      (S.stateLimit : I → H) := by
    simpa only [Function.comp_apply] using
      tendstoInMeasure_of_tendsto_Lp S.state_strong
  obtain ⟨rho, hrho, hpointwise⟩ := hmeasure.exists_seq_tendsto_ae
  have hpath : ∀ᵐ t ∂μ, ∀ j,
      (G.stateLp (S.subseq.idx (rho j)) : I → H) t =
        G.statePath (S.subseq.idx (rho j)) t := by
    apply ae_all_iff.2
    intro j
    exact BoundedContinuousFunction.coeFn_toLp
      (2 : ℝ≥0∞) μ ℝ (G.statePath (S.subseq.idx (rho j)))
  filter_upwards [hpointwise, hpath] with t ht hrep
  apply S.weakStatePath_eq_of_statePath_tendsto
    hself rho hrho.tendsto_atTop t (S.stateLimit t)
  simpa only [hrep] using ht

/-- Canonical weakly continuous representative generated by a synchronized
spectral extraction. -/
noncomputable def weaklyContinuousStateRepresentative
    (hself : ∀ m x y,
      ⟪G.projector m x, y⟫_ℝ = ⟪x, G.projector m y⟫_ℝ) :
    G.WeaklyContinuousStateRepresentative S where
  path := S.weakStatePath
  norm_le := S.weakStatePath_norm_le
  inner_continuous := S.weakStatePath_inner_continuous hself
  pointwise_weak_subsequence := S.exists_pointwiseWeakSubsequence
  path_ae_eq_stateLimit :=
    S.weakStatePath_ae_eq_stateLimit hself
  eq_of_statePath_tendsto :=
    S.weakStatePath_eq_of_statePath_tendsto hself

end StrongWeakPathSubsequence

end LeraySpectralCompactFamily

end LeraySpectral

end
