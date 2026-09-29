import PDEIdeas.OpenDomainSpectral
import PDEIdeas.LeraySpectralWeakCompactness

/-!
# Weak energy extraction for the subdomain family

The Galerkin levels of a subdomain family carry a uniform `L²_t V` energy
bound — it is the `liftLp_bound` field of `LeraySpectralCompactFamily`, and on
the unforced family it comes from the energy identity.  This file turns that
bound into actual convergence: along one strict subsequence the energies
converge **weakly** in `L²_t V`, and the embedded weak energy limit is
**identified** with the strong `L²_t H` state limit.

Neither convergence is an input.  Both are produced by
`LeraySpectralCompactFamily.exists_strongWeakSubsequence`, which combines the
weak compactness of balls in a separable Hilbert space with the strong
`L²_t H` compactness coming from the compact embedding, and then pins the two
limits together through the space-time embedding.

## What is subdomain-specific

Exactly one thing: separability of the energy-valued time `L²` space.  The
generic extraction is stated under
`[SeparableSpace (Lp V 2 μ)]`, and that instance is not found automatically
for `V = OpenDomainH1ZeroSigma Ω`.  It is supplied here by
`openDomainEnergyTimeLp_separableSpace`, from the separability of `Ω`'s energy
space (a subspace of the rectangle's second-countable ambient product,
`OpenDomainSpectral.openDomainH1ZeroSigma_separableSpace`) together with
separability of the time measure.  Everything else is the generic machinery.

## Main results

* `openDomainEnergyTimeLp_separableSpace` — the missing instance.
* `exists_strongWeakSubsequence` — the extraction, for any subdomain family.
* `exists_strongWeakPathSubsequence` — the same refined so that every finite
  spectral projection also converges uniformly in time.
* `state_strong`, `energy_weak`, `embed_energyLimit` — the three conclusions,
  named.
* `stateLimit_ae_eq_embed_energyLimit` — the identification in pointwise form.

## Scope

The family `G` itself is a hypothesis, not built here;
`OpenDomainTimeCompactness.openDomainCompactFamily` is what constructs it, and
the uniform bound is one of its fields.  No solution and no existence theorem
is claimed.

A note for anyone extending this file: stating a combined existential with
explicit `Lp` type ascriptions makes `isDefEq` diverge, because the closure
spaces' instances have two spellings that unification will not reconcile
cheaply.  The conclusions are therefore phrased as separate theorems about a
given `S : G.StrongWeakSubsequence`, whose types come from `S` itself, and the
one place a generic lemma is applied uses the explicit `@`-form with the
completeness instances passed by hand — the same convention the rectangle layer
uses in `BoxLerayWeakCompactness`.
-/

open Filter InnerProductSpace MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

namespace OpenDomainWeakEnergySubsequence

variable {n : ℕ} {Q : BoxIntegral.Box (Fin (n + 1))}

/-- The subdomain energy space is complete.  Re-declared locally because
instance search does not bridge the two spellings of the closure spaces'
uniformity. -/
local instance openDomainWeakEnergyH1Complete (Ω : OpenDomainInBox Q) :
    CompleteSpace (OpenDomainH1ZeroSigma Ω) :=
  openDomainH1ZeroSigma_completeSpace Ω

/-- The subdomain pivot space is complete, same caveat. -/
local instance openDomainWeakEnergyL2Complete (Ω : OpenDomainInBox Q) :
    CompleteSpace (OpenDomainL2Sigma Ω) :=
  openDomainL2Sigma_completeSpace Ω

/-! ## Separability of the energy-valued time `L²` space -/

/-- The energy-valued time `L²` space of a subdomain is second countable.
This is the only subdomain-specific input the extraction needs: `Ω`'s energy
space is separable because it is a subspace of the rectangle's second-countable
ambient product, and the time measure is separable because the interval is. -/
@[reducible] noncomputable def openDomainEnergyTimeLp_secondCountableTopology
    (Ω : OpenDomainInBox Q) {a b : ℝ} (μ : Measure (Icc a b))
    [IsFiniteMeasure μ] :
    SecondCountableTopology
      (Lp (OpenDomainH1ZeroSigma Ω) (2 : ℝ≥0∞) μ) := by
  letI htop : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.ofNat_ne_top⟩
  letI hE : SeparableSpace (OpenDomainH1ZeroSigma Ω) :=
    openDomainH1ZeroSigma_separableSpace Ω
  letI hmu : IsSeparable μ := inferInstance
  exact @MeasureTheory.Lp.SecondCountableTopology
    (Icc a b) (OpenDomainH1ZeroSigma Ω) inferInstance inferInstance
    μ (2 : ℝ≥0∞) inferInstance htop hmu hE

/-- The energy-valued time `L²` space of a subdomain is separable. -/
@[reducible] noncomputable def openDomainEnergyTimeLp_separableSpace
    (Ω : OpenDomainInBox Q) {a b : ℝ} (μ : Measure (Icc a b))
    [IsFiniteMeasure μ] :
    SeparableSpace (Lp (OpenDomainH1ZeroSigma Ω) (2 : ℝ≥0∞) μ) := by
  letI : SecondCountableTopology
      (Lp (OpenDomainH1ZeroSigma Ω) (2 : ℝ≥0∞) μ) :=
    openDomainEnergyTimeLp_secondCountableTopology Ω μ
  infer_instance

/-! ## The extraction -/

variable (Ω : OpenDomainInBox Q) {a b : ℝ}
    {μ : Measure (Icc a b)} [IsFiniteMeasure μ]

/-- **Simultaneous strong/weak extraction for a subdomain family.**

Nothing is assumed about convergence.  The uniform energy bound already
carried by the family (`liftLp_bound`) supplies weak `L²_t V` compactness, the
compact embedding supplies strong `L²_t H` compactness, and the two are
realized on one strict subsequence whose limits are identified through the
space-time embedding. -/
theorem exists_strongWeakSubsequence
    (G : LeraySpectralCompactFamily (I := Icc a b)
      (V := OpenDomainH1ZeroSigma Ω) (H := OpenDomainL2Sigma Ω) (μ := μ)) :
    Nonempty G.StrongWeakSubsequence := by
  exact @LeraySpectralCompactFamily.exists_strongWeakSubsequence
    (Icc a b) (OpenDomainH1ZeroSigma Ω) (OpenDomainL2Sigma Ω)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance (openDomainH1ZeroSigma_completeSpace Ω)
    inferInstance inferInstance (openDomainL2Sigma_completeSpace Ω)
    μ inferInstance G (openDomainEnergyTimeLp_separableSpace Ω μ)

/-- **The same extraction refined so that every finite spectral projection also
converges uniformly in time.** -/
theorem exists_strongWeakPathSubsequence
    (G : LeraySpectralCompactFamily (I := Icc a b)
      (V := OpenDomainH1ZeroSigma Ω) (H := OpenDomainL2Sigma Ω) (μ := μ)) :
    Nonempty G.StrongWeakPathSubsequence := by
  obtain ⟨S⟩ := exists_strongWeakSubsequence Ω G
  exact S.exists_pathwiseRefinement

/-! ## Named consequences of one extraction -/

variable {Ω}
variable {G : LeraySpectralCompactFamily (I := Icc a b)
  (V := OpenDomainH1ZeroSigma Ω) (H := OpenDomainL2Sigma Ω) (μ := μ)}

/-- Strong `L²_t H` convergence of the states along the extracted
subsequence. -/
theorem state_strong (S : G.StrongWeakSubsequence) :
    Tendsto (G.stateLp ∘ S.subseq.idx) atTop (𝓝 S.stateLimit) :=
  S.state_strong

/-- **Weak `L²_t V` convergence of the energies along the extracted
subsequence.**  Produced by the extraction, not assumed. -/
theorem energy_weak (S : G.StrongWeakSubsequence)
    (w : Lp (OpenDomainH1ZeroSigma Ω) (2 : ℝ≥0∞) μ) :
    Tendsto (fun k => ⟪G.energyLp (S.subseq.idx k), w⟫_ℝ) atTop
      (𝓝 ⟪S.energyLimit, w⟫_ℝ) :=
  S.energy_weak w

/-- **The embedded weak energy limit is the strong state limit.** -/
theorem embed_energyLimit (S : G.StrongWeakSubsequence) :
    G.embed.compLpL (2 : ℝ≥0∞) μ S.energyLimit = S.stateLimit :=
  S.embed_energyLimit

/-- Pointwise form of the identification: the state limit is a.e. the embedded
energy limit. -/
theorem stateLimit_ae_eq_embed_energyLimit (S : G.StrongWeakSubsequence) :
    (S.stateLimit : Icc a b → OpenDomainL2Sigma Ω) =ᵐ[μ]
      fun t => G.embed (S.energyLimit t) := by
  rw [← S.embed_energyLimit]
  exact G.embed.coeFn_compLpL S.energyLimit

end OpenDomainWeakEnergySubsequence
