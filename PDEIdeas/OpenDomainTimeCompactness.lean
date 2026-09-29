import PDEIdeas.OpenDomainSpectralCompactness

/-!
# Strong `L²`-in-time compactness for open-domain spectral paths

`PDEIdeas.OpenDomainSpectralCompactness` records that the energy-to-state embedding
`openDomainEnergyToState Ω : H¹₀σ(Ω) → L²σ(Ω)` is compact and that its finite spectral
heads approximate it in operator norm.  `PDEIdeas.GalerkinL2Compactness` turns exactly
that data, together with time regularity, into a strongly `L²(I; H)`-convergent
subsequence.  This file connects the two.

The sequence of paths is **abstract**: it is an arbitrary sequence

`u : ℕ → Icc a b →ᵇ H¹₀σ(Ω)`

subject only to explicitly stated uniform bounds.  Nothing here assumes that Galerkin
solutions on `Ω` exist, constructs them, or refers to any variational problem; the
file therefore does not depend on the Galerkin-tower and forcing-estimate developments,
and its conclusion applies to any family satisfying its three bounds.

## The three bounds

* **uniform state bound** — `‖openDomainEnergyToState Ω (u k t)‖ ≤ stateRadius`
  for all `k` and all times `t`: the `L∞(I; L²σ(Ω))` bound;
* **uniform energy bound** — `‖toLp 2 μI ℝ (u k)‖ ≤ energyRadius` for all `k`:
  the `L²(I; H¹₀σ(Ω))` bound;
* **common-dual derivative bound** — each spectral coordinate of the embedded path has,
  on `Icc a b`, the derivative obtained by evaluating a common dual path
  `dual k : ℝ → (H¹₀σ(Ω) →L[ℝ] ℝ)` at a fixed test mode, and the dual paths are
  square integrable in time with one uniform radius:
  `∫ x in a..b, ‖dual k x‖ ^ 2 ≤ dualRadius ^ 2`.

## Main results

* `compactFamilyOfExhaustionDualL2` — the missing generic constructor: spectral
  compactness data for an arbitrarily indexed Hilbert basis with a finite exhaustion,
  built from a common-dual derivative bound rather than from a variational problem.
* `openDomainCompactFamily` — its instantiation at the open-domain spectral
  representation.
* `exists_strongL2_subsequence_of_uniform_bounds` — **the strong `L²`-in-time
  subsequence theorem**: a strictly increasing `φ` and a limit `w ∈ L²(I; L²σ(Ω))` with
  `openDomainStateLp Ω u ∘ φ → w` in `L²(I; L²σ(Ω))`.
* `exists_strongL2_quadratic_subsequence_of_uniform_bounds` — the same subsequence
  carries every continuous quadratic observable of the state to the observable of the
  limit, in `L¹(I)`.

## Scope

The extraction is the abstract Aubin--Lions mechanism of the project: compactness of
the spatial embedding plus square-root-in-time equicontinuity of every finite spectral
head.  No statement is made about the limit `w` beyond this convergence: it is not
claimed to solve any equation, to be a Galerkin limit, or to inherit any nonlinear
identity.  The three bounds are hypotheses, supplied by whoever has a family of paths.
-/

open BoundedContinuousFunction Filter Function InnerProductSpace MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace Topology

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace OpenDomainTimeCompactness

/-! ## Generic layer: compactness data from a common-dual derivative bound -/

section Generic

variable {V H Test ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup Test] [NormedSpace ℝ Test]

/-- **Spectral compactness data from a common-dual derivative bound.**

This is the exhaustion-indexed counterpart of
`LeraySpectralCompactFamily.ofHilbertBasisOfProjectedL2Derivative`, with the projected
time derivative supplied by a common-test-space dual path rather than by a variational
Galerkin problem.  The finite head of index `m` is differentiated coordinatewise, its
derivative is the finite-mode synthesis of the dual path, and the uniform `L²` bound on
the dual path gives the square-root time modulus that Arzelà--Ascoli consumes. -/
noncomputable def compactFamilyOfExhaustionDualL2
    {a b : ℝ} (hab : a ≤ b)
    {μI : Measure (Icc a b)} [IsFiniteMeasure μI]
    (embed : V →L[ℝ] H) (embed_compact : IsCompactOperator embed)
    (basis : HilbertBasis ι ℝ H) (exhaustion : HilbertBasisExhaustion ι)
    (lift : ℕ → Icc a b →ᵇ V)
    (stateRadius : ℝ)
    (state_bound : ∀ k t, ‖embed (lift k t)‖ ≤ stateRadius)
    (liftLpRadius : ℝ) (liftLpRadius_nonneg : 0 ≤ liftLpRadius)
    (liftLp_bound : ∀ k,
      ‖BoundedContinuousFunction.toLp (2 : ℝ≥0∞) μI ℝ (lift k)‖ ≤ liftLpRadius)
    (testMode : ι → Test)
    (dual : ℕ → ℝ → (Test →L[ℝ] ℝ))
    (coordinate : ℕ → ι → ℝ → ℝ)
    (coordinate_eq : ∀ k i (t : Icc a b),
      coordinate k i t = ⟪embed (lift k t), basis i⟫_ℝ)
    (coordinate_hasDeriv : ∀ k i x, x ∈ Icc a b →
      HasDerivWithinAt (coordinate k i) (dual k x (testMode i)) (Icc a b) x)
    (dualRadius : ℝ≥0)
    (dual_memLp : ∀ k, MemLp (dual k) 2 (volume.restrict (Icc a b)))
    (dual_sq_integral_bound : ∀ k,
      ∫ x in a..b, ‖dual k x‖ ^ 2 ≤ (dualRadius : ℝ) ^ 2) :
    LeraySpectralCompactFamily (I := Icc a b) (V := V) (H := H) (μ := μI) := by
  classical
  let projector : ℕ → H →L[ℝ] H := fun m =>
    GalerkinProjectorSequence.finitePartialProjection basis (exhaustion.head m)
  let projectedExtension : ℕ → ℕ → ℝ → H := fun m k t =>
    ∑ i ∈ exhaustion.head m, coordinate k i t • basis i
  let projectedDerivative : ℕ → ℕ → ℝ → H := fun m k t =>
    VariationalGalerkinProblem.finiteModeSynthesis
      testMode basis (exhaustion.head m) (dual k t)
  apply LeraySpectralCompactFamily.ofHilbertBasisExhaustion basis exhaustion embed
    embed_compact lift stateRadius state_bound liftLpRadius liftLpRadius_nonneg
    liftLp_bound
  intro m
  let C₀ : ℝ≥0 :=
    VariationalGalerkinProblem.finiteModeSynthesisConstant
      testMode basis (exhaustion.head m)
  let C : ℝ≥0 := C₀ * dualRadius
  apply equicontinuous_subtype_of_uniform_sqrt
    (Set.range (lerayProjectedPath embed projector lift m)) C
  intro f s t
  rcases f with ⟨_, k, rfl⟩
  change
    dist (lerayProjectedPath embed projector lift m k s)
      (lerayProjectedPath embed projector lift m k t) ≤ (C : ℝ) * √(dist s t)
  have hext : ∀ q : Icc a b,
      projectedExtension m k q = lerayProjectedPath embed projector lift m k q := by
    intro q
    change (∑ i ∈ exhaustion.head m, coordinate k i q • basis i) =
      GalerkinProjectorSequence.finitePartialProjection basis (exhaustion.head m)
        (embed (lift k q))
    rw [GalerkinProjectorSequence.finitePartialProjection_apply_eq_sum]
    refine Finset.sum_congr rfl fun i _hi => ?_
    rw [coordinate_eq k i q]
  have hderiv : ∀ x ∈ Icc a b,
      HasDerivWithinAt (projectedExtension m k) (projectedDerivative m k x)
        (Icc a b) x := by
    intro x hx
    have hsum :
        HasDerivWithinAt
          (fun y => ∑ i ∈ exhaustion.head m, coordinate k i y • basis i)
          (∑ i ∈ exhaustion.head m, dual k x (testMode i) • basis i)
          (Icc a b) x :=
      HasDerivWithinAt.fun_sum fun i _hi =>
        (coordinate_hasDeriv k i x hx).smul_const (basis i)
    exact hsum
  have hmemLp : MemLp (projectedDerivative m k) 2 (volume.restrict (Icc a b)) :=
    VariationalGalerkinProblem.finiteModeSynthesis_memLp (dual k) 2
      (volume.restrict (Icc a b)) testMode basis (exhaustion.head m) (dual_memLp k)
  have hsq : ∫ x in a..b, ‖projectedDerivative m k x‖ ^ 2 ≤ (C : ℝ) ^ 2 := by
    have hsynth :=
      VariationalGalerkinProblem.intervalIntegral_norm_finiteModeSynthesis_sq_le
        hab (dual k) testMode basis (exhaustion.head m) (dual_memLp k)
    have hmono :
        (C₀ : ℝ) ^ 2 * ∫ x in a..b, ‖dual k x‖ ^ 2 ≤
          (C₀ : ℝ) ^ 2 * (dualRadius : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left (dual_sq_integral_bound k) (sq_nonneg _)
    have hC : (C : ℝ) ^ 2 = (C₀ : ℝ) ^ 2 * (dualRadius : ℝ) ^ 2 := by
      simp only [C, NNReal.coe_mul]
      ring
    calc
      ∫ x in a..b, ‖projectedDerivative m k x‖ ^ 2 ≤
          (C₀ : ℝ) ^ 2 * ∫ x in a..b, ‖dual k x‖ ^ 2 := hsynth
      _ ≤ (C₀ : ℝ) ^ 2 * (dualRadius : ℝ) ^ 2 := hmono
      _ = (C : ℝ) ^ 2 := hC.symm
  rw [← hext s, ← hext t]
  exact dist_le_sqrt_mul_of_hasDerivWithinAt_of_memLp hab
    (projectedExtension m k) (projectedDerivative m k) C hderiv hmemLp hsq s t

end Generic

/-! ## The open-domain instance -/

section OpenDomain

variable {n : ℕ} {Q : BoxIntegral.Box (Fin (n + 1))}
    {Test : Type*} [NormedAddCommGroup Test] [NormedSpace ℝ Test]

/-- The `L²(I; L²σ(Ω))` class of the embedded state path of an `Ω` spectral path. -/
noncomputable def openDomainStateLp {a b : ℝ} {μI : Measure (Icc a b)}
    [IsFiniteMeasure μI] (Ω : OpenDomainInBox Q)
    (u : ℕ → Icc a b →ᵇ OpenDomainH1ZeroSigma Ω) (k : ℕ) :
    Lp (OpenDomainL2Sigma Ω) 2 μI :=
  BoundedContinuousFunction.toLp (2 : ℝ≥0∞) μI ℝ
    ((openDomainEnergyToState Ω).compLeftContinuousBounded (Icc a b) (u k))

variable {Ω : OpenDomainInBox Q}

/-- **Compactness data for an abstract sequence of `Ω` spectral paths.**  The spatial
input is the compactness of `openDomainEnergyToState Ω` recorded by the spectral
representation; the temporal input is the common-dual derivative bound. -/
noncomputable def openDomainCompactFamily
    (S : OpenDomainCompactSpectralRepresentation Ω)
    {a b : ℝ} (hab : a ≤ b) {μI : Measure (Icc a b)} [IsFiniteMeasure μI]
    (u : ℕ → Icc a b →ᵇ OpenDomainH1ZeroSigma Ω)
    (stateRadius : ℝ)
    (state_bound : ∀ k t, ‖openDomainEnergyToState Ω (u k t)‖ ≤ stateRadius)
    (energyRadius : ℝ) (energyRadius_nonneg : 0 ≤ energyRadius)
    (energy_bound : ∀ k,
      ‖BoundedContinuousFunction.toLp (2 : ℝ≥0∞) μI ℝ (u k)‖ ≤ energyRadius)
    (testMode : S.Index → Test)
    (dual : ℕ → ℝ → (Test →L[ℝ] ℝ))
    (coordinate : ℕ → S.Index → ℝ → ℝ)
    (coordinate_eq : ∀ k i (t : Icc a b),
      coordinate k i t = ⟪openDomainEnergyToState Ω (u k t), S.stateBasis i⟫_ℝ)
    (coordinate_hasDeriv : ∀ k i x, x ∈ Icc a b →
      HasDerivWithinAt (coordinate k i) (dual k x (testMode i)) (Icc a b) x)
    (dualRadius : ℝ≥0)
    (dual_memLp : ∀ k, MemLp (dual k) 2 (volume.restrict (Icc a b)))
    (dual_sq_integral_bound : ∀ k,
      ∫ x in a..b, ‖dual k x‖ ^ 2 ≤ (dualRadius : ℝ) ^ 2) :
    LeraySpectralCompactFamily (I := Icc a b)
      (V := OpenDomainH1ZeroSigma Ω) (H := OpenDomainL2Sigma Ω) (μ := μI) :=
  -- the instances of the two closure spaces are supplied explicitly: the ones carried by
  -- `S` are the ones fixed when the spaces were built, and instance search cannot bridge
  -- the two spellings on its own.
  @compactFamilyOfExhaustionDualL2
    (OpenDomainH1ZeroSigma Ω) (OpenDomainL2Sigma Ω) Test S.Index
    _ _ _ _ (openDomainL2Sigma_completeSpace Ω) _ _
    a b hab μI _
    (openDomainEnergyToState Ω) S.embedding_compact S.stateBasis S.exhaustion u
    stateRadius state_bound energyRadius energyRadius_nonneg energy_bound
    testMode dual coordinate coordinate_eq coordinate_hasDeriv
    dualRadius dual_memLp dual_sq_integral_bound

/-- **Strong `L²`-in-time compactness on an open subdomain.**

From an abstract sequence of `Ω` spectral paths with a uniform state bound, a uniform
energy bound and a uniform common-dual derivative bound, a subsequence of the embedded
state paths converges strongly in `L²(I; L²σ(Ω))`. -/
theorem exists_strongL2_subsequence_of_uniform_bounds
    (S : OpenDomainCompactSpectralRepresentation Ω)
    {a b : ℝ} (hab : a ≤ b) {μI : Measure (Icc a b)} [IsFiniteMeasure μI]
    (u : ℕ → Icc a b →ᵇ OpenDomainH1ZeroSigma Ω)
    (stateRadius : ℝ)
    (state_bound : ∀ k t, ‖openDomainEnergyToState Ω (u k t)‖ ≤ stateRadius)
    (energyRadius : ℝ) (energyRadius_nonneg : 0 ≤ energyRadius)
    (energy_bound : ∀ k,
      ‖BoundedContinuousFunction.toLp (2 : ℝ≥0∞) μI ℝ (u k)‖ ≤ energyRadius)
    (testMode : S.Index → Test)
    (dual : ℕ → ℝ → (Test →L[ℝ] ℝ))
    (coordinate : ℕ → S.Index → ℝ → ℝ)
    (coordinate_eq : ∀ k i (t : Icc a b),
      coordinate k i t = ⟪openDomainEnergyToState Ω (u k t), S.stateBasis i⟫_ℝ)
    (coordinate_hasDeriv : ∀ k i x, x ∈ Icc a b →
      HasDerivWithinAt (coordinate k i) (dual k x (testMode i)) (Icc a b) x)
    (dualRadius : ℝ≥0)
    (dual_memLp : ∀ k, MemLp (dual k) 2 (volume.restrict (Icc a b)))
    (dual_sq_integral_bound : ∀ k,
      ∫ x in a..b, ‖dual k x‖ ^ 2 ≤ (dualRadius : ℝ) ^ 2) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ w : Lp (OpenDomainL2Sigma Ω) 2 μI,
        Tendsto (fun j => openDomainStateLp Ω u (φ j)) atTop (𝓝 w) := by
  obtain ⟨T⟩ :=
    @LeraySpectralCompactFamily.exists_strongL2_subsequence (Icc a b)
      (OpenDomainH1ZeroSigma Ω) (OpenDomainL2Sigma Ω) _ _ _ _ _ _ _ _ _
      (openDomainL2Sigma_completeSpace Ω) μI _
      (openDomainCompactFamily S hab u stateRadius state_bound energyRadius
        energyRadius_nonneg energy_bound testMode dual coordinate coordinate_eq
        coordinate_hasDeriv dualRadius dual_memLp dual_sq_integral_bound)
  exact ⟨T.subseq.idx, T.subseq.strictMono_idx, T.limit, T.converges⟩

/-- The extracted subsequence in the packaged form of
`PDEIdeas.GalerkinL2Compactness`. -/
theorem nonempty_strongL2_subsequence_of_uniform_bounds
    (S : OpenDomainCompactSpectralRepresentation Ω)
    {a b : ℝ} (hab : a ≤ b) {μI : Measure (Icc a b)} [IsFiniteMeasure μI]
    (u : ℕ → Icc a b →ᵇ OpenDomainH1ZeroSigma Ω)
    (stateRadius : ℝ)
    (state_bound : ∀ k t, ‖openDomainEnergyToState Ω (u k t)‖ ≤ stateRadius)
    (energyRadius : ℝ) (energyRadius_nonneg : 0 ≤ energyRadius)
    (energy_bound : ∀ k,
      ‖BoundedContinuousFunction.toLp (2 : ℝ≥0∞) μI ℝ (u k)‖ ≤ energyRadius)
    (testMode : S.Index → Test)
    (dual : ℕ → ℝ → (Test →L[ℝ] ℝ))
    (coordinate : ℕ → S.Index → ℝ → ℝ)
    (coordinate_eq : ∀ k i (t : Icc a b),
      coordinate k i t = ⟪openDomainEnergyToState Ω (u k t), S.stateBasis i⟫_ℝ)
    (coordinate_hasDeriv : ∀ k i x, x ∈ Icc a b →
      HasDerivWithinAt (coordinate k i) (dual k x (testMode i)) (Icc a b) x)
    (dualRadius : ℝ≥0)
    (dual_memLp : ∀ k, MemLp (dual k) 2 (volume.restrict (Icc a b)))
    (dual_sq_integral_bound : ∀ k,
      ∫ x in a..b, ‖dual k x‖ ^ 2 ≤ (dualRadius : ℝ) ^ 2) :
    Nonempty (StrongMetricSubsequence (openDomainStateLp (μI := μI) Ω u)) :=
  @LeraySpectralCompactFamily.exists_strongL2_subsequence (Icc a b)
    (OpenDomainH1ZeroSigma Ω) (OpenDomainL2Sigma Ω) _ _ _ _ _ _ _ _ _
    (openDomainL2Sigma_completeSpace Ω) μI _
    (openDomainCompactFamily S hab u stateRadius state_bound energyRadius
        energyRadius_nonneg energy_bound testMode dual coordinate coordinate_eq
        coordinate_hasDeriv dualRadius dual_memLp dual_sq_integral_bound)

/-- **Quadratic observables along the extracted subsequence.**  Every continuous
bilinear map of the state is carried to the observable of the limit in `L¹(I)`.  This is
the continuity statement of the `L²` machinery; it is not a claim about any equation
satisfied by the limit. -/
theorem exists_strongL2_quadratic_subsequence_of_uniform_bounds
    (S : OpenDomainCompactSpectralRepresentation Ω)
    {a b : ℝ} (hab : a ≤ b) {μI : Measure (Icc a b)} [IsFiniteMeasure μI]
    (u : ℕ → Icc a b →ᵇ OpenDomainH1ZeroSigma Ω)
    (stateRadius : ℝ)
    (state_bound : ∀ k t, ‖openDomainEnergyToState Ω (u k t)‖ ≤ stateRadius)
    (energyRadius : ℝ) (energyRadius_nonneg : 0 ≤ energyRadius)
    (energy_bound : ∀ k,
      ‖BoundedContinuousFunction.toLp (2 : ℝ≥0∞) μI ℝ (u k)‖ ≤ energyRadius)
    (testMode : S.Index → Test)
    (dual : ℕ → ℝ → (Test →L[ℝ] ℝ))
    (coordinate : ℕ → S.Index → ℝ → ℝ)
    (coordinate_eq : ∀ k i (t : Icc a b),
      coordinate k i t = ⟪openDomainEnergyToState Ω (u k t), S.stateBasis i⟫_ℝ)
    (coordinate_hasDeriv : ∀ k i x, x ∈ Icc a b →
      HasDerivWithinAt (coordinate k i) (dual k x (testMode i)) (Icc a b) x)
    (dualRadius : ℝ≥0)
    (dual_memLp : ∀ k, MemLp (dual k) 2 (volume.restrict (Icc a b)))
    (dual_sq_integral_bound : ∀ k,
      ∫ x in a..b, ‖dual k x‖ ^ 2 ≤ (dualRadius : ℝ) ^ 2)
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (B : OpenDomainL2Sigma Ω →L[ℝ] OpenDomainL2Sigma Ω →L[ℝ] N) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ w : Lp (OpenDomainL2Sigma Ω) 2 μI,
        Tendsto (fun j => openDomainStateLp Ω u (φ j)) atTop (𝓝 w) ∧
        Tendsto (fun j => B.quadraticLp (openDomainStateLp Ω u (φ j)))
          atTop (𝓝 (B.quadraticLp w)) := by
  obtain ⟨T, hT⟩ :=
    @LeraySpectralCompactFamily.exists_strongL2_quadraticL1_subsequence (Icc a b)
      (OpenDomainH1ZeroSigma Ω) (OpenDomainL2Sigma Ω) _ _ _ _ _ _ _ _ _
      (openDomainL2Sigma_completeSpace Ω) μI _
      (openDomainCompactFamily S hab u stateRadius state_bound energyRadius
        energyRadius_nonneg energy_bound testMode dual coordinate coordinate_eq
        coordinate_hasDeriv dualRadius dual_memLp dual_sq_integral_bound) N _ _ B
  exact ⟨T.subseq.idx, T.subseq.strictMono_idx, T.limit, T.converges, hT⟩

end OpenDomain

end OpenDomainTimeCompactness

end
