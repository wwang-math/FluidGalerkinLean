import PDEIdeas.OpenDomainGalerkinTestIdentity
import PDEIdeas.OpenDomainUnforcedUniformBounds

/-!
# Convergence of the projected spatial tests and of the projected initial data

`PDEIdeas.OpenDomainGalerkinTestIdentity` produces the finite-level tested
equation with the **projected** test `S.energyProjection m φ` and the initial
pairing read in the pivot space of the ambient rectangle, and passes a sequence
of such identities to the limit.  Two of the hypotheses it leaves open are
exactly the ones that say the projections disappear in the limit:

* `hψ`, the convergence of the projected spatial tests;
* `hu₀`, the convergence of the projected initial states.

This file discharges both.  Nothing about time compactness is involved: the
whole content is that the spectral heads exhaust the space, so the orthogonal
projections converge strongly, and that the maps used to read a finite head in
the ambient rectangle are continuous.

## What is proved

The core statement is box-independent and is stated for an arbitrary
`CompactEmbeddingSpectralRepresentation`:

* `CompactEmbeddingSpectralRepresentation.energyProjection_tendsto` — the
  spectral energy projections of a fixed test converge to that test in the
  energy norm;
* `CompactEmbeddingSpectralRepresentation.stateProjection_tendsto` — the same
  in the pivot space;
* `CompactEmbeddingSpectralRepresentation.energySynthesis_testProjection_tendsto`
  — the form the finite level actually produces, `S.energySynthesis m ∘
  S.testProjection m`, converges to the test as well.

Both come from `GalerkinProjectorSequence.finitePartialProjection_tendsto`
applied to the two Hilbert bases of the representation, so no new analysis is
introduced.  The subdomain statements then follow by continuity:

* `OpenDomainProjectedTestConvergence.energyToBoxState_energyProjection_tendsto`
  — the state pairing of the projected test converges in `BoxL2Sigma Q`;
* `OpenDomainProjectedTestConvergence.inner_energyToBoxState_energyProjection_tendsto`
  — hence so does the scalar pairing appearing on the right of the tested
  equation;
* `OpenDomainProjectedTestConvergence.initialPairing_tendsto_of_state_tendsto`
  — whenever the initial coefficients converge in the pivot space, their
  synthesised states converge in `BoxL2Sigma Q`; the identification
  `energyToBoxState_energySynthesis` is what makes the energy synthesis
  invisible here, so no energy-norm control of the initial data is needed;
* `OpenDomainProjectedTestConvergence.initialPairing_stateHeadProjection_tendsto`
  — the canonical instance, with the initial coefficients the spectral
  projections of one fixed element of `OpenDomainL2Sigma Ω`.

Finally
`OpenDomainProjectedTestConvergence.tested_weak_equation_limit_of_projected_data`
feeds these into
`OpenDomainGalerkinTestIdentity.tested_weak_equation_limit_of_galerkin`.  The
resulting limit equation carries no projection at all: the spatial test is the
fixed `φ` and the initial term is the fixed `x₀` read in the ambient pivot
space.
-/

open Filter InnerProductSpace MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

/-! ### Strong convergence of the spectral heads -/

namespace CompactEmbeddingSpectralRepresentation

variable {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {J : V →L[ℝ] H}
    (S : CompactEmbeddingSpectralRepresentation J)

/-- **The spectral energy projections of a fixed test converge to that test.**
The heads are the finite partial spans of the energy Hilbert basis along the
exhaustion of the index, so this is the strong convergence of an exhausted
orthogonal projector sequence. -/
theorem energyProjection_tendsto (φ : V) :
    Tendsto (fun m => S.energyProjection m φ) atTop (nhds φ) :=
  GalerkinProjectorSequence.finitePartialProjection_tendsto
    S.energyBasis S.exhaustion φ

/-- The same statement in the pivot space, for the state heads. -/
theorem stateProjection_tendsto (x : H) :
    Tendsto (fun m => S.stateProjection m x) atTop (nhds x) :=
  GalerkinProjectorSequence.finitePartialProjection_tendsto
    S.stateBasis S.exhaustion x

/-- The test as the finite level sees it -- projected to coefficients and
synthesised back -- also converges to the test.  This is the previous statement
transported along
`energySynthesis_testProjection_eq_energyProjection`. -/
theorem energySynthesis_testProjection_tendsto (φ : V) :
    Tendsto (fun m => S.energySynthesis m (S.testProjection m φ)) atTop
      (nhds φ) :=
  Tendsto.congr
    (fun m => (S.energySynthesis_testProjection_eq_energyProjection m φ).symm)
    (S.energyProjection_tendsto φ)

/-- The energy statement along any sequence of levels tending to infinity. -/
theorem energyProjection_comp_tendsto (φ : V) {lev : ℕ → ℕ}
    (hlev : Tendsto lev atTop atTop) :
    Tendsto (fun k => S.energyProjection (lev k) φ) atTop (nhds φ) :=
  (S.energyProjection_tendsto φ).comp hlev

/-- The pivot statement along any sequence of levels tending to infinity. -/
theorem stateProjection_comp_tendsto (x : H) {lev : ℕ → ℕ}
    (hlev : Tendsto lev atTop atTop) :
    Tendsto (fun k => S.stateProjection (lev k) x) atTop (nhds x) :=
  (S.stateProjection_tendsto x).comp hlev

end CompactEmbeddingSpectralRepresentation

namespace OpenDomainProjectedTestConvergence

open OpenDomainGalerkinTestIdentity OpenDomainWeakEquationLimit

variable {Q : BoxIntegral.Box (Fin 2)} {Ω : OpenDomainInBox Q}

/-! ### Reading a finite head in the ambient pivot space -/

/-- **The energy synthesis is invisible in the pivot space.**  A head
coefficient synthesised to an energy field and then read in `BoxL2Sigma Q` is
just that coefficient's own state, included into the rectangle.  Consequently
the initial pairing of the tested equation is controlled by pivot-space data
alone. -/
theorem energyToBoxState_energySynthesis
    (S : OpenDomainCompactSpectralRepresentation Ω) (m : ℕ)
    (x : S.stateSpace m) :
    OpenDomainConvectionLimit.energyToBoxState Ω (S.energySynthesis m x) =
      openDomainStateToBox Ω (S.stateSynthesis m x) :=
  (energyToBoxState_eq Ω (S.energySynthesis m x)).trans
    (congrArg (openDomainStateToBox Ω) (S.embedding_energySynthesis m x))

/-! ### The spatial test in the limit -/

/-- **The state pairing of the projected test converges.**  This is the exact
shape in which the projected test enters the tested equation, through
`OpenDomainConvectionLimit.energyToBoxState`. -/
theorem energyToBoxState_energyProjection_tendsto
    (S : OpenDomainCompactSpectralRepresentation Ω)
    (φ : OpenDomainH1ZeroSigma Ω) :
    Tendsto (fun m => OpenDomainConvectionLimit.energyToBoxState Ω
        (S.energyProjection m φ)) atTop
      (nhds (OpenDomainConvectionLimit.energyToBoxState Ω φ)) :=
  ((OpenDomainConvectionLimit.energyToBoxState Ω).continuous.tendsto φ).comp
    (S.energyProjection_tendsto φ)

/-- The scalar pairing on the right of the tested equation converges, for any
convergent sequence of pivot states. -/
theorem inner_energyToBoxState_energyProjection_tendsto
    (S : OpenDomainCompactSpectralRepresentation Ω)
    (φ : OpenDomainH1ZeroSigma Ω)
    (v : ℕ → BoxL2Sigma Q) (vLim : BoxL2Sigma Q)
    (hv : Tendsto v atTop (nhds vLim)) {lev : ℕ → ℕ}
    (hlev : Tendsto lev atTop atTop) :
    Tendsto (fun k => ⟪v k, OpenDomainConvectionLimit.energyToBoxState Ω
        (S.energyProjection (lev k) φ)⟫_ℝ) atTop
      (nhds ⟪vLim, OpenDomainConvectionLimit.energyToBoxState Ω φ⟫_ℝ) :=
  hv.inner ((energyToBoxState_energyProjection_tendsto S φ).comp hlev)

/-! ### The initial data in the limit -/

/-- **Criterion for the initial term.**  Convergence of the initial
coefficients in the pivot space is exactly what the limit theorem needs; by
`energyToBoxState_energySynthesis` the energy synthesis contributes nothing,
so the levels may grow arbitrarily. -/
theorem initialPairing_tendsto_of_state_tendsto
    (S : OpenDomainCompactSpectralRepresentation Ω) {lev : ℕ → ℕ}
    (init : ∀ k, S.stateSpace (lev k)) (x₀ : OpenDomainL2Sigma Ω)
    (hinit : Tendsto (fun k => (init k : OpenDomainL2Sigma Ω)) atTop
      (nhds x₀)) :
    Tendsto (fun k => OpenDomainConvectionLimit.energyToBoxState Ω
        (S.energySynthesis (lev k) (init k))) atTop
      (nhds (openDomainStateToBox Ω x₀)) :=
  Tendsto.congr
    (fun k => (energyToBoxState_energySynthesis S (lev k) (init k)).symm)
    (((openDomainStateToBox Ω).continuous.tendsto x₀).comp hinit)

/-- **The canonical instance.**  The initial coefficients are the spectral
projections of one fixed element of the pivot space -- the choice
`OpenDomainUnforcedUniformBounds.stateHeadProjection` already uses for the
unforced family -- and their synthesised states converge to that element read
in the rectangle. -/
theorem initialPairing_stateHeadProjection_tendsto
    (S : OpenDomainCompactSpectralRepresentation Ω)
    (x₀ : OpenDomainL2Sigma Ω) {lev : ℕ → ℕ}
    (hlev : Tendsto lev atTop atTop) :
    Tendsto (fun k => OpenDomainConvectionLimit.energyToBoxState Ω
        (S.energySynthesis (lev k)
          (OpenDomainUnforcedUniformBounds.stateHeadProjection S (lev k) x₀)))
      atTop (nhds (openDomainStateToBox Ω x₀)) :=
  initialPairing_tendsto_of_state_tendsto S
    (fun k => OpenDomainUnforcedUniformBounds.stateHeadProjection S (lev k) x₀)
    x₀ (S.stateProjection_comp_tendsto x₀ hlev)

/-! ### The limit equation without projections -/

/-- **The tested weak equation in the limit for unprojected data.**

The Galerkin data are canonical: at level `lev k` the initial coefficient is
the spectral projection of a fixed `x₀ : OpenDomainL2Sigma Ω`, the spatial test
is a fixed `φ`, and `u k` is an actual solution of the unforced coefficient
system.  Only the time-compactness hypotheses of
`OpenDomainGalerkinTestIdentity.tested_weak_equation_limit_of_galerkin` remain
assumed; its two projection hypotheses are discharged by the statements above,
and the resulting equation is tested by `φ` itself against the initial state
`x₀` itself. -/
theorem tested_weak_equation_limit_of_projected_data
    (L : BoxLadyzhenskayaRealization Q)
    (S : OpenDomainCompactSpectralRepresentation Ω)
    {a b : ℝ} (hab : a ≤ b)
    (eta : LerayIntervalTimeTest a b) (heta : eta.value b = 0)
    (lev : ℕ → ℕ) (hlev : Tendsto lev atTop atTop)
    (x₀ : OpenDomainL2Sigma Ω)
    (u : ∀ k, (unforcedProblem Ω L.toBoxEnergyL4Realization S (lev k)
        (OpenDomainUnforcedUniformBounds.stateHeadProjection S (lev k)
          x₀)).LocalSolutionOn (⟨a, le_rfl, hab⟩ : Icc a b))
    (φ : OpenDomainH1ZeroSigma Ω)
    (wLim : Lp (OpenDomainH1ZeroSigma Ω) (2 : ℝ≥0∞)
      (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b))
    (R : ℝ) (hbound : ∀ k, ‖energyPathLp hab (u k)‖ ≤ R)
    (Rs : ℝ) (hRs : ∀ k,
      ‖(OpenDomainConvectionLimit.energyToBoxState Ω).compLpL 2
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)
        (energyPathLp hab (u k))‖ ≤ Rs)
    (hstate : Tendsto
      (fun k => (OpenDomainConvectionLimit.energyToBoxState Ω).compLpL 2
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b)
        (energyPathLp hab (u k)))
      atTop
      (nhds ((OpenDomainConvectionLimit.energyToBoxState Ω).compLpL 2
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) wLim)))
    (hweak : ∀ Λ : Lp (OpenDomainH1ZeroSigma Ω) (2 : ℝ≥0∞)
        (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) →L[ℝ] ℝ,
      Tendsto (fun k => Λ (energyPathLp hab (u k))) atTop (nhds (Λ wLim))) :
    -stateTestIntegral eta
        ((OpenDomainConvectionLimit.energyToBoxState Ω).compLpL 2
          (SmoothBoxVariationalGalerkinLevel.intervalSubtypeMeasure a b) wLim)
        (OpenDomainConvectionLimit.energyToBoxState Ω φ) +
      diffusionTestIntegral Ω eta.toIntervalTimeTest wLim φ +
      convectionTestIntegral Ω L.toBoxEnergyL4Realization
        eta.toIntervalTimeTest wLim φ =
    ⟪openDomainStateToBox Ω x₀,
      OpenDomainConvectionLimit.energyToBoxState Ω φ⟫_ℝ * eta.value a :=
  tested_weak_equation_limit_of_galerkin L S hab eta heta lev
    (fun k => OpenDomainUnforcedUniformBounds.stateHeadProjection S (lev k) x₀)
    u φ wLim R hbound Rs hRs hstate hweak φ
    (S.energyProjection_comp_tendsto φ hlev) (openDomainStateToBox Ω x₀)
    (initialPairing_stateHeadProjection_tendsto S x₀ hlev)

end OpenDomainProjectedTestConvergence
