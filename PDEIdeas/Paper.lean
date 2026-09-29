import PDEIdeas.BoxLerayHopf
import PDEIdeas.BoxForcedLerayHopf
import PDEIdeas.OpenDomainGlobalBoundedEnclosure

/-!
# The paper's import surface

For a two-dimensional rectangular box, every solenoidal initial state and
every nonempty finite interval have an unforced, unit-viscosity weak solution.
The solution has compatible Bochner state and energy representatives, a weakly
continuous state representative attaining the datum, and an energy inequality
at every time. The endpoint is
`exists_zeroForcing_twoDimensional_lerayHopfSolution`.

The main intermediate constructions are transport integration by parts,
`boxEnergyToState_isCompactOperator_fourier`,
`compactEmbeddingSpectralRepresentation`, `boxLadyzhenskayaRealization`,
`BoxCompactSpectralRepresentation.exists_zeroForcingSolution2D`, and
`BoxCompactSpectralRepresentation.exists_zeroForcing_twoDimensional_strongWeakPath_subsequence`.

The box Poincaré inequality `boxPoincare` makes the energy norm equivalent to
the gradient seminorm, so `boxForcing_work_le` absorbs a continuous
energy-dual forcing with a continuous nonnegative dual-norm majorant into the
diffusion form with a state-independent remainder. The same conclusions then
hold for the driven problem: the forced endpoint is
`exists_forced_twoDimensional_lerayHopfSolution`, whose weak equation carries
the forcing term and whose energy inequality carries the accumulated work.

For an arbitrary bounded open planar domain, the unforced endpoint is
`OpenDomainGlobalBoundedEnclosure.exists_global_solution`. It constructs one
weakly continuous state path on nonnegative time with finite-horizon energy
representatives, the tested weak equation, and the energy inequality.

Mathlib supplies the divergence theorem, Gagliardo-Nirenberg-Sobolev inequality,
multi-torus Fourier theory, compact self-adjoint spectral theorem, Riesz
representation, Picard-Lindelof, Arzela-Ascoli, and Bochner integration.
-/
