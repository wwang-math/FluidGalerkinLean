import PDEIdeas.BoxLerayHopf

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

Mathlib supplies the divergence theorem, Gagliardo-Nirenberg-Sobolev inequality,
multi-torus Fourier theory, compact self-adjoint spectral theorem, Riesz
representation, Picard-Lindelof, Arzela-Ascoli, and Bochner integration.
-/
