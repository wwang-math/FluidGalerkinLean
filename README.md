# FluidGalerkinLean

Lean 4 source for the Galerkin construction of two-dimensional Leray-Hopf weak solutions on rectangular boxes.

Principal theorem: `exists_zeroForcing_twoDimensional_lerayHopfSolution`
(`PDEIdeas/BoxLerayHopf.lean`).

Box Poincare inequality and forcing absorption: `boxPoincare`,
`boxEnergy_norm_le_gradient`, `boxForcing_work_le` (`PDEIdeas/BoxPoincare.lean`).

Forced Galerkin family and its synchronized limit:
`exists_forced_twoDimensional_galerkinCompactness`
(`PDEIdeas/BoxForcedSpectralGalerkin.lean`).

Forced principal theorem: `exists_forced_twoDimensional_lerayHopfSolution`
(`PDEIdeas/BoxForcedLerayHopf.lean`).

```sh
lake exe cache get
lake build
lake build +PDEIdeas.PaperClaimChecks +PDEIdeas.PaperAxiomAudit
```
