import PDEIdeas.CompactEmbeddingSpectral
import PDEIdeas.EnergyConvectionForm

/-!
# Variational dynamics on abstract spectral state heads

`CompactEmbeddingSpectralRepresentation J` supplies the finite state heads
`S.stateSpace m` of a compact dense injection `J : V → H`, and
`VariationalGalerkin` supplies the finite-dimensional theory of a
`VariationalGalerkinProblem`: energy-driven existence on a prescribed interval,
the energy identity, and the a priori bound with dissipation.

Nothing connects the two.  A state head is a submodule of `H`, so the
completeness instance that every one of those theorems demands is not in scope
there, and the variational data live on `V`, so the forms must be pulled back
along an energy lift before any of them applies.  This file supplies exactly
that application layer, once, for an arbitrary representation.

The ODE is not reproved.  `exists_solutionOn_of_energy_budget`,
`LocalSolutionOn.energyIdentityOn` and
`LocalSolutionOn.aprioriBoundWithDissipationAtTime` are used as given, and
`EnergyConvectionForm.pullbackSystem` supplies the pulled-back system.

## Main statements

* `CompactEmbeddingSpectralRepresentation.spectralProblem`: the level-`m`
  variational problem carried by the spectral state head.
* `CompactEmbeddingSpectralRepresentation.exists_spectralSolutionOn`: every
  level carries a solution on the whole prescribed interval.
* `CompactEmbeddingSpectralRepresentation.spectralSolution_energyIdentityOn`
  and `..._aprioriBoundAtTime`: the energy identity and the energy-dissipation
  bound at the head, with the integrability side conditions discharged and the
  integrands written in the original forms.

## What this layer actually contributes

* Completeness of the head.  The head is finite dimensional, hence complete;
  supplied here as an instance, in the exact instance spelling those theorems
  ask for, so that they can be named at all on `S.stateSpace m`.
* The forcing bound.  `exists_solutionOn_of_energy_budget` wants a uniform
  bound on the dual norm of the forcing over the interval; continuity plus
  compactness of the interval produce it, so the caller never supplies it.
* Transport of absorption.  The caller states the Young-type absorption
  `2 * F t u ≤ g t + D u u` on the energy space `V`, which is where a Poincaré
  or Ladyzhenskaya estimate lives.  Each statement below instantiates it at the
  lifted trajectory, so nothing has to be restated at coefficient level.

## The energy lift

The lift `E : S.stateSpace m →L[ℝ] V` is a parameter, not a construction.  The
dynamics never uses a section property such as `J (E u) = u`, so leaving the
lift free keeps this layer independent of any particular tower construction and
lets a caller pass whichever lift its tower already provides.
-/

open InnerProductSpace MeasureTheory Set

noncomputable section

namespace CompactEmbeddingSpectralRepresentation

section Level

variable {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {J : V →L[ℝ] H}
variable (S : CompactEmbeddingSpectralRepresentation J) (m : ℕ)

/-- A spectral state head is spanned by finitely many basis vectors. -/
instance stateHeadFiniteDimensional :
    FiniteDimensional ℝ (S.stateSpace m) :=
  GalerkinProjectorSequence.finitePartialSpace_finiteDimensional
    S.stateBasis (S.exhaustion.head m)

/-- A spectral state head is therefore a Banach space, which is what the
finite-dimensional variational theorems require of their coefficient space.

The uniform structure is written out along the subspace-norm path rather than
left to instance search, which prefers the subtype uniformity on `↥(stateSpace
m)`.  The two are definitionally equal, but only the spelling below is the one
`VariationalGalerkinProblem.LocalSolutionOn` asks for, so only this spelling is
found where those theorems are applied. -/
instance stateHeadCompleteSpace :
    @CompleteSpace (S.stateSpace m)
      (@PseudoMetricSpace.toUniformSpace _
        (@SeminormedAddCommGroup.toPseudoMetricSpace _
          (@NormedAddCommGroup.toSeminormedAddCommGroup _
            (inferInstance : NormedAddCommGroup (S.stateSpace m))))) := by
  have hcomplete : CompleteSpace (S.stateSpace m) := by
    letI : IsUniformAddGroup (S.stateSpace m) :=
      (S.stateSpace m).toAddSubgroup.isUniformAddGroup
    exact FiniteDimensional.complete ℝ _
  exact hcomplete

variable (E : S.stateSpace m →L[ℝ] V)
    (C : EnergyConvectionForm V)
    (D : V →L[ℝ] V →L[ℝ] ℝ) (hD : ∀ u, 0 ≤ D u u)
    (F : ℝ → V →L[ℝ] ℝ)

/-- The level-`m` variational Galerkin problem carried by the spectral state
head: energy diffusion and convection pulled back along the lift, forcing
tested through the lift, and a prescribed initial state. -/
def spectralProblem (initial : S.stateSpace m) :
    VariationalGalerkinProblem (S.stateSpace m) where
  system := C.pullbackSystem E D hD
  forcing := fun t => (F t).comp E
  initial := initial

@[simp]
theorem spectralProblem_initial (initial : S.stateSpace m) :
    (S.spectralProblem m E C D hD F initial).initial = initial :=
  rfl

@[simp]
theorem spectralProblem_forcing_apply (initial : S.stateSpace m)
    (t : ℝ) (x : S.stateSpace m) :
    (S.spectralProblem m E C D hD F initial).forcing t x = F t (E x) :=
  rfl

@[simp]
theorem spectralProblem_diffusion_apply (initial : S.stateSpace m)
    (x y : S.stateSpace m) :
    (S.spectralProblem m E C D hD F initial).system.diffusion x y =
      D (E x) (E y) :=
  rfl

@[simp]
theorem spectralProblem_convection_apply (initial : S.stateSpace m)
    (x y z : S.stateSpace m) :
    (S.spectralProblem m E C D hD F initial).system.convection x y z =
      C.form (E x) (E y) (E z) :=
  rfl

/-- Continuity of the forcing survives testing through the lift. -/
theorem spectralProblem_forcing_continuous (initial : S.stateSpace m)
    (hF : Continuous F) :
    Continuous (S.spectralProblem m E C D hD F initial).forcing := by
  have hcomp : Continuous fun G : V →L[ℝ] ℝ => G.comp E := by fun_prop
  exact hcomp.comp hF

/-- **Existence at every spectral level.**  A bounded skew convection form, a
nonnegative diffusion form, and a forcing that is continuous and absorbed by
the diffusion form up to an integrable majorant closing the energy budget give
a solution of the level-`m` coefficient system on the whole interval.

The absorption hypothesis `hwork` is stated on the energy space `V`, where a
Poincaré or Ladyzhenskaya estimate produces it; it is instantiated at the
lifted state here.  No uniform forcing bound is requested: continuity on the
compact interval supplies one. -/
theorem exists_spectralSolutionOn (initial : S.stateSpace m)
    (hF : Continuous F)
    {a b : ℝ} (hab : a ≤ b)
    (g : ℝ → ℝ)
    (hgint : IntervalIntegrable g volume a b)
    (hg_nonneg : ∀ t ∈ Icc a b, 0 ≤ g t)
    (hwork : ∀ t ∈ Icc a b, ∀ u : V, 2 * F t u ≤ g t + D u u)
    (R : ℝ) (hR : 0 ≤ R)
    (hbudget : ‖initial‖ ^ 2 + ∫ s in a..b, g s ≤ R ^ 2) :
    Nonempty ((S.spectralProblem m E C D hD F initial).LocalSolutionOn
      (⟨a, le_rfl, hab⟩ : Icc a b)) := by
  have hFcont :=
    S.spectralProblem_forcing_continuous m E C D hD F initial hF
  obtain ⟨M₀, hM₀⟩ :=
    (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
      hFcont.continuousOn
  refine (S.spectralProblem m E C D hD F initial).exists_solutionOn_of_energy_budget
    hab hFcont (max M₀ 0) R (le_max_right _ _) hR ?_ g hgint hg_nonneg ?_ ?_
  · intro t ht
    exact (hM₀ t ht).trans (le_max_left _ _)
  · intro t ht x
    exact hwork t ht (E x)
  · exact hbudget

/-- **Energy identity at the spectral state head.**  The two integrability side
conditions of the finite-dimensional identity are automatic for a coefficient
trajectory with continuous forcing, and the integrands are the original energy
forms evaluated along the lifted trajectory. -/
theorem spectralSolution_energyIdentityOn (initial : S.stateSpace m)
    (hF : Continuous F)
    {tmin tmax : ℝ} {t₀ : Icc tmin tmax}
    (u : (S.spectralProblem m E C D hD F initial).LocalSolutionOn t₀)
    {a b : ℝ} (ha : a ∈ Icc tmin tmax) (hb : b ∈ Icc tmin tmax)
    (hab : a ≤ b) :
    ‖u.toFun b‖ ^ 2
      + 2 * ∫ s in a..b, D (E (u.toFun s)) (E (u.toFun s))
      = ‖u.toFun a‖ ^ 2 + 2 * ∫ s in a..b, F s (E (u.toFun s)) :=
  u.energyIdentityOn ha hb hab
    (u.diffusion_intervalIntegrable ha hb hab)
    (u.forcing_intervalIntegrable
      (S.spectralProblem_forcing_continuous m E C D hD F initial hF)
      ha hb hab)

/-- **Energy and dissipation bound at the spectral state head.**  The same
energy-space absorption that drives existence bounds the state norm and the
accumulated dissipation at every time, with the initial state of the level-`m`
problem on the right. -/
theorem spectralSolution_aprioriBoundAtTime (initial : S.stateSpace m)
    (hF : Continuous F)
    {tmax : ℝ} (t₀ : Icc (0 : ℝ) tmax) (hzero : (t₀ : ℝ) = 0)
    (u : (S.spectralProblem m E C D hD F initial).LocalSolutionOn t₀)
    (g : ℝ → ℝ) {T : ℝ} (hT : T ∈ Icc (0 : ℝ) tmax)
    (hgint : IntervalIntegrable g volume 0 T)
    (hwork : ∀ t ∈ Icc (0 : ℝ) T, ∀ v : V, 2 * F t v ≤ g t + D v v) :
    ‖u.toFun T‖ ^ 2 + ∫ s in (0 : ℝ)..T, D (E (u.toFun s)) (E (u.toFun s))
      ≤ ‖initial‖ ^ 2 + ∫ s in (0 : ℝ)..T, g s := by
  have hzeroMem : (0 : ℝ) ∈ Icc (0 : ℝ) tmax := ⟨le_rfl, hT.1.trans hT.2⟩
  have hAint :=
    u.diffusion_intervalIntegrable hzeroMem hT hT.1
  have hFint :=
    u.forcing_intervalIntegrable
      (S.spectralProblem_forcing_continuous m E C D hD F initial hF)
      hzeroMem hT hT.1
  exact u.aprioriBoundWithDissipationAtTime t₀ hzero g hT hAint hFint hgint
    fun s hs => hwork s hs (E (u.toFun s))

end Level

end CompactEmbeddingSpectralRepresentation

end
