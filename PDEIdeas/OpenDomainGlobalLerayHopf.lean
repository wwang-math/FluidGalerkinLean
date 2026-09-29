import PDEIdeas.OpenDomainGlobalLocalSolutions

/-! An unforced Leray--Hopf trajectory on the nonnegative time axis. -/

open Filter InnerProductSpace MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace OpenDomainGlobalLerayHopf

variable {Q : BoxIntegral.Box (Fin 2)} (Ω : OpenDomainInBox Q)
  (L : BoxLadyzhenskayaRealization Q)
  (S : OpenDomainCompactSpectralRepresentation Ω)
  (u₀ : OpenDomainL2Sigma Ω)

abbrev NonnegativeTime := Ici (0 : ℝ)

structure GlobalSolution where
  statePath : NonnegativeTime → OpenDomainL2Sigma Ω
  localSolution : ∀ n : ℕ,
    OpenDomainLerayHopfStatement.SolutionOn Ω L u₀ (Nat.cast_nonneg n)
  state_restrict : ∀ (n : ℕ) (t : Icc (0 : ℝ) (n : ℝ)),
    statePath ⟨t.1, t.2.1⟩ = (localSolution n).statePath t

def statePathOfSubsequence
    (D : OpenDomainGlobalProjectedCompactness.ProjectedSubsequence Ω L S u₀)
    (t : NonnegativeTime) : OpenDomainL2Sigma Ω :=
  (OpenDomainGlobalLocalSolutions.solution Ω L S u₀ D (Nat.ceil t.1)).statePath
    ⟨t.1, t.2, Nat.le_ceil t.1⟩

theorem statePathOfSubsequence_restrict
    (D : OpenDomainGlobalProjectedCompactness.ProjectedSubsequence Ω L S u₀)
    (n : ℕ) (t : Icc (0 : ℝ) (n : ℝ)) :
    statePathOfSubsequence Ω L S u₀ D ⟨t.1, t.2.1⟩ =
      (OpenDomainGlobalLocalSolutions.solution Ω L S u₀ D n).statePath t := by
  let c := Nat.ceil (t : ℝ)
  have htc : (t : ℝ) ≤ (c : ℝ) := Nat.le_ceil (t : ℝ)
  rcases le_total n c with h | h
  · exact (OpenDomainGlobalLocalSolutions.solution_statePath_eqOn
      Ω L S u₀ D n c h t).symm
  · exact OpenDomainGlobalLocalSolutions.solution_statePath_eqOn
      Ω L S u₀ D c n h ⟨t.1, t.2.1, htc⟩

def solutionOfSubsequence
    (D : OpenDomainGlobalProjectedCompactness.ProjectedSubsequence Ω L S u₀) :
    GlobalSolution Ω L u₀ where
  statePath := statePathOfSubsequence Ω L S u₀ D
  localSolution := OpenDomainGlobalLocalSolutions.solution Ω L S u₀ D
  state_restrict := statePathOfSubsequence_restrict Ω L S u₀ D

theorem exists_globalSolution
    (S : OpenDomainCompactSpectralRepresentation Ω) :
    Nonempty (GlobalSolution Ω L u₀) := by
  obtain ⟨D⟩ := OpenDomainGlobalProjectedCompactness.exists_projectedSubsequence
    Ω L S u₀
  exact ⟨solutionOfSubsequence Ω L S u₀ D⟩

theorem GlobalSolution.initial (U : GlobalSolution Ω L u₀) :
    U.statePath ⟨0, by simp [NonnegativeTime]⟩ = u₀ := by
  rw [U.state_restrict 0 ⟨0, by simp, by simp⟩]
  exact (U.localSolution 0).initial

private def clip (n : ℕ) (t : NonnegativeTime) : Icc (0 : ℝ) (n : ℝ) :=
  ⟨min t.1 (n : ℝ), le_min t.2 (Nat.cast_nonneg n), min_le_right _ _⟩

private theorem continuous_clip (n : ℕ) : Continuous (clip n) :=
  Continuous.subtype_mk (continuous_subtype_val.min continuous_const) _

theorem GlobalSolution.weaklyContinuous
    (U : GlobalSolution Ω L u₀) (y : OpenDomainL2Sigma Ω) :
    Continuous (fun t : NonnegativeTime => ⟪U.statePath t, y⟫_ℝ) := by
  rw [continuous_iff_continuousAt]
  intro t
  let n := Nat.ceil (t : ℝ) + 1
  have ht : (t : ℝ) < (n : ℝ) := by
    have hceil := Nat.le_ceil (t : ℝ)
    have hsucc : ((Nat.ceil (t : ℝ) : ℕ) : ℝ) < (n : ℝ) := by
      exact_mod_cast Nat.lt_succ_self (Nat.ceil (t : ℝ))
    exact lt_of_le_of_lt hceil hsucc
  have hmem : t ∈ ((Subtype.val : NonnegativeTime → ℝ) ⁻¹' Iio (n : ℝ)) := ht
  have hnear : ∀ᶠ s : NonnegativeTime in nhds t, (s : ℝ) < (n : ℝ) :=
    (isOpen_Iio.preimage continuous_subtype_val).mem_nhds hmem
  have hagree : (fun s : NonnegativeTime => ⟪U.statePath s, y⟫_ℝ) =ᶠ[nhds t]
      (fun s => ⟪(U.localSolution n).statePath (clip n s), y⟫_ℝ) := by
    filter_upwards [hnear] with s hs
    have hsle : (s : ℝ) ≤ (n : ℝ) := le_of_lt hs
    let q : Icc (0 : ℝ) (n : ℝ) := ⟨s.1, s.2, hsle⟩
    have hq : clip n s = q := by
      apply Subtype.ext
      exact min_eq_left hsle
    rw [hq]
    exact congrArg (fun z => ⟪z, y⟫_ℝ) (U.state_restrict n q)
  have hlocal : ContinuousAt
      (fun s : NonnegativeTime =>
        ⟪(U.localSolution n).statePath (clip n s), y⟫_ℝ) t :=
    ((U.localSolution n).weaklyContinuous y).comp
      (continuous_clip n) |>.continuousAt
  exact hlocal.congr_of_eventuallyEq hagree

theorem GlobalSolution.energyInequality
    (U : GlobalSolution Ω L u₀) (n : ℕ)
    (t : Icc (0 : ℝ) (n : ℝ)) :
    ‖U.statePath ⟨t.1, t.2.1⟩‖ ^ 2 +
      2 * ∫ s in Iic t,
        ‖openDomainEnergyGradient Ω ((U.localSolution n).energyPath s)‖ ^ 2
          ∂OpenDomainIntervalMeasureBridge.timeMeasure 0 (n : ℝ) ≤
      ‖u₀‖ ^ 2 := by
  rw [U.state_restrict n t]
  exact (U.localSolution n).energyInequality t

theorem GlobalSolution.weakEquation
    (U : GlobalSolution Ω L u₀) (n : ℕ)
    (eta : LerayIntervalTimeTest 0 (n : ℝ))
    (heta : eta.value (n : ℝ) = 0)
    (φ : OpenDomainH1ZeroSigma Ω) :
    OpenDomainConcreteWeakEquation.TestedEquation Ω L u₀
      (U.localSolution n).energyPath eta φ :=
  (U.localSolution n).weakEquation eta heta φ

end OpenDomainGlobalLerayHopf

end
