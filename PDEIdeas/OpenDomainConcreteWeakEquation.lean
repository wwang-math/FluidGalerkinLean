import PDEIdeas.OpenDomainConcreteEnergyLimit
import PDEIdeas.OpenDomainProjectedTestConvergence

/-! The canonical Galerkin family satisfies the tested weak equation in the limit. -/

open Filter InnerProductSpace MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 400000

namespace OpenDomainConcreteWeakEquation

variable {Q : BoxIntegral.Box (Fin 2)} (Ω : OpenDomainInBox Q)
  (L : BoxLadyzhenskayaRealization Q)
  (S : OpenDomainCompactSpectralRepresentation Ω)
  (u₀ : OpenDomainL2Sigma Ω) {T : ℝ} (hT : 0 ≤ T)

private def G := OpenDomainConcreteCompactFamily.compactFamily Ω L S u₀ hT

local instance openDomainEnergyComplete (Ω : OpenDomainInBox Q) :
    CompleteSpace (OpenDomainH1ZeroSigma Ω) :=
  openDomainH1ZeroSigma_completeSpace Ω

local instance openDomainStateComplete (Ω : OpenDomainInBox Q) :
    CompleteSpace (OpenDomainL2Sigma Ω) :=
  openDomainL2Sigma_completeSpace Ω

private theorem energyPathLp_eq (m : ℕ) :
    OpenDomainGalerkinTestIdentity.energyPathLp hT
      (OpenDomainUnforcedUniformBounds.solution Ω
        L.toBoxEnergyL4Realization S m u₀ hT) =
      (G Ω L S u₀ hT).energyLp m := by
  rfl

private theorem compLpL_comp
    {E F K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (A : F →L[ℝ] K) (B : E →L[ℝ] F) :
    (A.compLpL 2 μ).comp (B.compLpL 2 μ) =
      (A.comp B).compLpL 2 μ := by
  ext f
  filter_upwards [A.coeFn_compLpL ((B.compLpL 2 μ) f),
    B.coeFn_compLpL f, (A.comp B).coeFn_compLpL f] with x hA hB hAB
  simp only [ContinuousLinearMap.comp_apply]
  rw [hA, hB, hAB]
  rfl

private theorem embed_eq :
    (G Ω L S u₀ hT).embed = openDomainEnergyToState Ω := rfl

private theorem boxState_comp :
    (openDomainStateToBox Ω).comp (openDomainEnergyToState Ω) =
      OpenDomainConvectionLimit.energyToBoxState Ω := by
  apply ContinuousLinearMap.ext
  intro w
  exact (OpenDomainGalerkinTestIdentity.energyToBoxState_eq Ω w).symm

private theorem boxStateLp_eq (w : Lp (OpenDomainH1ZeroSigma Ω)
    (2 : ℝ≥0∞) (OpenDomainIntervalMeasureBridge.timeMeasure 0 T)) :
    ((openDomainStateToBox Ω).compLpL 2
      (OpenDomainIntervalMeasureBridge.timeMeasure 0 T))
        ((openDomainEnergyToState Ω).compLpL 2
          (OpenDomainIntervalMeasureBridge.timeMeasure 0 T) w) =
      (OpenDomainConvectionLimit.energyToBoxState Ω).compLpL 2
        (OpenDomainIntervalMeasureBridge.timeMeasure 0 T) w := by
  let μ := OpenDomainIntervalMeasureBridge.timeMeasure 0 T
  let A := openDomainStateToBox Ω
  let B := openDomainEnergyToState Ω
  have hcomp : (A.compLpL 2 μ).comp (B.compLpL 2 μ) =
      (OpenDomainConvectionLimit.energyToBoxState Ω).compLpL 2 μ :=
    (compLpL_comp μ A B).trans (congrArg (fun C => C.compLpL 2 μ)
      (boxState_comp Ω))
  exact congrArg (fun C => C w) hcomp

/-- The unforced tested equation for a time-energy path. -/
def TestedEquation
    (w : Lp (OpenDomainH1ZeroSigma Ω) (2 : ℝ≥0∞)
      (OpenDomainIntervalMeasureBridge.timeMeasure 0 T))
    (eta : LerayIntervalTimeTest 0 T) (φ : OpenDomainH1ZeroSigma Ω) : Prop :=
    -OpenDomainWeakEquationLimit.stateTestIntegral eta
        ((OpenDomainConvectionLimit.energyToBoxState Ω).compLpL 2
          (OpenDomainIntervalMeasureBridge.timeMeasure 0 T) w)
        (OpenDomainConvectionLimit.energyToBoxState Ω φ) +
      OpenDomainWeakEquationLimit.diffusionTestIntegral Ω
        eta.toIntervalTimeTest w φ +
      OpenDomainWeakEquationLimit.convectionTestIntegral Ω
        L.toBoxEnergyL4Realization eta.toIntervalTimeTest w φ =
    ⟪openDomainStateToBox Ω u₀,
      OpenDomainConvectionLimit.energyToBoxState Ω φ⟫_ℝ * eta.value 0

/-- The weak equation obtained from the canonical unforced Galerkin solutions. -/
theorem tested_weak_equation
    (SW : (G Ω L S u₀ hT).StrongWeakPathSubsequence)
    (eta : LerayIntervalTimeTest 0 T) (heta : eta.value T = 0)
    (φ : OpenDomainH1ZeroSigma Ω) :
    TestedEquation Ω L u₀ SW.energyLimit eta φ := by
  letI : CompleteSpace (OpenDomainH1ZeroSigma Ω) :=
    openDomainH1ZeroSigma_completeSpace Ω
  letI : CompleteSpace (OpenDomainL2Sigma Ω) :=
    openDomainL2Sigma_completeSpace Ω
  let G₀ := G Ω L S u₀ hT
  let μ := OpenDomainIntervalMeasureBridge.timeMeasure 0 T
  let A := (OpenDomainConvectionLimit.energyToBoxState Ω).compLpL 2 μ
  let u := fun k => OpenDomainUnforcedUniformBounds.solution Ω
    L.toBoxEnergyL4Realization S (SW.subseq.idx k) u₀ hT
  let w := fun k => OpenDomainGalerkinTestIdentity.energyPathLp hT (u k)
  have hbound : ∀ k, ‖w k‖ ≤ G₀.liftLpRadius := by
    intro k
    calc
      _ = ‖G₀.energyLp (SW.subseq.idx k)‖ :=
        congrArg norm (energyPathLp_eq Ω L S u₀ hT _)
      _ ≤ G₀.liftLpRadius := G₀.energyLp_norm_le _
  have hstate₀ : Tendsto (fun k =>
      ((openDomainStateToBox Ω).compLpL 2 μ) (G₀.stateLp (SW.subseq.idx k)))
      atTop (nhds (((openDomainStateToBox Ω).compLpL 2 μ) SW.stateLimit)) :=
    (((openDomainStateToBox Ω).compLpL 2 μ).continuous.tendsto SW.stateLimit).comp
      SW.state_strong
  have hstate : Tendsto (fun k => A (w k))
      atTop (nhds (A SW.energyLimit)) := by
    have hterm (k : ℕ) : A (w k) =
        ((openDomainStateToBox Ω).compLpL 2 μ)
          (G₀.stateLp (SW.subseq.idx k)) := by
      have h₁ : G₀.stateLp (SW.subseq.idx k) =
          (openDomainEnergyToState Ω).compLpL 2 μ
            (G₀.energyLp (SW.subseq.idx k)) := by
        calc
          _ = G₀.embed.compLpL 2 μ
                (G₀.energyLp (SW.subseq.idx k)) :=
              G₀.stateLp_eq_embed_energyLp _
          _ = _ := congrArg
            (fun B => B.compLpL 2 μ (G₀.energyLp (SW.subseq.idx k)))
            (embed_eq Ω L S u₀ hT)
      calc
        _ = A (G₀.energyLp (SW.subseq.idx k)) :=
          congrArg A (energyPathLp_eq Ω L S u₀ hT _)
        _ = ((openDomainStateToBox Ω).compLpL 2 μ)
              ((openDomainEnergyToState Ω).compLpL 2 μ
                (G₀.energyLp (SW.subseq.idx k))) :=
          (boxStateLp_eq Ω (T := T) _).symm
        _ = _ := congrArg ((openDomainStateToBox Ω).compLpL 2 μ) h₁.symm
    have hlim : A SW.energyLimit =
        ((openDomainStateToBox Ω).compLpL 2 μ) SW.stateLimit := by
      have h₁ : SW.stateLimit =
          (openDomainEnergyToState Ω).compLpL 2 μ SW.energyLimit := by
        calc
          _ = G₀.embed.compLpL 2 μ SW.energyLimit := SW.embed_energyLimit.symm
          _ = _ := congrArg (fun B => B.compLpL 2 μ SW.energyLimit)
            (embed_eq Ω L S u₀ hT)
      calc
        _ = ((openDomainStateToBox Ω).compLpL 2 μ)
              ((openDomainEnergyToState Ω).compLpL 2 μ SW.energyLimit) :=
          (boxStateLp_eq Ω (T := T) _).symm
        _ = _ := congrArg ((openDomainStateToBox Ω).compLpL 2 μ) h₁.symm
    have hstate₁ := Tendsto.congr (fun k => (hterm k).symm) hstate₀
    convert hstate₁ using 1
    exact congrArg nhds hlim
  have hnorm : Tendsto (fun k => ‖A (w k)‖) atTop
      (nhds ‖A SW.energyLimit‖) :=
    (continuous_norm.tendsto (A SW.energyLimit)).comp hstate
  obtain ⟨Rs, hRs₀⟩ := hnorm.bddAbove_range
  have hRs : ∀ k, ‖A (w k)‖ ≤ Rs := by
    intro k
    exact hRs₀ ⟨k, rfl⟩
  have hweak : ∀ Λ : Lp (OpenDomainH1ZeroSigma Ω) (2 : ℝ≥0∞) μ →L[ℝ] ℝ,
      Tendsto (fun k => Λ (w k))
        atTop (nhds (Λ SW.energyLimit)) := by
    intro Λ
    have h := @LeraySpectralCompactFamily.StrongWeakSubsequence.energy_clm_tendsto
      (Icc (0 : ℝ) T) (OpenDomainH1ZeroSigma Ω) (OpenDomainL2Sigma Ω)
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance (openDomainH1ZeroSigma_completeSpace Ω)
      inferInstance inferInstance
      μ inferInstance G₀ SW.toStrongWeakSubsequence Λ
    exact Tendsto.congr
      (fun k => congrArg Λ (energyPathLp_eq Ω L S u₀ hT _).symm) h
  exact OpenDomainProjectedTestConvergence.tested_weak_equation_limit_of_projected_data
    L S hT eta heta SW.subseq.idx SW.subseq.strictMono_idx.tendsto_atTop
    u₀ (fun k => OpenDomainUnforcedUniformBounds.solution Ω
      L.toBoxEnergyL4Realization S (SW.subseq.idx k) u₀ hT)
    φ SW.energyLimit G₀.liftLpRadius hbound Rs hRs hstate hweak


end OpenDomainConcreteWeakEquation

end
