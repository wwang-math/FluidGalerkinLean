import PDEIdeas.CompactnessInterface

open Filter

noncomputable section

/-- An extracted subsequence of the natural numbers. -/
structure ExtractedSubsequence where
  idx : ℕ → ℕ
  strictMono_idx : StrictMono idx

namespace ExtractedSubsequence

/-- The identity extraction, useful when a family already converges or is
constant. -/
def identity : ExtractedSubsequence where
  idx := fun n => n
  strictMono_idx := by
    intro m n hmn
    exact hmn

/-- Pull a family back along an extracted subsequence. -/
def pull {α : Type*} (σ : ExtractedSubsequence) (U : ℕ → α) : ℕ → α :=
  fun n => U (σ.idx n)

end ExtractedSubsequence

/-- Convergence of a sequence along an extracted subsequence, expressed in the
ambient topology of the codomain. Later developments can instantiate this with
strong or weak topologies on time-dependent function spaces. -/
def LimitAlong
    {α : Type*} [TopologicalSpace α]
    (U : ℕ → α)
    (σ : ExtractedSubsequence)
    (u : α) : Prop :=
  Tendsto (σ.pull U) atTop (nhds u)

/-- Output package for a future Aubin--Lions type theorem: an extracted
subsequence together with limits for the state and derivative families. The
topologies are intentionally left abstract so that later files can plug in the
appropriate strong and weak PDE topologies. -/
structure AubinLionsSubsequencePackage
    (StatePath DerivPath : Type*)
    [TopologicalSpace StatePath] [TopologicalSpace DerivPath]
    (U : ℕ → StatePath)
    (dU : ℕ → DerivPath) where
  subseq : ExtractedSubsequence
  stateLimit : StatePath
  derivLimit : DerivPath
  stateConverges : LimitAlong U subseq stateLimit
  derivConverges : LimitAlong dU subseq derivLimit

namespace AubinLionsSubsequencePackage

/-- Trivial subsequence extraction for constant state and derivative families.
This is a small but real compactness theorem: no Aubin--Lions machinery is
needed when the Galerkin family is literally constant in the approximation
index. -/
def of_constant
    {StatePath DerivPath : Type*}
    [TopologicalSpace StatePath] [TopologicalSpace DerivPath]
    (state : StatePath)
    (deriv : DerivPath) :
    AubinLionsSubsequencePackage StatePath DerivPath
      (fun _ : ℕ => state) (fun _ : ℕ => deriv) :=
  { subseq := ExtractedSubsequence.identity
    stateLimit := state
    derivLimit := deriv
    stateConverges := by
      simpa [LimitAlong, ExtractedSubsequence.pull, ExtractedSubsequence.identity]
        using (tendsto_const_nhds : Tendsto (fun _ : ℕ => state) atTop (nhds state))
    derivConverges := by
      simpa [LimitAlong, ExtractedSubsequence.pull, ExtractedSubsequence.identity]
        using (tendsto_const_nhds : Tendsto (fun _ : ℕ => deriv) atTop (nhds deriv)) }

end AubinLionsSubsequencePackage

section Interface

variable {H W : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup W] [GalerkinSystem H]

/-- Interface point for a future Aubin--Lions theorem. The `ready` field is the
estimate package already available from the Galerkin side; the remaining fields
record the target form of a subsequence-extraction theorem in whatever strong
and weak topologies are chosen later. -/
structure AubinLionsInterface
    (U : ℕ → ℝ → H)
    (dU : ℕ → ℝ → W)
    (T : ℝ)
    (StatePath DerivPath : Type*)
    [TopologicalSpace StatePath] [TopologicalSpace DerivPath] where
  ready : CompactnessReadyFamily U dU T
  stateFamily : ℕ → StatePath
  derivFamily : ℕ → DerivPath
  target : AubinLionsSubsequencePackage StatePath DerivPath stateFamily derivFamily

/-- A theorem-shaped abstraction of the Aubin--Lions extraction step. Instead
of supplying the extracted subsequence package by hand, later files can package
the chosen state/derivative path models together with an extraction operator
that consumes a compactness-ready family. -/
structure AubinLionsPrinciple
    (U : ℕ → ℝ → H)
    (dU : ℕ → ℝ → W)
    (T : ℝ)
    (StatePath DerivPath : Type*)
    [TopologicalSpace StatePath] [TopologicalSpace DerivPath] where
  stateFamily : ℕ → StatePath
  derivFamily : ℕ → DerivPath
  extract :
    CompactnessReadyFamily U dU T →
      AubinLionsSubsequencePackage StatePath DerivPath stateFamily derivFamily

namespace AubinLionsPrinciple

/-- Constant-family extraction principle for the full compactness-ready
interface.  The compactness-ready input is ignored because the state and
derivative path models are already constant in the Galerkin index. -/
def of_constant
    {U : ℕ → ℝ → H}
    {dU : ℕ → ℝ → W}
    {T : ℝ}
    {StatePath DerivPath : Type*}
    [TopologicalSpace StatePath] [TopologicalSpace DerivPath]
    (state : StatePath)
    (deriv : DerivPath) :
    AubinLionsPrinciple U dU T StatePath DerivPath :=
  { stateFamily := fun _ => state
    derivFamily := fun _ => deriv
    extract := fun _ =>
      AubinLionsSubsequencePackage.of_constant state deriv }

end AubinLionsPrinciple

namespace AubinLionsInterface

/-- Constructor packaging a compactness-ready Galerkin family together with a
chosen Aubin--Lions subsequence output. This keeps later system-specific files
focused on the PDE data rather than on record assembly. -/
def of_ready
    {U : ℕ → ℝ → H}
    {dU : ℕ → ℝ → W}
    {T : ℝ}
    {StatePath DerivPath : Type*}
    [TopologicalSpace StatePath] [TopologicalSpace DerivPath]
    (ready : CompactnessReadyFamily U dU T)
    (stateFamily : ℕ → StatePath)
    (derivFamily : ℕ → DerivPath)
    (target : AubinLionsSubsequencePackage StatePath DerivPath stateFamily derivFamily) :
    AubinLionsInterface U dU T StatePath DerivPath :=
  { ready := ready
    stateFamily := stateFamily
    derivFamily := derivFamily
    target := target }

/-- Build the Aubin--Lions interface directly from a compactness-ready family
and an extraction principle, without separately naming the extracted target. -/
def of_principle
    {U : ℕ → ℝ → H}
    {dU : ℕ → ℝ → W}
    {T : ℝ}
    {StatePath DerivPath : Type*}
    [TopologicalSpace StatePath] [TopologicalSpace DerivPath]
    (ready : CompactnessReadyFamily U dU T)
    (principle : AubinLionsPrinciple U dU T StatePath DerivPath) :
    AubinLionsInterface U dU T StatePath DerivPath :=
  { ready := ready
    stateFamily := principle.stateFamily
    derivFamily := principle.derivFamily
    target := principle.extract ready }

end AubinLionsInterface

end Interface

section ReadyInterface

variable {H W : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup W]

/-- A lighter Aubin--Lions interface for coordinate-side compactness packages.
Unlike `AubinLionsInterface`, this consumes only the energy/time-derivative
package `AubinLionsReadyFamily`, so it does not require a Galerkin dissipation
operator on the coordinate space. -/
structure AubinLionsReadyInterface
    (U : ℕ → ℝ → H)
    (dU : ℕ → ℝ → W)
    (T : ℝ)
    (StatePath DerivPath : Type*)
    [TopologicalSpace StatePath] [TopologicalSpace DerivPath] where
  ready : AubinLionsReadyFamily U dU T
  stateFamily : ℕ → StatePath
  derivFamily : ℕ → DerivPath
  target : AubinLionsSubsequencePackage StatePath DerivPath stateFamily derivFamily

/-- A theorem-shaped abstraction of the lighter coordinate Aubin--Lions
extraction step. It is the coordinate analogue of `AubinLionsPrinciple`, but
its input is `AubinLionsReadyFamily` rather than the stronger
`CompactnessReadyFamily`. -/
structure AubinLionsReadyPrinciple
    (U : ℕ → ℝ → H)
    (dU : ℕ → ℝ → W)
    (T : ℝ)
    (StatePath DerivPath : Type*)
    [TopologicalSpace StatePath] [TopologicalSpace DerivPath] where
  stateFamily : ℕ → StatePath
  derivFamily : ℕ → DerivPath
  extract :
    AubinLionsReadyFamily U dU T →
      AubinLionsSubsequencePackage StatePath DerivPath stateFamily derivFamily

namespace AubinLionsReadyPrinciple

/-- Constant-family extraction principle for the lighter coordinate-side
interface.  This is the reusable version of the common endpoint trick where
the chosen path model is independent of the Galerkin index. -/
def of_constant
    {U : ℕ → ℝ → H}
    {dU : ℕ → ℝ → W}
    {T : ℝ}
    {StatePath DerivPath : Type*}
    [TopologicalSpace StatePath] [TopologicalSpace DerivPath]
    (state : StatePath)
    (deriv : DerivPath) :
    AubinLionsReadyPrinciple U dU T StatePath DerivPath :=
  { stateFamily := fun _ => state
    derivFamily := fun _ => deriv
    extract := fun _ =>
      AubinLionsSubsequencePackage.of_constant state deriv }

end AubinLionsReadyPrinciple

namespace AubinLionsReadyInterface

/-- Constructor packaging an Aubin--Lions-ready coordinate family together
with a chosen subsequence output. -/
def of_ready
    {U : ℕ → ℝ → H}
    {dU : ℕ → ℝ → W}
    {T : ℝ}
    {StatePath DerivPath : Type*}
    [TopologicalSpace StatePath] [TopologicalSpace DerivPath]
    (ready : AubinLionsReadyFamily U dU T)
    (stateFamily : ℕ → StatePath)
    (derivFamily : ℕ → DerivPath)
    (target : AubinLionsSubsequencePackage StatePath DerivPath stateFamily derivFamily) :
    AubinLionsReadyInterface U dU T StatePath DerivPath :=
  { ready := ready
    stateFamily := stateFamily
    derivFamily := derivFamily
    target := target }

/-- Build the lighter coordinate interface directly from an extraction
principle. -/
def of_principle
    {U : ℕ → ℝ → H}
    {dU : ℕ → ℝ → W}
    {T : ℝ}
    {StatePath DerivPath : Type*}
    [TopologicalSpace StatePath] [TopologicalSpace DerivPath]
    (ready : AubinLionsReadyFamily U dU T)
    (principle : AubinLionsReadyPrinciple U dU T StatePath DerivPath) :
    AubinLionsReadyInterface U dU T StatePath DerivPath :=
  { ready := ready
    stateFamily := principle.stateFamily
    derivFamily := principle.derivFamily
    target := principle.extract ready }

end AubinLionsReadyInterface

end ReadyInterface
