import Mathlib.Analysis.BoxIntegral.Box.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic

noncomputable section

variable {n : ℕ}

/-- Homogeneous Dirichlet boundary condition for a scalar field on a box. -/
def ZeroDirichletScalarOnBox
    (I : BoxIntegral.Box (Fin (n + 1)))
    (f : (Fin (n + 1) → ℝ) → ℝ) : Prop :=
  ∀ i : Fin (n + 1), ∀ x : Fin n → ℝ,
    f (i.insertNth (I.upper i) x) = 0 ∧
    f (i.insertNth (I.lower i) x) = 0

/-- Homogeneous Dirichlet boundary condition for a vector field on a box. -/
def ZeroDirichletVectorOnBox
    (I : BoxIntegral.Box (Fin (n + 1)))
    (v : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)) : Prop :=
  ∀ i : Fin (n + 1), ∀ x : Fin n → ℝ,
    v (i.insertNth (I.upper i) x) = 0 ∧
    v (i.insertNth (I.lower i) x) = 0

/-- Homogeneous Neumann condition for a scalar field on a box, encoded as the
vanishing of the normal derivative on each coordinate face. -/
def HomogeneousNeumannScalarOnBox
    (I : BoxIntegral.Box (Fin (n + 1)))
    (f' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] ℝ) : Prop :=
  ∀ i : Fin (n + 1), ∀ x : Fin n → ℝ,
    f' (i.insertNth (I.upper i) x) (Pi.single i 1) = 0 ∧
    f' (i.insertNth (I.lower i) x) (Pi.single i 1) = 0

/-- A vector Dirichlet condition implies the scalar Dirichlet condition for
every component. -/
theorem ZeroDirichletVectorOnBox.component
    (I : BoxIntegral.Box (Fin (n + 1)))
    (v : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ))
    (hv : ZeroDirichletVectorOnBox I v)
    (j : Fin (n + 1)) :
    ZeroDirichletScalarOnBox I (fun y => v y j) := by
  intro i x
  constructor
  · have h := (hv i x).1
    simpa using congrArg (fun y => y j) h
  · have h := (hv i x).2
    simpa using congrArg (fun y => y j) h
