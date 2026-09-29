import PDEIdeas.VariationalGalerkin
import Mathlib.Analysis.ODE.Gronwall

/-! Right derivatives inherited from a closed-interval ODE solution. -/

open Filter Set

namespace ClosedIntervalRightDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : ℝ → E} {f' : E} {a b t : ℝ}

theorem of_Icc (ht : t ∈ Ico a b)
    (hf : HasDerivWithinAt f f' (Icc a b) t) :
    HasDerivWithinAt f f' (Ici t) t := by
  rcases eq_or_lt_of_le ht.1 with h | h
  · subst t
    change HasDerivAtFilter f f' (nhdsWithin a (Ici a) ×ˢ pure a)
    change HasDerivAtFilter f f' (nhdsWithin a (Icc a b) ×ˢ pure a) at hf
    simpa only [nhdsWithin_Icc_eq_nhdsGE ht.2] using hf
  · exact (hf.hasDerivAt (Icc_mem_nhds h ht.2)).hasDerivWithinAt

end ClosedIntervalRightDerivative
