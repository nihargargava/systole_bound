module

public import main

public section

/-!
# Proved systolic-growth theorem

The independent statement is in `Challenge.lean`. This proof uses the
completed arithmetic, prime-decomposition and surface-gluing constructions.
Comparator checks that it proves exactly the independent statement and
uses only the permitted standard logical axioms.
-/

-- Use mathlib-style docstrings, not the imported DoCarmo documentation tags.
set_option linter.shared.mathTag false

namespace SystolicGrowth

open Filter

/-- The supremal systole grows at least as fast as `(4 / 3) * log g`
in the limit over all genera. -/
theorem systolic_growth_lower_bound :
    (4 / 3 : ℝ) ≤ liminf (fun g : ℕ ↦ Sys g / Real.log g) atTop :=
  main_theorem_unconditional

#print axioms systolic_growth_lower_bound

end SystolicGrowth
