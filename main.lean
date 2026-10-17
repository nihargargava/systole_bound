module

public import MainTheorem

@[expose] public section

/-!
# Systolic growth in every genus

`Sys g` is the supremum of the systoles of closed oriented hyperbolic
surfaces of genus `g`. The main result is
`4 / 3 ≤ liminf (fun g ↦ Sys g / Real.log g) atTop`.

`main_theorem_unconditional` is the completed theorem. Its proof combines
the arithmetic surfaces, prime-cube decompositions and surface gluing
constructed in `MainTheorem`.
-/

-- Use mathlib-style docstrings, not the imported DoCarmo documentation tags.
set_option linter.shared.mathTag false

namespace SystolicGrowth

open Filter

/-- Original conditional interface, retained for compatibility.
The unconditional theorem below constructs all mathematical inputs. -/
theorem main_theorem
    (geo : GeometricInput) (cm : TargetUniformCookMagyarInput) :
    (4 / 3 : ℝ) ≤ liminf (fun g : ℕ ↦ Sys g / Real.log g) atTop :=
  main_theorem_reduced_to_inputs geo buserSarnakSurfaces cm

#print axioms main_theorem

/-- The supremal systole grows at least as fast as
`(4 / 3) * log g` in the limit over all genera. All inputs are constructed
by the proof; the theorem has no mathematical assumptions. -/
theorem main_theorem_unconditional :
    (4 / 3 : ℝ) ≤ liminf (fun g : ℕ ↦ Sys g / Real.log g) atTop :=
  MainTheorem.systolic_growth_lower_bound

#print axioms main_theorem_unconditional

/-- Historical theorem name, retained as an alias of the completed proof. -/
theorem main_theorem_skeleton :
    (4 / 3 : ℝ) ≤ liminf (fun g : ℕ ↦ Sys g / Real.log g) atTop :=
  main_theorem_unconditional

#print axioms main_theorem_skeleton

end SystolicGrowth
