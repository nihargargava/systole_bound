module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Core.Reduction
public import BuserSarnak.ArithmeticSurfaces
public import CookMagyar.CubicEstimates
public import Geometry.SurfaceGluing

@[expose] public section

/-!
# The three constructions and the systolic-growth bound

The three verified inputs below supply the arithmetic surfaces, the uniform
prime representation theorem, and the geometric joining construction.
`systolic_growth_lower_bound` combines them into the bound exported by
`main.lean`. Supporting estimates live in their arithmetic, analytic and
geometric modules; this file records how the constructions fit together.
-/

-- Use mathlib-style docstrings, not the imported DoCarmo documentation tags.
set_option linter.shared.mathTag false

namespace SystolicGrowth

namespace MainTheorem

open Filter

/-- The explicit arithmetic surfaces, with their genus markings and
the Buser--Sarnak systole estimate. -/
noncomputable def arithmeticSurfaces : BuserSarnakInput :=
  SystolicGrowth.buserSarnakSurfaces

/-- The uniform prime representation input from the proved major-arc,
minor-arc, singular-series and real-density estimates. -/
noncomputable def primeCubeDecompositions : TargetUniformCookMagyarInput :=
  targetUniformCookMagyar
    (SystolicGrowth.cookMagyarCircleMethod
      CookMagyarCircle.separatedCubicEstimates)

/-- The marked chain construction and conformal hyperbolic replacement,
together with the logarithmic systole upper bound. -/
theorem surfaceGluing : GeometricInput :=
  geometricInput

/-- The systolic-growth liminf bound, with all three inputs constructed. -/
theorem systolic_growth_lower_bound :
    (4 / 3 : ℝ) ≤ liminf (fun g : ℕ ↦ Sys g / Real.log g) atTop :=
  main_theorem_reduced_to_inputs
    surfaceGluing arithmeticSurfaces primeCubeDecompositions

#print axioms arithmeticSurfaces
#print axioms primeCubeDecompositions
#print axioms surfaceGluing
#print axioms systolic_growth_lower_bound

end MainTheorem

end SystolicGrowth
