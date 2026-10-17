module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.MainLowerInterface
public import CookMagyar.MajorArcExerciseGaps
public import CookMagyar.MinorArcExerciseGaps
public import CookMagyar.HuaAsymptotic

@[expose] public section

/-!
# Separated major- and minor-arc estimates for prime cubes

The minor-arc estimate supplies one positive logarithmic cutoff exponent,
chosen independently of the number of summands. For each arity at least 33
and each positive error tolerance, the estimate holds at all sufficiently
large scales, uniformly in the target integer. The major-arc estimate uses
the same cutoff.

`separatedCubicEstimates` combines the positive main coefficient, both arc
errors and Hua's moment estimate. Each arc error receives one quarter of
the main coefficient, leaving a positive lower-bound margin.
-/

open Filter

namespace SystolicGrowth
namespace CookMagyarCircle

open CookMagyarArcs

/-- A logarithmic cutoff exponent supplied by the uniform minor-arc estimate. -/
noncomputable def minorArcCutoffExponent : ℕ :=
  Classical.choose exercise_exists_minor_error_logarithmic_cutoff

/-- The selected logarithmic exponent is positive. -/
theorem minorArcCutoffExponent_pos : 0 < minorArcCutoffExponent :=
  (Classical.choose_spec exercise_exists_minor_error_logarithmic_cutoff).1

/-- For each arity and positive tolerance, all sufficiently large scales
satisfy the minor-arc bound uniformly in the target integer. -/
theorem minorArcCutoffExponent_minor_bound (n : ℕ) (hn : 33 ≤ n)
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, ∀ T : ℕ,
      ‖cubicMinorArcIntegral n N T
        (logarithmicDenominatorCutoff minorArcCutoffExponent N)‖ ≤
          c * cubicMainScale n N :=
  (Classical.choose_spec exercise_exists_minor_error_logarithmic_cutoff).2
    n hn c hc

/-- Major- and minor-arc estimates with one quarter of the positive main
coefficient allotted to each error, together with Hua's moment bound. -/
noncomputable def separatedCubicEstimates : SeparatedCubicEstimates := by
  refine
    { minSummands := 33
      minSummands_ge_thirtyThree := le_rfl
      cutoff := fun _ N => logarithmicDenominatorCutoff minorArcCutoffExponent N
      mainCoefficient := provedCubicMainCoefficient
      mainCoefficient_pos := ?_
      main_lower := ?_
      major_error := ?_
      minor_error := ?_
      hua := cubicHuaEstimate }
  · intro n hn
    exact provedCubicMainCoefficient_pos hn
  · intro n hn
    exact provedCubicMainCoefficient_main_lower hn
  · intro n hn
    exact eventually_majorArc_error_small minorArcCutoffExponent
      minorArcCutoffExponent_pos n hn
      (div_pos (provedCubicMainCoefficient_pos hn) (by norm_num))
  · intro n hn
    filter_upwards [minorArcCutoffExponent_minor_bound n hn
      (c := provedCubicMainCoefficient n / 4)
      (div_pos (provedCubicMainCoefficient_pos hn) (by norm_num))] with N hN
    intro T _
    exact hN T

end CookMagyarCircle
end SystolicGrowth

#print axioms SystolicGrowth.CookMagyarCircle.separatedCubicEstimates
