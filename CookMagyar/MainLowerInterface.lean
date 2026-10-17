module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.MainTermUniformLower
public import CookMagyar.Uniformity

@[expose] public section

open Filter

namespace SystolicGrowth.CookMagyarCircle

/-! The verified main-term coefficient in the exact eventual form required by
`SeparatedCubicEstimates.main_lower`. -/

/-- Choose the proved arity-dependent main-term coefficient, with an
irrelevant zero value below the admissible arity threshold. -/
noncomputable def provedCubicMainCoefficient (n : ℕ) : ℝ :=
  if hn : 33 ≤ n then
    Classical.choose (exists_uniform_cubicSingularMainTerm_lower hn)
  else 0

/-- The chosen coefficient is positive at all relevant arities. -/
theorem provedCubicMainCoefficient_pos {n : ℕ} (hn : 33 ≤ n) :
    0 < provedCubicMainCoefficient n := by
  simpa [provedCubicMainCoefficient, hn] using
    (Classical.choose_spec (exists_uniform_cubicSingularMainTerm_lower hn)).1

/-- The chosen coefficient satisfies the exact eventual, target-uniform
`main_lower` obligation of `SeparatedCubicEstimates`. -/
theorem provedCubicMainCoefficient_main_lower
    {n : ℕ} (hn : 33 ≤ n) :
    ∀ᶠ N : ℕ in atTop, ∀ T, IsAdmissibleTarget n N T →
      provedCubicMainCoefficient n * cubicMainScale n N ≤
        cubicSingularMainTerm n N T := by
  have hbound :=
    (Classical.choose_spec (exists_uniform_cubicSingularMainTerm_lower hn)).2
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN T hT
  have hwindow := CookMagyarReal.normalizedTargetWindow_of_cookMagyarWindow
    (by omega : 0 < n) hN hT.2
  simpa [provedCubicMainCoefficient, hn] using
    hbound N T hN hT.1 hwindow

end SystolicGrowth.CookMagyarCircle
