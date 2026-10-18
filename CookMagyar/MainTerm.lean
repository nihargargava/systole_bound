module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.SingularIntegral
public import CookMagyar.SingularSeries

@[expose] public section

namespace SystolicGrowth
namespace CookMagyarCircle

/-! # The concrete cubic circle-method main term -/

/-- The natural size `N^(n-3)` of a one-equation diagonal cubic count. -/
noncomputable def cubicMainScale (n N : ℕ) : ℝ :=
  (N : ℝ) ^ (n - 3)

theorem cubicMainScale_pos {n N : ℕ} (hN : 0 < N) :
    0 < cubicMainScale n N := by
  exact pow_pos (by exact_mod_cast hN) _

/-- The real coefficient obtained from the arithmetic singular series and
the Archimedean singular integral at the normalized target `T/N³`. -/
noncomputable def cubicSingularCoefficient (n N T : ℕ) : ℝ :=
  (CookMagyarFiniteFourier.singularSeries n T *
    CookMagyarReal.singularIntegral n
      (CookMagyarReal.normalizedTarget N T)).re

/-- The exact main term approximated by the major arcs. -/
noncomputable def cubicSingularMainTerm (n N T : ℕ) : ℝ :=
  cubicSingularCoefficient n N T * cubicMainScale n N

end CookMagyarCircle
end SystolicGrowth
