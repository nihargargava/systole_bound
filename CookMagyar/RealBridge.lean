module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.RealSolution
public import CookMagyar.Scale

@[expose] public section

namespace SystolicGrowth
namespace CookMagyarReal

/-! # From the integer scale window to the real place

`CookMagyar.Scale` avoids cube roots by expressing the target window with
integer inequalities.  The singular integral uses the normalized real target
`T / N³`.  This file proves that the two formulations agree and therefore
produces the explicit nonsingular real solution needed on every admissible
major-arc scale.
-/

/-- The target after cubic rescaling. -/
noncomputable def normalizedTarget (N T : ℕ) : ℝ :=
  (T : ℝ) / (N : ℝ) ^ 3

/-- The division-free integer window implies the compact real window. -/
theorem normalizedTargetWindow_of_cookMagyarWindow
    {n N T : ℕ} (hn : 0 < n) (hN : 0 < N)
    (hwindow : CookMagyarWindow n N T) :
    NormalizedTargetWindow n (normalizedTarget N T) := by
  have hNreal : 0 < (N : ℝ) ^ 3 := pow_pos (by exact_mod_cast hN) 3
  have hn3 : 1 ≤ 3 * n := by omega
  have hn5 : 1 ≤ 5 * n := by omega
  have hlower :
      ((3 * n : ℝ) - 1) * (N : ℝ) ^ 3 ≤ 3 * (T : ℝ) := by
    exact_mod_cast hwindow.1
  have hupper :
      5 * (T : ℝ) ≤ ((5 * n : ℝ) - 1) * (N : ℝ) ^ 3 := by
    exact_mod_cast hwindow.2
  constructor
  · unfold normalizedTarget
    rw [le_div_iff₀ hNreal]
    nlinarith
  · unfold normalizedTarget
    rw [div_le_iff₀ hNreal]
    nlinarith

/-- Every admissible integer target and scale has the required nonsingular
point in the open real unit cube. -/
theorem nonsingularOpenUnitSolution_of_cookMagyarWindow
    {n N T : ℕ} (hn : 0 < n) (hN : 0 < N)
    (hwindow : CookMagyarWindow n N T) :
    Nonempty (NonsingularOpenUnitSolution n (normalizedTarget N T)) :=
  exists_nonsingularOpenUnitSolution hn
    (normalizedTargetWindow_of_cookMagyarWindow hn hN hwindow)

end CookMagyarReal
end SystolicGrowth
