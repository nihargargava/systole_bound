module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Data.ENNReal.Inv

@[expose] public section

/-!
# The numerical systole bound from disk area

Open-radius hyperbolic disk-area inequalities extend to half the systole
by continuity. Inverting `cosh` gives the exact uniform `arcosh` bound.
This numeric consequence does not construct the geometric area inputs.
-/

open Set
open scoped ENNReal Topology

namespace SystolicGrowth

/-- **Math.** If every positive radius below half a nonnegative length
has hyperbolic disk area within the genus budget, that length is at most
`2 arcosh(2g - 1)`. The endpoint inequality is derived by continuity. -/
theorem systole_le_arcosh_of_open_disk_area_bounds
    {g : ℕ} {L : ℝ} (hg : 2 ≤ g) (hL : 0 ≤ L)
    (harea : ∀ r : ℝ, 0 < r → r < L / 2 →
      2 * Real.pi * (Real.cosh r - 1) ≤ 4 * Real.pi * ((g : ℝ) - 1)) :
    L ≤ 2 * Real.arcosh (2 * (g : ℝ) - 1) := by
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have htarget : 1 ≤ 2 * (g : ℝ) - 1 := by linarith
  by_cases hLzero : L = 0
  · rw [hLzero]
    exact mul_nonneg (by norm_num) (Real.arcosh_nonneg htarget)
  have hhalf : 0 < L / 2 := by positivity
  have hbound : Ioo (0 : ℝ) (L / 2) ⊆
      {r : ℝ | Real.cosh r ≤ 2 * (g : ℝ) - 1} := by
    intro r hr
    have hraw := harea r hr.1 hr.2
    have hsmall : Real.cosh r - 1 ≤ 2 * ((g : ℝ) - 1) := by
      have hh : 2 * Real.pi * (Real.cosh r - 1) ≤
          2 * Real.pi * (2 * ((g : ℝ) - 1)) := by
        convert hraw using 1
        ring
      exact le_of_mul_le_mul_left hh (by positivity)
    change Real.cosh r ≤ 2 * (g : ℝ) - 1
    linarith only [hsmall]
  have hclosed : IsClosed {r : ℝ | Real.cosh r ≤ 2 * (g : ℝ) - 1} :=
    isClosed_le Real.continuous_cosh continuous_const
  have hboundary : Real.cosh (L / 2) ≤ 2 * (g : ℝ) - 1 := by
    apply (hclosed.closure_subset_iff.mpr hbound)
    rw [closure_Ioo hhalf.ne]
    exact ⟨hhalf.le, le_rfl⟩
  have harcosh := (Real.arcosh_le_arcosh (Real.cosh_pos (L / 2))
    (by linarith : 0 < 2 * (g : ℝ) - 1)).mpr hboundary
  rw [Real.arcosh_cosh hhalf.le] at harcosh
  linarith only [harcosh]

/-- **Math.** The same uniform bound for an extended-real systole. Every
finite nonnegative test length below it satisfies the geometric disk-area
budget; density of finite nonnegative reals gives the bound without first
assuming that the systole is finite. -/
theorem systoleENNReal_le_arcosh_of_open_disk_area_bounds
    {g : ℕ} {S : ℝ≥0∞} (hg : 2 ≤ g)
    (harea : ∀ L : ℝ, 0 ≤ L → ENNReal.ofReal L ≤ S →
      ∀ r : ℝ, 0 < r → r < L / 2 →
        2 * Real.pi * (Real.cosh r - 1) ≤ 4 * Real.pi * ((g : ℝ) - 1)) :
    S ≤ ENNReal.ofReal (2 * Real.arcosh (2 * (g : ℝ) - 1)) := by
  refine ENNReal.le_of_forall_nnreal_lt fun L hL => ?_
  have hbudget := harea L L.coe_nonneg
    (by simpa only [ENNReal.ofReal_coe_nnreal] using hL.le)
  have hbound := systole_le_arcosh_of_open_disk_area_bounds hg L.coe_nonneg hbudget
  simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hbound

#print axioms systole_le_arcosh_of_open_disk_area_bounds
#print axioms systoleENNReal_le_arcosh_of_open_disk_area_bounds

end SystolicGrowth
