module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.HuaOrthogonality
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

open Filter Asymptotics

namespace SystolicGrowth
namespace CookMagyarCircle

/-! # The public weak cubic Hua estimate

The unweighted `5+ε` solution count is now proved. This module absorbs the
eight logarithmic von--Mangoldt factors into the remaining power gap. -/

/-- The weighted unweighted-count envelope is little-o of the exact target
scale used by `CubicHuaEstimate`. -/
theorem cubicUnweightedHuaEstimate : CubicUnweightedHuaEstimate := by
  obtain ⟨C, hC, hcountBound⟩ :=
    exists_cubicEighthSolutionCount_rpow_five_bound
      (by norm_num : (0 : ℝ) < 1 / 4)
  have hcount :
      (fun N : ℕ => (cubicEighthSolutionCount N : ℝ)) =O[atTop]
        (fun N : ℕ => Real.rpow (N + 1 : ℝ) (21 / 4)) := by
    apply IsBigO.of_bound C
    apply Filter.Eventually.of_forall
    intro N
    have hcnonneg : 0 ≤ (cubicEighthSolutionCount N : ℝ) := by positivity
    have hpowNonneg : 0 ≤ Real.rpow (N + 1 : ℝ) (21 / 4) := by
      change 0 ≤ (N + 1 : ℝ) ^ (21 / 4 : ℝ)
      exact Real.rpow_nonneg (by positivity) _
    simpa only [Real.norm_eq_abs, abs_of_nonneg hcnonneg,
      abs_of_nonneg hpowNonneg,
      show (5 : ℝ) + 1 / 4 = 21 / 4 by norm_num] using hcountBound N
  have htend : Tendsto (fun N : ℕ => (N + 1 : ℝ)) atTop atTop := by
    convert tendsto_atTop_add_const_right _ (1 : ℝ)
      tendsto_natCast_atTop_atTop using 1
  have hlog :
      (fun N : ℕ => Real.log (N + 1 : ℝ) ^ 8) =o[atTop]
        (fun N : ℕ => Real.rpow (N + 1 : ℝ) (1 / 4)) := by
    have hraw :=
      (isLittleO_log_rpow_rpow_atTop (s := (1 / 4 : ℝ)) 8
        (by norm_num)).comp_tendsto htend
    apply hraw.congr
    · intro N
      change Real.log (N + 1 : ℝ) ^ (8 : ℝ) =
        Real.log (N + 1 : ℝ) ^ (8 : ℕ)
      exact Real.rpow_natCast _ _
    · intro N
      rfl
  have hprod := hlog.mul_isBigO hcount
  have hscale : cubicUnweightedHuaScale =o[atTop]
      (fun N : ℕ => Real.rpow (N + 1 : ℝ) (11 / 2)) := by
    have hright :
        (fun N : ℕ => Real.rpow (N + 1 : ℝ) (1 / 4) *
          Real.rpow (N + 1 : ℝ) (21 / 4)) =
        (fun N : ℕ => Real.rpow (N + 1 : ℝ) (11 / 2)) := by
      funext N
      have hX : 0 < (N + 1 : ℝ) := by positivity
      change (N + 1 : ℝ) ^ (1 / 4 : ℝ) *
          (N + 1 : ℝ) ^ (21 / 4 : ℝ) =
        (N + 1 : ℝ) ^ (11 / 2 : ℝ)
      rw [← Real.rpow_add hX]
      norm_num
    rw [hright] at hprod
    change (fun N : ℕ => Real.log (N + 1 : ℝ) ^ 8 *
      (cubicEighthSolutionCount N : ℝ)) =o[atTop]
        (fun N : ℕ => Real.rpow (N + 1 : ℝ) (11 / 2))
    exact hprod
  have hdenom :
      (fun N : ℕ => Real.rpow (N + 1 : ℝ) (11 / 2)) =O[atTop]
        (fun N : ℕ => (N : ℝ) ^ 5 * Real.sqrt N) := by
    apply IsBigO.of_bound (Real.rpow 2 (11 / 2))
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hXle : (N + 1 : ℝ) ≤ 2 * N := by linarith
    have hpow : Real.rpow (N + 1 : ℝ) (11 / 2) ≤
        Real.rpow (2 * (N : ℝ)) (11 / 2) :=
      Real.rpow_le_rpow (by positivity) hXle (by norm_num)
    have hmul : Real.rpow (2 * (N : ℝ)) (11 / 2) =
        Real.rpow 2 (11 / 2) * Real.rpow (N : ℝ) (11 / 2) := by
      change (2 * (N : ℝ)) ^ (11 / 2 : ℝ) =
        (2 : ℝ) ^ (11 / 2 : ℝ) * (N : ℝ) ^ (11 / 2 : ℝ)
      exact Real.mul_rpow (by norm_num) (by positivity)
    have hNrepr : Real.rpow (N : ℝ) (11 / 2) =
        (N : ℝ) ^ 5 * Real.sqrt N := by
      change (N : ℝ) ^ (11 / 2 : ℝ) =
        (N : ℝ) ^ 5 * Real.sqrt N
      rw [show (11 / 2 : ℝ) = 5 + 1 / 2 by norm_num,
        Real.rpow_add (by positivity : (0 : ℝ) < N)]
      rw [Real.sqrt_eq_rpow]
      exact congrArg (fun t : ℝ => t * (N : ℝ) ^ (1 / 2 : ℝ))
        (Real.rpow_natCast (N : ℝ) 5)
    have hraw : Real.rpow (N + 1 : ℝ) (11 / 2) ≤
        Real.rpow 2 (11 / 2) * ((N : ℝ) ^ 5 * Real.sqrt N) := calc
      Real.rpow (N + 1 : ℝ) (11 / 2) ≤
          Real.rpow (2 * (N : ℝ)) (11 / 2) := hpow
      _ = Real.rpow 2 (11 / 2) *
          ((N : ℝ) ^ 5 * Real.sqrt N) := by rw [hmul, hNrepr]
    have hleftNonneg : 0 ≤ Real.rpow (N + 1 : ℝ) (11 / 2) := by
      change 0 ≤ (N + 1 : ℝ) ^ (11 / 2 : ℝ)
      exact Real.rpow_nonneg (by positivity) _
    have hrightNonneg : 0 ≤ (N : ℝ) ^ 5 * Real.sqrt N := by positivity
    simpa only [Real.norm_eq_abs, abs_of_nonneg hleftNonneg,
      abs_of_nonneg hrightNonneg] using hraw
  exact hscale.trans_isBigO hdenom

/-- Unconditional weak eighth-moment bound for cubic von--Mangoldt sums. -/
theorem cubicHuaEstimate : CubicHuaEstimate :=
  cubicUnweightedHuaEstimate.toCubicHuaEstimate

#print axioms SystolicGrowth.CookMagyarCircle.cubicUnweightedHuaEstimate
#print axioms SystolicGrowth.CookMagyarCircle.cubicHuaEstimate

end CookMagyarCircle
end SystolicGrowth
