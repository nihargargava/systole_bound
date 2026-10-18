module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Data.Int.CardIntervalMod
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

@[expose] public section

open scoped BigOperators

namespace SystolicGrowth
namespace CookMagyarCircle

/-! # Uniform all-residue counting

Every residue, including nonunits, has density `1/q` in an initial
integer interval, with a discrepancy strictly smaller than one. This is
the elementary arithmetic input to the unweighted major-arc model.
-/

/-- Exact count of an arbitrary residue in `[0,t)`. -/
theorem cubicAllResidueCount_eq_div_add_indicator
    (q t r : ℕ) (hq : 0 < q) :
    t.count (· ≡ r [MOD q]) =
      t / q + if r % q < t % q then 1 else 0 :=
  Nat.count_modEq_card t hq r

/-- The count of any residue in `[0,t)` differs from its uniform density
by at most one, independently of the residue and modulus. -/
theorem abs_cubicAllResidueCount_sub_density_le_one
    (q t r : ℕ) (hq : 0 < q) :
    |(t.count (· ≡ r [MOD q]) : ℝ) - (t : ℝ) / q| ≤ 1 := by
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
  have hrem : (t % q : ℝ) < q := by
    exact_mod_cast Nat.mod_lt t hq
  have hrem0 : (0 : ℝ) ≤ t % q := by positivity
  have hratio0 : (0 : ℝ) ≤ (t % q : ℝ) / q := div_nonneg hrem0 hqreal.le
  have hratio1 : (t % q : ℝ) / q < 1 := (div_lt_one hqreal).2 hrem
  have hsplit : (t : ℝ) / q = ((t / q : ℕ) : ℝ) + (t % q : ℝ) / q := by
    have ht : t % q + q * (t / q) = t := Nat.mod_add_div t q
    have htr : (t % q : ℝ) + (q : ℝ) * ((t / q : ℕ) : ℝ) = t := by
      exact_mod_cast ht
    calc
      (t : ℝ) / q =
          ((t % q : ℝ) + (q : ℝ) * ((t / q : ℕ) : ℝ)) / q := by
            rw [htr]
      _ = ((t / q : ℕ) : ℝ) + (t % q : ℝ) / q := by
        field_simp [hqreal.ne']
        ring
  rw [cubicAllResidueCount_eq_div_add_indicator q t r hq, hsplit]
  by_cases hr : r % q < t % q
  · simp only [hr, if_true, Nat.cast_add, Nat.cast_one]
    rw [show ((t / q : ℕ) : ℝ) + 1 -
        (((t / q : ℕ) : ℝ) + (t % q : ℝ) / q) =
        1 - (t % q : ℝ) / q by ring]
    rw [abs_of_nonneg (by linarith)]
    linarith
  · simp only [hr, if_false, add_zero]
    rw [show ((t / q : ℕ) : ℝ) -
        (((t / q : ℕ) : ℝ) + (t % q : ℝ) / q) =
        -((t % q : ℝ) / q) by ring]
    rw [abs_neg, abs_of_nonneg hratio0]
    linarith

/-- The inclusive interval `0 ≤ k ≤ m` has the same indicator sum as the
corresponding prefix count of length `m+1`. -/
theorem sum_cubicAllResidueIndicator_Icc (q m r : ℕ) :
    (∑ k ∈ Finset.Icc 0 m,
      if k ≡ r [MOD q] then (1 : ℝ) else 0) =
        ((m + 1).count (· ≡ r [MOD q]) : ℝ) := by
  rw [← Nat.range_succ_eq_Icc_zero, Nat.count_eq_card_filter_range]
  simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul, mul_one]

/-- Uniform partial-sum discrepancy in the precise inclusive endpoint
convention used by Abel summation. -/
theorem abs_sum_cubicAllResidueError_Icc_le_one
    (q m r : ℕ) (hq : 0 < q) :
    |(∑ k ∈ Finset.Icc 0 m,
        ((if k ≡ r [MOD q] then (1 : ℝ) else 0) - 1 / (q : ℝ)))| ≤ 1 := by
  rw [Finset.sum_sub_distrib, sum_cubicAllResidueIndicator_Icc]
  have hcard : (Finset.Icc 0 m).card = m + 1 := by simp
  simp only [Finset.sum_const, hcard, nsmul_eq_mul]
  convert abs_cubicAllResidueCount_sub_density_le_one q (m + 1) r hq using 1
  ring_nf

end CookMagyarCircle
end SystolicGrowth
