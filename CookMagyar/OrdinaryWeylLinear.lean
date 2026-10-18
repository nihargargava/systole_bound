module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.AuxiliaryPowerCutoff
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

open Finset

namespace SystolicGrowth
namespace CookMagyarCircle

/-! # Linear character sums for ordinary cubic Weyl differencing -/

/-- The exact geometric-series bound for a unit complex ratio away from
one. The zero-distance case is handled by the separate trivial bound. -/
theorem norm_unitGeometricSum_le_two_div
    (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (X : ℕ) :
    ‖∑ m ∈ Finset.range X, z ^ m‖ ≤ 2 / ‖z - 1‖ := by
  rw [geom_sum_eq hz1, norm_div]
  have hnum : ‖z ^ X - 1‖ ≤ 2 := by
    calc
      ‖z ^ X - 1‖ ≤ ‖z ^ X‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by simp [norm_pow, hz]; norm_num
  exact div_le_div_of_nonneg_right hnum (norm_nonneg _)

theorem addChar_eq_pow_one (theta : ℝ) (m : ℕ) :
    addChar theta m = (addChar theta 1) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [addChar_add theta m 1, ih, pow_succ]

/-- The finite linear phase sum is always bounded by its number of terms. -/
theorem norm_linearAddCharSum_le_length (theta : ℝ) (X : ℕ) :
    ‖∑ m ∈ Finset.range X, addChar theta m‖ ≤ X := by
  calc
    ‖∑ m ∈ Finset.range X, addChar theta m‖ ≤
        ∑ m ∈ Finset.range X, ‖addChar theta m‖ := norm_sum_le _ _
    _ = X := by simp

/-- The complementary geometric bound, prior to comparing the
denominator with distance to the nearest integer. -/
theorem norm_linearAddCharSum_le_two_div
    (theta : ℝ) (X : ℕ) (h : addChar theta 1 ≠ 1) :
    ‖∑ m ∈ Finset.range X, addChar theta m‖ ≤
      2 / ‖addChar theta 1 - 1‖ := by
  have heq : (∑ m ∈ Finset.range X, addChar theta m) =
      ∑ m ∈ Finset.range X, (addChar theta 1) ^ m := by
    apply Finset.sum_congr rfl
    intro m _
    exact addChar_eq_pow_one theta m
  rw [heq]
  exact norm_unitGeometricSum_le_two_div _ (norm_addChar theta 1) h X

/-- Chord length on the unit circle dominates four times the distance
to the nearest integer. This is the analytic input for the Weyl linear
sum estimate. -/
theorem four_mul_abs_le_norm_addChar_sub_one_of_abs_le_half
    {delta : ℝ} (hdelta : |delta| ≤ 1 / 2) :
    4 * |delta| ≤ ‖addChar delta 1 - 1‖ := by
  have hx0 : 0 ≤ 2 * |delta| := by positivity
  have hx1 : 2 * |delta| ≤ 1 := by linarith
  have hsin : 2 * |delta| ≤ Real.sin (Real.pi * |delta|) := by
    have harg : Real.pi / 2 * (2 * |delta|) = Real.pi * |delta| := by ring
    simpa only [harg] using Real.le_sin_mul hx0 hx1
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  have harg : |Real.pi * delta| ≤ Real.pi := by
    rw [abs_mul, abs_of_nonneg hpi]
    nlinarith
  have hsinabs : |Real.sin (Real.pi * delta)| =
      Real.sin (Real.pi * |delta|) := by
    rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi harg]
    rw [abs_mul, abs_of_nonneg hpi]
  have he : addChar delta 1 =
      Complex.exp (Complex.I * ((2 * Real.pi * delta : ℝ) : ℂ)) := by
    unfold addChar
    congr 1
    push_cast
    ring
  rw [he, Complex.norm_exp_I_mul_ofReal_sub_one]
  have harg' : (2 * Real.pi * delta) / 2 = Real.pi * delta := by ring
  rw [harg', Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    hsinabs]
  nlinarith

/-- The chord estimate in nearest-integer form. -/
theorem four_mul_abs_sub_round_le_norm_addChar_sub_one (theta : ℝ) :
    4 * |theta - (round theta : ℤ)| ≤ ‖addChar theta 1 - 1‖ := by
  let delta : ℝ := theta - (round theta : ℤ)
  have hdelta : |delta| ≤ 1 / 2 := abs_sub_round theta
  have hperiod : addChar theta 1 = addChar delta 1 := by
    have htheta : theta = delta + (round theta : ℤ) := by
      dsimp [delta]
      ring
    rw [htheta, CookMagyarArcs.addChar_add_int]
  rw [hperiod]
  exact four_mul_abs_le_norm_addChar_sub_one_of_abs_le_half hdelta

/-- The classical finite linear-sum bound with the zero-distance case
spelled out. Lean's real inverse sends zero to zero, so using a bare
`min(X, (2‖θ‖)⁻¹)` at distance zero would be false. -/
theorem norm_linearAddCharSum_le_distanceEnvelope
    (theta : ℝ) (X : ℕ) :
    ‖∑ m ∈ Finset.range X, addChar theta m‖ ≤
      if |theta - (round theta : ℤ)| = 0 then (X : ℝ)
      else min (X : ℝ) (1 / (2 * |theta - (round theta : ℤ)|)) := by
  let d : ℝ := |theta - (round theta : ℤ)|
  by_cases hd0 : d = 0
  · simpa only [d, hd0, if_pos] using norm_linearAddCharSum_le_length theta X
  · have hd : 0 < d := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hd0)
    have hchord : 4 * d ≤ ‖addChar theta 1 - 1‖ :=
      four_mul_abs_sub_round_le_norm_addChar_sub_one theta
    have hnorm : 0 < ‖addChar theta 1 - 1‖ :=
      (by positivity : 0 < 4 * d).trans_le hchord
    have hz : addChar theta 1 ≠ 1 := by
      intro he
      simp [he] at hnorm
    have hfrac : 2 / ‖addChar theta 1 - 1‖ ≤ 1 / (2 * d) := by
      exact (div_le_div_iff₀ hnorm (by positivity : 0 < 2 * d)).2
        (by nlinarith [hchord])
    have hgeom := norm_linearAddCharSum_le_two_div theta X hz
    have hlen := norm_linearAddCharSum_le_length theta X
    have hmin : ‖∑ m ∈ Finset.range X, addChar theta m‖ ≤
        min (X : ℝ) (1 / (2 * d)) := le_min hlen (hgeom.trans hfrac)
    simpa [d, hd0] using hmin

/-- Translation of the summation interval only introduces a unit phase. -/
theorem norm_shiftedLinearAddCharSum_le_distanceEnvelope
    (theta : ℝ) (M X : ℕ) :
    ‖∑ m ∈ Finset.range X, addChar theta (M + m)‖ ≤
      if |theta - (round theta : ℤ)| = 0 then (X : ℝ)
      else min (X : ℝ) (1 / (2 * |theta - (round theta : ℤ)|)) := by
  have heq : (∑ m ∈ Finset.range X, addChar theta (M + m)) =
      addChar theta M * (∑ m ∈ Finset.range X, addChar theta m) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    exact addChar_add theta M m
  rw [heq, norm_mul, norm_addChar, one_mul]
  exact norm_linearAddCharSum_le_distanceEnvelope theta X

/-- Arbitrary lower polynomial coefficients leave a unit prefactor in
the final linear sum after cubic differencing. -/
theorem norm_unitPhase_shiftedLinearAddCharSum_le_distanceEnvelope
    (theta : ℝ) (M X : ℕ) (c : ℂ) (hc : ‖c‖ = 1) :
    ‖∑ m ∈ Finset.range X, c * addChar theta (M + m)‖ ≤
      if |theta - (round theta : ℤ)| = 0 then (X : ℝ)
      else min (X : ℝ) (1 / (2 * |theta - (round theta : ℤ)|)) := by
  rw [← Finset.mul_sum, norm_mul, hc, one_mul]
  exact norm_shiftedLinearAddCharSum_le_distanceEnvelope theta M X

end CookMagyarCircle
end SystolicGrowth
