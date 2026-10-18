module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.PerronOscillatoryKernel
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

@[expose] public section

/-!
# Harmonic summation at a half-integer Perron endpoint

The middle range of the truncated Perron remainder contains reciprocal
distances to `m + 1/2`. Reflection pairs the integer indices on either side
of that endpoint and bounds the whole range by a harmonic sum. This is the
arithmetic summation step after the scalar oscillatory kernel estimate.
-/

namespace SystolicGrowth.CookMagyarCircle

open Finset

/-- The reciprocal gaps on the symmetric integer range are twice the
one-sided half-integer harmonic sum. -/
theorem sum_perronHalfInteger_inv_gap_eq (m : ℕ) :
    (∑ k ∈ range (2 * (m + 1)),
      1 / |((m : ℝ) + 1 / 2) - (k : ℝ)|) =
      2 * ∑ j ∈ range (m + 1), 1 / ((j : ℝ) + 1 / 2) := by
  have hleft :
      (∑ k ∈ range (m + 1), 1 / |((m : ℝ) + 1 / 2) - (k : ℝ)|) =
        ∑ j ∈ range (m + 1), 1 / ((j : ℝ) + 1 / 2) := by
    rw [← sum_range_reflect (fun k : ℕ =>
      1 / |((m : ℝ) + 1 / 2) - (k : ℝ)|) (m + 1)]
    apply sum_congr rfl
    intro j hj
    have hjm : j ≤ m := Nat.le_of_lt_succ (mem_range.mp hj)
    have hcast : ((m + 1 - 1 - j : ℕ) : ℝ) = (m : ℝ) - (j : ℝ) := by
      simp [Nat.cast_sub hjm]
    rw [hcast]
    have hgap : (m : ℝ) + 1 / 2 - ((m : ℝ) - (j : ℝ)) =
        (j : ℝ) + 1 / 2 := by ring
    rw [hgap, abs_of_pos (by positivity)]
  have hright :
      (∑ j ∈ range (m + 1),
        1 / |((m : ℝ) + 1 / 2) - ((m + 1 + j : ℕ) : ℝ)|) =
        ∑ j ∈ range (m + 1), 1 / ((j : ℝ) + 1 / 2) := by
    apply sum_congr rfl
    intro j _
    have hgap : (m : ℝ) + 1 / 2 - ((m + 1 + j : ℕ) : ℝ) =
        -((j : ℝ) + 1 / 2) := by push_cast; ring
    rw [hgap, abs_neg, abs_of_pos (by positivity)]
  rw [show 2 * (m + 1) = (m + 1) + (m + 1) by omega, sum_range_add,
    hleft, hright]
  ring

/-- Summing reciprocal half-integer gaps costs only one logarithm. -/
theorem sum_perronHalfInteger_inv_gap_le (m : ℕ) :
    (∑ k ∈ range (2 * (m + 1)),
      1 / |((m : ℝ) + 1 / 2) - (k : ℝ)|) ≤
        4 * (1 + Real.log ((m : ℝ) + 1)) := by
  have hterm (j : ℕ) :
      1 / ((j : ℝ) + 1 / 2) ≤ 2 * ((j : ℝ) + 1)⁻¹ := by
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    rw [show 2 * ((j : ℝ) + 1)⁻¹ = 2 / ((j : ℝ) + 1) by ring]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    linarith
  have hsum := sum_le_sum (s := range (m + 1)) (fun j _ => hterm j)
  have hHarmonic : (∑ j ∈ range (m + 1), ((j : ℝ) + 1)⁻¹) =
      (harmonic (m + 1) : ℝ) := by
    simp [harmonic]
  rw [sum_perronHalfInteger_inv_gap_eq]
  calc
    _ ≤ 2 * ∑ j ∈ range (m + 1), 2 * ((j : ℝ) + 1)⁻¹ := by gcongr
    _ = 4 * (harmonic (m + 1) : ℝ) := by rw [← mul_sum, hHarmonic]; ring
    _ ≤ 4 * (1 + Real.log ((m : ℝ) + 1)) := by
      gcongr
      simpa using harmonic_le_one_add_log (m + 1)

/-- Von Mangoldt weights add the second logarithm in the middle-range
Perron remainder. The estimate applies to every subrange of the symmetric
integer window, so strict source cutoffs can be retained. -/
theorem sum_vonMangoldt_perronHalfInteger_inv_gap_le
    (m : ℕ) (s : Finset ℕ) (hs : s ⊆ range (2 * (m + 1))) :
    (∑ k ∈ s,
      ArithmeticFunction.vonMangoldt k / |((m : ℝ) + 1 / 2) - (k : ℝ)|) ≤
        4 * Real.log (2 * ((m : ℝ) + 1)) *
          (1 + Real.log ((m : ℝ) + 1)) := by
  have hlog : 0 ≤ Real.log (2 * ((m : ℝ) + 1)) :=
    Real.log_nonneg (by have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith)
  have hweight (k : ℕ) (hk : k ∈ range (2 * (m + 1))) :
      ArithmeticFunction.vonMangoldt k ≤ Real.log (2 * ((m : ℝ) + 1)) := by
    by_cases hk0 : k = 0
    · simpa [hk0] using hlog
    · apply ArithmeticFunction.vonMangoldt_le_log.trans
      have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk0
      apply Real.log_le_log hkpos
      have hkr : (k : ℝ) < 2 * ((m : ℝ) + 1) := by
        exact_mod_cast mem_range.mp hk
      exact hkr.le
  have hsum :
      (∑ k ∈ range (2 * (m + 1)),
        ArithmeticFunction.vonMangoldt k / |((m : ℝ) + 1 / 2) - (k : ℝ)|) ≤
      Real.log (2 * ((m : ℝ) + 1)) *
        ∑ k ∈ range (2 * (m + 1)),
          1 / |((m : ℝ) + 1 / 2) - (k : ℝ)| := by
    rw [mul_sum]
    apply sum_le_sum
    intro k hk
    simpa only [mul_one_div] using div_le_div_of_nonneg_right (hweight k hk)
      (abs_nonneg (((m : ℝ) + 1 / 2) - (k : ℝ)))
  calc
    _ ≤ ∑ k ∈ range (2 * (m + 1)),
        ArithmeticFunction.vonMangoldt k / |((m : ℝ) + 1 / 2) - (k : ℝ)| := by
      apply sum_le_sum_of_subset_of_nonneg hs
      intro k _ _
      exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (abs_nonneg _)
    _ ≤ Real.log (2 * ((m : ℝ) + 1)) *
        ∑ k ∈ range (2 * (m + 1)),
          1 / |((m : ℝ) + 1 / 2) - (k : ℝ)| := hsum
    _ ≤ Real.log (2 * ((m : ℝ) + 1)) *
        (4 * (1 + Real.log ((m : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left (sum_perronHalfInteger_inv_gap_le m) hlog
    _ = _ := by ring

/-- In the integer middle window, logarithmic frequency separation is
controlled by the reciprocal arithmetic gap at the half-integer endpoint. -/
theorem perronHalfInteger_inv_log_le (m k : ℕ) (hk : 0 < k)
    (hkmax : (k : ℝ) ≤ 2 * ((m : ℝ) + 1 / 2)) :
    1 / |Real.log (((m : ℝ) + 1 / 2) / (k : ℝ))| ≤
      (2 * ((m : ℝ) + 1 / 2)) / |((m : ℝ) + 1 / 2) - (k : ℝ)| := by
  have hx : (0 : ℝ) < (m : ℝ) + 1 / 2 := by positivity
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hgap : 0 < |((m : ℝ) + 1 / 2) - (k : ℝ)| :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (perronHalfInteger_gap m k)
  have hmax : 0 < max ((m : ℝ) + 1 / 2) (k : ℝ) := lt_max_of_lt_left hx
  have hsep := perronLogRatio_gap ((m : ℝ) + 1 / 2) (k : ℝ) hx hkpos
  have hfreq : 0 < |Real.log (((m : ℝ) + 1 / 2) / (k : ℝ))| :=
    (div_pos hgap hmax).trans_le hsep
  have hmaxle : max ((m : ℝ) + 1 / 2) (k : ℝ) ≤ 2 * ((m : ℝ) + 1 / 2) :=
    max_le (by linarith) hkmax
  apply (div_le_div_iff₀ hfreq hgap).2
  calc
    1 * |((m : ℝ) + 1 / 2) - (k : ℝ)| ≤
        |Real.log (((m : ℝ) + 1 / 2) / (k : ℝ))| *
          max ((m : ℝ) + 1 / 2) (k : ℝ) := by
      simpa using (div_le_iff₀ hmax).1 hsep
    _ ≤ (2 * ((m : ℝ) + 1 / 2)) *
        |Real.log (((m : ℝ) + 1 / 2) / (k : ℝ))| := by
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hmaxle hfreq.le

/-- The logarithmic-denominator middle-range sum has the two logarithms
required by the uniform truncated-Perron error budget. -/
theorem sum_vonMangoldt_perronHalfInteger_inv_log_le
    (m : ℕ) (s : Finset ℕ) (hs : s ⊆ range (2 * (m + 1)))
    (hkpos : ∀ k ∈ s, 0 < k) :
    (∑ k ∈ s, ArithmeticFunction.vonMangoldt k /
      |Real.log (((m : ℝ) + 1 / 2) / (k : ℝ))|) ≤
      8 * ((m : ℝ) + 1 / 2) * Real.log (2 * ((m : ℝ) + 1)) *
        (1 + Real.log ((m : ℝ) + 1)) := by
  have hsum :
      (∑ k ∈ s, ArithmeticFunction.vonMangoldt k /
        |Real.log (((m : ℝ) + 1 / 2) / (k : ℝ))|) ≤
      (2 * ((m : ℝ) + 1 / 2)) *
        ∑ k ∈ s, ArithmeticFunction.vonMangoldt k /
          |((m : ℝ) + 1 / 2) - (k : ℝ)| := by
    rw [mul_sum]
    apply sum_le_sum
    intro k hk
    have hknat : k ≤ 2 * m + 1 := by have h := mem_range.mp (hs hk); omega
    have hkreal : (k : ℝ) ≤ 2 * ((m : ℝ) + 1 / 2) := by
      have h : (k : ℝ) ≤ 2 * (m : ℝ) + 1 := by exact_mod_cast hknat
      linarith
    have h := mul_le_mul_of_nonneg_left
      (perronHalfInteger_inv_log_le m k (hkpos k hk) hkreal)
      (ArithmeticFunction.vonMangoldt_nonneg (n := k))
    convert h using 1 <;> ring
  calc
    _ ≤ (2 * ((m : ℝ) + 1 / 2)) *
        ∑ k ∈ s, ArithmeticFunction.vonMangoldt k /
          |((m : ℝ) + 1 / 2) - (k : ℝ)| := hsum
    _ ≤ (2 * ((m : ℝ) + 1 / 2)) *
        (4 * Real.log (2 * ((m : ℝ) + 1)) *
          (1 + Real.log ((m : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left (sum_vonMangoldt_perronHalfInteger_inv_gap_le m s hs)
        (by positivity)
    _ = _ := by ring

/-- The middle-window coefficient sum fits the exact `log(m+2)^2` budget
used by the project's uniform Perron theorem. -/
theorem sum_vonMangoldt_perronHalfInteger_inv_log_le_major_budget
    (m : ℕ) (s : Finset ℕ) (hs : s ⊆ range (2 * (m + 1)))
    (hkpos : ∀ k ∈ s, 0 < k) :
    (∑ k ∈ s, ArithmeticFunction.vonMangoldt k /
      |Real.log (((m : ℝ) + 1 / 2) / (k : ℝ))|) ≤
      48 * ((m : ℝ) + 1 / 2) * Real.log ((m : ℝ) + 2) ^ 2 := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hlog2 : Real.log 2 ≤ Real.log ((m : ℝ) + 2) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hlogM : Real.log ((m : ℝ) + 1) ≤ Real.log ((m : ℝ) + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlogM0 : 0 ≤ Real.log ((m : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hL0 : 0 ≤ Real.log ((m : ℝ) + 2) := by linarith
  have hfirst : Real.log (2 * ((m : ℝ) + 1)) ≤
      2 * Real.log ((m : ℝ) + 2) := by
    rw [Real.log_mul (by norm_num) (by positivity)]
    linarith
  have hsecond : 1 + Real.log ((m : ℝ) + 1) ≤
      3 * Real.log ((m : ℝ) + 2) := by linarith
  calc
    _ ≤ 8 * ((m : ℝ) + 1 / 2) * Real.log (2 * ((m : ℝ) + 1)) *
        (1 + Real.log ((m : ℝ) + 1)) :=
      sum_vonMangoldt_perronHalfInteger_inv_log_le m s hs hkpos
    _ ≤ 8 * ((m : ℝ) + 1 / 2) * (2 * Real.log ((m : ℝ) + 2)) *
        (3 * Real.log ((m : ℝ) + 2)) := by gcongr
    _ = _ := by ring

/-- The scalar amplitude stays at most four on the middle Perron window
when the absolute-convergence abscissa is at most two. -/
theorem perron_middle_amplitude_le_four
    (x σ : ℝ) (k : ℕ) (hx : 0 < x) (hk : 0 < k)
    (hσ : 0 ≤ σ) (hσmax : σ ≤ 2) (hlo : x / 2 ≤ (k : ℝ)) :
    (x / (k : ℝ)) ^ σ ≤ 4 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hratio : x / (k : ℝ) ≤ 2 := (div_le_iff₀ hkpos).2 (by linarith)
  calc
    _ ≤ (2 : ℝ) ^ σ := Real.rpow_le_rpow (div_pos hx hkpos).le hratio hσ
    _ ≤ (2 : ℝ) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hσmax
    _ = 4 := by norm_num

/-- The entire von-Mangoldt-weighted middle-range scalar truncation error
fits the project's Perron budget. The infinite phase contour has not been
identified with its indicator value in this theorem. -/
theorem sum_middle_perronScalarKernel_truncation_error_le
    (m : ℕ) (s : Finset ℕ) (σ H : ℝ) (hσ : 0 < σ) (hσmax : σ ≤ 2)
    (hH : 0 < H) (hs : s ⊆ range (2 * (m + 1)))
    (hkpos : ∀ k ∈ s, 0 < k)
    (hlo : ∀ k ∈ s, ((m : ℝ) + 1 / 2) / 2 ≤ (k : ℝ)) :
    (∑ k ∈ s, ArithmeticFunction.vonMangoldt k *
      ‖(((((m : ℝ) + 1 / 2) / (k : ℝ)) ^ σ : ℝ) : ℂ) *
          perronPhaseContourLimit σ (Real.log (((m : ℝ) + 1 / 2) / (k : ℝ))) -
        ∫ t in -H..H, perronScalarKernel ((m : ℝ) + 1 / 2) k σ t‖) ≤
      3456 * ((m : ℝ) + 1 / 2) * Real.log ((m : ℝ) + 2) ^ 2 / H := by
  have hx : (0 : ℝ) < (m : ℝ) + 1 / 2 := by positivity
  have hpoint (k : ℕ) (hk : k ∈ s) :
      ArithmeticFunction.vonMangoldt k *
        ‖(((((m : ℝ) + 1 / 2) / (k : ℝ)) ^ σ : ℝ) : ℂ) *
            perronPhaseContourLimit σ (Real.log (((m : ℝ) + 1 / 2) / (k : ℝ))) -
          ∫ t in -H..H, perronScalarKernel ((m : ℝ) + 1 / 2) k σ t‖ ≤
      (72 / H) * (ArithmeticFunction.vonMangoldt k /
        |Real.log (((m : ℝ) + 1 / 2) / (k : ℝ))|) := by
    have hlog := perronHalfInteger_log_ne_zero m k (hkpos k hk)
    have herr := norm_perronScalarKernel_limit_sub_integral_le
      ((m : ℝ) + 1 / 2) σ H k hx (hkpos k hk) hσ hH hlog
    have hamp := perron_middle_amplitude_le_four
      ((m : ℝ) + 1 / 2) σ k hx (hkpos k hk) hσ.le hσmax (hlo k hk)
    have hbound : 18 * (((m : ℝ) + 1 / 2) / (k : ℝ)) ^ σ /
        (H * |Real.log (((m : ℝ) + 1 / 2) / (k : ℝ))|) ≤
      72 / (H * |Real.log (((m : ℝ) + 1 / 2) / (k : ℝ))|) := by
      gcongr
      linarith
    calc
      _ ≤ ArithmeticFunction.vonMangoldt k *
          (72 / (H * |Real.log (((m : ℝ) + 1 / 2) / (k : ℝ))|)) :=
        mul_le_mul_of_nonneg_left (herr.trans hbound) ArithmeticFunction.vonMangoldt_nonneg
      _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring
  calc
    _ ≤ ∑ k ∈ s, (72 / H) * (ArithmeticFunction.vonMangoldt k /
        |Real.log (((m : ℝ) + 1 / 2) / (k : ℝ))|) := sum_le_sum hpoint
    _ = (72 / H) * ∑ k ∈ s, ArithmeticFunction.vonMangoldt k /
        |Real.log (((m : ℝ) + 1 / 2) / (k : ℝ))| := (mul_sum _ _ _).symm
    _ ≤ (72 / H) *
        (48 * ((m : ℝ) + 1 / 2) * Real.log ((m : ℝ) + 2) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (sum_vonMangoldt_perronHalfInteger_inv_log_le_major_budget m s hs hkpos)
        (by positivity)
    _ = _ := by ring

end SystolicGrowth.CookMagyarCircle

#print axioms SystolicGrowth.CookMagyarCircle.sum_perronHalfInteger_inv_gap_eq
#print axioms SystolicGrowth.CookMagyarCircle.sum_perronHalfInteger_inv_gap_le
#print axioms SystolicGrowth.CookMagyarCircle.sum_vonMangoldt_perronHalfInteger_inv_gap_le
#print axioms SystolicGrowth.CookMagyarCircle.perronHalfInteger_inv_log_le
#print axioms SystolicGrowth.CookMagyarCircle.sum_vonMangoldt_perronHalfInteger_inv_log_le
#print axioms SystolicGrowth.CookMagyarCircle.sum_vonMangoldt_perronHalfInteger_inv_log_le_major_budget
#print axioms SystolicGrowth.CookMagyarCircle.sum_middle_perronScalarKernel_truncation_error_le
