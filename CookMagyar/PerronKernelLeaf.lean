module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-!
# A first absolute bound for the scalar Perron kernel

On a vertical line of positive real part, the kernel's numerator has a
constant norm and its denominator has norm at least the real part. This
pointwise bound is the elementary domination input for interchanging an
absolutely convergent Dirichlet series with a finite vertical integral.

It does not prove cancellation in the truncated kernel. That analytic
estimate is still required for `exercise_truncatedPerron_error`.
-/

namespace SystolicGrowth.CookMagyarCircle

open MeasureTheory

/-- The scalar factor appearing after the logarithmic derivative is expanded
as a Dirichlet series on a vertical Perron contour. -/
noncomputable def perronScalarKernel (x : ℝ) (k : ℕ) (σ t : ℝ) : ℂ :=
  ((x / (k : ℝ) : ℝ) : ℂ) ^ ((σ : ℂ) + Complex.I * (t : ℂ)) /
    ((σ : ℂ) + Complex.I * (t : ℂ))

/-- Pointwise absolute domination of one Perron integrand. The positive
integer `k` is the index of the future twisted von Mangoldt series. -/
theorem norm_perronScalarKernel_le (x σ t : ℝ) (k : ℕ)
    (hx : 0 < x) (hk : 0 < k) (hσ : 0 < σ) :
    ‖perronScalarKernel x k σ t‖ ≤ (x / (k : ℝ)) ^ σ / σ := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  have hy : 0 < x / (k : ℝ) := div_pos hx hkreal
  let s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
  have hsre : s.re = σ := by simp [s]
  have hden : σ ≤ ‖s‖ := by
    simpa only [hsre] using Complex.re_le_norm s
  calc
    ‖perronScalarKernel x k σ t‖ = (x / (k : ℝ)) ^ σ / ‖s‖ := by
      change ‖((x / (k : ℝ) : ℝ) : ℂ) ^ s / s‖ = _
      rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy, hsre]
    _ ≤ (x / (k : ℝ)) ^ σ / σ :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hy.le σ) hσ hden

/-- The scalar Perron kernel is continuous along a vertical line with
positive real part. -/
theorem continuous_perronScalarKernel (x σ : ℝ) (k : ℕ)
    (hx : 0 < x) (hk : 0 < k) (hσ : 0 < σ) :
    Continuous (fun t : ℝ => perronScalarKernel x k σ t) := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  have hy : 0 < x / (k : ℝ) := div_pos hx hkreal
  have hbase : ((x / (k : ℝ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hy.ne'
  have hs : Continuous (fun t : ℝ => (σ : ℂ) + Complex.I * (t : ℂ)) := by
    fun_prop
  have hden (t : ℝ) : (σ : ℂ) + Complex.I * (t : ℂ) ≠ 0 := by
    apply Complex.ne_zero_of_re_pos
    simpa using hσ
  have hpow : Continuous
      (fun t : ℝ => ((x / (k : ℝ) : ℝ) : ℂ) ^
        ((σ : ℂ) + Complex.I * (t : ℂ))) :=
    hs.const_cpow (Or.inl hbase)
  convert hpow.div hs hden using 1
  funext t
  rfl

/-- A finite Perron contour therefore has a genuine interval integral for
each positive integer coefficient index. -/
theorem intervalIntegrable_perronScalarKernel (x σ H : ℝ) (k : ℕ)
    (hx : 0 < x) (hk : 0 < k) (hσ : 0 < σ) :
    IntervalIntegrable (fun t : ℝ => perronScalarKernel x k σ t)
      volume (-H) H :=
  (continuous_perronScalarKernel x σ k hx hk hσ).intervalIntegrable (-H) H

/-- A half-integer Perron endpoint stays at least half a unit from every
integer index, including zero. -/
theorem perronHalfInteger_gap (m k : ℕ) :
    (1 / 2 : ℝ) ≤ |((m : ℝ) + 1 / 2) - (k : ℝ)| := by
  by_cases hkm : k ≤ m
  · have hkmR : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hkm
    rw [abs_of_nonneg (by linarith : 0 ≤ (m : ℝ) + 1 / 2 - (k : ℝ))]
    linarith
  · have hmk : m + 1 ≤ k := by omega
    have hmkR : (m : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hmk
    rw [abs_of_nonpos (by linarith : (m : ℝ) + 1 / 2 - (k : ℝ) ≤ 0)]
    linarith

/-- The imaginary coordinate also controls the denominator. In particular,
this supplies a height-dependent bound for the endpoint terms of a truncated
vertical contour, without asserting cancellation of its integral. -/
theorem norm_perronScalarKernel_le_div_max (x σ t : ℝ) (k : ℕ)
    (hx : 0 < x) (hk : 0 < k) (hσ : 0 < σ) :
    ‖perronScalarKernel x k σ t‖ ≤
      (x / (k : ℝ)) ^ σ / max σ |t| := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  have hy : 0 < x / (k : ℝ) := div_pos hx hkreal
  let s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
  have hsre : s.re = σ := by simp [s]
  have hsim : s.im = t := by simp [s]
  have hden : max σ |t| ≤ ‖s‖ := by
    apply max_le
    · simpa only [hsre] using Complex.re_le_norm s
    · simpa only [hsim] using Complex.abs_im_le_norm s
  calc
    ‖perronScalarKernel x k σ t‖ = (x / (k : ℝ)) ^ σ / ‖s‖ := by
      change ‖((x / (k : ℝ) : ℝ) : ℂ) ^ s / s‖ = _
      rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy, hsre]
    _ ≤ (x / (k : ℝ)) ^ σ / max σ |t| :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hy.le σ)
        (lt_of_lt_of_le hσ (le_max_left σ |t|)) hden

/-- Relative distance is controlled by the logarithmic distance of two
positive reals. This converts the half-integer separation into the middle
range Perron denominator used in the integrated kernel estimate. -/
theorem perronLogRatio_gap (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    |x - y| / max x y ≤ |Real.log (x / y)| := by
  by_cases hxy : y ≤ x
  · have hratio : 1 ≤ x / y := (le_div_iff₀ hy).2 (by linarith)
    have hlog : 0 ≤ Real.log (x / y) := Real.log_nonneg hratio
    calc
      |x - y| / max x y = 1 - (x / y)⁻¹ := by
        rw [abs_of_nonneg (sub_nonneg.mpr hxy), max_eq_left hxy]
        field_simp [ne_of_gt hx, ne_of_gt hy]
      _ ≤ Real.log (x / y) :=
        Real.one_sub_inv_le_log_of_pos (div_pos hx hy)
      _ = |Real.log (x / y)| := (abs_of_nonneg hlog).symm
  · have hyx : x ≤ y := le_of_not_ge hxy
    have hratio : x / y ≤ 1 := by
      refine (div_le_iff₀ hy).2 ?_
      simpa only [one_mul] using hyx
    have hlog : Real.log (x / y) ≤ 0 := by
      have h := Real.log_le_sub_one_of_pos (div_pos hx hy)
      linarith
    calc
      |x - y| / max x y = 1 - x / y := by
        rw [abs_of_nonpos (sub_nonpos.mpr hyx), max_eq_right hyx]
        field_simp [ne_of_gt hx, ne_of_gt hy]
        linarith
      _ ≤ -Real.log (x / y) := by
        have h := Real.log_le_sub_one_of_pos (div_pos hx hy)
        linarith
      _ = |Real.log (x / y)| := (abs_of_nonpos hlog).symm

/-- The scalar Perron indicator at the half-integer endpoint is exactly the
repository's inclusive natural-number cutoff. -/
theorem perronHalfInteger_lt_iff (m k : ℕ) :
    (k : ℝ) < (m : ℝ) + 1 / 2 ↔ k ≤ m := by
  constructor
  · intro hk
    by_contra hkm
    have hmk : m + 1 ≤ k := by omega
    have hcast : (m : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hmk
    linarith
  · intro hk
    have hcast : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hk
    linarith

end SystolicGrowth.CookMagyarCircle

#check Complex.norm_cpow_eq_rpow_re_of_pos
#check Complex.re_le_norm
#check div_le_div_of_nonneg_left
#print axioms SystolicGrowth.CookMagyarCircle.norm_perronScalarKernel_le
#print axioms SystolicGrowth.CookMagyarCircle.continuous_perronScalarKernel
#print axioms SystolicGrowth.CookMagyarCircle.intervalIntegrable_perronScalarKernel
#print axioms SystolicGrowth.CookMagyarCircle.perronHalfInteger_gap
#print axioms SystolicGrowth.CookMagyarCircle.norm_perronScalarKernel_le_div_max
#print axioms SystolicGrowth.CookMagyarCircle.perronLogRatio_gap
#print axioms SystolicGrowth.CookMagyarCircle.perronHalfInteger_lt_iff
