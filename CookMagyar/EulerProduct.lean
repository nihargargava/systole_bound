module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.NumberTheory.SumPrimeReciprocals

@[expose] public section

open scoped Topology

namespace SystolicGrowth
namespace CookMagyarEulerProduct

/-! # Positivity of absolutely convergent Euler products

This is the abstract analytic step used after the local-factor estimate
`|μ_p(T) - 1| ≪ p⁻¹⁻δ`.  It is independent of the cubic polynomial: an
absolutely summable perturbation of `1`, with every factor positive, has a
strictly positive infinite product.
-/

/-- Absolute summability of the deviations from `1` implies ordinary
summability of those deviations. -/
theorem summable_sub_one_of_summable_abs
    {ι : Type*} {f : ι → ℝ}
    (h : Summable fun i ↦ |f i - 1|) :
    Summable fun i ↦ f i - 1 := by
  apply Summable.of_norm
  simpa only [Real.norm_eq_abs] using h

/-- A positive, absolutely convergent perturbation of the constant Euler
factor `1` has a strictly positive product. -/
theorem zero_lt_tprod_of_pos_of_summable_abs_sub_one
    {ι : Type*} {f : ι → ℝ}
    (hpos : ∀ i, 0 < f i)
    (hsum : Summable fun i ↦ |f i - 1|) :
    0 < ∏' i, f i := by
  let u : ι → ℝ := fun i ↦ f i - 1
  have hu : Summable u := by
    exact summable_sub_one_of_summable_abs hsum
  have hlog : Summable fun i ↦ Real.log (f i) := by
    have h := Real.summable_log_one_add_of_summable hu
    exact h.congr fun i ↦ by
      simp only [u]
      congr 1
      ring
  rw [← Real.rexp_tsum_eq_tprod hpos hlog]
  exact Real.exp_pos _

/-- In particular the product cannot vanish. -/
theorem tprod_ne_zero_of_pos_of_summable_abs_sub_one
    {ι : Type*} {f : ι → ℝ}
    (hpos : ∀ i, 0 < f i)
    (hsum : Summable fun i ↦ |f i - 1|) :
    ∏' i, f i ≠ 0 :=
  ne_of_gt (zero_lt_tprod_of_pos_of_summable_abs_sub_one hpos hsum)

/-- The power-saving local-factor estimate used in Cook--Magyar implies
absolute summability over the primes. -/
theorem summable_abs_sub_one_of_prime_rpow_bound
    {mu : Nat.Primes → ℝ} {C delta : ℝ}
    (hdelta : 0 < delta)
    (hbound : ∀ p : Nat.Primes,
      |mu p - 1| ≤ C * (p : ℝ) ^ (-(1 + delta))) :
    Summable fun p : Nat.Primes ↦ |mu p - 1| := by
  have hseries :
      Summable fun p : Nat.Primes ↦
        C * (p : ℝ) ^ (-(1 + delta)) := by
    apply Summable.mul_left
    exact Nat.Primes.summable_rpow.mpr (by linarith)
  exact hseries.of_nonneg_of_le
    (fun _ ↦ abs_nonneg _)
    hbound

/-- Uniform `p^(-1-δ)` control and positivity are enough for a strictly
positive Euler product. -/
theorem zero_lt_tprod_of_prime_rpow_bound
    {mu : Nat.Primes → ℝ} {C delta : ℝ}
    (hpos : ∀ p, 0 < mu p)
    (hdelta : 0 < delta)
    (hbound : ∀ p : Nat.Primes,
      |mu p - 1| ≤ C * (p : ℝ) ^ (-(1 + delta))) :
    0 < ∏' p : Nat.Primes, mu p :=
  zero_lt_tprod_of_pos_of_summable_abs_sub_one hpos
    (summable_abs_sub_one_of_prime_rpow_bound hdelta hbound)

/-- Elementary logarithmic lower bound on the half-unit disk around `1`.
This is the quantitative inequality behind a uniform Euler-tail bound. -/
theorem neg_two_mul_abs_le_log_one_add {u : ℝ}
    (hu : |u| ≤ 1 / 2) :
    -2 * |u| ≤ Real.log (1 + u) := by
  have hulower : -(1 / 2 : ℝ) ≤ u := (neg_le_of_abs_le hu)
  have hpos : 0 < 1 + u := by linarith
  have hbasic := Real.one_sub_inv_le_log_of_pos hpos
  have hid : 1 - (1 + u)⁻¹ = u / (1 + u) := by
    field_simp
    ring
  rw [hid] at hbasic
  by_cases hu0 : 0 ≤ u
  · rw [abs_of_nonneg hu0]
    have hfrac : 0 ≤ u / (1 + u) := div_nonneg hu0 hpos.le
    linarith
  · have hu0' : u ≤ 0 := le_of_not_ge hu0
    rw [abs_of_nonpos hu0']
    have hmul : 2 * u * (1 + u) ≤ u := by
      nlinarith
    have hfrac : 2 * u ≤ u / (1 + u) :=
      (le_div_iff₀ hpos).2 hmul
    linarith

/-- A summable uniform majorant for the deviations gives an explicit lower
bound for the infinite product.  This is the form needed to make singular
series positivity uniform in a moving target. -/
theorem exp_neg_two_tsum_le_tprod
    {ι : Type*} {f a : ι → ℝ}
    (ha : Summable a)
    (ha_half : ∀ i, a i ≤ 1 / 2)
    (hdev : ∀ i, |f i - 1| ≤ a i) :
    Real.exp (-2 * ∑' i, a i) ≤ ∏' i, f i := by
  have hpos : ∀ i, 0 < f i := by
    intro i
    have hlower : -a i ≤ f i - 1 := neg_le_of_abs_le (hdev i)
    have hhalf := ha_half i
    linarith
  have hu : Summable fun i ↦ f i - 1 := by
    apply Summable.of_norm_bounded ha
    intro i
    simpa only [Real.norm_eq_abs] using hdev i
  have hlog : Summable fun i ↦ Real.log (f i) := by
    have h := Real.summable_log_one_add_of_summable hu
    exact h.congr fun i ↦ by
      congr 1
      ring
  have hterm : ∀ i, -2 * a i ≤ Real.log (f i) := by
    intro i
    have habs : |f i - 1| ≤ 1 / 2 := (hdev i).trans (ha_half i)
    have hlogLower := neg_two_mul_abs_le_log_one_add habs
    have hmul : -2 * a i ≤ -2 * |f i - 1| := by
      nlinarith [hdev i]
    calc
      -2 * a i ≤ -2 * |f i - 1| := hmul
      _ ≤ Real.log (1 + (f i - 1)) := hlogLower
      _ = Real.log (f i) := by
        congr 1
        ring
  have hneg : Summable fun i ↦ -2 * a i := ha.mul_left (-2)
  have hsum : (∑' i, -2 * a i) ≤ ∑' i, Real.log (f i) :=
    hneg.tsum_le_tsum hterm hlog
  rw [← Real.rexp_tsum_eq_tprod hpos hlog]
  apply Real.exp_le_exp.mpr
  simpa only [tsum_mul_left] using hsum

end CookMagyarEulerProduct
end SystolicGrowth
