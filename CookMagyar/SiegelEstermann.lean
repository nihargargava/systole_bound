module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.NumberTheory.LSeries.Positivity
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp

@[expose] public section

/-!
# The quantitative truncation in Estermann's lemma

This is the real power-series step in Montgomery--Vaughan, Lemma 11.13
(printed pages 371--372).  The coefficients are those of `ζ(s) f(s)` in
powers of `2 - s`; subtracting the pole changes every coefficient by `f(1)`.
The analytic application must construct these coefficients, their
nonnegativity, the pole-subtracted expansion, and the Cauchy bound.
-/

namespace SystolicGrowth.CookMagyarCircle

open Finset Metric
open scoped ComplexOrder Topology NNReal

/-- The source truncation index, chosen to make the geometric remainder at
most one half. -/
noncomputable def estermannTruncation (M : ℝ) : ℕ :=
  Nat.floor (Real.log (80 * M) / Real.log (10 / 7 : ℝ))

/-- A pole-subtracted expansion with Cauchy's coefficient bound gives the
finite inequality used in Estermann's argument. -/
theorem estermann_truncation_inequality
    {b : ℕ → ℝ} {a M sigma Z : ℝ}
    (hM : 0 ≤ M) (hsigma : 19 / 20 ≤ sigma) (hsigma' : sigma < 1)
    (hb : ∀ k, 0 ≤ b k) (hb0 : 1 ≤ b 0)
    (hcoeff : ∀ k, |b k - a| ≤ 12 * M * (2 / 3 : ℝ) ^ k)
    (hexpansion : HasSum (fun k : ℕ => (b k - a) * (2 - sigma) ^ k)
      (Z + a / (1 - sigma))) (K : ℕ) :
    1 ≤ a * (2 - sigma) ^ (K + 1) / (1 - sigma) + Z +
      40 * M * (7 / 10 : ℝ) ^ (K + 1) := by
  have hu : 0 ≤ 2 - sigma := by linarith
  have hdelta : 0 < 1 - sigma := by linarith
  have hratio : (2 / 3 : ℝ) * (2 - sigma) ≤ 7 / 10 := by linarith
  have hterm (k : ℕ) : ‖(b k - a) * (2 - sigma) ^ k‖ ≤
      (12 * M) * (7 / 10 : ℝ) ^ k := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hu k)]
    calc
      |b k - a| * (2 - sigma) ^ k ≤
          (12 * M * (2 / 3 : ℝ) ^ k) * (2 - sigma) ^ k :=
        mul_le_mul_of_nonneg_right (hcoeff k) (pow_nonneg hu k)
      _ = (12 * M) * ((2 / 3 : ℝ) * (2 - sigma)) ^ k := by rw [mul_pow]; ring
      _ ≤ (12 * M) * (7 / 10 : ℝ) ^ k :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hratio k) (by positivity)
  have htail := norm_sub_le_of_geometric_bound_of_hasSum
    (by norm_num : (7 / 10 : ℝ) < 1) hterm hexpansion (K + 1)
  have htail' : (∑ k ∈ range (K + 1), (b k - a) * (2 - sigma) ^ k) -
      (Z + a / (1 - sigma)) ≤ 40 * M * (7 / 10 : ℝ) ^ (K + 1) := by
    apply le_trans (le_abs_self _)
    simpa only [Real.norm_eq_abs,
      show 12 * M * (7 / 10 : ℝ) ^ (K + 1) / (1 - 7 / 10) =
        40 * M * (7 / 10 : ℝ) ^ (K + 1) by ring] using htail
  have hb_sum : 1 ≤ ∑ k ∈ range (K + 1), b k * (2 - sigma) ^ k := by
    calc
      1 ≤ b 0 * (2 - sigma) ^ 0 := by simpa using hb0
      _ ≤ ∑ k ∈ range (K + 1), b k * (2 - sigma) ^ k :=
        single_le_sum (fun k _ => mul_nonneg (hb k) (pow_nonneg hu k))
          (by simp)
  have hsplit : (∑ k ∈ range (K + 1), (b k - a) * (2 - sigma) ^ k) =
      (∑ k ∈ range (K + 1), b k * (2 - sigma) ^ k) -
        a * ∑ k ∈ range (K + 1), (2 - sigma) ^ k := by
    simp only [sub_mul, sum_sub_distrib, mul_sum]
  have hgeom : (∑ k ∈ range (K + 1), (2 - sigma) ^ k) =
      ((2 - sigma) ^ (K + 1) - 1) / (1 - sigma) := by
    simpa only [show 2 - sigma - 1 = 1 - sigma by ring] using
      geom_sum_eq (by linarith : 2 - sigma ≠ 1) (K + 1)
  rw [hsplit, hgeom] at htail'
  have hid : a * (((2 - sigma) ^ (K + 1) - 1) / (1 - sigma)) +
      a / (1 - sigma) = a * (2 - sigma) ^ (K + 1) / (1 - sigma) := by
    field_simp [ne_of_gt hdelta]
    ring
  linarith

/-- The integer truncation chosen in the source bounds the complete
geometric remainder, including its factor `40 M`. -/
theorem estermann_tail_truncation_bound {M : ℝ} (hM : 1 ≤ M) :
    40 * M * (7 / 10 : ℝ) ^ (estermannTruncation M + 1) ≤ 1 / 2 := by
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hlogpos : 0 < Real.log (10 / 7 : ℝ) := Real.log_pos (by norm_num)
  have hfloor := Nat.lt_floor_add_one (Real.log (80 * M) / Real.log (10 / 7 : ℝ))
  change Real.log (80 * M) / Real.log (10 / 7 : ℝ) <
    (estermannTruncation M : ℝ) + 1 at hfloor
  have hmul : Real.log (80 * M) ≤
      ((estermannTruncation M : ℝ) + 1) * Real.log (10 / 7 : ℝ) :=
    ((div_lt_iff₀ hlogpos).mp hfloor).le
  have hlogratio : Real.log (7 / 10 : ℝ) = -Real.log (10 / 7 : ℝ) := by
    rw [show (7 / 10 : ℝ) = (10 / 7 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hpow : (7 / 10 : ℝ) ^ (estermannTruncation M + 1) ≤ 1 / (80 * M) := by
    apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_pow, hlogratio, one_div, Real.log_inv]
    push_cast
    linarith
  calc
    _ ≤ 40 * M * (1 / (80 * M)) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = 1 / 2 := by field_simp; ring

/-- The source logarithmic truncation has controlled growth throughout
`[19/20, 1)`.  This estimate keeps the final exponent exactly `3 (1 - σ)`. -/
theorem estermann_truncation_power_bound
    {M sigma : ℝ} (hM : 1 ≤ M) (hsigma : 19 / 20 ≤ sigma) (hsigma' : sigma < 1) :
    (2 - sigma) ^ (estermannTruncation M + 1) ≤
      2 * Real.rpow M (3 * (1 - sigma)) := by
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hu : 0 < 2 - sigma := by linarith
  have hu1 : 1 ≤ 2 - sigma := by linarith
  have hu21 : 2 - sigma ≤ 21 / 20 := by linarith
  have hdelta : 0 ≤ 1 - sigma := by linarith
  have hdelta20 : 1 - sigma ≤ 1 / 20 := by linarith
  have hA : 0 ≤ Real.log (2 - sigma) := Real.log_nonneg hu1
  have hAdelta : Real.log (2 - sigma) ≤ 1 - sigma := by
    have := Real.log_le_sub_one_of_pos hu
    linarith
  have hA21 : Real.log (2 - sigma) ≤ Real.log (21 / 20 : ℝ) :=
    Real.log_le_log hu hu21
  have hL : 0 ≤ Real.log M := Real.log_nonneg hM
  have hd : (6 / 17 : ℝ) ≤ Real.log (10 / 7 : ℝ) := by
    have := Real.le_log_one_add_of_nonneg (x := (3 / 7 : ℝ)) (by norm_num)
    norm_num at this ⊢
    exact this
  have hdpos : 0 < Real.log (10 / 7 : ℝ) := by linarith
  have hB : 0 ≤ Real.log (80 : ℝ) := Real.log_nonneg (by norm_num)
  have hBupper : Real.log (80 : ℝ) ≤ 4396 / 1000 := by
    have h3 := Real.log_three_lt_d9
    calc
      Real.log (80 : ℝ) ≤ Real.log ((3 : ℝ) ^ 4) :=
        Real.log_le_log (by norm_num) (by norm_num)
      _ = 4 * Real.log (3 : ℝ) := by rw [Real.log_pow]; norm_num
      _ ≤ 4396 / 1000 := by linarith
  have hquot : Real.log (2 - sigma) / Real.log (10 / 7 : ℝ) ≤
      (17 / 6 : ℝ) * (1 - sigma) := by
    apply (div_le_iff₀ hdpos).mpr
    have := mul_le_mul_of_nonneg_right hd
      (by positivity : 0 ≤ (17 / 6 : ℝ) * (1 - sigma))
    nlinarith
  have hsmall : Real.log (80 : ℝ) *
      (Real.log (2 - sigma) / Real.log (10 / 7 : ℝ)) ≤
        (4396 / 1000 : ℝ) * (17 / 6) * (1 / 20) := by
    calc
      _ ≤ Real.log (80 : ℝ) * ((17 / 6 : ℝ) * (1 - sigma)) :=
        mul_le_mul_of_nonneg_left hquot hB
      _ ≤ (4396 / 1000 : ℝ) * ((17 / 6 : ℝ) * (1 - sigma)) :=
        mul_le_mul_of_nonneg_right hBupper (by positivity)
      _ ≤ (4396 / 1000 : ℝ) * (17 / 6) * (1 / 20) := by nlinarith
  have hlarge : Real.log M *
      (Real.log (2 - sigma) / Real.log (10 / 7 : ℝ)) ≤
        3 * (1 - sigma) * Real.log M := by
    calc
      _ ≤ Real.log M * ((17 / 6 : ℝ) * (1 - sigma)) :=
        mul_le_mul_of_nonneg_left hquot hL
      _ ≤ 3 * (1 - sigma) * Real.log M := by
        nlinarith [mul_nonneg hdelta hL]
  have h40 : (38 / 61 : ℝ) ≤ Real.log (40 / 21 : ℝ) := by
    have := Real.le_log_one_add_of_nonneg (x := (19 / 21 : ℝ)) (by norm_num)
    norm_num at this ⊢
    exact this
  have hlog2 : Real.log (21 / 20 : ℝ) +
      (4396 / 1000 : ℝ) * (17 / 6) * (1 / 20) ≤ Real.log (2 : ℝ) := by
    have hlogdiv : Real.log (40 / 21 : ℝ) =
        Real.log (2 : ℝ) - Real.log (21 / 20 : ℝ) := by
      rw [show (40 / 21 : ℝ) = 2 / (21 / 20) by norm_num]
      exact Real.log_div (by norm_num) (by norm_num)
    rw [hlogdiv] at h40
    linarith
  have ht : 0 ≤ Real.log (80 * M) / Real.log (10 / 7 : ℝ) :=
    div_nonneg (Real.log_nonneg (by linarith)) hdpos.le
  have hK := Nat.floor_le ht
  change (estermannTruncation M : ℝ) ≤
    Real.log (80 * M) / Real.log (10 / 7 : ℝ) at hK
  have hlogM : Real.log (80 * M) = Real.log (80 : ℝ) + Real.log M :=
    Real.log_mul (by norm_num) (ne_of_gt hMpos)
  have hpowlog : ((estermannTruncation M : ℝ) + 1) * Real.log (2 - sigma) ≤
      Real.log (2 : ℝ) + 3 * (1 - sigma) * Real.log M := by
    calc
      _ ≤ (Real.log (80 * M) / Real.log (10 / 7 : ℝ) + 1) *
          Real.log (2 - sigma) :=
        mul_le_mul_of_nonneg_right (by linarith) hA
      _ = Real.log (2 - sigma) +
          Real.log (80 : ℝ) * (Real.log (2 - sigma) / Real.log (10 / 7 : ℝ)) +
          Real.log M * (Real.log (2 - sigma) / Real.log (10 / 7 : ℝ)) := by
        rw [hlogM]
        ring
      _ ≤ Real.log (2 : ℝ) + 3 * (1 - sigma) * Real.log M := by linarith
  calc
    (2 - sigma) ^ (estermannTruncation M + 1) =
        Real.exp (((estermannTruncation M : ℝ) + 1) * Real.log (2 - sigma)) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hu]
      push_cast
      congr 1
      ring
    _ ≤ Real.exp (Real.log (2 : ℝ) + 3 * (1 - sigma) * Real.log M) :=
      Real.exp_le_exp.mpr hpowlog
    _ = 2 * Real.rpow M (3 * (1 - sigma)) := by
      change Real.exp (Real.log (2 : ℝ) + 3 * (1 - sigma) * Real.log M) =
        2 * (M ^ (3 * (1 - sigma)) : ℝ)
      rw [Real.exp_add, Real.exp_log (by norm_num), Real.rpow_def_of_pos hMpos]
      congr 2
      ring

/-- The quantitative real power-series conclusion of Estermann's lemma.
Its hypotheses are the pole-subtracted expansion and Cauchy coefficient
bound, not a cancellation or lower-bound premise. -/
theorem estermann_lower_bound_of_coefficients
    {b : ℕ → ℝ} {a M sigma Z : ℝ}
    (hM : 1 ≤ M) (hsigma : 19 / 20 ≤ sigma) (hsigma' : sigma < 1)
    (hb : ∀ k, 0 ≤ b k) (hb0 : 1 ≤ b 0) (hZ : Z ≤ 0)
    (hcoeff : ∀ k, |b k - a| ≤ 12 * M * (2 / 3 : ℝ) ^ k)
    (hexpansion : HasSum (fun k : ℕ => (b k - a) * (2 - sigma) ^ k)
      (Z + a / (1 - sigma))) :
    (1 / 4 : ℝ) * (1 - sigma) * Real.rpow M (-3 * (1 - sigma)) ≤ a := by
  have hdelta : 0 < 1 - sigma := by linarith
  have hu : 0 < 2 - sigma := by linarith
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hp := estermann_truncation_inequality (by linarith : 0 ≤ M)
    hsigma hsigma' hb hb0 hcoeff hexpansion (estermannTruncation M)
  have ht := estermann_tail_truncation_bound hM
  have hg := estermann_truncation_power_bound hM hsigma hsigma'
  have hhalf : (1 / 2 : ℝ) ≤
      a * (2 - sigma) ^ (estermannTruncation M + 1) / (1 - sigma) := by linarith
  have hmul : (1 / 2 : ℝ) * (1 - sigma) ≤
      a * (2 - sigma) ^ (estermannTruncation M + 1) :=
    (le_div_iff₀ hdelta).mp hhalf
  have ha : 0 ≤ a := by
    have hpow := pow_pos hu (estermannTruncation M + 1)
    nlinarith
  have hg' := mul_le_mul_of_nonneg_left hg ha
  have hmain : (1 / 4 : ℝ) * (1 - sigma) ≤
      a * Real.rpow M (3 * (1 - sigma)) := by nlinarith
  have hrpow : 0 < Real.rpow M (3 * (1 - sigma)) := Real.rpow_pos_of_pos hMpos _
  have hdiv := (div_le_iff₀ hrpow).mpr hmain
  have heq : (1 / 4 : ℝ) * (1 - sigma) * Real.rpow M (-3 * (1 - sigma)) =
      (1 / 4 : ℝ) * (1 - sigma) / Real.rpow M (3 * (1 - sigma)) := by
    change (1 / 4 : ℝ) * (1 - sigma) * (M ^ (-3 * (1 - sigma)) : ℝ) =
      (1 / 4 : ℝ) * (1 - sigma) / (M ^ (3 * (1 - sigma)) : ℝ)
    rw [show -3 * (1 - sigma) = -(3 * (1 - sigma)) by ring, Real.rpow_neg hMpos.le]
    ring
  rw [heq]
  exact hdiv

/-- The Taylor coefficient at `2`, with the alternating sign appropriate
for expansion in powers of `2 - s`. -/
noncomputable def estermannTaylorCoefficient (g : ℂ → ℂ) (k : ℕ) : ℂ :=
  (-1) ^ k * (k.factorial : ℂ)⁻¹ * iteratedDeriv k g 2

/-- Cauchy's derivative estimate gives the precise normalized coefficient
bound used in the quantitative truncation. -/
theorem norm_estermannTaylorCoefficient_le
    {g : ℂ → ℂ} {M : ℝ}
    (hg : DiffContOnCl ℂ g (Metric.ball 2 (3 / 2)))
    (hbound : ∀ z ∈ Metric.sphere (2 : ℂ) (3 / 2), ‖g z‖ ≤ 12 * M)
    (k : ℕ) :
    ‖estermannTaylorCoefficient g k‖ ≤ 12 * M * (2 / 3 : ℝ) ^ k := by
  have hfactorial : 0 < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  have hderiv := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    k (by norm_num : (0 : ℝ) < 3 / 2) hg hbound
  have hnorm : ‖estermannTaylorCoefficient g k‖ =
      ‖iteratedDeriv k g 2‖ / (k.factorial : ℝ) := by
    simp only [estermannTaylorCoefficient, norm_mul, norm_pow, norm_neg, norm_one,
      one_pow, one_mul, norm_inv, Complex.norm_natCast]
    ring
  rw [hnorm]
  have hquot : ‖iteratedDeriv k g 2‖ / (k.factorial : ℝ) ≤
      12 * M / (3 / 2 : ℝ) ^ k := by
    apply (div_le_iff₀ hfactorial).mpr
    calc
      ‖iteratedDeriv k g 2‖ ≤ (k.factorial : ℝ) * (12 * M) / (3 / 2 : ℝ) ^ k := hderiv
      _ = (12 * M / (3 / 2 : ℝ) ^ k) * (k.factorial : ℝ) := by ring
  calc
    _ ≤ 12 * M / (3 / 2 : ℝ) ^ k := hquot
    _ = 12 * M * (2 / 3 : ℝ) ^ k := by
      rw [div_eq_mul_inv, ← inv_pow]
      norm_num

/-- The pole-subtracted analytic remainder has its actual Taylor expansion
on the entire disc needed by Estermann's argument. -/
theorem hasSum_estermannTaylorCoefficient
    {g : ℂ → ℂ} {sigma : ℝ}
    (hg : DifferentiableOn ℂ g (Metric.ball 2 (3 / 2)))
    (hsigma : 19 / 20 ≤ sigma) (hsigma' : sigma < 1) :
    HasSum (fun k : ℕ => (estermannTaylorCoefficient g k).re * (2 - sigma) ^ k)
      (g (sigma : ℂ)).re := by
  have hsigma2 : sigma ≤ 2 := by linarith
  have hball : (sigma : ℂ) ∈ Metric.ball (2 : ℂ) (3 / 2) := by
    rw [Metric.mem_ball, dist_eq_norm]
    norm_cast
    rw [Real.norm_eq_abs, abs_of_nonpos (by linarith : sigma - 2 ≤ 0)]
    linarith
  have htaylor := Complex.hasSum_taylorSeries_on_ball hg hball
  have hcomplex : HasSum (fun k : ℕ => estermannTaylorCoefficient g k *
      (((2 - sigma : ℝ) : ℂ) ^ k)) (g (sigma : ℂ)) := by
    apply htaylor.congr_fun
    intro k
    simp only [estermannTaylorCoefficient, smul_eq_mul]
    have hsub : (sigma : ℂ) - 2 = -((2 - sigma : ℝ) : ℂ) := by push_cast; ring
    rw [hsub, neg_pow]
    ring
  simpa only [Complex.mul_re, ← Complex.ofReal_pow, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero] using Complex.hasSum_re hcomplex

/-- Analytic version of the quantitative truncation core.  The only
positivity input concerns the actual alternating Taylor coefficients of
the remainder after adding back its pole; the Cauchy estimate and
power-series convergence are constructed here. -/
theorem estermann_lower_bound_of_analytic_remainder
    {g : ℂ → ℂ} {a M sigma Z : ℝ}
    (hM : 1 ≤ M) (hsigma : 19 / 20 ≤ sigma) (hsigma' : sigma < 1)
    (hg : DiffContOnCl ℂ g (Metric.ball 2 (3 / 2)))
    (hbound : ∀ z ∈ Metric.sphere (2 : ℂ) (3 / 2), ‖g z‖ ≤ 12 * M)
    (hpositive : ∀ k, 0 ≤ a + (estermannTaylorCoefficient g k).re)
    (hzero : 1 ≤ a + (g 2).re)
    (hvalue : (g (sigma : ℂ)).re = Z + a / (1 - sigma)) (hZ : Z ≤ 0) :
    (1 / 4 : ℝ) * (1 - sigma) * Real.rpow M (-3 * (1 - sigma)) ≤ a := by
  let b : ℕ → ℝ := fun k => a + (estermannTaylorCoefficient g k).re
  apply estermann_lower_bound_of_coefficients hM hsigma hsigma'
    (b := b) hpositive
  · simpa [b, estermannTaylorCoefficient] using hzero
  · exact hZ
  · intro k
    change |a + (estermannTaylorCoefficient g k).re - a| ≤ _
    rw [add_sub_cancel_left]
    exact (Complex.abs_re_le_norm _).trans (norm_estermannTaylorCoefficient_le hg hbound k)
  · simpa only [b, add_sub_cancel_left, hvalue] using
      hasSum_estermannTaylorCoefficient hg.differentiableOn hsigma hsigma'

/-- Every alternating Taylor coefficient of the simple pole at `1` is
exactly its residue. -/
theorem estermannTaylorCoefficient_pole (a : ℂ) (k : ℕ) :
    estermannTaylorCoefficient (fun z => a / (z - 1)) k = a := by
  have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  unfold estermannTaylorCoefficient
  simp only [div_eq_mul_inv]
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_comp_sub_const,
    iteratedDeriv_eq_iterate]
  dsimp only
  rw [iter_deriv_inv]
  norm_num
  calc
    (-1 : ℂ) ^ k * (k.factorial : ℂ)⁻¹ *
        (a * ((-1 : ℂ) ^ k * (k.factorial : ℂ))) =
        ((-1 : ℂ) ^ k * (-1 : ℂ) ^ k) * a *
          ((k.factorial : ℂ)⁻¹ * (k.factorial : ℂ)) := by ring
    _ = a := by rw [← pow_add, Even.neg_one_pow ⟨k, rfl⟩, inv_mul_cancel₀ hf]; ring

/-- Nonnegative Dirichlet coefficients supply the required alternating
Taylor-coefficient positivity of the actual meromorphic series after its
simple pole is removed. -/
theorem estermann_remainder_coefficients_nonneg
    {r : ℕ → ℂ} {g : ℂ → ℂ} {a : ℝ}
    (hr : ∀ n, 0 ≤ r n)
    (hconv : LSeries.abscissaOfAbsConv r < (2 : ℝ))
    (hg : DiffContOnCl ℂ g (Metric.ball 2 (3 / 2)))
    (hseries : ∀ s : ℂ, 1 < s.re → g s + (a : ℂ) / (s - 1) = LSeries r s)
    (k : ℕ) :
    0 ≤ a + (estermannTaylorCoefficient g k).re := by
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have heq : (fun s : ℂ => g s + (a : ℂ) / (s - 1)) =ᶠ[𝓝 (2 : ℂ)] LSeries r := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    exact hseries s hs
  have hgAt : AnalyticAt ℂ g 2 :=
    (hg.hasFPowerSeriesOnBall (by norm_num : (0 : ℝ≥0) < 3 / 2)).analyticAt
  have hpoleAt : AnalyticAt ℂ (fun s : ℂ => (a : ℂ) / (s - 1)) 2 := by
    fun_prop (disch := norm_num)
  have hcoeff : estermannTaylorCoefficient (LSeries r) k =
      estermannTaylorCoefficient g k + (a : ℂ) := by
    unfold estermannTaylorCoefficient
    rw [← heq.iteratedDeriv_eq k, iteratedDeriv_fun_add hgAt.contDiffAt hpoleAt.contDiffAt]
    calc
      (-1 : ℂ) ^ k * (k.factorial : ℂ)⁻¹ *
          (iteratedDeriv k g 2 + iteratedDeriv k (fun s : ℂ => (a : ℂ) / (s - 1)) 2) =
          (-1 : ℂ) ^ k * (k.factorial : ℂ)⁻¹ * iteratedDeriv k g 2 +
            estermannTaylorCoefficient (fun s : ℂ => (a : ℂ) / (s - 1)) k := by
        unfold estermannTaylorCoefficient
        ring
      _ = _ := by rw [estermannTaylorCoefficient_pole]
  have hnonneg : 0 ≤ estermannTaylorCoefficient (LSeries r) k := by
    have halternate := LSeries.iteratedDeriv_alternating hr hconv k
    have hfactorial : 0 ≤ ((k.factorial : ℝ)⁻¹ : ℂ) := by
      rw [← Complex.ofReal_inv, Complex.zero_le_real]
      positivity
    have heq' : estermannTaylorCoefficient (LSeries r) k =
        (((k.factorial : ℝ)⁻¹ : ℂ)) *
          ((-1 : ℂ) ^ k * iteratedDeriv k (LSeries r) 2) := by
      simp only [estermannTaylorCoefficient, Complex.ofReal_natCast]
      ring
    rw [heq']
    exact mul_nonneg hfactorial halternate
  rw [hcoeff] at hnonneg
  simpa only [Complex.add_re, Complex.ofReal_re, add_comm] using
    (Complex.nonneg_iff.mp hnonneg).1

/-- The coefficient at one makes the constant Taylor coefficient at least
one, without weakening the actual Dirichlet-series identity. -/
theorem estermann_remainder_constant_ge_one
    {r : ℕ → ℂ} {g : ℂ → ℂ} {a : ℝ}
    (hr : ∀ n, 0 ≤ r n) (hr1 : r 1 = 1)
    (hconv : LSeriesSummable r 2)
    (hseries : g 2 + (a : ℂ) = LSeries r 2) :
    1 ≤ a + (g 2).re := by
  have hsum : Summable (LSeries.term r 2) := hconv
  have hterm : ∀ n, 0 ≤ LSeries.term r 2 n := fun n => LSeries.term_nonneg (hr n) 2
  have hone : (1 : ℂ) ≤ LSeries r 2 := by
    rw [LSeries]
    simpa [LSeries.term_of_ne_zero one_ne_zero, hr1] using
      hsum.le_tsum 1 (fun n _ => hterm n)
  rw [← hseries] at hone
  simpa only [Complex.le_def, Complex.one_re, Complex.one_im, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, add_zero, add_comm] using hone.1

/-- Quantitative Estermann conclusion with the actual Dirichlet series as
its source.  Convergence, nonnegative coefficients and the first coefficient
are the genuine arithmetic hypotheses; no Taylor positivity is assumed. -/
theorem estermann_lower_bound_of_LSeries_remainder
    {r : ℕ → ℂ} {g : ℂ → ℂ} {a M sigma Z : ℝ}
    (hM : 1 ≤ M) (hsigma : 19 / 20 ≤ sigma) (hsigma' : sigma < 1)
    (hg : DiffContOnCl ℂ g (Metric.ball 2 (3 / 2)))
    (hbound : ∀ z ∈ Metric.sphere (2 : ℂ) (3 / 2), ‖g z‖ ≤ 12 * M)
    (hr : ∀ n, 0 ≤ r n) (hr1 : r 1 = 1)
    (hsummable : ∀ s : ℂ, 1 < s.re → LSeriesSummable r s)
    (hseries : ∀ s : ℂ, 1 < s.re → g s + (a : ℂ) / (s - 1) = LSeries r s)
    (hvalue : (g (sigma : ℂ)).re = Z + a / (1 - sigma)) (hZ : Z ≤ 0) :
    (1 / 4 : ℝ) * (1 - sigma) * Real.rpow M (-3 * (1 - sigma)) ≤ a := by
  have habscissa : LSeries.abscissaOfAbsConv r < (2 : ℝ) :=
    (hsummable (3 / 2) (by norm_num)).abscissaOfAbsConv_le.trans_lt (by norm_num)
  apply estermann_lower_bound_of_analytic_remainder hM hsigma hsigma' hg hbound
  · exact estermann_remainder_coefficients_nonneg hr habscissa hg hseries
  · apply estermann_remainder_constant_ge_one hr hr1 (hsummable 2 (by norm_num))
    simpa only [show (2 : ℂ) - 1 = 1 by norm_num, div_one] using hseries 2 (by norm_num)
  · exact hvalue
  · exact hZ

/-- The entire part of zeta has a conductor-independent bound on the
closed Estermann disc.  The constant is constructed by compactness. -/
theorem exists_estermann_zeta_bound :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ s ∈ Metric.closedBall (2 : ℂ) (3 / 2),
      ‖riemannZeta₀ s‖ ≤ B := by
  have hcompact : IsCompact (riemannZeta₀ '' Metric.closedBall (2 : ℂ) (3 / 2)) :=
    (isCompact_closedBall (2 : ℂ) (3 / 2)).image
      differentiable_riemannZeta₀.continuous
  obtain ⟨B, hB⟩ := hcompact.isBounded.exists_norm_le
  refine ⟨max 1 B, le_max_left _ _, ?_⟩
  intro s hs
  exact (hB _ ⟨s, hs, rfl⟩).trans (le_max_right _ _)

/-- The pole-subtracted product, defined across the removable point `1`. -/
noncomputable def estermannRemainder (f : ℂ → ℂ) (s : ℂ) : ℂ :=
  riemannZeta₀ s * f s + dslope f 1 s

theorem estermannRemainder_add_pole {f : ℂ → ℂ} {s : ℂ} (hs : s ≠ 1) :
    estermannRemainder f s + f 1 / (s - 1) = riemannZeta s * f s := by
  rw [estermannRemainder, dslope_of_ne f hs, slope_def_field,
    riemannZeta_eq_inv_sub_add hs]
  field_simp [sub_ne_zero.mpr hs]
  ring

/-- Removing the simple pole preserves analyticity and boundary
continuity on the actual Estermann disc. -/
theorem diffContOnCl_estermannRemainder {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f (Metric.ball 2 (3 / 2))) :
    DiffContOnCl ℂ (estermannRemainder f) (Metric.ball 2 (3 / 2)) := by
  have h1 : (1 : ℂ) ∈ Metric.ball (2 : ℂ) (3 / 2) := by
    rw [Metric.mem_ball, dist_eq_norm]
    norm_num
  have hnhds : Metric.ball (2 : ℂ) (3 / 2) ∈ 𝓝 (1 : ℂ) := isOpen_ball.mem_nhds h1
  have hdiff : DifferentiableOn ℂ (dslope f 1) (Metric.ball 2 (3 / 2)) :=
    (Complex.differentiableOn_dslope hnhds).mpr hf.differentiableOn
  have hcont : ContinuousOn (dslope f 1) (closure (Metric.ball (2 : ℂ) (3 / 2))) :=
    (continuousOn_dslope (Filter.mem_of_superset hnhds subset_closure)).mpr
      ⟨hf.continuousOn, hf.differentiableAt isOpen_ball h1⟩
  constructor
  · exact (differentiable_riemannZeta₀.differentiableOn.mul hf.differentiableOn).add hdiff
  · exact (differentiable_riemannZeta₀.continuous.continuousOn.mul hf.continuousOn).add hcont

/-- The actual analytic remainder is bounded on the circle using only a
universal zeta bound and the given bound on `f`. -/
theorem norm_estermannRemainder_le
    {f : ℂ → ℂ} {B M : ℝ}
    (hM : 0 ≤ M)
    (hB : ∀ s ∈ Metric.closedBall (2 : ℂ) (3 / 2), ‖riemannZeta₀ s‖ ≤ B)
    (hf : ∀ s ∈ Metric.closedBall (2 : ℂ) (3 / 2), ‖f s‖ ≤ M)
    {s : ℂ} (hs : s ∈ Metric.sphere (2 : ℂ) (3 / 2)) :
    ‖estermannRemainder f s‖ ≤ (B + 4) * M := by
  have hsball := Metric.sphere_subset_closedBall hs
  have h1ball : (1 : ℂ) ∈ Metric.closedBall (2 : ℂ) (3 / 2) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    norm_num
  have hsep : (1 / 2 : ℝ) ≤ ‖s - 1‖ := by
    have hcircle : ‖s - 2‖ = (3 / 2 : ℝ) := mem_sphere_iff_norm.mp hs
    have htriangle := norm_add_le (s - 1) (1 - (2 : ℂ))
    rw [show s - 1 + (1 - (2 : ℂ)) = s - 2 by ring] at htriangle
    norm_num at htriangle
    linarith
  have hsne : s ≠ 1 := by
    intro heq
    rw [heq, sub_self, norm_zero] at hsep
    norm_num at hsep
  have hslope : ‖dslope f 1 s‖ ≤ 4 * M := by
    rw [dslope_of_ne f hsne, slope_def_field, norm_div]
    apply (div_le_iff₀ (by linarith : 0 < ‖s - 1‖)).mpr
    have hnorm := (norm_sub_le (f s) (f 1)).trans (add_le_add (hf s hsball) (hf 1 h1ball))
    nlinarith
  calc
    ‖estermannRemainder f s‖ ≤ ‖riemannZeta₀ s * f s‖ + ‖dslope f 1 s‖ := norm_add_le _ _
    _ ≤ B * M + 4 * M := by
      rw [norm_mul]
      exact add_le_add (mul_le_mul (hB s hsball) (hf s hsball) (norm_nonneg _)
        ((norm_nonneg _).trans (hB s hsball))) hslope
    _ = _ := by ring

/-- A nonnegative Dirichlet expansion forces the residue factor at `1`
to be real; this is obtained from the actual values to the right of `1`
and boundary continuity, not assumed as an extra character property. -/
theorem estermann_function_at_one_real
    {f : ℂ → ℂ} {r : ℕ → ℂ}
    (hf : DiffContOnCl ℂ f (Metric.ball 2 (3 / 2)))
    (hr : ∀ n, 0 ≤ r n)
    (hseries : ∀ s : ℂ, 1 < s.re → riemannZeta s * f s = LSeries r s) :
    (f 1).im = 0 := by
  have hreal (x : ℝ) (hx : 1 < x) : (f (x : ℂ)).im = 0 := by
    have hnonneg : 0 ≤ LSeries r (x : ℂ) := by
      rw [LSeries]
      exact tsum_nonneg fun n => LSeries.term_nonneg (hr n) x
    have him := (Complex.nonneg_iff.mp hnonneg).2
    rw [← hseries x (by simpa using hx), Complex.mul_im,
      riemannZeta_im_eq_zero_of_one_lt hx] at him
    have hre := riemannZeta_re_pos_of_one_lt hx
    nlinarith
  have h1 : (1 : ℂ) ∈ Metric.ball (2 : ℂ) (3 / 2) := by
    rw [Metric.mem_ball, dist_eq_norm]
    norm_num
  have hfc : ContinuousAt f (1 : ℂ) := (hf.differentiableAt isOpen_ball h1).continuousAt
  have hco : ContinuousAt Complex.ofReal (1 : ℝ) := Complex.continuous_ofReal.continuousAt
  have hcomp : ContinuousAt (fun x : ℝ => f (x : ℂ)) 1 :=
    hfc.comp_of_eq hco (by norm_num)
  have hc : ContinuousAt (fun x : ℝ => (f (x : ℂ)).im) 1 :=
    Complex.continuous_im.continuousAt.comp hcomp
  have heq : (fun x : ℝ => (f (x : ℂ)).im) =ᶠ[𝓝[>] (1 : ℝ)] (fun _ => 0) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hreal x hx
  have hzero : Filter.Tendsto (fun x : ℝ => (f (x : ℂ)).im) (𝓝[>] (1 : ℝ)) (𝓝 0) :=
    (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (0 : ℝ))
      (𝓝[>] (1 : ℝ)) (𝓝 0)).congr' heq.symm
  exact tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds) hzero

/-- The complete analytic product version of the truncation step, with
the zeta constant supplied by the compact bound proved above. -/
theorem estermann_lower_bound_of_zeta_product
    {f : ℂ → ℂ} {r : ℕ → ℂ} {B M sigma : ℝ}
    (hB : 1 ≤ B)
    (hzeta : ∀ s ∈ Metric.closedBall (2 : ℂ) (3 / 2), ‖riemannZeta₀ s‖ ≤ B)
    (hM : 1 ≤ M) (hsigma : 19 / 20 ≤ sigma) (hsigma' : sigma < 1)
    (hf : DiffContOnCl ℂ f (Metric.ball 2 (3 / 2)))
    (hbound : ∀ s ∈ Metric.closedBall (2 : ℂ) (3 / 2), ‖f s‖ ≤ M)
    (hr : ∀ n, 0 ≤ r n) (hr1 : r 1 = 1)
    (hsummable : ∀ s : ℂ, 1 < s.re → LSeriesSummable r s)
    (hseries : ∀ s : ℂ, 1 < s.re → riemannZeta s * f s = LSeries r s)
    (hsign : (riemannZeta (sigma : ℂ) * f (sigma : ℂ)).re ≤ 0) :
    (1 / 4 : ℝ) * (1 - sigma) *
      Real.rpow ((B + 4) * M) (-3 * (1 - sigma)) ≤ (f 1).re := by
  have hM' : 1 ≤ (B + 4) * M := by nlinarith
  have hreal : f 1 = ((f 1).re : ℂ) := by
    apply Complex.ext <;> simp [estermann_function_at_one_real hf hr hseries]
  apply estermann_lower_bound_of_LSeries_remainder (r := r) (g := estermannRemainder f)
    (Z := (riemannZeta (sigma : ℂ) * f (sigma : ℂ)).re)
    hM' hsigma hsigma' (diffContOnCl_estermannRemainder hf)
  · intro z hz
    have h := norm_estermannRemainder_le (by linarith : 0 ≤ M) hzeta hbound hz
    exact h.trans (by nlinarith)
  · exact hr
  · exact hr1
  · exact hsummable
  · intro s hs
    have hsne : s ≠ 1 := by intro heq; rw [heq] at hs; norm_num at hs
    rw [← hreal, estermannRemainder_add_pole hsne]
    exact hseries s hs
  · have hsne : (sigma : ℂ) ≠ 1 := by exact_mod_cast ne_of_lt hsigma'
    have h := congrArg Complex.re (estermannRemainder_add_pole (f := f) hsne)
    rw [hreal] at h
    have hpole : (((f 1).re : ℂ) / ((sigma : ℂ) - 1)).re =
        -(f 1).re / (1 - sigma) := by
      rw [show (sigma : ℂ) - 1 = ((sigma - 1 : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_div, Complex.ofReal_re]
      field_simp [show sigma - 1 ≠ 0 by linarith, show 1 - sigma ≠ 0 by linarith]
      ring
    rw [Complex.add_re, hpole] at h
    rw [neg_div, ← sub_eq_add_neg] at h
    exact (sub_eq_iff_eq_add).mp h
  · exact hsign

/-- The entire-part bound also proves the needed sign of zeta sufficiently
close to its real pole, with a conductor-independent distance. -/
theorem estermann_zeta_re_nonpos
    {B sigma : ℝ} (hB : 1 ≤ B)
    (hzeta : ∀ s ∈ Metric.closedBall (2 : ℂ) (3 / 2), ‖riemannZeta₀ s‖ ≤ B)
    (hsigma : 19 / 20 ≤ sigma) (hsigma' : sigma < 1)
    (hclose : 1 - sigma ≤ 1 / (2 * B)) :
    (riemannZeta (sigma : ℂ)).re ≤ 0 := by
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hdelta : 0 < 1 - sigma := by linarith
  have hsne : (sigma : ℂ) ≠ 1 := by exact_mod_cast ne_of_lt hsigma'
  have hball : (sigma : ℂ) ∈ Metric.closedBall (2 : ℂ) (3 / 2) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    norm_cast
    rw [Real.norm_eq_abs, abs_of_nonpos (by linarith : sigma - 2 ≤ 0)]
    linarith
  have hzero : (riemannZeta₀ (sigma : ℂ)).re ≤ B :=
    (Complex.re_le_norm _).trans (hzeta _ hball)
  have hproduct : 2 * B * (1 - sigma) ≤ 1 := by
    have := (le_div_iff₀ (by positivity : 0 < 2 * B)).mp hclose
    nlinarith
  have hinv : 2 * B ≤ 1 / (1 - sigma) := (le_div_iff₀ hdelta).mpr hproduct
  have hformula : (riemannZeta (sigma : ℂ)).re =
      -(1 / (1 - sigma)) + (riemannZeta₀ (sigma : ℂ)).re := by
    rw [riemannZeta_eq_inv_sub_add hsne, Complex.add_re]
    congr 1
    rw [show (sigma : ℂ) - 1 = ((sigma - 1 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_inv, Complex.ofReal_re]
    field_simp [show sigma - 1 ≠ 0 by linarith, show 1 - sigma ≠ 0 by linarith]
    ring
  rw [hformula]
  linarith

/-- A genuine quantitative Estermann lemma with internally constructed
universal constants.  The pole is removed analytically, all Taylor
positivity is obtained from the actual Dirichlet series, and the sign of
zeta is proved on a fixed interval ending at `1`.

The universal factor `C` replaces the source's explicit numerical zeta
estimate; it is independent of `f`, its conductor, `M` and `sigma`.
Shrinking the source interval by the universal `eta` is harmless for the
ineffective Siegel argument. -/
theorem exists_estermann_constants :
    ∃ C eta : ℝ, 1 ≤ C ∧ 0 < eta ∧ eta ≤ 1 / 20 ∧
      ∀ (f : ℂ → ℂ) (r : ℕ → ℂ) (M sigma : ℝ),
        1 ≤ M →
        DiffContOnCl ℂ f (Metric.ball 2 (3 / 2)) →
        (∀ s ∈ Metric.closedBall (2 : ℂ) (3 / 2), ‖f s‖ ≤ M) →
        (∀ n, 0 ≤ r n) → r 1 = 1 →
        (∀ s : ℂ, 1 < s.re → LSeriesSummable r s) →
        (∀ s : ℂ, 1 < s.re → riemannZeta s * f s = LSeries r s) →
        1 - eta ≤ sigma → sigma < 1 → 0 ≤ f (sigma : ℂ) →
        (1 / 4 : ℝ) * (1 - sigma) *
          Real.rpow (C * M) (-3 * (1 - sigma)) ≤ (f 1).re := by
  obtain ⟨B, hB, hzeta⟩ := exists_estermann_zeta_bound
  let eta : ℝ := min (1 / 20) (1 / (2 * B))
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have heta : 0 < eta := lt_min (by norm_num) (by positivity)
  have heta20 : eta ≤ 1 / 20 := min_le_left _ _
  have hetaB : eta ≤ 1 / (2 * B) := min_le_right _ _
  refine ⟨B + 4, eta, by linarith, heta, heta20, ?_⟩
  intro f r M sigma hM hf hbound hr hr1 hsummable hseries hsigma hsigma' hf_sigma
  have hsigma20 : 19 / 20 ≤ sigma := by linarith
  apply estermann_lower_bound_of_zeta_product hB hzeta hM hsigma20 hsigma'
    hf hbound hr hr1 hsummable hseries
  have hzeta_nonpos := estermann_zeta_re_nonpos hB hzeta hsigma20 hsigma'
    (by linarith : 1 - sigma ≤ 1 / (2 * B))
  obtain ⟨hfre, hfim⟩ := Complex.nonneg_iff.mp hf_sigma
  rw [Complex.mul_re, ← hfim, mul_zero, sub_zero]
  exact mul_nonpos_of_nonpos_of_nonneg hzeta_nonpos hfre

#print axioms estermann_truncation_inequality
#print axioms estermann_lower_bound_of_coefficients
#print axioms estermann_lower_bound_of_analytic_remainder
#print axioms estermann_lower_bound_of_LSeries_remainder
#print axioms exists_estermann_constants

end SystolicGrowth.CookMagyarCircle
