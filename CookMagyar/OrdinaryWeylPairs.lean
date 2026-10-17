module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.OrdinaryWeylSpacing
public import CookMagyar.HuaDivisorBound
public import CookMagyar.HuaShift

@[expose] public section

open scoped BigOperators

namespace SystolicGrowth
namespace CookMagyarCircle

open CookMagyarArcs

/-- Positive bounded factor pairs with fixed product. -/
def positiveProductPairFiber (N r : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter fun hk =>
    hk.1 * hk.2 = r

/-- The explicit arbitrary-range spacing envelope at denominator `q`,
including the reduction from `6α` to `q/gcd(q,6)`. -/
noncomputable def sixMulSpacingEnvelopeBound (N q : ℕ) (Y : ℝ) : ℝ :=
  (((N * N / (q / Nat.gcd q 6) + 1 : ℕ) : ℝ) * 28 *
    (Y + ((q / Nat.gcd q 6 : ℕ) : ℝ) *
      (1 + Real.log ((q / Nat.gcd q 6 : ℕ) : ℝ))))

/-- Spacing-envelope bound retaining an arbitrary constant in the rational
approximation error `|beta|≤K/q²`. -/
noncomputable def sixMulSpacingEnvelopeBoundWithError
    (N q : ℕ) (Y : ℝ) (K : ℕ) : ℝ :=
  (((N * N / (q / Nat.gcd q 6) + 1 : ℕ) : ℝ) *
    ((2 * (2 * (6 * K) + 2) : ℕ) : ℝ) *
      (Y + ((q / Nat.gcd q 6 : ℕ) : ℝ) *
        (1 + Real.log ((q / Nat.gcd q 6 : ℕ) : ℝ))))

/-- The coarse spacing envelope expressed with the original denominator. -/
noncomputable def coarseSpacingEnvelopeBound (N q : ℕ) (Y : ℝ) : ℝ :=
  (6 * (N * N : ℝ) / q + 1) * 28 * (Y + q * (1 + Real.log q))

/-- The logarithmic cross-term in the thresholded cubic spacing envelope
is absorbed by a progression of length at least `B^6`. -/
theorem pow_four_log_crossTerm_le
    (B X q : ℝ)
    (hB : 1 ≤ B) (hB6X : B ^ 6 ≤ X)
    (hlogq : Real.log q ≤ 4 * B) :
    B ^ 4 * X ^ 2 * (1 + Real.log q) ≤ 5 * X ^ 3 / B := by
  have hBpos : 0 < B := by linarith
  have hB6pos : 0 < B ^ 6 := by positivity
  have hXpos : 0 < X := lt_of_lt_of_le hB6pos hB6X
  have hUle : 1 + Real.log q ≤ 5 * B := by linarith
  have hB5U : B ^ 5 * (1 + Real.log q) ≤ 5 * B ^ 6 := by
    calc
      B ^ 5 * (1 + Real.log q) ≤ B ^ 5 * (5 * B) :=
        mul_le_mul_of_nonneg_left hUle (by positivity)
      _ = 5 * B ^ 6 := by ring
  apply (le_div_iff₀ hBpos).2
  calc
    B ^ 4 * X ^ 2 * (1 + Real.log q) * B =
        (B ^ 5 * (1 + Real.log q)) * X ^ 2 := by ring
    _ ≤ (5 * B ^ 6) * X ^ 2 :=
      mul_le_mul_of_nonneg_right hB5U (by positivity)
    _ ≤ 5 * X ^ 3 := by
      have hmul := mul_le_mul_of_nonneg_right hB6X
        (by positivity : 0 ≤ X ^ 2)
      nlinarith [hmul]

/-- The full polynomial part of the thresholded cubic spacing envelope has
one inverse-log saving when the rational denominator lies in the transformed
Hua window. The hypothesis `hBpow` is the real-power consequence of the
window's exponent lower bound. -/
theorem pow_four_normalizedSpacingPolynomial_le
    (B X q : ℝ) (rho : ℕ)
    (hB : 1 ≤ B) (hB6X : B ^ 6 ≤ X)
    (hB5q : B ^ 5 ≤ q) (hqUpper : q * B ^ rho ≤ X ^ 3)
    (hBpow : B ^ 6 ≤ B ^ rho) (hlogq : Real.log q ≤ 4 * B) :
    B ^ 4 * (6 * X ^ 2 / q + 1) * 28 *
        (X + q * (1 + Real.log q)) ≤ 1176 * X ^ 3 / B := by
  have hBpos : 0 < B := by linarith
  have hXpos : 0 < X := by
    have h : 0 < B ^ 6 := by positivity
    linarith
  have hqpos : 0 < q := by
    have h : 0 < B ^ 5 := by positivity
    linarith
  have hlogfactor : 0 ≤ 1 + Real.log q := by
    have hB5one : (1 : ℝ) ≤ B ^ 5 := by
      calc
        1 = (1 : ℝ) ^ 5 := by norm_num
        _ ≤ B ^ 5 := by gcongr
    have hqone : (1 : ℝ) ≤ q := le_trans hB5one hB5q
    have := Real.log_nonneg hqone
    linarith
  have hfactorBound : 1 + Real.log q ≤ 5 * B := by linarith
  have hratio : B ^ 4 / q ≤ 1 / B := by
    apply (div_le_div_iff₀ hqpos hBpos).2
    nlinarith [hB5q]
  have hleading : B ^ 4 * (6 * X ^ 2 / q) * X ≤ 6 * X ^ 3 / B := by
    calc
      B ^ 4 * (6 * X ^ 2 / q) * X = 6 * X ^ 3 * (B ^ 4 / q) := by
        field_simp
      _ ≤ 6 * X ^ 3 * (1 / B) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = 6 * X ^ 3 / B := by ring
  have hcross := pow_four_log_crossTerm_le B X q hB hB6X hlogq
  have hcrossSix : 6 * (B ^ 4 * X ^ 2 * (1 + Real.log q)) ≤
      30 * X ^ 3 / B := by
    calc
      6 * (B ^ 4 * X ^ 2 * (1 + Real.log q)) ≤
          6 * (5 * X ^ 3 / B) :=
        mul_le_mul_of_nonneg_left hcross (by norm_num : (0 : ℝ) ≤ 6)
      _ = 30 * X ^ 3 / B := by ring
  have hB5B6 : B ^ 5 ≤ B ^ 6 := by
    calc
      B ^ 5 = B ^ 5 * 1 := by ring
      _ ≤ B ^ 5 * B := mul_le_mul_of_nonneg_left hB (by positivity)
      _ = B ^ 6 := by ring
  have hXone : 1 ≤ X := by
    have hB6one : (1 : ℝ) ≤ B ^ 6 := by
      calc
        1 = (1 : ℝ) ^ 6 := by norm_num
        _ ≤ B ^ 6 := by gcongr
    linarith
  have hB5X2 : B ^ 5 ≤ X ^ 2 := by
    calc
      B ^ 5 ≤ B ^ 6 := hB5B6
      _ ≤ X := hB6X
      _ ≤ X ^ 2 := by nlinarith [sq_nonneg (X - 1)]
  have hunit : B ^ 4 * X ≤ X ^ 3 / B := by
    apply (le_div_iff₀ hBpos).2
    nlinarith [hB5X2]
  have hlarge : B ^ 4 * q * (1 + Real.log q) ≤ 5 * X ^ 3 / B := by
    apply (le_div_iff₀ hBpos).2
    have hfac := mul_le_mul_of_nonneg_left hfactorBound
      (by positivity : 0 ≤ B ^ 4 * q)
    have hpowwindow := mul_le_mul_of_nonneg_left hBpow
      (by positivity : 0 ≤ q)
    have hwindow := hpowwindow.trans hqUpper
    nlinarith [hfac, hwindow]
  have hcrossExpand : B ^ 4 * (6 * X ^ 2 / q *
      (q * (1 + Real.log q))) =
      6 * (B ^ 4 * X ^ 2 * (1 + Real.log q)) := by
    field_simp
  calc
    B ^ 4 * (6 * X ^ 2 / q + 1) * 28 *
        (X + q * (1 + Real.log q))
        = 28 * (B ^ 4 * (6 * X ^ 2 / q * X +
            6 * X ^ 2 / q * (q * (1 + Real.log q)) + X +
            q * (1 + Real.log q))) := by ring
    _ = 28 * (B ^ 4 * (6 * X ^ 2 / q * X) +
          B ^ 4 * (6 * X ^ 2 / q * (q * (1 + Real.log q))) +
          B ^ 4 * X + B ^ 4 * (q * (1 + Real.log q))) := by ring
    _ = 28 * (B ^ 4 * (6 * X ^ 2 / q) * X +
          6 * (B ^ 4 * X ^ 2 * (1 + Real.log q)) +
          B ^ 4 * X + B ^ 4 * q * (1 + Real.log q)) := by
      rw [hcrossExpand]
      ring
    _ ≤ 28 * (6 * X ^ 3 / B + 30 * X ^ 3 / B +
          X ^ 3 / B + 5 * X ^ 3 / B) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 28)
      nlinarith [hleading, hcrossSix, hunit, hlarge]
    _ = 1176 * X ^ 3 / B := by ring

/-- The ordinary spacing polynomial remains `O(X^3/B)` after a scale loss
`K` in the approximation error, provided that loss is covered by the lower
denominator, progression-length, and upper-denominator margins. -/
theorem pow_four_scaledNormalizedSpacingPolynomial_le
    (B X q K : ℝ) (rho : ℕ)
    (hB : 1 ≤ B) (hK : 1 ≤ K)
    (hK6X : K * B ^ 6 ≤ X) (hK5q : K * B ^ 5 ≤ q)
    (hqUpper : q * B ^ rho ≤ X ^ 3)
    (hK6pow : K * B ^ 6 ≤ B ^ rho)
    (hlogq : Real.log q ≤ 4 * B) :
    B ^ 4 * K * (6 * X ^ 2 / q + 1) * 28 *
        (X + q * (1 + Real.log q)) ≤ 1176 * X ^ 3 / B := by
  have hBpos : 0 < B := by linarith
  have hXpos : 0 < X := by
    have hB6pos : 0 < B ^ 6 := by positivity
    have h : 0 < K * B ^ 6 := by positivity
    linarith
  have hqpos : 0 < q := by
    have h : 0 < K * B ^ 5 := by positivity
    linarith
  have hlogfactor : 0 ≤ 1 + Real.log q := by
    have hB5one : (1 : ℝ) ≤ B ^ 5 := by
      calc
        1 = (1 : ℝ) ^ 5 := by norm_num
        _ ≤ B ^ 5 := by gcongr
    have hKscaled : B ^ 5 ≤ K * B ^ 5 := by
      simpa using mul_le_mul_of_nonneg_right hK
        (by positivity : 0 ≤ B ^ 5)
    have hqone : (1 : ℝ) ≤ q := le_trans hB5one (le_trans hKscaled hK5q)
    have := Real.log_nonneg hqone
    linarith
  have hfactorBound : 1 + Real.log q ≤ 5 * B := by linarith
  have hratio : K * B ^ 4 / q ≤ 1 / B := by
    apply (div_le_div_iff₀ hqpos hBpos).2
    nlinarith [hK5q]
  have hleading : K * B ^ 4 * (6 * X ^ 2 / q) * X ≤
      6 * X ^ 3 / B := by
    calc
      K * B ^ 4 * (6 * X ^ 2 / q) * X =
          6 * X ^ 3 * (K * B ^ 4 / q) := by field_simp
      _ ≤ 6 * X ^ 3 * (1 / B) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = 6 * X ^ 3 / B := by ring
  have hK5factor : K * B ^ 5 * (1 + Real.log q) ≤ 5 * K * B ^ 6 := by
    calc
      K * B ^ 5 * (1 + Real.log q) ≤ K * B ^ 5 * (5 * B) :=
        mul_le_mul_of_nonneg_left hfactorBound (by positivity)
      _ = 5 * K * B ^ 6 := by ring
  have hcross : K * B ^ 4 * X ^ 2 * (1 + Real.log q) ≤
      5 * X ^ 3 / B := by
    apply (le_div_iff₀ hBpos).2
    calc
      K * B ^ 4 * X ^ 2 * (1 + Real.log q) * B =
          (K * B ^ 5 * (1 + Real.log q)) * X ^ 2 := by ring
      _ ≤ (5 * K * B ^ 6) * X ^ 2 :=
        mul_le_mul_of_nonneg_right hK5factor (by positivity)
      _ ≤ 5 * X ^ 3 := by
        have hmul := mul_le_mul_of_nonneg_right hK6X
          (by positivity : 0 ≤ X ^ 2)
        nlinarith [hmul]
  have hK5B6 : K * B ^ 5 ≤ K * B ^ 6 := by
    exact mul_le_mul_of_nonneg_left
      (by
        calc
          B ^ 5 = B ^ 5 * 1 := by ring
          _ ≤ B ^ 5 * B := mul_le_mul_of_nonneg_left hB (by positivity)
          _ = B ^ 6 := by ring)
      (le_trans (by norm_num) hK)
  have hXone : 1 ≤ X := by
    have hB6one : (1 : ℝ) ≤ B ^ 6 := by
      calc
        1 = (1 : ℝ) ^ 6 := by norm_num
        _ ≤ B ^ 6 := by gcongr
    have hmul := mul_le_mul_of_nonneg_right hK
      (by positivity : 0 ≤ B ^ 6)
    linarith
  have hK5X : K * B ^ 5 ≤ X := hK5B6.trans hK6X
  have hunit : K * B ^ 4 * X ≤ X ^ 3 / B := by
    apply (le_div_iff₀ hBpos).2
    have hmul := mul_le_mul_of_nonneg_right hK5X (by positivity : 0 ≤ X)
    nlinarith [hmul, sq_nonneg (X - 1)]
  have hKpowq : K * B ^ 6 * q ≤ X ^ 3 := by
    have hmul := mul_le_mul_of_nonneg_right hK6pow (le_of_lt hqpos)
    nlinarith [hqUpper, hmul]
  have hlarge : K * B ^ 4 * q * (1 + Real.log q) ≤
      5 * X ^ 3 / B := by
    apply (le_div_iff₀ hBpos).2
    have hfac := mul_le_mul_of_nonneg_left hfactorBound
      (by positivity : 0 ≤ K * B ^ 4 * q)
    nlinarith [hfac, hKpowq]
  have hcrossSix : 6 * (K * B ^ 4 * X ^ 2 * (1 + Real.log q)) ≤
      30 * X ^ 3 / B := by
    calc
      6 * (K * B ^ 4 * X ^ 2 * (1 + Real.log q)) ≤
          6 * (5 * X ^ 3 / B) :=
        mul_le_mul_of_nonneg_left hcross (by norm_num : (0 : ℝ) ≤ 6)
      _ = 30 * X ^ 3 / B := by ring
  have hcrossExpand : K * B ^ 4 * (6 * X ^ 2 / q *
      (q * (1 + Real.log q))) =
      6 * (K * B ^ 4 * X ^ 2 * (1 + Real.log q)) := by
    field_simp
  calc
    B ^ 4 * K * (6 * X ^ 2 / q + 1) * 28 *
        (X + q * (1 + Real.log q))
        = 28 * (K * B ^ 4 * (6 * X ^ 2 / q * X +
            6 * X ^ 2 / q * (q * (1 + Real.log q)) + X +
            q * (1 + Real.log q))) := by ring
    _ = 28 * (K * B ^ 4 * (6 * X ^ 2 / q) * X +
          6 * (K * B ^ 4 * X ^ 2 * (1 + Real.log q)) +
          K * B ^ 4 * X + K * B ^ 4 * q * (1 + Real.log q)) := by
      field_simp
    _ ≤ 28 * (6 * X ^ 3 / B + 30 * X ^ 3 / B +
          X ^ 3 / B + 5 * X ^ 3 / B) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 28)
      nlinarith [hleading, hcrossSix, hunit, hlarge]
    _ = 1176 * X ^ 3 / B := by ring

/-- Specialize the normalized polynomial estimate to the concrete coarse
spacing envelope used by the cubic fourth-moment bound. -/
theorem pow_four_coarseSpacingEnvelopeBound_le
    (B : ℝ) (N q : ℕ) (rho : ℕ)
    (hB : 1 ≤ B) (hB6X : B ^ 6 ≤ (N + 1 : ℝ))
    (hB5q : B ^ 5 ≤ (q : ℝ))
    (hqUpper : (q : ℝ) * B ^ rho ≤ (N + 1 : ℝ) ^ 3)
    (hBpow : B ^ 6 ≤ B ^ rho)
    (hlogq : Real.log (q : ℝ) ≤ 4 * B) :
    B ^ 4 * coarseSpacingEnvelopeBound N q (N + 1 : ℝ) ≤
      1176 * (N + 1 : ℝ) ^ 3 / B := by
  have hNle : (N : ℝ) ≤ (N + 1 : ℝ) := by norm_num
  have hNnonneg : 0 ≤ (N : ℝ) := by positivity
  have hqpos : 0 < (q : ℝ) := by
    have hB5pos : 0 < B ^ 5 := by positivity
    linarith
  have hB5one : (1 : ℝ) ≤ B ^ 5 := by
    calc
      1 = (1 : ℝ) ^ 5 := by norm_num
      _ ≤ B ^ 5 := by gcongr
  have hqone : (1 : ℝ) ≤ (q : ℝ) := le_trans hB5one hB5q
  have hgeneric := pow_four_normalizedSpacingPolynomial_le B
    (N + 1 : ℝ) (q : ℝ) rho hB hB6X hB5q hqUpper hBpow hlogq
  have hN2 : (N : ℝ) ^ 2 ≤ (N + 1 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((N + 1 : ℝ) - (N : ℝ))]
  have hfactor :
      6 * (N : ℝ) ^ 2 / (q : ℝ) + 1 ≤
        6 * (N + 1 : ℝ) ^ 2 / (q : ℝ) + 1 := by
    have hdiv := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hN2 (by norm_num : (0 : ℝ) ≤ 6))
      (le_of_lt hqpos)
    linarith
  have hrest : 0 ≤ (N + 1 : ℝ) + (q : ℝ) *
      (1 + Real.log (q : ℝ)) := by
    have hlognonneg : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqone
    positivity
  have hcoarse : B ^ 4 * (6 * (N : ℝ) ^ 2 / (q : ℝ) + 1) * 28 *
      ((N + 1 : ℝ) + (q : ℝ) * (1 + Real.log (q : ℝ))) ≤
      B ^ 4 * (6 * (N + 1 : ℝ) ^ 2 / (q : ℝ) + 1) * 28 *
      ((N + 1 : ℝ) + (q : ℝ) * (1 + Real.log (q : ℝ))) := by
    gcongr
  unfold coarseSpacingEnvelopeBound
  calc
    B ^ 4 * ((6 * ((N : ℝ) * (N : ℝ)) / (q : ℝ) + 1) * 28 *
        ((N + 1 : ℝ) + (q : ℝ) * (1 + Real.log (q : ℝ)))) =
      B ^ 4 * (6 * (N : ℝ) ^ 2 / (q : ℝ) + 1) * 28 *
        ((N + 1 : ℝ) + (q : ℝ) * (1 + Real.log (q : ℝ))) := by
          ring
    _ ≤ B ^ 4 * (6 * (N + 1 : ℝ) ^ 2 / (q : ℝ) + 1) * 28 *
        ((N + 1 : ℝ) + (q : ℝ) * (1 + Real.log (q : ℝ))) := hcoarse
    _ ≤ 1176 * (N + 1 : ℝ) ^ 3 / B := by
      exact hgeneric

/-- With threshold `T=B^4`, the rich-divisor contribution is at most a
constant times `X^3/B`, provided the seventh-log moment's logarithm is at
most `5B`. -/
theorem divisorThresholdTail_pow_four_le
    (B : ℝ) (N : ℕ) (hB : 1 ≤ B) (hN : 0 < N)
    (hlog : 1 + Real.log ((N * N : ℕ) : ℝ) ≤ 5 * B) :
    (N + 1 : ℝ) * ((N * N : ℕ) : ℝ) *
        (1 + Real.log ((N * N : ℕ) : ℝ)) ^ 7 / B ^ 8 ≤
      78125 * (N + 1 : ℝ) ^ 3 / B := by
  have hBpos : 0 < B := by linarith
  have hZone : (1 : ℝ) ≤ ((N * N : ℕ) : ℝ) := by
    have hNat : 1 ≤ N * N :=
      Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.mul_pos hN hN))
    exact_mod_cast hNat
  have hlognonneg : 0 ≤ Real.log ((N * N : ℕ) : ℝ) :=
    Real.log_nonneg hZone
  have hA_nonneg : 0 ≤ 1 + Real.log ((N * N : ℕ) : ℝ) := by linarith
  have hA7 : (1 + Real.log ((N * N : ℕ) : ℝ)) ^ 7 ≤
      78125 * B ^ 7 := by
    calc
      (1 + Real.log ((N * N : ℕ) : ℝ)) ^ 7 ≤ (5 * B) ^ 7 := by
        gcongr
      _ = 78125 * B ^ 7 := by ring
  have hN2le : ((N * N : ℕ) : ℝ) ≤ (N + 1 : ℝ) ^ 2 := by
    push_cast
    nlinarith [sq_nonneg ((N + 1 : ℝ) - N)]
  have hnum : (N + 1 : ℝ) * ((N * N : ℕ) : ℝ) *
      (1 + Real.log ((N * N : ℕ) : ℝ)) ^ 7 ≤
      78125 * (N + 1 : ℝ) ^ 3 * B ^ 7 := by
    calc
      (N + 1 : ℝ) * ((N * N : ℕ) : ℝ) *
          (1 + Real.log ((N * N : ℕ) : ℝ)) ^ 7 ≤
        (N + 1 : ℝ) * (N + 1 : ℝ) ^ 2 *
          (1 + Real.log ((N * N : ℕ) : ℝ)) ^ 7 := by gcongr
      _ ≤ (N + 1 : ℝ) * (N + 1 : ℝ) ^ 2 * (78125 * B ^ 7) := by
        gcongr
      _ = 78125 * (N + 1 : ℝ) ^ 3 * B ^ 7 := by ring
  apply (div_le_div_iff₀ (pow_pos hBpos 8) hBpos).2
  calc
    (N + 1 : ℝ) * ((N * N : ℕ) : ℝ) *
        (1 + Real.log ((N * N : ℕ) : ℝ)) ^ 7 * B ≤
      78125 * (N + 1 : ℝ) ^ 3 * B ^ 7 * B :=
        mul_le_mul_of_nonneg_right hnum (le_of_lt hBpos)
    _ = 78125 * (N + 1 : ℝ) ^ 3 * B ^ 8 := by ring

/-- A concrete logarithm-to-small-power inequality for natural denominators.
It will absorb the `log q` factor once the auxiliary denominator range is
substituted. -/
theorem log_nat_le_hundred_rpow
    {q : ℕ} (hq : 0 < q) :
    Real.log (q : ℝ) ≤ 100 * Real.rpow (q : ℝ) (1 / 100 : ℝ) := by
  have h := Real.log_le_rpow_div (by positivity : (0 : ℝ) ≤ q)
    (by norm_num : (0 : ℝ) < (1 / 100 : ℝ))
  norm_num [div_eq_mul_inv] at h ⊢
  simpa [mul_comm] using h

/-- Replace the reduced denominator by the original denominator at a cost
of an absolute factor six. -/
theorem sixMulSpacingEnvelopeBound_le_coarse
    (N q : ℕ) (Y : ℝ) (hq : 0 < q) (hY : 0 ≤ Y) :
    sixMulSpacingEnvelopeBound N q Y ≤
      (6 * (N * N : ℝ) / q + 1) * 28 *
        (Y + q * (1 + Real.log q)) := by
  let q₀ := q / Nat.gcd q 6
  have hgq : Nat.gcd q 6 ∣ q := Nat.gcd_dvd_left q 6
  have hfactor : q = q₀ * Nat.gcd q 6 := by
    dsimp [q₀]
    exact (Nat.div_mul_cancel hgq).symm
  have hq₀pos : 0 < q₀ := by
    by_contra h
    have hz : q₀ = 0 := Nat.eq_zero_of_not_pos h
    have hqzero : q = 0 := by simpa [hz] using hfactor
    exact (Nat.ne_of_gt hq) hqzero
  have hg_le_six : Nat.gcd q 6 ≤ 6 :=
    Nat.le_of_dvd (by decide : 0 < 6) (Nat.gcd_dvd_right q 6)
  have hq_le : q ≤ q₀ * 6 := by
    rw [hfactor]
    exact Nat.mul_le_mul_left q₀ hg_le_six
  have hq₀_le : q₀ ≤ q :=
    (six_mul_reduced_denominator_bounds q).2
  have hq₀realpos : (0 : ℝ) < q₀ := by exact_mod_cast hq₀pos
  have hqrealpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hq0real : (q₀ : ℝ) ≤ q := by exact_mod_cast hq₀_le
  have hq_le' : q ≤ 6 * q₀ := by simpa [Nat.mul_comm] using hq_le
  have hqscale : (q : ℝ) ≤ 6 * q₀ := by exact_mod_cast hq_le'
  have hqrealone : (1 : ℝ) ≤ q := by exact_mod_cast (Nat.succ_le_of_lt hq)
  have hq0realone : (1 : ℝ) ≤ q₀ := by
    exact_mod_cast (Nat.succ_le_of_lt hq₀pos)
  have hlog : Real.log q₀ ≤ Real.log q :=
    Real.log_le_log hq₀realpos hq0real
  have hlog0 : 0 ≤ Real.log q₀ := Real.log_nonneg hq0realone
  have hlogQ : 0 ≤ Real.log q := Real.log_nonneg hqrealone
  have hfac : 0 ≤ 1 + Real.log q₀ := by linarith
  have hfac_le : 1 + Real.log q₀ ≤ 1 + Real.log q := by linarith
  have hproduct : q₀ * (1 + Real.log q₀) ≤ q * (1 + Real.log q) :=
    mul_le_mul hq0real hfac_le (by linarith) (by positivity)
  have hbase : 0 ≤ (N * N : ℝ) := by positivity
  have hquot : (((N * N) / q₀ : ℕ) : ℝ) ≤
      (N * N : ℝ) / q₀ := by
    simpa [Nat.cast_mul] using
      (Nat.cast_div_le : (((N * N) / q₀ : ℕ) : ℝ) ≤
        ((N * N : ℕ) : ℝ) / (q₀ : ℝ))
  have hquot_le : (N * N : ℝ) / q₀ ≤
      6 * (N * N : ℝ) / q := by
    apply (div_le_div_iff₀ hq₀realpos hqrealpos).2
    have hmul := mul_le_mul_of_nonneg_left hqscale hbase
    nlinarith [hmul]
  have hA : (((N * N / q₀ + 1 : ℕ) : ℝ)) ≤
      6 * (N * N : ℝ) / q + 1 := by
    push_cast
    linarith [hquot.trans hquot_le]
  have hB : Y + q₀ * (1 + Real.log q₀) ≤
      Y + q * (1 + Real.log q) := by linarith
  have hA0 : 0 ≤ (((N * N / q₀ + 1 : ℕ) : ℝ)) := by positivity
  have hB0 : 0 ≤ Y + q₀ * (1 + Real.log q₀) := by positivity
  calc
    sixMulSpacingEnvelopeBound N q Y =
        (((N * N / q₀ + 1 : ℕ) : ℝ) * 28) *
          (Y + q₀ * (1 + Real.log q₀)) := by
            simp [sixMulSpacingEnvelopeBound, q₀, mul_assoc]
    _ ≤ (6 * (N * N : ℝ) / q + 1) * 28 *
          (Y + q * (1 + Real.log q)) := by
      gcongr

/-- Scaling a natural frequency into the real linear coefficient. -/
theorem addChar_nat_mul (alpha : ℝ) (a m : ℕ) :
    addChar alpha (a * m) = addChar ((a : ℝ) * alpha) m := by
  unfold addChar
  congr 1
  push_cast
  ring

/-- The zero-safe linear envelope is monotone in the length parameter. -/
theorem linearDistanceEnvelope_mono {Y₁ Y₂ theta : ℝ}
    (hY : Y₁ ≤ Y₂) :
    linearDistanceEnvelope Y₁ theta ≤ linearDistanceEnvelope Y₂ theta := by
  by_cases hz : periodicDistance theta 0 = 0
  · simp [linearDistanceEnvelope, hz, hY]
  · simp only [linearDistanceEnvelope, hz, if_false]
    exact min_le_min hY le_rfl

private theorem sum_range_succ_eq_sum_Icc (R : ℕ) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.range R, f (j + 1)) =
      ∑ r ∈ Finset.Icc 1 R, f r := by
  classical
  refine Finset.sum_bij (fun j _ => j + 1) ?_ ?_ ?_ ?_
  · intro j hj
    exact Finset.mem_Icc.mpr ⟨by omega,
      Nat.succ_le_of_lt (Finset.mem_range.mp hj)⟩
  · intro j hj k hk hEq
    omega
  · intro r hr
    refine ⟨r - 1, Finset.mem_range.mpr ?_, ?_⟩
    · have := Finset.mem_Icc.mp hr
      omega
    · have := Finset.mem_Icc.mp hr
      omega
  · intro j hj
    rfl

/-- Projection to the first factor injects a positive fixed-product fiber
into the divisor set. -/
theorem card_positiveProductPairFiber_le_divisors
    (N r : ℕ) (hr : 0 < r) :
    (positiveProductPairFiber N r).card ≤ r.divisors.card := by
  classical
  refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
  · intro hk hhk
    rw [Finset.mem_coe]
    have hmem := (Finset.mem_filter.mp hhk).1
    have hprod := (Finset.mem_filter.mp hhk).2
    have hdiv : hk.1 ∣ r := ⟨hk.2, hprod.symm⟩
    exact Nat.mem_divisors.mpr ⟨hdiv, hr.ne'⟩
  · intro hk hhk kl hkl heq
    have hhk' := (Finset.mem_filter.mp hhk).1
    have hhkprod := (Finset.mem_filter.mp hhk).2
    have hklprod := (Finset.mem_filter.mp hkl).2
    have hfst : hk.1 = kl.1 := heq
    have hprod : hk.1 * hk.2 = hk.1 * kl.2 := by
      calc
        hk.1 * hk.2 = r := hhkprod
        _ = kl.1 * kl.2 := hklprod.symm
        _ = hk.1 * kl.2 := by rw [← hfst]
    have hpos : 0 < hk.1 := by
      have := (Finset.mem_Icc.mp (Finset.mem_product.mp hhk').1).1
      omega
    have hsnd : hk.2 = kl.2 := Nat.eq_of_mul_eq_mul_left hpos hprod
    exact Prod.ext hfst hsnd

/-- Reindex a nonnegative weight on bounded positive factor pairs by product,
retaining the exact divisor-count multiplicity instead of a pointwise
subpower majorant. -/
theorem sum_positiveProductPairs_le_divisorWeightedEnvelope
    (N : ℕ) (f : ℕ → ℝ) (hf : ∀ r, 0 ≤ f r) :
    (∑ hk ∈ (Finset.Icc 1 N).product (Finset.Icc 1 N),
      f (hk.1 * hk.2)) ≤
      ∑ r ∈ Finset.Icc 1 (N * N), (r.divisors.card : ℝ) * f r := by
  classical
  let domain := (Finset.Icc 1 N).product (Finset.Icc 1 N)
  let target := Finset.Icc 1 (N * N)
  let productMap : ℕ × ℕ → ℕ := fun hk => hk.1 * hk.2
  have hmaps : ∀ hk ∈ domain, productMap hk ∈ target := by
    intro hk hhk
    have hhk' := Finset.mem_product.mp hhk
    have hfst := Finset.mem_Icc.mp hhk'.1
    have hsnd := Finset.mem_Icc.mp hhk'.2
    apply Finset.mem_Icc.mpr
    constructor
    · exact Nat.mul_pos (by omega) (by omega)
    · exact Nat.mul_le_mul hfst.2 hsnd.2
  have hdecomp :
      (∑ hk ∈ domain, f (productMap hk)) =
        ∑ r ∈ target,
          ∑ hk ∈ positiveProductPairFiber N r, f (productMap hk) := by
    have hsum := Finset.sum_fiberwise_of_maps_to hmaps
      (fun hk => f (productMap hk))
    simpa [domain, target, productMap, positiveProductPairFiber] using hsum.symm
  have hfiberConst (r : ℕ) :
      (∑ hk ∈ positiveProductPairFiber N r, f r) =
        ((positiveProductPairFiber N r).card : ℝ) * f r := by
    simp [Finset.sum_const, nsmul_eq_mul]
  calc
    (∑ hk ∈ (Finset.Icc 1 N).product (Finset.Icc 1 N),
        f (hk.1 * hk.2)) =
        ∑ r ∈ target,
          ∑ hk ∈ positiveProductPairFiber N r, f (productMap hk) := by
            simpa [domain, productMap] using hdecomp
    _ = ∑ r ∈ target,
          ((positiveProductPairFiber N r).card : ℝ) * f r := by
            apply Finset.sum_congr rfl
            intro r hr
            have hconst : ∀ hk ∈ positiveProductPairFiber N r,
                f (productMap hk) = f r := by
              intro hk hhk
              have hproduct := (Finset.mem_filter.mp hhk).2
              simp [productMap, hproduct]
            rw [Finset.sum_congr rfl hconst]
            exact hfiberConst r
    _ ≤ ∑ r ∈ target, (r.divisors.card : ℝ) * f r := by
          apply Finset.sum_le_sum
          intro r hr
          have hrpos : 0 < r := by
            have := Finset.mem_Icc.mp hr
            omega
          have hcount := card_positiveProductPairFiber_le_divisors N r hrpos
          have hcountR :
              ((positiveProductPairFiber N r).card : ℝ) ≤
                (r.divisors.card : ℝ) := by exact_mod_cast hcount
          exact mul_le_mul_of_nonneg_right hcountR (hf r)

/-- The divisor estimate is uniform over the size of the containing box. -/
theorem exists_positiveProductPairFiber_rpow_bound
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N r : ℕ, 0 < r →
      ((positiveProductPairFiber N r).card : ℝ) ≤
        C * Real.rpow (r : ℝ) ε := by
  obtain ⟨C, hC, hbound⟩ := exists_divisor_rpow_bound hε
  refine ⟨C, hC, fun N r hr ↦ ?_⟩
  have hcard := card_positiveProductPairFiber_le_divisors N r hr
  have hcardR :
      ((positiveProductPairFiber N r).card : ℝ) ≤ (r.divisors.card : ℝ) :=
    by exact_mod_cast hcard
  exact hcardR.trans (hbound r (Nat.ne_of_gt hr))

/-- Reindex a nonnegative weight on bounded positive factor pairs by their
product, and insert the uniform subpolynomial divisor multiplicity. -/
theorem exists_uniform_sum_positiveProductPairs_le_divisor_envelope
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (f : ℕ → ℝ),
      (∀ r, 0 ≤ f r) →
      (∑ hk ∈ (Finset.Icc 1 N).product (Finset.Icc 1 N),
        f (hk.1 * hk.2)) ≤
        C * Real.rpow ((N * N : ℕ) : ℝ) ε *
          ∑ r ∈ Finset.Icc 1 (N * N), f r := by
  classical
  obtain ⟨C, hC, hdiv⟩ := exists_divisor_rpow_bound hε
  refine ⟨C, hC, fun N f hf => ?_⟩
  let domain := (Finset.Icc 1 N).product (Finset.Icc 1 N)
  let target := Finset.Icc 1 (N * N)
  let productMap : ℕ × ℕ → ℕ := fun hk => hk.1 * hk.2
  have hmaps : ∀ hk ∈ domain, productMap hk ∈ target := by
    intro hk hhk
    have hhk' := Finset.mem_product.mp hhk
    have hfst := Finset.mem_Icc.mp hhk'.1
    have hsnd := Finset.mem_Icc.mp hhk'.2
    apply Finset.mem_Icc.mpr
    constructor
    · exact Nat.mul_pos (by omega) (by omega)
    · exact Nat.mul_le_mul hfst.2 hsnd.2
  have hdecomp :
      (∑ hk ∈ domain, f (productMap hk)) =
        ∑ r ∈ target,
          ∑ hk ∈ positiveProductPairFiber N r, f (productMap hk) := by
    have hsum := Finset.sum_fiberwise_of_maps_to hmaps
      (fun hk => f (productMap hk))
    simpa [domain, target, productMap, positiveProductPairFiber] using
      hsum.symm
  have hfiberConst (r : ℕ) :
      (∑ hk ∈ positiveProductPairFiber N r, f r) =
        ((positiveProductPairFiber N r).card : ℝ) * f r := by
    simp [Finset.sum_const, nsmul_eq_mul]
  calc
    (∑ hk ∈ domain, f (productMap hk)) =
        ∑ r ∈ target,
          ∑ hk ∈ positiveProductPairFiber N r, f (productMap hk) := hdecomp
    _ = ∑ r ∈ target,
        ((positiveProductPairFiber N r).card : ℝ) * f r := by
      apply Finset.sum_congr rfl
      intro r hr
      have hconst : ∀ hk ∈ positiveProductPairFiber N r,
          f (productMap hk) = f r := by
        intro hk hhk
        have hproduct := (Finset.mem_filter.mp hhk).2
        simp [productMap, hproduct]
      rw [Finset.sum_congr rfl hconst]
      exact hfiberConst r
    _ ≤ ∑ r ∈ target,
        (C * Real.rpow ((N * N : ℕ) : ℝ) ε) * f r := by
      apply Finset.sum_le_sum
      intro r hr
      have hr' := Finset.mem_Icc.mp hr
      have hrpos : 0 < r := by omega
      have hpow : Real.rpow (r : ℝ) ε ≤
          Real.rpow ((N * N : ℕ) : ℝ) ε := by
        apply Real.rpow_le_rpow
        · exact_mod_cast (Nat.zero_le r)
        · exact_mod_cast hr'.2
        · exact hε.le
      have hcount := card_positiveProductPairFiber_le_divisors N r hrpos
      have hcountR :
          ((positiveProductPairFiber N r).card : ℝ) ≤
            (r.divisors.card : ℝ) := by exact_mod_cast hcount
      have hcountBound :
          ((positiveProductPairFiber N r).card : ℝ) ≤
            C * Real.rpow (r : ℝ) ε :=
        hcountR.trans (hdiv r hrpos.ne')
      have hcountEnvelope :
          ((positiveProductPairFiber N r).card : ℝ) ≤
            C * Real.rpow ((N * N : ℕ) : ℝ) ε := by
        exact hcountBound.trans (mul_le_mul_of_nonneg_left hpow hC.le)
      exact mul_le_mul_of_nonneg_right hcountEnvelope (hf r)
    _ = C * Real.rpow ((N * N : ℕ) : ℝ) ε *
        ∑ r ∈ target, f r := by
      rw [Finset.mul_sum]
    _ = C * Real.rpow ((N * N : ℕ) : ℝ) ε *
        ∑ r ∈ Finset.Icc 1 (N * N), f r := by rfl

/-- Pointwise specialization of the absolute-constant pair-product bound. -/
theorem exists_sum_positiveProductPairs_le_divisor_envelope
    (N : ℕ) {ε : ℝ} (hε : 0 < ε)
    (f : ℕ → ℝ) (hf : ∀ r, 0 ≤ f r) :
    ∃ C : ℝ, 0 < C ∧
      (∑ hk ∈ (Finset.Icc 1 N).product (Finset.Icc 1 N),
        f (hk.1 * hk.2)) ≤
        C * Real.rpow ((N * N : ℕ) : ℝ) ε *
          ∑ r ∈ Finset.Icc 1 (N * N), f r := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_sum_positiveProductPairs_le_divisor_envelope hε
  exact ⟨C, hC, hbound N f hf⟩

/-- Combine divisor multiplicities with the proved arbitrary-range
six-frequency spacing estimate. This is the weighted pair-product bound
needed by the two-difference Weyl inequality. -/
theorem exists_uniform_sum_positiveProductPairs_sixMul_envelope_le
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N a q : ℕ) (alpha beta Y : ℝ),
      (hq : 0 < q) → (hac : Nat.Coprime a q) →
      (halpha : alpha = rationalCenter a q + beta) →
      (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2) → (hY : 0 ≤ Y) →
      (∑ hk ∈ (Finset.Icc 1 N).product (Finset.Icc 1 N),
        linearDistanceEnvelope Y (6 * alpha * (hk.1 * hk.2 : ℕ))) ≤
        C * Real.rpow ((N * N : ℕ) : ℝ) ε *
          sixMulSpacingEnvelopeBound N q Y := by
  obtain ⟨C, hC, hpair⟩ :=
    exists_uniform_sum_positiveProductPairs_le_divisor_envelope hε
  refine ⟨C, hC, fun N a q alpha beta Y hq hac halpha hbeta hY => ?_⟩
  have hpair' := hpair N
    (fun r => linearDistanceEnvelope Y (6 * alpha * (r : ℕ)))
    (fun r => linearDistanceEnvelope_nonneg
      (Y := Y) (theta := 6 * alpha * r) hY)
  have hshift :
      (∑ r ∈ Finset.Icc 1 (N * N),
        linearDistanceEnvelope Y (6 * alpha * (r : ℕ))) =
      ∑ j ∈ Finset.range (N * N),
        linearDistanceEnvelope Y ((6 * alpha) * (1 + j : ℕ)) := by
    have h := (sum_range_succ_eq_sum_Icc (N * N)
      (fun r => linearDistanceEnvelope Y (6 * alpha * (r : ℕ)))).symm
    simpa [Nat.one_add] using h
  have hspacing := sum_sixMul_linearDistanceEnvelope_range_le Y
    (a := a) (q := q) (B := 1) (R := N * N)
    hq hac halpha hbeta hY
  have hfactor : 0 ≤ C * Real.rpow ((N * N : ℕ) : ℝ) ε := by
    apply mul_nonneg hC.le
    exact Real.rpow_nonneg (by positivity) _
  calc
    (∑ hk ∈ (Finset.Icc 1 N).product (Finset.Icc 1 N),
        linearDistanceEnvelope Y (6 * alpha * (hk.1 * hk.2 : ℕ))) ≤
        C * Real.rpow ((N * N : ℕ) : ℝ) ε *
          ∑ r ∈ Finset.Icc 1 (N * N),
            linearDistanceEnvelope Y (6 * alpha * (r : ℕ)) := hpair'
    _ = C * Real.rpow ((N * N : ℕ) : ℝ) ε *
          ∑ j ∈ Finset.range (N * N),
            linearDistanceEnvelope Y ((6 * alpha) * (1 + j : ℕ)) := by
      rw [hshift]
    _ ≤ C * Real.rpow ((N * N : ℕ) : ℝ) ε *
          sixMulSpacingEnvelopeBound N q Y := by
      apply mul_le_mul_of_nonneg_left _ hfactor
      simpa [sixMulSpacingEnvelopeBound, mul_assoc] using hspacing

/-- Pointwise specialization of the uniform six-frequency pair estimate. -/
theorem exists_sum_positiveProductPairs_sixMul_envelope_le
    (N a q : ℕ) (alpha beta Y : ℝ)
    (hq : 0 < q) (hac : Nat.Coprime a q)
    (halpha : alpha = rationalCenter a q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (hY : 0 ≤ Y) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      (∑ hk ∈ (Finset.Icc 1 N).product (Finset.Icc 1 N),
        linearDistanceEnvelope Y (6 * alpha * (hk.1 * hk.2 : ℕ))) ≤
        C * Real.rpow ((N * N : ℕ) : ℝ) ε *
          sixMulSpacingEnvelopeBound N q Y := by
  obtain ⟨C, hC, hpair⟩ :=
    exists_uniform_sum_positiveProductPairs_sixMul_envelope_le hε
  exact ⟨C, hC, hpair N a q alpha beta Y hq hac halpha hbeta hY⟩

/-- Generic divisor-threshold split: any nonnegative factor-pair envelope
bounded by `Y` and with total spacing mass `S` pays `T*S` plus the proved
seventh-log rich-divisor tail. -/
theorem sum_positiveProductPairs_le_divisorThreshold_of_spacingBound
    (N : ℕ) (E : ℕ → ℝ) (Y T S : ℝ)
    (hY : 0 ≤ Y) (hT : 0 < T)
    (hE_nonneg : ∀ r, 0 ≤ E r) (hE_le : ∀ r, E r ≤ Y)
    (hspacing : (∑ r ∈ Finset.Icc 1 (N * N), E r) ≤ S) :
    (∑ hk ∈ (Finset.Icc 1 N).product (Finset.Icc 1 N),
      E (hk.1 * hk.2)) ≤
      T * S + Y * (((N * N : ℕ) : ℝ) *
        (1 + Real.log ((N * N : ℕ) : ℝ)) ^ 7) / T ^ 2 := by
  classical
  let M := N * N
  let I := Finset.Icc 1 M
  let f : ℕ → ℝ := fun r => (r.divisors.card : ℝ)
  let B := I.filter fun r => T ≤ f r
  let G := I.filter fun r => ¬ T ≤ f r
  have hdiv_nonneg : ∀ r, 0 ≤ f r := by
    intro r
    positivity
  have hpair :
      (∑ hk ∈ (Finset.Icc 1 N).product (Finset.Icc 1 N),
        E (hk.1 * hk.2)) ≤ ∑ r ∈ I, f r * E r := by
    simpa [I, f, M] using
      (sum_positiveProductPairs_le_divisorWeightedEnvelope N E hE_nonneg)
  have hpoint : ∀ r ∈ I,
      f r * E r ≤ if T ≤ f r then Y * f r else T * E r := by
    intro r hr
    by_cases hrich : T ≤ f r
    · simp only [hrich, if_pos]
      calc
        f r * E r = E r * f r := by ring
        _ ≤ Y * f r := mul_le_mul_of_nonneg_right (hE_le r) (hdiv_nonneg r)
    · simp only [hrich]
      exact mul_le_mul_of_nonneg_right (le_of_not_ge hrich) (hE_nonneg r)
  have hsplitBound :
      (∑ r ∈ I, f r * E r) ≤
        Y * (∑ r ∈ B, f r) + T * (∑ r ∈ G, E r) := by
    calc
      (∑ r ∈ I, f r * E r) ≤
          ∑ r ∈ I, (if T ≤ f r then Y * f r else T * E r) :=
        Finset.sum_le_sum fun r hr => hpoint r hr
      _ = Y * (∑ r ∈ B, f r) + T * (∑ r ∈ G, E r) := by
        have hBsum : (∑ r ∈ B, f r) =
            ∑ r ∈ I, if T ≤ f r then f r else 0 := by
          simp [B, Finset.sum_filter]
        have hGsum : (∑ r ∈ G, E r) =
            ∑ r ∈ I, if T ≤ f r then 0 else E r := by
          calc
            (∑ r ∈ G, E r) =
                ∑ r ∈ I, if ¬ T ≤ f r then E r else 0 := by
              simp [G, Finset.sum_filter]
            _ = ∑ r ∈ I, if T ≤ f r then 0 else E r := by
              apply Finset.sum_congr rfl
              intro r hr
              by_cases h : T ≤ f r <;> simp [h]
        rw [hBsum, hGsum]
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro r hr
        by_cases h : T ≤ f r <;> simp [h]
  have htailScaled : T ^ 2 * (∑ r ∈ B, f r) ≤
      (M : ℝ) * (1 + Real.log (M : ℝ)) ^ 7 := by
    simpa [B, I, f, M] using
      (divisorThresholdedTail_le (M := M) (P := fun r => T ≤
        (r.divisors.card : ℝ)) T 1 hT (by norm_num) (by
          intro r hr hrich
          simpa using hrich))
  have htail : (∑ r ∈ B, f r) ≤
      ((M : ℝ) * (1 + Real.log (M : ℝ)) ^ 7) / T ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hT)).2
    simpa [mul_comm] using htailScaled
  calc
    (∑ hk ∈ (Finset.Icc 1 N).product (Finset.Icc 1 N), E (hk.1 * hk.2)) ≤
        ∑ r ∈ I, f r * E r := hpair
    _ ≤ Y * (∑ r ∈ B, f r) + T * (∑ r ∈ G, E r) := hsplitBound
    _ ≤ Y * (((M : ℝ) * (1 + Real.log (M : ℝ)) ^ 7) / T ^ 2) + T * S := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left htail hY
        · apply mul_le_mul_of_nonneg_left _ hT.le
          calc
            (∑ r ∈ G, E r) ≤ ∑ r ∈ I, E r :=
              Finset.sum_le_sum_of_subset_of_nonneg
                (s := G) (t := I) (f := E) (Finset.filter_subset _ _)
                (by
                  intro r hr _
                  exact hE_nonneg r)
            _ ≤ S := by simpa [I, M] using hspacing
    _ = T * S +
          Y * (((N * N : ℕ) : ℝ) *
            (1 + Real.log ((N * N : ℕ) : ℝ)) ^ 7) / T ^ 2 := by
          simp [M]
          ring

/-- Bound the concrete positive second-difference sum by the weighted
factor-pair envelope. The second-difference phase is linear in the base
variable, with slope `6αhk`; all remaining terms form a unit prefactor. -/
theorem norm_cubicSecondDifferenceTripleSum_le_pairEnvelope
    (alpha : ℝ) (N : ℕ) :
    ‖cubicSecondDifferenceTripleSum alpha N‖ ≤
      ∑ hk ∈ (Finset.Icc 1 N).product (Finset.Icc 1 N),
        linearDistanceEnvelope (N + 1 : ℝ)
          (6 * alpha * (hk.1 * hk.2 : ℕ)) := by
  classical
  have hdecomp : cubicSecondDifferenceTripleSum alpha N =
      ∑ h ∈ Finset.Icc 1 N,
        ∑ km ∈ positiveCubicShiftPairs (N - h),
          addChar alpha (3 * h * km.1 * (2 * km.2 + h + km.1)) := by
    unfold cubicSecondDifferenceTripleSum
    simpa [cubicSecondDifferenceFrequency] using
      (sum_positiveShiftPairs_eq_secondDifferenceTriples N
        (fun h k m => addChar alpha (3 * h * k * (2 * m + h + k)))).symm
  rw [hdecomp]
  calc
    _ ≤ ∑ h ∈ Finset.Icc 1 N,
        ‖∑ km ∈ positiveCubicShiftPairs (N - h),
          addChar alpha (3 * h * km.1 * (2 * km.2 + h + km.1))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ h ∈ Finset.Icc 1 N,
        ∑ k ∈ Finset.Icc 1 (N - h),
          linearDistanceEnvelope (N + 1 : ℝ) (6 * alpha * (h * k : ℕ)) := by
      apply Finset.sum_le_sum
      intro h hh
      rw [sum_positiveCubicShiftPairs_eq_sum_by_shift (N - h)
        (fun k m => addChar alpha (3 * h * k * (2 * m + h + k)))]
      calc
        _ ≤ ∑ k ∈ Finset.Icc 1 (N - h),
            ‖∑ m ∈ Finset.range (N - h + 1 - k),
              addChar alpha (3 * h * k * (2 * m + h + k))‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ Finset.Icc 1 (N - h),
            linearDistanceEnvelope (N + 1 : ℝ) (6 * alpha * (h * k : ℕ)) := by
          apply Finset.sum_le_sum
          intro k hk
          have hbound : k ≤ N - h := (Finset.mem_Icc.mp hk).2
          let X := N - h + 1 - k
          let theta := 6 * alpha * (h * k : ℕ)
          let c := addChar alpha (3 * h * k * (h + k))
          have hc : ‖c‖ = 1 := by simp [c]
          have hphase (m : ℕ) :
              addChar alpha (3 * h * k * (2 * m + h + k)) =
                c * addChar theta m := by
            have hfreq :
                3 * h * k * (2 * m + h + k) =
                  3 * h * k * (h + k) + (6 * h * k) * m := by ring
            rw [hfreq, addChar_add]
            dsimp [c, theta]
            congr 1
            rw [addChar_nat_mul]
            congr 1
            push_cast
            ring
          have hsumEq :
              (∑ m ∈ Finset.range X,
                addChar alpha (3 * h * k * (2 * m + h + k))) =
              ∑ m ∈ Finset.range X, c * addChar theta m := by
            apply Finset.sum_congr rfl
            intro m hm
            exact hphase m
          have hlinear := norm_unitPhase_shiftedLinearAddCharSum_le_distanceEnvelope
            theta 0 X c hc
          have hlinear' :
              ‖∑ m ∈ Finset.range X, c * addChar theta m‖ ≤
                linearDistanceEnvelope (X : ℝ) theta := by
            simpa [linearDistanceEnvelope,
              CookMagyarArcs.periodicDistance_eq_abs_sub_round] using hlinear
          have hXle : X ≤ N + 1 := by
            dsimp [X]
            omega
          have hYmono := linearDistanceEnvelope_mono
            (Y₁ := (X : ℝ)) (Y₂ := (N + 1 : ℝ)) (theta := theta)
              (by exact_mod_cast hXle)
          have htheta : theta = 6 * alpha * (h * k : ℕ) := by
            rfl
          calc
            ‖∑ m ∈ Finset.range (N - h + 1 - k),
                addChar alpha (3 * h * k * (2 * m + h + k))‖ =
                ‖∑ m ∈ Finset.range X, c * addChar theta m‖ := by
                  simpa [X] using congrArg (fun z : ℂ => ‖z‖) hsumEq
            _ ≤ linearDistanceEnvelope (N + 1 : ℝ) theta :=
              hlinear'.trans hYmono
            _ = linearDistanceEnvelope (N + 1 : ℝ)
                (6 * alpha * (h * k : ℕ)) := by rw [htheta]
    _ ≤ ∑ h ∈ Finset.Icc 1 N,
        ∑ k ∈ Finset.Icc 1 N,
          linearDistanceEnvelope (N + 1 : ℝ) (6 * alpha * (h * k : ℕ)) := by
      apply Finset.sum_le_sum
      intro h hh
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Icc_subset_Icc_right (by omega))
      intro k hk hnot
      exact linearDistanceEnvelope_nonneg (by positivity)
    _ = ∑ hk ∈ (Finset.Icc 1 N).product (Finset.Icc 1 N),
        linearDistanceEnvelope (N + 1 : ℝ)
          (6 * alpha * (hk.1 * hk.2 : ℕ)) := by
      symm
      exact Finset.sum_product (Finset.Icc 1 N) (Finset.Icc 1 N)
        (fun hk => linearDistanceEnvelope (N + 1 : ℝ)
          (6 * alpha * (hk.1 * hk.2 : ℕ)))

/-- Replace the pointwise subpower divisor bound in the pair-spacing
estimate by a threshold split and the proved cubic divisor moment. The small
divisor counts cost `T`; the rich tail costs the seventh-log moment divided
by `T²`. -/
theorem sum_positiveProductPairs_sixMul_envelope_le_divisorThreshold
    (N a q : ℕ) (alpha beta Y T : ℝ)
    (hq : 0 < q) (hac : Nat.Coprime a q)
    (halpha : alpha = rationalCenter a q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (hY : 0 ≤ Y) (hT : 0 < T) :
    (∑ hk ∈ (Finset.Icc 1 N).product (Finset.Icc 1 N),
      linearDistanceEnvelope Y (6 * alpha * (hk.1 * hk.2 : ℕ))) ≤
      T * sixMulSpacingEnvelopeBound N q Y +
        Y * (((N * N : ℕ) : ℝ) *
          (1 + Real.log ((N * N : ℕ) : ℝ)) ^ 7) / T ^ 2 := by
  classical
  let M := N * N
  let I := Finset.Icc 1 M
  let E : ℕ → ℝ := fun r =>
    linearDistanceEnvelope Y (6 * alpha * (r : ℕ))
  let f : ℕ → ℝ := fun r => (r.divisors.card : ℝ)
  let B := I.filter fun r => T ≤ f r
  let G := I.filter fun r => ¬ T ≤ f r
  have hE_nonneg : ∀ r, 0 ≤ E r := by
    intro r
    exact linearDistanceEnvelope_nonneg hY
  have hE_le : ∀ r, E r ≤ Y := by
    intro r
    exact linearDistanceEnvelope_le Y (6 * alpha * (r : ℕ))
  have hdiv_nonneg : ∀ r, 0 ≤ f r := by
    intro r
    positivity
  have hpair :
      (∑ hk ∈ (Finset.Icc 1 N).product (Finset.Icc 1 N),
        E (hk.1 * hk.2)) ≤
        ∑ r ∈ I, f r * E r := by
    simpa [I, E, f, M] using
      (sum_positiveProductPairs_le_divisorWeightedEnvelope N E hE_nonneg)
  have hpoint : ∀ r ∈ I,
      f r * E r ≤ if T ≤ f r then Y * f r else T * E r := by
    intro r hr
    by_cases hrich : T ≤ f r
    · simp only [hrich, if_pos]
      calc
        f r * E r = E r * f r := by ring
        _ ≤ Y * f r := mul_le_mul_of_nonneg_right (hE_le r) (hdiv_nonneg r)
    · simp only [hrich]
      exact mul_le_mul_of_nonneg_right (le_of_not_ge hrich) (hE_nonneg r)
  have hsplitBound :
      (∑ r ∈ I, f r * E r) ≤
        Y * (∑ r ∈ B, f r) + T * (∑ r ∈ G, E r) := by
    calc
      (∑ r ∈ I, f r * E r) ≤
          ∑ r ∈ I, (if T ≤ f r then Y * f r else T * E r) :=
        Finset.sum_le_sum fun r hr => hpoint r hr
      _ = Y * (∑ r ∈ B, f r) + T * (∑ r ∈ G, E r) := by
        have hBsum : (∑ r ∈ B, f r) =
            ∑ r ∈ I, if T ≤ f r then f r else 0 := by
          simp [B, Finset.sum_filter]
        have hGsum : (∑ r ∈ G, E r) =
            ∑ r ∈ I, if T ≤ f r then 0 else E r := by
          calc
            (∑ r ∈ G, E r) =
                ∑ r ∈ I, if ¬ T ≤ f r then E r else 0 := by
              simp [G, Finset.sum_filter]
            _ = ∑ r ∈ I, if T ≤ f r then 0 else E r := by
              apply Finset.sum_congr rfl
              intro r hr
              by_cases h : T ≤ f r <;> simp [h]
        rw [hBsum, hGsum]
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro r hr
        by_cases h : T ≤ f r <;> simp [h]
  have htailScaled : T ^ 2 * (∑ r ∈ B, f r) ≤
      (M : ℝ) * (1 + Real.log (M : ℝ)) ^ 7 := by
    simpa [B, I, f, M] using
      (divisorThresholdedTail_le (M := M) (P := fun r => T ≤
        (r.divisors.card : ℝ)) T 1 hT (by norm_num) (by
          intro r hr hrich
          simpa using hrich))
  have htail : (∑ r ∈ B, f r) ≤
      ((M : ℝ) * (1 + Real.log (M : ℝ)) ^ 7) / T ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hT)).2
    simpa [mul_comm] using htailScaled
  have hspacing : (∑ r ∈ I, E r) ≤ sixMulSpacingEnvelopeBound N q Y := by
    have hshift :
        (∑ r ∈ Finset.Icc 1 M, E r) =
          ∑ j ∈ Finset.range M,
            linearDistanceEnvelope Y ((6 * alpha) * (1 + j : ℕ)) := by
      have h := (sum_range_succ_eq_sum_Icc M
        (fun r => linearDistanceEnvelope Y (6 * alpha * (r : ℕ)))).symm
      simpa [E, M, Nat.one_add, mul_assoc] using h
    have hbound := sum_sixMul_linearDistanceEnvelope_range_le Y
      (a := a) (q := q) (B := 1) (R := M)
      hq hac halpha hbeta hY
    rw [hshift]
    calc
      (∑ j ∈ Finset.range M,
          linearDistanceEnvelope Y ((6 * alpha) * (1 + j : ℕ))) ≤
          ((N * N) / (q / Nat.gcd q 6) + 1 : ℕ) *
            (28 * (Y + ((q / Nat.gcd q 6 : ℕ) : ℝ) *
              (1 + Real.log ((q / Nat.gcd q 6 : ℕ) : ℝ)))) := by
        simpa [M] using hbound
      _ = sixMulSpacingEnvelopeBound N q Y := by
        simp [sixMulSpacingEnvelopeBound]
        ring
  calc
    (∑ hk ∈ (Finset.Icc 1 N).product (Finset.Icc 1 N),
        linearDistanceEnvelope Y (6 * alpha * (hk.1 * hk.2 : ℕ))) ≤
        ∑ r ∈ I, f r * E r := hpair
    _ ≤ Y * (∑ r ∈ B, f r) + T * (∑ r ∈ G, E r) := hsplitBound
    _ ≤ Y * (((M : ℝ) * (1 + Real.log (M : ℝ)) ^ 7) / T ^ 2) +
          T * sixMulSpacingEnvelopeBound N q Y := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left htail hY
        · apply mul_le_mul_of_nonneg_left _ hT.le
          calc
            (∑ r ∈ G, E r) ≤ ∑ r ∈ I, E r :=
              Finset.sum_le_sum_of_subset_of_nonneg
                (s := G) (t := I) (f := E) (Finset.filter_subset _ _)
                (by
                  intro r hr _
                  exact hE_nonneg r)
            _ ≤ sixMulSpacingEnvelopeBound N q Y := hspacing
    _ = T * sixMulSpacingEnvelopeBound N q Y +
          Y * ((M : ℝ) * (1 + Real.log (M : ℝ)) ^ 7) / T ^ 2 := by ring
    _ = T * sixMulSpacingEnvelopeBound N q Y +
          Y * (((N * N : ℕ) : ℝ) *
            (1 + Real.log ((N * N : ℕ) : ℝ)) ^ 7) / T ^ 2 := by
              rfl

/-- Divisor-threshold pair bound retaining the larger shell occupancy from
an approximation error `|beta|≤K/q²`. -/
theorem sum_positiveProductPairs_sixMul_envelope_le_divisorThreshold_of_error_constant
    (N a q K : ℕ) (alpha beta Y T : ℝ)
    (hq : 0 < q) (hac : Nat.Coprime a q)
    (halpha : alpha = rationalCenter a q + beta)
    (hbeta : |beta| ≤ (K : ℝ) / (q : ℝ) ^ 2)
    (hY : 0 ≤ Y) (hT : 0 < T) :
    (∑ hk ∈ (Finset.Icc 1 N).product (Finset.Icc 1 N),
      linearDistanceEnvelope Y (6 * alpha * (hk.1 * hk.2 : ℕ))) ≤
      T * sixMulSpacingEnvelopeBoundWithError N q Y K +
        Y * (((N * N : ℕ) : ℝ) *
          (1 + Real.log ((N * N : ℕ) : ℝ)) ^ 7) / T ^ 2 := by
  classical
  let M := N * N
  let E : ℕ → ℝ := fun r =>
    linearDistanceEnvelope Y (6 * alpha * (r : ℕ))
  have hE_nonneg : ∀ r, 0 ≤ E r := by
    intro r
    exact linearDistanceEnvelope_nonneg hY
  have hE_le : ∀ r, E r ≤ Y := by
    intro r
    exact linearDistanceEnvelope_le Y (6 * alpha * (r : ℕ))
  have hshift :
      (∑ r ∈ Finset.Icc 1 M, E r) =
        ∑ j ∈ Finset.range M,
          linearDistanceEnvelope Y ((6 * alpha) * (1 + j : ℕ)) := by
    have h := (sum_range_succ_eq_sum_Icc M
      (fun r => linearDistanceEnvelope Y (6 * alpha * (r : ℕ)))).symm
    simpa [E, M, Nat.one_add, mul_assoc] using h
  have hbound := sum_sixMul_linearDistanceEnvelope_range_le_of_error_constant
    (a := a) (q := q) (B := 1) (R := M) (K := K) Y
      hq hac halpha hbeta hY
  have hspacing :
      (∑ r ∈ Finset.Icc 1 (N * N), E r) ≤
        sixMulSpacingEnvelopeBoundWithError N q Y K := by
    rw [show (N * N : ℕ) = M by rfl, hshift]
    calc
      (∑ j ∈ Finset.range M,
          linearDistanceEnvelope Y ((6 * alpha) * (1 + j : ℕ))) ≤
          ((M / (q / Nat.gcd q 6) + 1 : ℕ) : ℝ) *
            ((2 * (2 * (6 * K) + 2) : ℕ) : ℝ) *
              (Y + ((q / Nat.gcd q 6 : ℕ) : ℝ) *
                (1 + Real.log ((q / Nat.gcd q 6 : ℕ) : ℝ))) := by
        simpa [M] using hbound
      _ = sixMulSpacingEnvelopeBoundWithError N q Y K := by
        simp [sixMulSpacingEnvelopeBoundWithError, M]
  exact sum_positiveProductPairs_le_divisorThreshold_of_spacingBound
    N E Y T (sixMulSpacingEnvelopeBoundWithError N q Y K)
      hY hT hE_nonneg hE_le hspacing

/-- The gcd-reduced six-multiple spacing envelope inherits the same
normalized bound as the original rational denominator. -/
theorem pow_four_sixMulSpacingEnvelopeBound_le
    (B : ℝ) (N q : ℕ) (rho : ℕ)
    (hB : 1 ≤ B) (hB6X : B ^ 6 ≤ (N + 1 : ℝ))
    (hB5q : B ^ 5 ≤ (q : ℝ))
    (hqUpper : (q : ℝ) * B ^ rho ≤ (N + 1 : ℝ) ^ 3)
    (hBpow : B ^ 6 ≤ B ^ rho)
    (hlogq : Real.log (q : ℝ) ≤ 4 * B) :
    B ^ 4 * sixMulSpacingEnvelopeBound N q (N + 1 : ℝ) ≤
      1176 * (N + 1 : ℝ) ^ 3 / B := by
  have hqpos : 0 < q := by
    have hB5pos : 0 < B ^ 5 := by positivity
    exact_mod_cast (show (0 : ℝ) < (q : ℝ) by linarith)
  have hcoarse := sixMulSpacingEnvelopeBound_le_coarse N q
    (N + 1 : ℝ) hqpos (by positivity)
  have hscale := mul_le_mul_of_nonneg_left hcoarse
    (by positivity : 0 ≤ B ^ 4)
  calc
    B ^ 4 * sixMulSpacingEnvelopeBound N q (N + 1 : ℝ) ≤
        B ^ 4 * coarseSpacingEnvelopeBound N q (N + 1 : ℝ) := hscale
    _ ≤ 1176 * (N + 1 : ℝ) ^ 3 / B :=
      pow_four_coarseSpacingEnvelopeBound_le B N q rho
        hB hB6X hB5q hqUpper hBpow hlogq

/-- The shell occupancy loss for `|beta|≤K/q²` is at most `K` times the
ordinary occupancy. This isolates the only new constant introduced by the
progression affine change. -/
theorem sixMulSpacingEnvelopeBoundWithError_le_mul
    (N q K : ℕ) (Y : ℝ) (hq : 0 < q) (hK : 1 ≤ K) (hY : 0 ≤ Y) :
    sixMulSpacingEnvelopeBoundWithError N q Y K ≤
      (K : ℝ) * sixMulSpacingEnvelopeBound N q Y := by
  have hgpos : 0 < Nat.gcd q 6 := Nat.gcd_pos_of_pos_left 6 hq
  have hq0pos : 0 < q / Nat.gcd q 6 :=
    Nat.div_pos (Nat.le_of_dvd hq (Nat.gcd_dvd_left q 6)) hgpos
  have hq0one : 1 ≤ q / Nat.gcd q 6 := Nat.succ_le_of_lt hq0pos
  have hlog : 0 ≤ Real.log ((q / Nat.gcd q 6 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hq0one)
  have hrest : 0 ≤ Y + ((q / Nat.gcd q 6 : ℕ) : ℝ) *
      (1 + Real.log ((q / Nat.gcd q 6 : ℕ) : ℝ)) := by positivity
  have hfactor :
      (2 * (2 * (6 * K) + 2) : ℕ) ≤ 28 * K := by omega
  have hfactor' :
      ((2 * (2 * (6 * K) + 2) : ℕ) : ℝ) ≤ 28 * (K : ℝ) := by
    exact_mod_cast hfactor
  have hcount :
      0 ≤ ((N * N / (q / Nat.gcd q 6) + 1 : ℕ) : ℝ) := by positivity
  unfold sixMulSpacingEnvelopeBoundWithError sixMulSpacingEnvelopeBound
  calc
    (((N * N / (q / Nat.gcd q 6) + 1 : ℕ) : ℝ) *
        ((2 * (2 * (6 * K) + 2) : ℕ) : ℝ)) *
        (Y + ((q / Nat.gcd q 6 : ℕ) : ℝ) *
          (1 + Real.log ((q / Nat.gcd q 6 : ℕ) : ℝ))) ≤
      (((N * N / (q / Nat.gcd q 6) + 1 : ℕ) : ℝ) *
        (28 * (K : ℝ))) *
        (Y + ((q / Nat.gcd q 6 : ℕ) : ℝ) *
          (1 + Real.log ((q / Nat.gcd q 6 : ℕ) : ℝ))) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hfactor' hcount) hrest
    _ = (K : ℝ) *
        ((((N * N / (q / Nat.gcd q 6) + 1 : ℕ) : ℝ) * 28) *
          (Y + ((q / Nat.gcd q 6 : ℕ) : ℝ) *
            (1 + Real.log ((q / Nat.gcd q 6 : ℕ) : ℝ)))) := by ring

/-- The `B^-1` spacing saving survives the progression error constant once
the lower-denominator, progression-length, and upper-window margins all
cover the factor `K`. -/
theorem pow_four_sixMulSpacingEnvelopeBoundWithError_le
    (B : ℝ) (N q K : ℕ) (rho : ℕ)
    (hB : 1 ≤ B) (hK : 1 ≤ K)
    (hK6X : (K : ℝ) * B ^ 6 ≤ (N + 1 : ℝ))
    (hK5q : (K : ℝ) * B ^ 5 ≤ (q : ℝ))
    (hqUpper : (q : ℝ) * B ^ rho ≤ (N + 1 : ℝ) ^ 3)
    (hK6pow : (K : ℝ) * B ^ 6 ≤ B ^ rho)
    (hlogq : Real.log (q : ℝ) ≤ 4 * B) :
    B ^ 4 * sixMulSpacingEnvelopeBoundWithError N q (N + 1 : ℝ) K ≤
      1176 * (N + 1 : ℝ) ^ 3 / B := by
  have hKreal : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hBpos : 0 < B := by linarith
  have hKpos : 0 < (K : ℝ) := by linarith
  have hqrealpos : 0 < (q : ℝ) := by
    have hB5pos : 0 < B ^ 5 := by positivity
    exact (mul_pos hKpos hB5pos).trans_le hK5q
  have hq : 0 < q := by
    exact_mod_cast hqrealpos
  have herror := sixMulSpacingEnvelopeBoundWithError_le_mul
    N q K (N + 1 : ℝ) hq hK (by positivity)
  have hscale : B ^ 4 * sixMulSpacingEnvelopeBoundWithError N q
      (N + 1 : ℝ) K ≤
      B ^ 4 * ((K : ℝ) * sixMulSpacingEnvelopeBound N q (N + 1 : ℝ)) :=
    mul_le_mul_of_nonneg_left herror (by positivity)
  have hpoly := pow_four_scaledNormalizedSpacingPolynomial_le
    B (N + 1 : ℝ) (q : ℝ) (K : ℝ) rho hB hKreal
      hK6X hK5q hqUpper hK6pow hlogq
  have hN2 : (N : ℝ) ^ 2 ≤ (N + 1 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((N + 1 : ℝ) - (N : ℝ))]
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast hq
  have hfactor : 6 * (N : ℝ) ^ 2 / (q : ℝ) + 1 ≤
      6 * (N + 1 : ℝ) ^ 2 / (q : ℝ) + 1 := by
    have hdiv := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hN2 (by norm_num : (0 : ℝ) ≤ 6))
      (le_of_lt hqpos)
    linarith
  have hrest : 0 ≤ (N + 1 : ℝ) + (q : ℝ) *
      (1 + Real.log (q : ℝ)) := by
    have hB5one : (1 : ℝ) ≤ B ^ 5 := by
      calc
        1 = (1 : ℝ) ^ 5 := by norm_num
        _ ≤ B ^ 5 := by gcongr
    have hKscaled : B ^ 5 ≤ (K : ℝ) * B ^ 5 := by
      simpa using mul_le_mul_of_nonneg_right hKreal
        (by positivity : 0 ≤ B ^ 5)
    have hqone : (1 : ℝ) ≤ (q : ℝ) :=
      le_trans hB5one (le_trans hKscaled hK5q)
    have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqone
    positivity
  have hcoarse : (K : ℝ) *
      ((6 * (N : ℝ) ^ 2 / (q : ℝ) + 1) * 28 *
        ((N + 1 : ℝ) + (q : ℝ) * (1 + Real.log (q : ℝ)))) ≤
      (K : ℝ) *
      ((6 * (N + 1 : ℝ) ^ 2 / (q : ℝ) + 1) * 28 *
        ((N + 1 : ℝ) + (q : ℝ) * (1 + Real.log (q : ℝ)))) := by
    gcongr
  have hpoly' : B ^ 4 * (K : ℝ) *
      ((6 * (N + 1 : ℝ) ^ 2 / (q : ℝ) + 1) * 28 *
        ((N + 1 : ℝ) + (q : ℝ) * (1 + Real.log (q : ℝ)))) ≤
      1176 * (N + 1 : ℝ) ^ 3 / B := by
    simpa [mul_assoc] using hpoly
  calc
    B ^ 4 * sixMulSpacingEnvelopeBoundWithError N q (N + 1 : ℝ) K ≤
        B ^ 4 * ((K : ℝ) * sixMulSpacingEnvelopeBound N q (N + 1 : ℝ)) := hscale
    _ ≤ B ^ 4 * (K : ℝ) *
        ((6 * (N + 1 : ℝ) ^ 2 / (q : ℝ) + 1) * 28 *
          ((N + 1 : ℝ) + (q : ℝ) * (1 + Real.log (q : ℝ)))) := by
            have hbase := sixMulSpacingEnvelopeBound_le_coarse N q
              (N + 1 : ℝ) hq (by positivity)
            have hbase' := mul_le_mul_of_nonneg_left hbase
              (mul_nonneg (by positivity : 0 ≤ B ^ 4)
                (by positivity : 0 ≤ (K : ℝ)))
            have hcoarse' := mul_le_mul_of_nonneg_left hcoarse
              (by positivity : 0 ≤ B ^ 4)
            calc
              B ^ 4 * ((K : ℝ) * sixMulSpacingEnvelopeBound N q (N + 1 : ℝ)) ≤
                  B ^ 4 * (K : ℝ) *
                    ((6 * (N : ℝ) ^ 2 / (q : ℝ) + 1) * 28 *
                      ((N + 1 : ℝ) + (q : ℝ) * (1 + Real.log (q : ℝ)))) := by
                        simpa [coarseSpacingEnvelopeBound, pow_two, Nat.cast_mul,
                          mul_assoc, mul_left_comm,
                          mul_comm] using hbase'
              _ = B ^ 4 * ((K : ℝ) *
                    ((6 * (N : ℝ) ^ 2 / (q : ℝ) + 1) * 28 *
                      ((N + 1 : ℝ) + (q : ℝ) * (1 + Real.log (q : ℝ))))) := by ring
              _ ≤ B ^ 4 * ((K : ℝ) *
                    ((6 * (N + 1 : ℝ) ^ 2 / (q : ℝ) + 1) * 28 *
                      ((N + 1 : ℝ) + (q : ℝ) * (1 + Real.log (q : ℝ))))) := hcoarse'
              _ = B ^ 4 * (K : ℝ) *
                    ((6 * (N + 1 : ℝ) ^ 2 / (q : ℝ) + 1) * 28 *
                      ((N + 1 : ℝ) + (q : ℝ) * (1 + Real.log (q : ℝ)))) := by ring
    _ ≤ 1176 * (N + 1 : ℝ) ^ 3 / B := hpoly'

/-- Complete the thresholded fixed-product pair bound at `T=B^4`.
Both the ordinary spacing contribution and the rich-divisor moment tail now
save one reciprocal power of the logarithmic scale. -/
theorem sum_positiveProductPairs_sixMul_envelope_le_logSaving
    (B : ℝ) (N a q : ℕ) (alpha beta : ℝ) (rho : ℕ)
    (hB : 1 ≤ B) (hB6X : B ^ 6 ≤ (N + 1 : ℝ))
    (hB5q : B ^ 5 ≤ (q : ℝ))
    (hqUpper : (q : ℝ) * B ^ rho ≤ (N + 1 : ℝ) ^ 3)
    (hBpow : B ^ 6 ≤ B ^ rho)
    (hlogq : Real.log (q : ℝ) ≤ 4 * B)
    (hlogMoment : 1 + Real.log ((N * N : ℕ) : ℝ) ≤ 5 * B)
    (hN : 0 < N)
    (hq : 0 < q) (hac : Nat.Coprime a q)
    (halpha : alpha = rationalCenter a q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2) :
    (∑ hk ∈ (Finset.Icc 1 N).product (Finset.Icc 1 N),
      linearDistanceEnvelope (N + 1 : ℝ)
        (6 * alpha * (hk.1 * hk.2 : ℕ))) ≤
      79301 * (N + 1 : ℝ) ^ 3 / B := by
  have hT : 0 < B ^ 4 := by positivity
  have hsplit := sum_positiveProductPairs_sixMul_envelope_le_divisorThreshold
    N a q alpha beta (N + 1 : ℝ) (B ^ 4) hq hac halpha hbeta
      (by positivity) hT
  have hspacing := pow_four_sixMulSpacingEnvelopeBound_le
    B N q rho hB hB6X hB5q hqUpper hBpow hlogq
  have htail := divisorThresholdTail_pow_four_le B N hB
    hN hlogMoment
  have htail' :
      (N + 1 : ℝ) * (((N * N : ℕ) : ℝ) *
        (1 + Real.log ((N * N : ℕ) : ℝ)) ^ 7) / (B ^ 4) ^ 2 ≤
      78125 * (N + 1 : ℝ) ^ 3 / B := by
    rw [show (B ^ 4) ^ 2 = B ^ 8 by ring]
    simpa [mul_assoc] using htail
  have hcombine := add_le_add hspacing htail'
  calc
    (∑ hk ∈ (Finset.Icc 1 N).product (Finset.Icc 1 N),
      linearDistanceEnvelope (N + 1 : ℝ)
        (6 * alpha * (hk.1 * hk.2 : ℕ))) ≤
      B ^ 4 * sixMulSpacingEnvelopeBound N q (N + 1 : ℝ) +
        (N + 1 : ℝ) * (((N * N : ℕ) : ℝ) *
          (1 + Real.log ((N * N : ℕ) : ℝ)) ^ 7) / (B ^ 4) ^ 2 := hsplit
    _ ≤ 1176 * (N + 1 : ℝ) ^ 3 / B +
        78125 * (N + 1 : ℝ) ^ 3 / B := hcombine
    _ = 79301 * (N + 1 : ℝ) ^ 3 / B := by ring

/-- The two logarithm hypotheses used by the scaled spacing envelope follow
from Hua's coarse size range `q ≤ (P+2)^3` and the quotient progression
coordinate bound `M ≤ P`. The floor-log parameter is taken at the original
scale `P`, not at the shorter progression length. -/
theorem source_logarithm_bounds_of_size_ranges
    (P M q : ℕ) (hM : M ≤ P) (hqpos : 0 < q)
    (hq : q ≤ (P + 2) ^ 3)
    (hB : 3 ≤ Nat.floor (Real.log ((P : ℝ) + 2))) :
    Real.log (q : ℝ) ≤ 4 * (Nat.floor (Real.log ((P : ℝ) + 2)) : ℝ) ∧
      1 + Real.log (((M + 1) * (M + 1) : ℕ) : ℝ) ≤
        5 * (Nat.floor (Real.log ((P : ℝ) + 2)) : ℝ) := by
  let B : ℕ := Nat.floor (Real.log ((P : ℝ) + 2))
  let L : ℝ := Real.log ((P : ℝ) + 2)
  have hLpos : 0 < L := by
    dsimp [L]
    apply Real.log_pos
    have harg : (1 : ℝ) < (P : ℝ) + 2 := by
      exact_mod_cast (show 1 < P + 2 by omega)
    exact harg
  have hBcast : (B : ℝ) ≤ L := by
    dsimp [B, L]
    exact Nat.floor_le hLpos.le
  have hLlt : L < (B : ℝ) + 1 := by
    dsimp [B, L]
    exact_mod_cast Nat.lt_floor_add_one (Real.log ((P : ℝ) + 2))
  have hBcastLower : (3 : ℝ) ≤ (B : ℝ) := by
    dsimp [B]
    exact_mod_cast hB
  have hPpos : (0 : ℝ) < (P : ℝ) + 2 := by positivity
  have hqRealPos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
  have hqReal : (q : ℝ) ≤ (((P + 2) ^ 3 : ℕ) : ℝ) := by
    exact_mod_cast hq
  have hlogq : Real.log (q : ℝ) ≤ 3 * L := by
    calc
      Real.log (q : ℝ) ≤ Real.log ((((P + 2) ^ 3 : ℕ) : ℝ)) :=
        Real.log_le_log hqRealPos hqReal
      _ = 3 * L := by
        simp [L, Nat.cast_pow, Nat.cast_add, Real.log_pow]
  have hMadd : M + 1 ≤ P + 2 := by omega
  have hMsquare : (M + 1) * (M + 1) ≤ (P + 2) * (P + 2) := by
    exact Nat.mul_le_mul hMadd hMadd
  have hMsquareReal :
      (((M + 1) * (M + 1) : ℕ) : ℝ) ≤
        (((P + 2) * (P + 2) : ℕ) : ℝ) := by exact_mod_cast hMsquare
  have hlogM :
      Real.log (((M + 1) * (M + 1) : ℕ) : ℝ) ≤ 2 * L := by
    calc
      Real.log (((M + 1) * (M + 1) : ℕ) : ℝ) ≤
          Real.log (((P + 2) * (P + 2) : ℕ) : ℝ) :=
        Real.log_le_log (by positivity) hMsquareReal
      _ = 2 * L := by
        dsimp [L]
        rw [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
        rw [Real.log_mul (by positivity) (by positivity)]
        ring
  constructor
  · have hscale : 3 * L ≤ 4 * (B : ℝ) := by nlinarith
    exact hlogq.trans hscale
  · have hscale : 1 + 2 * L ≤ 5 * (B : ℝ) := by nlinarith
    linarith

/-- Progression-scaled version of the logarithmic-saving pair estimate. The
error constant `K` is charged explicitly against all three denominator and
length margins; no approximation hypothesis is silently normalized away. -/
theorem sum_positiveProductPairs_sixMul_envelope_le_logSaving_of_error_constant
    (B : ℝ) (N a q K : ℕ) (alpha beta : ℝ) (rho : ℕ)
    (hB : 1 ≤ B) (hK : 1 ≤ K)
    (hK6X : (K : ℝ) * B ^ 6 ≤ (N + 1 : ℝ))
    (hK5q : (K : ℝ) * B ^ 5 ≤ (q : ℝ))
    (hqUpper : (q : ℝ) * B ^ rho ≤ (N + 1 : ℝ) ^ 3)
    (hK6pow : (K : ℝ) * B ^ 6 ≤ B ^ rho)
    (hlogq : Real.log (q : ℝ) ≤ 4 * B)
    (hlogMoment : 1 + Real.log ((N * N : ℕ) : ℝ) ≤ 5 * B)
    (hN : 0 < N)
    (hq : 0 < q) (hac : Nat.Coprime a q)
    (halpha : alpha = rationalCenter a q + beta)
    (hbeta : |beta| ≤ (K : ℝ) / (q : ℝ) ^ 2) :
    (∑ hk ∈ (Finset.Icc 1 N).product (Finset.Icc 1 N),
      linearDistanceEnvelope (N + 1 : ℝ)
        (6 * alpha * (hk.1 * hk.2 : ℕ))) ≤
      79301 * (N + 1 : ℝ) ^ 3 / B := by
  have hT : 0 < B ^ 4 := by positivity
  have hsplit := sum_positiveProductPairs_sixMul_envelope_le_divisorThreshold_of_error_constant
    N a q K alpha beta (N + 1 : ℝ) (B ^ 4) hq hac halpha hbeta
      (by positivity) hT
  have hspacing := pow_four_sixMulSpacingEnvelopeBoundWithError_le
    B N q K rho hB hK hK6X hK5q hqUpper hK6pow hlogq
  have htail := divisorThresholdTail_pow_four_le B N hB hN hlogMoment
  have htail' :
      (N + 1 : ℝ) * (((N * N : ℕ) : ℝ) *
        (1 + Real.log ((N * N : ℕ) : ℝ)) ^ 7) / (B ^ 4) ^ 2 ≤
      78125 * (N + 1 : ℝ) ^ 3 / B := by
    rw [show (B ^ 4) ^ 2 = B ^ 8 by ring]
    simpa [mul_assoc] using htail
  have hcombine := add_le_add hspacing htail'
  calc
    (∑ hk ∈ (Finset.Icc 1 N).product (Finset.Icc 1 N),
      linearDistanceEnvelope (N + 1 : ℝ)
        (6 * alpha * (hk.1 * hk.2 : ℕ))) ≤
      B ^ 4 * sixMulSpacingEnvelopeBoundWithError N q
        (N + 1 : ℝ) K +
        (N + 1 : ℝ) * (((N * N : ℕ) : ℝ) *
          (1 + Real.log ((N * N : ℕ) : ℝ)) ^ 7) / (B ^ 4) ^ 2 := hsplit
    _ ≤ 1176 * (N + 1 : ℝ) ^ 3 / B +
        78125 * (N + 1 : ℝ) ^ 3 / B := hcombine
    _ = 79301 * (N + 1 : ℝ) ^ 3 / B := by ring

/-- Discharge the four scaled-spacing margins from a power bound on the
progression step. Here `K=s^3`; the lower denominator cutoff and the Hua
upper exponent are stated at the natural-power level used by the source
range adapters. -/
theorem sum_positiveProductPairs_sixMul_envelope_le_logSaving_of_progression_power_ranges
    (B M step a q rho e sigma0 : ℕ)
    (hB : 1 ≤ B) (hstep : 0 < step) (hstepBound : step ≤ B ^ e)
    (hcutoff : 3 * e + 5 ≤ sigma0)
    (hlower : B ^ sigma0 < q)
    (hlength : B ^ (3 * e + 6) ≤ M + 2)
    (hupper : q * B ^ rho ≤ (M + 2) ^ 3)
    (hrho : 3 * e + 6 ≤ rho)
    (hlogq : Real.log (q : ℝ) ≤ 4 * B)
    (hlogMoment : 1 + Real.log (((M + 1) * (M + 1) : ℕ) : ℝ) ≤ 5 * B)
    (hac : Nat.Coprime a q) :
    (∑ hk ∈ (Finset.Icc 1 (M + 1)).product (Finset.Icc 1 (M + 1)),
      linearDistanceEnvelope (M + 2 : ℝ)
        (6 * rationalCenter a q * (hk.1 * hk.2 : ℕ))) ≤
      79301 * (M + 2 : ℝ) ^ 3 / B := by
  let K := step ^ 3
  have hKpow : K ≤ B ^ (3 * e) := by
    dsimp [K]
    calc
      step ^ 3 ≤ (B ^ e) ^ 3 := by gcongr
      _ = B ^ (3 * e) := by
        rw [← pow_mul]
        congr 1
        omega
  have hKone : 1 ≤ K := by
    dsimp [K]
    have hs : 1 ≤ step := Nat.succ_le_of_lt hstep
    calc
      1 = (1 : ℕ) ^ 3 := by norm_num
      _ ≤ step ^ 3 := by gcongr
  have hK5qNat : K * B ^ 5 ≤ q := by
    have hprod : K * B ^ 5 ≤ B ^ (3 * e + 5) := by
      calc
        K * B ^ 5 ≤ B ^ (3 * e) * B ^ 5 := Nat.mul_le_mul_right _ hKpow
        _ = B ^ (3 * e + 5) := by rw [← pow_add]
    have hpow : B ^ (3 * e + 5) ≤ B ^ sigma0 := by gcongr
    exact hprod.trans (hpow.trans hlower.le)
  have hK6Nat : K * B ^ 6 ≤ M + 2 := by
    have hprod : K * B ^ 6 ≤ B ^ (3 * e + 6) := by
      calc
        K * B ^ 6 ≤ B ^ (3 * e) * B ^ 6 := Nat.mul_le_mul_right _ hKpow
        _ = B ^ (3 * e + 6) := by rw [← pow_add]
    exact hprod.trans hlength
  have hK6rhoNat : K * B ^ 6 ≤ B ^ rho := by
    have hprod : K * B ^ 6 ≤ B ^ (3 * e + 6) := by
      calc
        K * B ^ 6 ≤ B ^ (3 * e) * B ^ 6 := Nat.mul_le_mul_right _ hKpow
        _ = B ^ (3 * e + 6) := by rw [← pow_add]
    exact hprod.trans (by gcongr)
  have hK6X : (K : ℝ) * (B : ℝ) ^ 6 ≤ (M + 2 : ℝ) := by exact_mod_cast hK6Nat
  have hK6XPair : (K : ℝ) * (B : ℝ) ^ 6 ≤ ((M + 1 : ℕ) : ℝ) + 1 := by
    calc
      (K : ℝ) * (B : ℝ) ^ 6 ≤ (M + 2 : ℝ) := hK6X
      _ = ((M + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
  have hK5q : (K : ℝ) * (B : ℝ) ^ 5 ≤ (q : ℝ) := by
    exact_mod_cast hK5qNat
  have hUpperPairNat : q * B ^ rho ≤ ((M + 1) + 1) ^ 3 := by
    simpa using hupper
  have hUpperPair : (q : ℝ) * (B : ℝ) ^ rho ≤
      (((M + 1 : ℕ) : ℝ) + 1) ^ 3 := by
    exact_mod_cast hUpperPairNat
  have hK6pow : (K : ℝ) * (B : ℝ) ^ 6 ≤ (B : ℝ) ^ rho := by
    exact_mod_cast hK6rhoNat
  have hq : 0 < q := by
    have hq' : 0 < (q : ℝ) := by
      have hBpos : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
      have hBpow : (1 : ℝ) ≤ (B : ℝ) ^ sigma0 := one_le_pow₀ hBpos
      have hlow' : (B : ℝ) ^ sigma0 < (q : ℝ) := by exact_mod_cast hlower
      linarith
    exact_mod_cast hq'
  have hBreal : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hpair := sum_positiveProductPairs_sixMul_envelope_le_logSaving_of_error_constant
    (B : ℝ) (M + 1) a q K (rationalCenter a q) 0 rho hBreal hKone
    hK6XPair hK5q hUpperPair hK6pow
    hlogq hlogMoment (by omega) hq hac (by simp) (by simp; positivity)
  have hcast : ((M : ℝ) + 1 + 1) = (M : ℝ) + 2 := by ring
  simpa [hcast] using hpair

/-- Source-size specialization of the progression-scaled pair-saving bound.
The two logarithmic hypotheses are discharged from `q≤(P+2)^3` and the
quotient-coordinate bound `M≤P`, so they are no longer independent inputs. -/
theorem sum_positiveProductPairs_sixMul_envelope_le_logSaving_of_progression_power_ranges_source_size
    (P M step a q rho e sigma0 : ℕ)
    (hB : 3 ≤ Nat.floor (Real.log ((P : ℝ) + 2)))
    (hM : M ≤ P) (hstep : 0 < step)
    (hstepBound : step ≤ (Nat.floor (Real.log ((P : ℝ) + 2))) ^ e)
    (hcutoff : 3 * e + 5 ≤ sigma0)
    (hlower : (Nat.floor (Real.log ((P : ℝ) + 2))) ^ sigma0 < q)
    (hlength : (Nat.floor (Real.log ((P : ℝ) + 2))) ^ (3 * e + 6) ≤ M + 2)
    (hupper : q * (Nat.floor (Real.log ((P : ℝ) + 2))) ^ rho ≤ (M + 2) ^ 3)
    (hrho : 3 * e + 6 ≤ rho) (hac : Nat.Coprime a q) :
    (∑ hk ∈ (Finset.Icc 1 (M + 1)).product (Finset.Icc 1 (M + 1)),
      linearDistanceEnvelope (M + 2 : ℝ)
        (6 * rationalCenter a q * (hk.1 * hk.2 : ℕ))) ≤
      79301 * (M + 2 : ℝ) ^ 3 /
        (Nat.floor (Real.log ((P : ℝ) + 2)) : ℝ) := by
  let B := Nat.floor (Real.log ((P : ℝ) + 2))
  have hBpos : 1 ≤ B := by dsimp [B]; omega
  have hpowpos : 1 ≤ B ^ rho := one_le_pow₀ (by exact_mod_cast hBpos)
  have hqleM : q ≤ (M + 2) ^ 3 := by
    calc
      q = q * 1 := by simp
      _ ≤ q * B ^ rho := Nat.mul_le_mul_left q hpowpos
      _ ≤ (M + 2) ^ 3 := by simpa [B] using hupper
  have hqleP : q ≤ (P + 2) ^ 3 := by
    exact hqleM.trans (Nat.pow_le_pow_left (by omega) 3)
  have hqpos : 0 < q := by
    have hqreal : (0 : ℝ) < (q : ℝ) := by
      have hpow : (1 : ℝ) ≤ (B : ℝ) ^ sigma0 := by
        exact one_le_pow₀ (by exact_mod_cast hBpos)
      have hlowerReal : (B : ℝ) ^ sigma0 < (q : ℝ) := by
        exact_mod_cast (by simpa [B] using hlower)
      linarith
    exact_mod_cast hqreal
  have hlogs := source_logarithm_bounds_of_size_ranges P M q hM hqpos hqleP hB
  exact sum_positiveProductPairs_sixMul_envelope_le_logSaving_of_progression_power_ranges
    B M step a q rho e sigma0 hBpos hstep hstepBound hcutoff hlower hlength hupper
    hrho hlogs.1 hlogs.2 hac

/-- Arbitrary fixed powers of logarithmic saving are available when the
source cutoff, progression length, and denominator window carry the matching
exponent margins. The proof reuses the fixed `B^-1` estimate at the larger
scale `C=B^delta`; the Hua budget supplies enough room to round down the
upper-window exponent at that scale. -/
theorem sum_positiveProductPairs_sixMul_envelope_le_logSaving_of_progression_power_ranges_source_size_order
    (P M step a q rho e sigma0 delta : ℕ)
    (hB : 3 ≤ Nat.floor (Real.log ((P : ℝ) + 2)))
    (hM : M ≤ P) (hstep : 0 < step)
    (hstepBound : step ≤ (Nat.floor (Real.log ((P : ℝ) + 2))) ^ e)
    (hdelta : 1 ≤ delta)
    (hcutoff : 3 * e + 5 * delta ≤ sigma0)
    (hlower : (Nat.floor (Real.log ((P : ℝ) + 2))) ^ sigma0 < q)
    (hlength : (Nat.floor (Real.log ((P : ℝ) + 2))) ^ (3 * e + 6 * delta) ≤ M + 2)
    (hupper : q * (Nat.floor (Real.log ((P : ℝ) + 2))) ^ rho ≤ (M + 2) ^ 3)
    (hrho : 3 * e + 7 * delta ≤ rho) (hac : Nat.Coprime a q) :
    (∑ hk ∈ (Finset.Icc 1 (M + 1)).product (Finset.Icc 1 (M + 1)),
      linearDistanceEnvelope (M + 2 : ℝ)
        (6 * rationalCenter a q * (hk.1 * hk.2 : ℕ))) ≤
      79301 * (M + 2 : ℝ) ^ 3 /
        ((Nat.floor (Real.log ((P : ℝ) + 2)) : ℝ) ^ delta) := by
  let B := Nat.floor (Real.log ((P : ℝ) + 2))
  let C : ℝ := (B : ℝ) ^ delta
  let R := rho / delta
  have hBpos : 1 ≤ B := by dsimp [B]; omega
  have hBreal : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hBpos
  have hBpow : B ≤ B ^ delta := by
    calc
      B = B ^ 1 := by simp
      _ ≤ B ^ delta := by gcongr
  have hBscale : (B : ℝ) ≤ C := by
    dsimp [C]
    exact_mod_cast hBpow
  have hCpos : 1 ≤ C := by
    dsimp [C]
    exact one_le_pow₀ hBreal
  have hdeltaPos : 0 < delta := by omega
  have hdivDecomp : delta * (rho / delta) + rho % delta = rho :=
    Nat.div_add_mod rho delta
  have hdivRem : rho % delta < delta := Nat.mod_lt _ hdeltaPos
  have hdivMargin : 3 * e + 6 * delta ≤ delta * R := by
    dsimp [R]
    omega
  have hRle : delta * R ≤ rho := by
    dsimp [R]
    exact Nat.mul_div_le rho delta
  have hKone : 1 ≤ step ^ 3 := by
    have hs : 1 ≤ step := Nat.succ_le_of_lt hstep
    calc
      1 = (1 : ℕ) ^ 3 := by norm_num
      _ ≤ step ^ 3 := by gcongr
  have hKpow : step ^ 3 ≤ B ^ (3 * e) := by
    calc
      step ^ 3 ≤ (B ^ e) ^ 3 := by gcongr
      _ = B ^ (3 * e) := by rw [← pow_mul]; congr 1; omega
  have hK6Nat : step ^ 3 * B ^ (6 * delta) ≤ M + 2 := by
    calc
      step ^ 3 * B ^ (6 * delta) ≤ B ^ (3 * e) * B ^ (6 * delta) :=
        Nat.mul_le_mul_right _ hKpow
      _ = B ^ (3 * e + 6 * delta) := by rw [← pow_add]
      _ ≤ M + 2 := by gcongr
  have hK5Nat : step ^ 3 * B ^ (5 * delta) ≤ q := by
    have hprod : step ^ 3 * B ^ (5 * delta) ≤ B ^ (3 * e + 5 * delta) := by
      calc
        step ^ 3 * B ^ (5 * delta) ≤ B ^ (3 * e) * B ^ (5 * delta) :=
          Nat.mul_le_mul_right _ hKpow
        _ = B ^ (3 * e + 5 * delta) := by rw [← pow_add]
    have hcut : B ^ (3 * e + 5 * delta) ≤ B ^ sigma0 := by gcongr
    exact hprod.trans (hcut.trans hlower.le)
  have hK6RhoNat : step ^ 3 * B ^ (6 * delta) ≤ B ^ (delta * R) := by
    have hprod : step ^ 3 * B ^ (6 * delta) ≤ B ^ (3 * e + 6 * delta) := by
      calc
        step ^ 3 * B ^ (6 * delta) ≤ B ^ (3 * e) * B ^ (6 * delta) :=
          Nat.mul_le_mul_right _ hKpow
        _ = B ^ (3 * e + 6 * delta) := by rw [← pow_add]
    exact hprod.trans (by gcongr)
  have hUpperNat : q * B ^ (delta * R) ≤ (M + 2) ^ 3 := by
    calc
      q * B ^ (delta * R) ≤ q * B ^ rho := Nat.mul_le_mul_left q (by gcongr)
      _ ≤ (M + 2) ^ 3 := hupper
  have hqleM : q ≤ (M + 2) ^ 3 := by
    have hpowpos : 1 ≤ B ^ rho := one_le_pow₀ (by omega)
    calc
      q = q * 1 := by simp
      _ ≤ q * B ^ rho := Nat.mul_le_mul_left q hpowpos
      _ ≤ (M + 2) ^ 3 := hupper
  have hqleP : q ≤ (P + 2) ^ 3 := by
    exact hqleM.trans (Nat.pow_le_pow_left (by omega) 3)
  have hq : 0 < q := by
    have hqreal : (0 : ℝ) < (q : ℝ) := by
      have hpow : (1 : ℝ) ≤ (B : ℝ) ^ sigma0 := one_le_pow₀ hBreal
      have hlowerReal : (B : ℝ) ^ sigma0 < (q : ℝ) := by
        exact_mod_cast (by simpa [B] using hlower)
      linarith
    exact_mod_cast hqreal
  have hlogs := source_logarithm_bounds_of_size_ranges P M q hM hq hqleP hB
  have hlogq : Real.log (q : ℝ) ≤ 4 * C := by
    calc
      Real.log (q : ℝ) ≤ 4 * (B : ℝ) := by simpa [B] using hlogs.1
      _ ≤ 4 * C := by nlinarith [hBscale]
  have hlogMoment :
      1 + Real.log (((M + 1) * (M + 1) : ℕ) : ℝ) ≤ 5 * C := by
    calc
      1 + Real.log (((M + 1) * (M + 1) : ℕ) : ℝ) ≤ 5 * (B : ℝ) := by
        simpa [B] using hlogs.2
      _ ≤ 5 * C := by nlinarith [hBscale]
  have hK6XReal :
      ((step ^ 3 : ℕ) : ℝ) * ((B : ℝ) ^ delta) ^ 6 ≤ (M + 2 : ℝ) := by
    have hnat : step ^ 3 * B ^ (6 * delta) ≤ M + 2 := hK6Nat
    exact_mod_cast (by simpa [pow_mul, Nat.cast_pow, Nat.mul_comm] using hnat)
  have hK5qReal :
      ((step ^ 3 : ℕ) : ℝ) * ((B : ℝ) ^ delta) ^ 5 ≤ (q : ℝ) := by
    have hnat : step ^ 3 * B ^ (5 * delta) ≤ q := hK5Nat
    exact_mod_cast (by simpa [pow_mul, Nat.cast_pow, Nat.mul_comm] using hnat)
  have hUpperReal :
      (q : ℝ) * ((B : ℝ) ^ delta) ^ R ≤ (M + 2 : ℝ) ^ 3 := by
    have hnat : q * B ^ (delta * R) ≤ (M + 2) ^ 3 := hUpperNat
    exact_mod_cast (by simpa [pow_mul] using hnat)
  have hK6RhoReal :
      ((step ^ 3 : ℕ) : ℝ) * ((B : ℝ) ^ delta) ^ 6 ≤ ((B : ℝ) ^ delta) ^ R := by
    have hnat : step ^ 3 * B ^ (6 * delta) ≤ B ^ (delta * R) := hK6RhoNat
    exact_mod_cast (by simpa [pow_mul, Nat.cast_pow, Nat.mul_comm] using hnat)
  have hK6XPair :
      ((step ^ 3 : ℕ) : ℝ) * ((B : ℝ) ^ delta) ^ 6 ≤ ((M + 1 : ℕ) : ℝ) + 1 := by
    calc
      ((step ^ 3 : ℕ) : ℝ) * ((B : ℝ) ^ delta) ^ 6 ≤ (M + 2 : ℝ) := hK6XReal
      _ = ((M + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
  have hUpperPair :
      (q : ℝ) * ((B : ℝ) ^ delta) ^ R ≤ (((M + 1 : ℕ) : ℝ) + 1) ^ 3 := by
    calc
      (q : ℝ) * ((B : ℝ) ^ delta) ^ R ≤ (M + 2 : ℝ) ^ 3 := hUpperReal
      _ = (((M + 1 : ℕ) : ℝ) + 1) ^ 3 := by
        push_cast
        ring
  have hpair := sum_positiveProductPairs_sixMul_envelope_le_logSaving_of_error_constant
    C (M + 1) a q (step ^ 3) (rationalCenter a q) 0 R hCpos hKone
    hK6XPair hK5qReal hUpperPair hK6RhoReal hlogq hlogMoment
    (by omega) hq hac (by simp) (by simp; positivity)
  have hcast : ((M : ℝ) + 1 + 1) = (M : ℝ) + 2 := by ring
  simpa [B, C, hcast] using hpair

/-- The complete positive second-difference sum is bounded by the
divisor-weighted arbitrary-range spacing estimate. -/
theorem exists_uniform_norm_cubicSecondDifferenceTripleSum_le_spacing
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (alpha : ℝ) (N a q : ℕ) (beta : ℝ),
      (hq : 0 < q) → (hac : Nat.Coprime a q) →
      (halpha : alpha = rationalCenter a q + beta) →
      (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2) →
      ‖cubicSecondDifferenceTripleSum alpha N‖ ≤
        C * Real.rpow ((N * N : ℕ) : ℝ) ε *
          sixMulSpacingEnvelopeBound N q (N + 1 : ℝ) := by
  obtain ⟨C, hC, hpair⟩ :=
    exists_uniform_sum_positiveProductPairs_sixMul_envelope_le hε
  refine ⟨C, hC, fun alpha N a q beta hq hac halpha hbeta => ?_⟩
  have hpair' := hpair N a q alpha beta (N + 1 : ℝ)
    hq hac halpha hbeta (by positivity)
  exact (norm_cubicSecondDifferenceTripleSum_le_pairEnvelope alpha N).trans hpair'

/-- Pointwise specialization of the uniform second-difference spacing
estimate. -/
theorem exists_norm_cubicSecondDifferenceTripleSum_le_spacing
    (alpha : ℝ) (N a q : ℕ) (beta : ℝ)
    (hq : 0 < q) (hac : Nat.Coprime a q)
    (halpha : alpha = rationalCenter a q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ‖cubicSecondDifferenceTripleSum alpha N‖ ≤
        C * Real.rpow ((N * N : ℕ) : ℝ) ε *
          sixMulSpacingEnvelopeBound N q (N + 1 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_norm_cubicSecondDifferenceTripleSum_le_spacing hε
  exact ⟨C, hC, hbound alpha N a q beta hq hac halpha hbeta⟩

/-- Feed the divisor-weighted spacing estimate into the exact fourth-power
cubic differencing inequality already proved for `x^3-x`. -/
theorem exists_norm_cubicUnweightedExpSum_four_le_spacing
    (alpha : ℝ) (N a q : ℕ) (beta : ℝ)
    (hq : 0 < q) (hac : Nat.Coprime a q)
    (halpha : alpha = rationalCenter a q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ‖cubicUnweightedExpSum alpha N‖ ^ 4 ≤
        6 * (N + 1 : ℝ) ^ 3 +
          16 * (N + 1 : ℝ) *
            (C * Real.rpow ((N * N : ℕ) : ℝ) ε *
              sixMulSpacingEnvelopeBound N q (N + 1 : ℝ)) := by
  obtain ⟨C, hC, hD⟩ :=
    exists_norm_cubicSecondDifferenceTripleSum_le_spacing
      alpha N a q beta hq hac halpha hbeta hε
  refine ⟨C, hC, ?_⟩
  have hbase := norm_cubicUnweightedExpSum_four_le_secondDifference alpha N
  calc
    ‖cubicUnweightedExpSum alpha N‖ ^ 4 ≤
        6 * (N + 1 : ℝ) ^ 3 +
          16 * (N + 1 : ℝ) * ‖cubicSecondDifferenceTripleSum alpha N‖ := hbase
    _ ≤ 6 * (N + 1 : ℝ) ^ 3 +
          16 * (N + 1 : ℝ) *
            (C * Real.rpow ((N * N : ℕ) : ℝ) ε *
              sixMulSpacingEnvelopeBound N q (N + 1 : ℝ)) := by
      gcongr

/-- The same fourth-power estimate with the reduced denominator replaced
by `q`, leaving only elementary polynomial and logarithmic factors. -/
theorem exists_norm_cubicUnweightedExpSum_four_le_coarse
    (alpha : ℝ) (N a q : ℕ) (beta : ℝ)
    (hq : 0 < q) (hac : Nat.Coprime a q)
    (halpha : alpha = rationalCenter a q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ‖cubicUnweightedExpSum alpha N‖ ^ 4 ≤
        6 * (N + 1 : ℝ) ^ 3 +
          16 * (N + 1 : ℝ) *
            (C * Real.rpow ((N * N : ℕ) : ℝ) ε *
              coarseSpacingEnvelopeBound N q (N + 1 : ℝ)) := by
  obtain ⟨C, hC, hweyl⟩ :=
    exists_norm_cubicUnweightedExpSum_four_le_spacing
      alpha N a q beta hq hac halpha hbeta hε
  refine ⟨C, hC, ?_⟩
  have hcoarse := sixMulSpacingEnvelopeBound_le_coarse N q
    (N + 1 : ℝ) hq (by positivity)
  calc
    ‖cubicUnweightedExpSum alpha N‖ ^ 4 ≤
        6 * (N + 1 : ℝ) ^ 3 +
          16 * (N + 1 : ℝ) *
            (C * Real.rpow ((N * N : ℕ) : ℝ) ε *
              sixMulSpacingEnvelopeBound N q (N + 1 : ℝ)) := hweyl
    _ ≤ 6 * (N + 1 : ℝ) ^ 3 +
          16 * (N + 1 : ℝ) *
            (C * Real.rpow ((N * N : ℕ) : ℝ) ε *
              coarseSpacingEnvelopeBound N q (N + 1 : ℝ)) := by
      have hscale : 0 ≤ C * Real.rpow ((N * N : ℕ) : ℝ) ε :=
        mul_nonneg hC.le (Real.rpow_nonneg (by positivity) _)
      have hinner := mul_le_mul_of_nonneg_left hcoarse hscale
      have houter := mul_le_mul_of_nonneg_left hinner (by positivity :
        0 ≤ 16 * (N + 1 : ℝ))
      unfold coarseSpacingEnvelopeBound
      nlinarith

/- The uniform variants below expose one absolute constant before the
frequency, length, and rational-approximation data. -/
theorem exists_uniform_norm_cubicUnweightedExpSum_four_le_spacing
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (alpha : ℝ) (N a q : ℕ) (beta : ℝ),
      (hq : 0 < q) → (hac : Nat.Coprime a q) →
      (halpha : alpha = rationalCenter a q + beta) →
      (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2) →
      ‖cubicUnweightedExpSum alpha N‖ ^ 4 ≤
        6 * (N + 1 : ℝ) ^ 3 +
          16 * (N + 1 : ℝ) *
            (C * Real.rpow ((N * N : ℕ) : ℝ) ε *
              sixMulSpacingEnvelopeBound N q (N + 1 : ℝ)) := by
  obtain ⟨C, hC, hD⟩ :=
    exists_uniform_norm_cubicSecondDifferenceTripleSum_le_spacing hε
  refine ⟨C, hC, fun alpha N a q beta hq hac halpha hbeta => ?_⟩
  have hbase := norm_cubicUnweightedExpSum_four_le_secondDifference alpha N
  have hD' := hD alpha N a q beta hq hac halpha hbeta
  calc
    ‖cubicUnweightedExpSum alpha N‖ ^ 4 ≤
        6 * (N + 1 : ℝ) ^ 3 +
          16 * (N + 1 : ℝ) * ‖cubicSecondDifferenceTripleSum alpha N‖ := hbase
    _ ≤ 6 * (N + 1 : ℝ) ^ 3 +
          16 * (N + 1 : ℝ) *
            (C * Real.rpow ((N * N : ℕ) : ℝ) ε *
              sixMulSpacingEnvelopeBound N q (N + 1 : ℝ)) := by
      gcongr

/-- Uniform coarse-denominator fourth-power Weyl envelope. -/
theorem exists_uniform_norm_cubicUnweightedExpSum_four_le_coarse
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (alpha : ℝ) (N a q : ℕ) (beta : ℝ),
      (hq : 0 < q) → (hac : Nat.Coprime a q) →
      (halpha : alpha = rationalCenter a q + beta) →
      (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2) →
      ‖cubicUnweightedExpSum alpha N‖ ^ 4 ≤
        6 * (N + 1 : ℝ) ^ 3 +
          16 * (N + 1 : ℝ) *
            (C * Real.rpow ((N * N : ℕ) : ℝ) ε *
              coarseSpacingEnvelopeBound N q (N + 1 : ℝ)) := by
  obtain ⟨C, hC, hW⟩ :=
    exists_uniform_norm_cubicUnweightedExpSum_four_le_spacing hε
  refine ⟨C, hC, fun alpha N a q beta hq hac halpha hbeta => ?_⟩
  have hW' := hW alpha N a q beta hq hac halpha hbeta
  have hcoarse := sixMulSpacingEnvelopeBound_le_coarse N q
    (N + 1 : ℝ) hq (by positivity)
  have hscale : 0 ≤ C * Real.rpow ((N * N : ℕ) : ℝ) ε :=
    mul_nonneg hC.le (Real.rpow_nonneg (by positivity) _)
  calc
    ‖cubicUnweightedExpSum alpha N‖ ^ 4 ≤
        6 * (N + 1 : ℝ) ^ 3 +
          16 * (N + 1 : ℝ) *
            (C * Real.rpow ((N * N : ℕ) : ℝ) ε *
              sixMulSpacingEnvelopeBound N q (N + 1 : ℝ)) := hW'
    _ ≤ 6 * (N + 1 : ℝ) ^ 3 +
          16 * (N + 1 : ℝ) *
            (C * Real.rpow ((N * N : ℕ) : ℝ) ε *
              coarseSpacingEnvelopeBound N q (N + 1 : ℝ)) := by
      have := mul_le_mul_of_nonneg_left hcoarse hscale
      unfold coarseSpacingEnvelopeBound at this ⊢
      nlinarith

set_option maxHeartbeats 800000 in
/-- Simplify the explicit fourth-power bound to the power-shaped ordinary
Weyl estimate at the loss required for the auxiliary 32nd moment. -/
theorem exists_norm_cubicUnweightedExpSum_four_le_weyl
    : ∃ K : ℝ, 0 < K ∧ ∀ (alpha : ℝ) (N a q : ℕ) (beta : ℝ),
      (hN : 8 ≤ N) → (hq : 0 < q) → (hqmax : q ≤ 3 * N ^ 3) →
      (hac : Nat.Coprime a q) →
      (halpha : alpha = rationalCenter a q + beta) →
      (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2) →
      ‖cubicUnweightedExpSum alpha N‖ ^ 4 ≤
        K * Real.rpow (N : ℝ) (4 + 1 / 12 : ℝ) *
          (1 / (q : ℝ) + 1 / (N : ℝ) +
            (q : ℝ) / (N : ℝ) ^ 3) := by
  obtain ⟨C, hC, hfour⟩ :=
    exists_uniform_norm_cubicUnweightedExpSum_four_le_coarse
      (ε := (1 / 1000 : ℝ)) (by norm_num)
  refine ⟨48 + 16 * C * 120000, by positivity, ?_⟩
  intro alpha N a q beta hN hq hqmax hac halpha hbeta
  have hNpos : 0 < N := by omega
  have hNrealpos : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hNrealone : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast (Nat.succ_le_of_lt hq)
  let x : ℝ := N
  let y : ℝ := q
  have hxpos : 0 < x := by dsimp [x]; exact hNrealpos
  have hxone : 1 ≤ x := by dsimp [x]; exact hNrealone
  have hypos : 0 < y := by dsimp [y]; exact hqpos
  have hyone : 1 ≤ y := by dsimp [y]; exact hqone
  have hyupper : y ≤ 3 * x ^ 3 := by
    dsimp [x, y]
    exact_mod_cast hqmax
  have hyquarter : Real.rpow y (1 / 100 : ℝ) ≤
      3 * Real.rpow x (3 / 100 : ℝ) := by
    have hpow := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ y)
      hyupper (by norm_num : (0 : ℝ) ≤ (1 / 100 : ℝ))
    have hthree : Real.rpow (3 : ℝ) (1 / 100 : ℝ) ≤ 3 := by
      calc
        Real.rpow 3 (1 / 100 : ℝ) ≤ Real.rpow 3 (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 3 := by norm_num
    calc
      Real.rpow y (1 / 100 : ℝ) ≤ Real.rpow (3 * x ^ 3) (1 / 100 : ℝ) := hpow
      _ = Real.rpow 3 (1 / 100 : ℝ) * Real.rpow (x ^ 3) (1 / 100 : ℝ) := by
        exact Real.mul_rpow (by norm_num) (by positivity)
      _ = Real.rpow 3 (1 / 100 : ℝ) * Real.rpow x (3 / 100 : ℝ) := by
        have hpow3 := Real.rpow_natCast_mul (by positivity : (0 : ℝ) ≤ x)
          3 (1 / 100 : ℝ)
        norm_num at hpow3
        exact congrArg (fun z : ℝ => Real.rpow 3 (1 / 100 : ℝ) * z) hpow3.symm
      _ ≤ 3 * Real.rpow x (3 / 100 : ℝ) := by
        exact mul_le_mul_of_nonneg_right hthree (Real.rpow_nonneg hxpos.le _)
  have hNsmallpow : 1 ≤ Real.rpow x (3 / 100 : ℝ) := by
    calc
      1 = Real.rpow 1 (3 / 100 : ℝ) := by norm_num
      _ ≤ Real.rpow x (3 / 100 : ℝ) :=
        Real.rpow_le_rpow (by norm_num) hxone (by norm_num)
  have hlog : 1 + Real.log y ≤ 303 * Real.rpow x (3 / 100 : ℝ) := by
    have hlogy := log_nat_le_hundred_rpow (q := q) hq
    calc
      1 + Real.log y ≤ 1 + 100 * Real.rpow y (1 / 100 : ℝ) := by
        have hlogy' : Real.log y ≤ 100 * Real.rpow y (1 / 100 : ℝ) := by
          simpa [y] using hlogy
        linarith
      _ ≤ 1 + 300 * Real.rpow x (3 / 100 : ℝ) := by
        have hlogpow := mul_le_mul_of_nonneg_left hyquarter
          (by norm_num : (0 : ℝ) ≤ 100)
        nlinarith [hlogpow]
      _ ≤ 303 * Real.rpow x (3 / 100 : ℝ) := by linarith [hNsmallpow]
  have hdivisor :
      Real.rpow ((N * N : ℕ) : ℝ) (1 / 1000 : ℝ) =
        Real.rpow x (1 / 500 : ℝ) := by
    dsimp [x]
    rw [Nat.cast_mul]
    have hsq : (N : ℝ) * (N : ℝ) = (N : ℝ) ^ 2 := by ring
    rw [hsq]
    rw [← Real.rpow_natCast_mul (by positivity : (0 : ℝ) ≤ (N : ℝ)) 2
      (1 / 1000 : ℝ)]
    congr 1
    norm_num
  let d : ℝ := Real.rpow x (1 / 500 : ℝ)
  let l : ℝ := Real.rpow x (3 / 100 : ℝ)
  let U : ℝ := Real.rpow x (1 / 12 : ℝ)
  have hdnonneg : 0 ≤ d := by dsimp [d]; exact Real.rpow_nonneg hxpos.le _
  have hlnonneg : 0 ≤ l := by dsimp [l]; exact Real.rpow_nonneg hxpos.le _
  have hUnonneg : 0 ≤ U := by dsimp [U]; exact Real.rpow_nonneg hxpos.le _
  have hdleU : d ≤ U := by
    dsimp [d, U]
    apply Real.rpow_le_rpow_of_exponent_le hxone
    norm_num
  have hdlleU : d * l ≤ U := by
    dsimp [d, l, U]
    rw [← Real.rpow_add hxpos]
    apply Real.rpow_le_rpow_of_exponent_le hxone
    norm_num
  have hN2leN3 : x ^ 2 ≤ x ^ 3 := by nlinarith [sq_nonneg (x - 1)]
  have hfour := hfour alpha N a q beta
    hq hac halpha hbeta
  have hbase :
      6 * (N + 1 : ℝ) ^ 3 ≤ 48 * U * x ^ 3 := by
    have hNplus : (N + 1 : ℝ) ≤ 2 * x := by dsimp [x]; nlinarith
    have hUone : 1 ≤ U := by
      dsimp [U]
      calc
        1 = Real.rpow 1 (1 / 12 : ℝ) := by norm_num
        _ ≤ Real.rpow x (1 / 12 : ℝ) :=
          Real.rpow_le_rpow (by norm_num) hxone (by norm_num)
    calc
      6 * (N + 1 : ℝ) ^ 3 ≤ 6 * (2 * x) ^ 3 := by gcongr
      _ = 48 * x ^ 3 := by ring
      _ ≤ 48 * U * x ^ 3 := by
        calc
          48 * x ^ 3 = (48 * x ^ 3) * 1 := by ring
          _ ≤ (48 * x ^ 3) * U := mul_le_mul_of_nonneg_left hUone (by positivity)
          _ = 48 * U * x ^ 3 := by ring
  have hEnvelope :
      (N + 1 : ℝ) * d * coarseSpacingEnvelopeBound N q (N + 1 : ℝ) ≤
        120000 * U * (x ^ 4 / y + x ^ 3 + y * x) := by
    have hNplus : (N + 1 : ℝ) ≤ 2 * x := by dsimp [x]; nlinarith
    have hinside : (N + 1 : ℝ) + y * (1 + Real.log y) ≤
        2 * x + 303 * y * l := by
      have hlog' : 1 + Real.log y ≤ 303 * l := hlog
      calc
        _ ≤ 2 * x + y * (303 * l) :=
          add_le_add hNplus (mul_le_mul_of_nonneg_left hlog' (by positivity))
        _ = 2 * x + 303 * y * l := by ring
    have hprod :
        (2 * x) * d * (6 * x ^ 2 / y + 1) * (2 * x + 303 * y * l) =
          24 * (d * x ^ 4 / y) + 3636 * (d * x ^ 3 * l) +
            4 * (d * x ^ 2) + 606 * (d * y * x * l) := by
      field_simp [hypos.ne']
      ring
    have hpow1 : d * x ^ 4 / y ≤ U * (x ^ 4 / y) := by
      have := mul_le_mul_of_nonneg_right hdleU (by positivity : 0 ≤ x ^ 4 / y)
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
    have hpow2 : d * x ^ 3 * l ≤ U * x ^ 3 := by
      calc
        d * x ^ 3 * l = (d * l) * x ^ 3 := by ring
        _ ≤ U * x ^ 3 := mul_le_mul_of_nonneg_right hdlleU (by positivity)
    have hpow3 : d * x ^ 2 ≤ U * x ^ 3 := by
      calc
        d * x ^ 2 ≤ U * x ^ 2 :=
          mul_le_mul_of_nonneg_right hdleU (by positivity)
        _ ≤ U * x ^ 3 := by gcongr
    have hpow4 : d * y * x * l ≤ U * (y * x) := by
      calc
        d * y * x * l = (d * l) * (y * x) := by ring
        _ ≤ U * (y * x) := mul_le_mul_of_nonneg_right hdlleU (by positivity)
    unfold coarseSpacingEnvelopeBound
    have hcombine :
        28 * ((N + 1 : ℝ) * d) *
            (6 * x ^ 2 / y + 1) * ((N + 1 : ℝ) + y * (1 + Real.log y)) ≤
          28 * ((2 * x) * d) * (6 * x ^ 2 / y + 1) *
            (2 * x + 303 * y * l) := by
      calc
        _ ≤ 28 * ((N + 1 : ℝ) * d) * (6 * x ^ 2 / y + 1) *
              (2 * x + 303 * y * l) := by gcongr
        _ ≤ 28 * ((2 * x) * d) * (6 * x ^ 2 / y + 1) *
              (2 * x + 303 * y * l) := by gcongr
    have hsum :
        28 * (24 * (d * x ^ 4 / y) + 3636 * (d * x ^ 3 * l) +
          4 * (d * x ^ 2) + 606 * (d * y * x * l)) ≤
        120000 * U * (x ^ 4 / y + x ^ 3 + y * x) := by
      have h1 := mul_le_mul_of_nonneg_left hpow1 (by norm_num : (0 : ℝ) ≤ 28 * 24)
      have h2 := mul_le_mul_of_nonneg_left hpow2 (by norm_num : (0 : ℝ) ≤ 28 * 3636)
      have h3 := mul_le_mul_of_nonneg_left hpow3 (by norm_num : (0 : ℝ) ≤ 28 * 4)
      have h4 := mul_le_mul_of_nonneg_left hpow4 (by norm_num : (0 : ℝ) ≤ 28 * 606)
      have htarget : 0 ≤ U * (x ^ 4 / y + x ^ 3 + y * x) := by positivity
      calc
        _ = 28 * 24 * (d * x ^ 4 / y) + 28 * 3636 * (d * x ^ 3 * l) +
              28 * 4 * (d * x ^ 2) + 28 * 606 * (d * y * x * l) := by ring
        _ ≤ 28 * 24 * (U * (x ^ 4 / y)) + 28 * 3636 * (U * x ^ 3) +
              28 * 4 * (U * x ^ 3) + 28 * 606 * (U * (y * x)) := by
          exact add_le_add (add_le_add (add_le_add h1 h2) h3) h4
        _ ≤ 120000 * U * (x ^ 4 / y + x ^ 3 + y * x) := by
          have hA : 0 ≤ U * (x ^ 4 / y) := by positivity
          have hB : 0 ≤ U * x ^ 3 := by positivity
          have hC' : 0 ≤ U * (y * x) := by positivity
          have hweighted :
              672 * (U * (x ^ 4 / y)) + 101920 * (U * x ^ 3) +
                16968 * (U * (y * x)) ≤
              120000 * U * (x ^ 4 / y + x ^ 3 + y * x) := by
            have hcoef1 : (672 : ℝ) ≤ 120000 := by norm_num
            have hcoef2 : (101920 : ℝ) ≤ 120000 := by norm_num
            have hcoef3 : (16968 : ℝ) ≤ 120000 := by norm_num
            have h1' := mul_le_mul_of_nonneg_right hcoef1 hA
            have h2' := mul_le_mul_of_nonneg_right hcoef2 hB
            have h3' := mul_le_mul_of_nonneg_right hcoef3 hC'
            calc
              _ ≤ 120000 * (U * (x ^ 4 / y)) + 120000 * (U * x ^ 3) +
                    120000 * (U * (y * x)) := add_le_add (add_le_add h1' h2') h3'
              _ = 120000 * U * (x ^ 4 / y + x ^ 3 + y * x) := by ring
          calc
            _ = 672 * (U * (x ^ 4 / y)) + 101920 * (U * x ^ 3) +
                16968 * (U * (y * x)) := by ring
            _ ≤ 120000 * U * (x ^ 4 / y + x ^ 3 + y * x) := hweighted
    calc
      (N + 1 : ℝ) * d *
          ((6 * (N * N : ℝ) / q + 1) * 28 *
            ((N + 1 : ℝ) + q * (1 + Real.log q)))
        = 28 * ((N + 1 : ℝ) * d) *
            (6 * x ^ 2 / y + 1) * ((N + 1 : ℝ) + y * (1 + Real.log y)) := by
              rw [show (N : ℝ) = x from rfl, show (q : ℝ) = y from rfl]
              ring
      _ ≤ 28 * ((2 * x) * d) * (6 * x ^ 2 / y + 1) *
            (2 * x + 303 * y * l) := hcombine
      _ = 28 * (24 * (d * x ^ 4 / y) + 3636 * (d * x ^ 3 * l) +
            4 * (d * x ^ 2) + 606 * (d * y * x * l)) := by
              calc
                _ = 28 * ((2 * x) * d * (6 * x ^ 2 / y + 1) *
                    (2 * x + 303 * y * l)) := by ring
                _ = _ := congrArg (fun z : ℝ => 28 * z) hprod
      _ ≤ 120000 * U * (x ^ 4 / y + x ^ 3 + y * x) := hsum
  have hWnonneg : 0 ≤ x ^ 4 / y + x ^ 3 + y * x := by positivity
  have hbound := hfour
  rw [hdivisor] at hbound
  have hscaleC : 0 ≤ 16 * C := by positivity
  have hmul := mul_le_mul_of_nonneg_left hEnvelope hscaleC
  have hfinal :
      ‖cubicUnweightedExpSum alpha N‖ ^ 4 ≤
        48 * U * x ^ 3 + 16 * C * 120000 * U *
          (x ^ 4 / y + x ^ 3 + y * x) := by
    calc
      _ ≤ 6 * (N + 1 : ℝ) ^ 3 +
            16 * (N + 1 : ℝ) * (C * d * coarseSpacingEnvelopeBound N q (N + 1 : ℝ)) := hbound
      _ ≤ 48 * U * x ^ 3 +
            16 * C * 120000 * U * (x ^ 4 / y + x ^ 3 + y * x) := by
          have hsecond :
              16 * (N + 1 : ℝ) * (C * d * coarseSpacingEnvelopeBound N q (N + 1 : ℝ)) ≤
                16 * C * 120000 * U * (x ^ 4 / y + x ^ 3 + y * x) := by
            calc
              _ = 16 * C * ((N + 1 : ℝ) * d * coarseSpacingEnvelopeBound N q (N + 1 : ℝ)) := by ring
              _ ≤ 16 * C * (120000 * U * (x ^ 4 / y + x ^ 3 + y * x)) := hmul
              _ = _ := by ring
          exact add_le_add hbase hsecond
  have hshape :
      U * (x ^ 4 / y + x ^ 3 + y * x) =
        Real.rpow x (4 + 1 / 12 : ℝ) *
          (1 / y + 1 / x + y / x ^ 3) := by
    have hxpow : Real.rpow x (4 + 1 / 12 : ℝ) = x ^ 4 * U := by
      calc
        Real.rpow x (4 + 1 / 12 : ℝ) =
            Real.rpow x (4 : ℝ) * Real.rpow x (1 / 12 : ℝ) :=
          Real.rpow_add hxpos 4 (1 / 12 : ℝ)
        _ = x ^ 4 * Real.rpow x (1 / 12 : ℝ) := by
          exact congrArg (fun z : ℝ => z * Real.rpow x (1 / 12 : ℝ))
            (Real.rpow_natCast x 4)
    calc
      U * (x ^ 4 / y + x ^ 3 + y * x) =
          (x ^ 4 * U) * (1 / y + 1 / x + y / x ^ 3) := by
            field_simp [hypos.ne', hxpos.ne']
      _ = Real.rpow x (4 + 1 / 12 : ℝ) *
            (1 / y + 1 / x + y / x ^ 3) := by rw [← hxpow]
  have hmain : 48 * U * x ^ 3 ≤
      48 * U * (x ^ 4 / y + x ^ 3 + y * x) := by
    have hdivnonneg : 0 ≤ x ^ 4 / y := div_nonneg (by positivity) hypos.le
    have hymulnonneg : 0 ≤ y * x := mul_nonneg hypos.le hxpos.le
    have hW : x ^ 3 ≤ x ^ 4 / y + x ^ 3 + y * x := by
      exact (le_add_of_nonneg_left hdivnonneg).trans
        (le_add_of_nonneg_right hymulnonneg)
    exact mul_le_mul_of_nonneg_left hW (by positivity)
  have hsumfinal :
      48 * U * x ^ 3 + 16 * C * 120000 * U *
          (x ^ 4 / y + x ^ 3 + y * x) ≤
        (48 + 16 * C * 120000) *
          U * (x ^ 4 / y + x ^ 3 + y * x) := by
    nlinarith
  have hrewrite :
      (48 + 16 * C * 120000) *
          U * (x ^ 4 / y + x ^ 3 + y * x) =
        (48 + 16 * C * 120000) * Real.rpow x (4 + 1 / 12 : ℝ) *
          (1 / y + 1 / x + y / x ^ 3) := by
    calc
      _ = (48 + 16 * C * 120000) *
            (U * (x ^ 4 / y + x ^ 3 + y * x)) := by ring
      _ = (48 + 16 * C * 120000) * Real.rpow x (4 + 1 / 12 : ℝ) *
            (1 / y + 1 / x + y / x ^ 3) := by
              rw [hshape]
              ring
  rw [show (N : ℝ) = x from rfl, show (q : ℝ) = y from rfl]
  calc
    _ ≤ 48 * U * x ^ 3 + 16 * C * 120000 * U *
          (x ^ 4 / y + x ^ 3 + y * x) := hfinal
    _ ≤ (48 + 16 * C * 120000) *
          U * (x ^ 4 / y + x ^ 3 + y * x) := hsumfinal
    _ = (48 + 16 * C * 120000) * Real.rpow x (4 + 1 / 12 : ℝ) *
          (1 / y + 1 / x + y / x ^ 3) := hrewrite

end CookMagyarCircle
end SystolicGrowth

#print axioms SystolicGrowth.CookMagyarCircle.card_positiveProductPairFiber_le_divisors
#print axioms SystolicGrowth.CookMagyarCircle.exists_positiveProductPairFiber_rpow_bound
#print axioms SystolicGrowth.CookMagyarCircle.exists_sum_positiveProductPairs_le_divisor_envelope
#print axioms SystolicGrowth.CookMagyarCircle.norm_cubicSecondDifferenceTripleSum_le_pairEnvelope
#print axioms SystolicGrowth.CookMagyarCircle.exists_norm_cubicSecondDifferenceTripleSum_le_spacing
#print axioms SystolicGrowth.CookMagyarCircle.exists_norm_cubicUnweightedExpSum_four_le_spacing
#print axioms SystolicGrowth.CookMagyarCircle.sixMulSpacingEnvelopeBound_le_coarse
#print axioms SystolicGrowth.CookMagyarCircle.pow_four_log_crossTerm_le
#print axioms SystolicGrowth.CookMagyarCircle.pow_four_normalizedSpacingPolynomial_le
#print axioms SystolicGrowth.CookMagyarCircle.pow_four_scaledNormalizedSpacingPolynomial_le
#print axioms SystolicGrowth.CookMagyarCircle.pow_four_coarseSpacingEnvelopeBound_le
#print axioms SystolicGrowth.CookMagyarCircle.divisorThresholdTail_pow_four_le
#print axioms SystolicGrowth.CookMagyarCircle.pow_four_sixMulSpacingEnvelopeBound_le
#print axioms SystolicGrowth.CookMagyarCircle.sixMulSpacingEnvelopeBoundWithError_le_mul
#print axioms SystolicGrowth.CookMagyarCircle.pow_four_sixMulSpacingEnvelopeBoundWithError_le
#print axioms SystolicGrowth.CookMagyarCircle.sum_positiveProductPairs_le_divisorThreshold_of_spacingBound
#print axioms SystolicGrowth.CookMagyarCircle.sum_positiveProductPairs_sixMul_envelope_le_divisorThreshold_of_error_constant
#print axioms SystolicGrowth.CookMagyarCircle.sum_positiveProductPairs_sixMul_envelope_le_logSaving
#print axioms SystolicGrowth.CookMagyarCircle.sum_positiveProductPairs_sixMul_envelope_le_logSaving_of_error_constant
#print axioms SystolicGrowth.CookMagyarCircle.sum_positiveProductPairs_sixMul_envelope_le_logSaving_of_progression_power_ranges
#print axioms SystolicGrowth.CookMagyarCircle.source_logarithm_bounds_of_size_ranges
#print axioms SystolicGrowth.CookMagyarCircle.sum_positiveProductPairs_sixMul_envelope_le_logSaving_of_progression_power_ranges_source_size
#print axioms SystolicGrowth.CookMagyarCircle.sum_positiveProductPairs_sixMul_envelope_le_logSaving_of_progression_power_ranges_source_size_order
#print axioms SystolicGrowth.CookMagyarCircle.exists_norm_cubicUnweightedExpSum_four_le_coarse
#print axioms SystolicGrowth.CookMagyarCircle.exists_norm_cubicUnweightedExpSum_four_le_weyl
