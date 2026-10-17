module

public import CookMagyar.SingularSeries
public import CookMagyar.PrimePowerTail

@[expose] public section

/-!
# Prime local-factor decomposition

This file records the exact reindexing needed to combine the prime-modulus
estimate with the higher-prime-power tail.  The summability hypothesis is
explicit: later arithmetic modules must discharge it rather than hiding it in
an Euler-product assumption.
-/

namespace SystolicGrowth
namespace CookMagyarFiniteFourier

open scoped BigOperators

theorem primeLocalFactor_eq_prime_add_higherTail
    {p n T : ℕ}
    (hsum : Summable (fun k : ℕ ↦
      singularSeriesTerm n T (p ^ (k + 1)))) :
    primeLocalFactor p n T =
      1 + singularSeriesTerm n T p +
        ∑' k : ℕ, singularSeriesTerm n T (p ^ (k + 2)) := by
  let f : ℕ → ℂ := fun k ↦ singularSeriesTerm n T (p ^ (k + 1))
  have hsplit := hsum.sum_add_tsum_nat_add 1
  have hshift : (∑' k : ℕ, f (k + 1)) =
      ∑' k : ℕ, singularSeriesTerm n T (p ^ (k + 2)) := by
    apply tsum_congr
    intro k
    simp [f, Nat.add_comm, Nat.add_left_comm]
  have hfirst : (∑ i ∈ Finset.range 1, f i) = f 0 := by
    simp [f]
  unfold primeLocalFactor
  rw [show (∑' k : ℕ, singularSeriesTerm n T (p ^ (k + 1))) = ∑' k : ℕ, f k by rfl]
  rw [← hsplit, hfirst, hshift]
  simp [f, Nat.pow_succ]
  ring

theorem primeLocalFactor_eq_prime_add_higherTail_of_large_prime
    {p n T : ℕ} [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 33 ≤ n) :
    primeLocalFactor p n T =
      1 + singularSeriesTerm n T p +
        ∑' k : ℕ, singularSeriesTerm n T (p ^ (k + 2)) := by
  have htailNorm :=
    CookMagyarPrimePower.summable_norm_singularSeriesTerm_higherPrimePower
      (T := T) hp hp5 hn
  have htail : Summable (fun k : ℕ ↦
      singularSeriesTerm n T (p ^ (k + 2))) := by
    apply Summable.of_norm
    exact htailNorm
  apply primeLocalFactor_eq_prime_add_higherTail
  apply (summable_nat_add_iff 1).mp
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

theorem norm_primeLocalFactor_sub_one_le_large_prime
    {p n T : ℕ} [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 33 ≤ n) :
    ‖primeLocalFactor p n T - 1‖ ≤
      (40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n / (p : ℝ) ^ 7 +
        ((2 : ℝ) ^ n * ((5 : ℝ) / 4) ^ (n - 1)) *
          (1 + (p : ℝ)) * ((p : ℝ)⁻¹) ^ (n - 2) /
            (1 - ((p : ℝ)⁻¹) ^ (n - 2)) := by
  have hsplit := primeLocalFactor_eq_prime_add_higherTail_of_large_prime
    (p := p) (n := n) (T := T) hp hp5 hn
  have htailNorm :=
    CookMagyarPrimePower.summable_norm_singularSeriesTerm_higherPrimePower
      (T := T) hp hp5 hn
  have hn32 : 32 ≤ n := by omega
  have hprime := norm_singularSeriesTerm_prime_le_inv_pow hp hp5 hn32 T
  have htail :=
    CookMagyarPrimePower.tsum_norm_singularSeriesTerm_higherPrimePower_le
      (T := T) hp hp5 hn
  rw [hsplit]
  calc
    ‖1 + singularSeriesTerm n T p +
        ∑' k : ℕ, singularSeriesTerm n T (p ^ (k + 2)) - 1‖ =
        ‖singularSeriesTerm n T p +
          ∑' k : ℕ, singularSeriesTerm n T (p ^ (k + 2))‖ := by
            congr 1
            ring
    _ ≤ ‖singularSeriesTerm n T p‖ +
          ‖∑' k : ℕ, singularSeriesTerm n T (p ^ (k + 2))‖ := norm_add_le _ _
    _ ≤ ‖singularSeriesTerm n T p‖ +
          ∑' k : ℕ, ‖singularSeriesTerm n T (p ^ (k + 2))‖ := by
            gcongr
            exact norm_tsum_le_tsum_norm htailNorm
    _ ≤ (40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n / (p : ℝ) ^ 7 +
        ((2 : ℝ) ^ n * ((5 : ℝ) / 4) ^ (n - 1)) *
          (1 + (p : ℝ)) * ((p : ℝ)⁻¹) ^ (n - 2) /
            (1 - ((p : ℝ)⁻¹) ^ (n - 2)) := by
            exact add_le_add hprime htail

theorem abs_realPart_primeLocalFactor_sub_one_le_large_prime
    {p n T : ℕ} [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 33 ≤ n) :
    |(primeLocalFactor p n T).re - 1| ≤
      (40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n / (p : ℝ) ^ 7 +
        ((2 : ℝ) ^ n * ((5 : ℝ) / 4) ^ (n - 1)) *
          (1 + (p : ℝ)) * ((p : ℝ)⁻¹) ^ (n - 2) /
            (1 - ((p : ℝ)⁻¹) ^ (n - 2)) := by
  have hnorm := norm_primeLocalFactor_sub_one_le_large_prime
    (p := p) (n := n) (T := T) hp hp5 hn
  have hre := Complex.abs_re_le_norm (primeLocalFactor p n T - 1)
  rw [Complex.sub_re] at hre
  simpa using hre.trans hnorm

theorem primeLocalFactor_re_pos_of_deviation_lt_one
    {p n T : ℕ}
    (hdev : |(primeLocalFactor p n T).re - 1| < 1) :
    0 < (primeLocalFactor p n T).re := by
  have hlow : -(1 : ℝ) < (primeLocalFactor p n T).re - 1 := by
    have habsneg : -(1 : ℝ) < -|(primeLocalFactor p n T).re - 1| := by
      linarith
    exact habsneg.trans_le (neg_abs_le _)
  linarith

theorem norm_primeLocalFactor_sub_one_le_large_prime_of_half_ratio
    {p n T : ℕ} [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 33 ≤ n)
    (hr : ((p : ℝ)⁻¹) ^ (n - 2) ≤ 1 / 2) :
    ‖primeLocalFactor p n T - 1‖ ≤
      (40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n / (p : ℝ) ^ 7 +
        2 * (((2 : ℝ) ^ n * ((5 : ℝ) / 4) ^ (n - 1)) *
          (1 + (p : ℝ)) * ((p : ℝ)⁻¹) ^ (n - 2)) := by
  have hbase := norm_primeLocalFactor_sub_one_le_large_prime
    (p := p) (n := n) (T := T) hp hp5 hn
  let r : ℝ := ((p : ℝ)⁻¹) ^ (n - 2)
  let A : ℝ := ((2 : ℝ) ^ n * ((5 : ℝ) / 4) ^ (n - 1)) * (1 + (p : ℝ))
  have hr' : r ≤ 1 / 2 := by simpa [r] using hr
  have hden : 0 < 1 - r := by linarith
  have hA : 0 ≤ A := by positivity
  have hAr : 0 ≤ A * r := mul_nonneg hA (by positivity)
  have htail : A * r / (1 - r) ≤ 2 * (A * r) := by
    apply (div_le_iff₀ hden).2
    nlinarith
  change ‖primeLocalFactor p n T - 1‖ ≤
      (40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n / (p : ℝ) ^ 7 + A * r / (1 - r) at hbase
  change ‖primeLocalFactor p n T - 1‖ ≤
      (40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n / (p : ℝ) ^ 7 + 2 * (A * r)
  exact hbase.trans (add_le_add_right htail
    ((40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n / (p : ℝ) ^ 7))

theorem inv_pow_le_half_of_prime_large
    {p n : ℕ} (hp5 : 5 ≤ p) (hn : 33 ≤ n) :
    ((p : ℝ)⁻¹) ^ (n - 2) ≤ 1 / 2 := by
  have hinv : (p : ℝ)⁻¹ ≤ (5 : ℝ)⁻¹ := by
    simpa [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 5)
        (by exact_mod_cast hp5))
  have hbase : ((p : ℝ)⁻¹) ^ (n - 2) ≤ ((5 : ℝ)⁻¹) ^ (n - 2) :=
    pow_le_pow_left₀ (by positivity) hinv _
  have hexp : 31 ≤ n - 2 := by omega
  have hexp' : ((5 : ℝ)⁻¹) ^ (n - 2) ≤ ((5 : ℝ)⁻¹) ^ 31 :=
    pow_le_pow_of_le_one (by positivity) (by norm_num) hexp
  calc
    ((p : ℝ)⁻¹) ^ (n - 2) ≤ ((5 : ℝ)⁻¹) ^ (n - 2) := hbase
    _ ≤ ((5 : ℝ)⁻¹) ^ 31 := hexp'
    _ ≤ 1 / 2 := by norm_num

theorem inv_pow_split_three_of_prime_large
    {p n : ℕ} (hp5 : 5 ≤ p) (hn : 33 ≤ n) :
    ((p : ℝ)⁻¹) ^ (n - 2) ≤
      ((1 / 5 : ℝ) ^ (n - 5)) * (p : ℝ)⁻¹ ^ 3 := by
  have hinv : (p : ℝ)⁻¹ ≤ (5 : ℝ)⁻¹ := by
    simpa [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 5)
        (by exact_mod_cast hp5))
  have hrem : ((p : ℝ)⁻¹) ^ (n - 5) ≤ (1 / 5 : ℝ) ^ (n - 5) := by
    simpa [one_div] using
      (pow_le_pow_left₀ (by positivity) hinv (n - 5))
  have hshift : n - 2 = (n - 5) + 3 := by omega
  rw [hshift, pow_add]
  exact mul_le_mul_of_nonneg_right hrem (by positivity)

theorem tail_numerator_refined_of_prime_large
    {p n : ℕ} (hp5 : 5 ≤ p) (hn : 33 ≤ n) :
    2 * (((2 : ℝ) ^ n * ((5 : ℝ) / 4) ^ (n - 1)) *
      (1 + (p : ℝ)) * ((p : ℝ)⁻¹) ^ (n - 2)) ≤
      2 * (((2 : ℝ) ^ n * ((5 : ℝ) / 4) ^ (n - 1)) *
        (1 + (p : ℝ)) * ((1 / 5 : ℝ) ^ (n - 5) * (p : ℝ)⁻¹ ^ 3)) := by
  have hsplit := inv_pow_split_three_of_prime_large hp5 hn
  gcongr

theorem tail_numerator_pneg_two_of_prime_large
    {p n : ℕ} (hp5 : 5 ≤ p) (hn : 33 ≤ n) :
    2 * (((2 : ℝ) ^ n * ((5 : ℝ) / 4) ^ (n - 1)) *
      (1 + (p : ℝ)) * ((p : ℝ)⁻¹) ^ (n - 2)) ≤
      4 * (((2 : ℝ) ^ n * ((5 : ℝ) / 4) ^ (n - 1)) *
        ((1 / 5 : ℝ) ^ (n - 5)) * (p : ℝ)⁻¹ ^ 2) := by
  have href := tail_numerator_refined_of_prime_large hp5 hn
  have hponeNat : 1 ≤ p := by omega
  have hpone : (1 : ℝ) ≤ p := by exact_mod_cast hponeNat
  have hpne : (p : ℝ) ≠ 0 := by positivity
  have hfac : (1 + (p : ℝ)) * (p : ℝ)⁻¹ ^ 3 ≤ 2 * (p : ℝ)⁻¹ ^ 2 := by
    field_simp [hpne]
    nlinarith
  calc
    2 * (((2 : ℝ) ^ n * ((5 : ℝ) / 4) ^ (n - 1)) *
        (1 + (p : ℝ)) * ((p : ℝ)⁻¹) ^ (n - 2)) ≤
      2 * (((2 : ℝ) ^ n * ((5 : ℝ) / 4) ^ (n - 1)) *
        (1 + (p : ℝ)) * ((1 / 5 : ℝ) ^ (n - 5) * (p : ℝ)⁻¹ ^ 3)) := href
    _ = 2 * (((2 : ℝ) ^ n * ((5 : ℝ) / 4) ^ (n - 1)) *
        ((1 / 5 : ℝ) ^ (n - 5))) *
        ((1 + (p : ℝ)) * (p : ℝ)⁻¹ ^ 3) := by ring
    _ ≤ 2 * (((2 : ℝ) ^ n * ((5 : ℝ) / 4) ^ (n - 1)) *
        ((1 / 5 : ℝ) ^ (n - 5))) * (2 * (p : ℝ)⁻¹ ^ 2) := by
      gcongr
    _ = 4 * (((2 : ℝ) ^ n * ((5 : ℝ) / 4) ^ (n - 1)) *
        ((1 / 5 : ℝ) ^ (n - 5)) * (p : ℝ)⁻¹ ^ 2) := by ring

theorem tail_coefficient_le_one_of_large_n
    {n : ℕ} (hn : 33 ≤ n) :
    4 * ((2 : ℝ) ^ n * ((5 : ℝ) / 4) ^ (n - 1)) *
        ((1 / 5 : ℝ) ^ (n - 5)) ≤ 1 := by
  have hn5 : 5 ≤ n := by omega
  have hsplit1 : n - 1 = (n - 5) + 4 := by omega
  have hsplit2 : n = (n - 5) + 5 := by omega
  have hpow : (28 : ℕ) ≤ n - 5 := by omega
  have hidentity :
      4 * ((2 : ℝ) ^ n * ((5 : ℝ) / 4) ^ (n - 1)) *
          ((1 / 5 : ℝ) ^ (n - 5)) =
        (625 / 2 : ℝ) * ((1 / 2 : ℝ) ^ (n - 5)) := by
    rw [hsplit1, pow_add, hsplit2, pow_add]
    simp only [Nat.sub_add_cancel hn5]
    have hcomb :
        ((5 : ℝ) / 4) ^ (n - 5) * (1 / 5 : ℝ) ^ (n - 5) =
          (1 / 4 : ℝ) ^ (n - 5) := by
      rw [← mul_pow]
      ring
    have hcomb2 :
        (2 : ℝ) ^ (n - 5) * (1 / 4 : ℝ) ^ (n - 5) =
          (1 / 2 : ℝ) ^ (n - 5) := by
      rw [← mul_pow]
      ring
    calc
      4 * (2 ^ (n - 5) * 2 ^ 5 *
          (((5 : ℝ) / 4) ^ (n - 5) * ((5 : ℝ) / 4) ^ 4)) *
          (1 / 5 : ℝ) ^ (n - 5) =
          4 * 2 ^ 5 * ((5 : ℝ) / 4) ^ 4 *
            (2 ^ (n - 5) * (((5 : ℝ) / 4) ^ (n - 5) *
              (1 / 5 : ℝ) ^ (n - 5))) := by ring
      _ = (625 / 2 : ℝ) * ((1 / 2 : ℝ) ^ (n - 5)) := by
        rw [hcomb, ← hcomb2]
        norm_num
  rw [hidentity]
  calc
    (625 / 2 : ℝ) * (1 / 2 : ℝ) ^ (n - 5) ≤
        (625 / 2 : ℝ) * (1 / 2 : ℝ) ^ 28 := by
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_of_le_one (by norm_num) (by norm_num) hpow)
            (by norm_num)
    _ ≤ 1 := by norm_num

theorem tail_numerator_le_inv_sq_of_prime_large
    {p n : ℕ} (hp5 : 5 ≤ p) (hn : 33 ≤ n) :
    2 * (((2 : ℝ) ^ n * ((5 : ℝ) / 4) ^ (n - 1)) *
      (1 + (p : ℝ)) * ((p : ℝ)⁻¹) ^ (n - 2)) ≤
      (p : ℝ)⁻¹ ^ 2 := by
  have hshape := tail_numerator_pneg_two_of_prime_large hp5 hn
  have hcoef := tail_coefficient_le_one_of_large_n hn
  have hcoefmul := mul_le_mul_of_nonneg_right hcoef (by positivity :
    0 ≤ (p : ℝ)⁻¹ ^ 2)
  calc
    2 * (((2 : ℝ) ^ n * ((5 : ℝ) / 4) ^ (n - 1)) *
        (1 + (p : ℝ)) * ((p : ℝ)⁻¹) ^ (n - 2)) ≤
      4 * (((2 : ℝ) ^ n * ((5 : ℝ) / 4) ^ (n - 1)) *
        ((1 / 5 : ℝ) ^ (n - 5)) * (p : ℝ)⁻¹ ^ 2) := hshape
    _ = (4 * ((2 : ℝ) ^ n * ((5 : ℝ) / 4) ^ (n - 1)) *
        ((1 / 5 : ℝ) ^ (n - 5))) * (p : ℝ)⁻¹ ^ 2 := by ring
    _ ≤ (p : ℝ)⁻¹ ^ 2 := by simpa using hcoefmul

theorem norm_primeLocalFactor_sub_one_le_prime_plus_inv_sq
    {p n T : ℕ} [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 33 ≤ n) :
    ‖primeLocalFactor p n T - 1‖ ≤
      (40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n / (p : ℝ) ^ 7 +
        (p : ℝ)⁻¹ ^ 2 := by
  have hbase := norm_primeLocalFactor_sub_one_le_large_prime_of_half_ratio
    (p := p) (n := n) (T := T) hp hp5 hn
    (inv_pow_le_half_of_prime_large hp5 hn)
  have htail := tail_numerator_le_inv_sq_of_prime_large hp5 hn
  exact hbase.trans (add_le_add_right htail
    ((40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n / (p : ℝ) ^ 7))

theorem norm_primeLocalFactor_sub_one_le_rpow_two
    {p n T : ℕ} [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 33 ≤ n) :
    ‖primeLocalFactor p n T - 1‖ ≤
      (((40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n) + 1) *
        (p : ℝ)⁻¹ ^ 2 := by
  have hbase := norm_primeLocalFactor_sub_one_le_prime_plus_inv_sq
    (p := p) (n := n) (T := T) hp hp5 hn
  have hponeNat : 1 ≤ p := by omega
  have hpone : (1 : ℝ) ≤ p := by exact_mod_cast hponeNat
  have hpne : (p : ℝ) ≠ 0 := by positivity
  have hppos : (0 : ℝ) < p := by positivity
  have hinv : (p : ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hppos]
    exact hpone
  have hinvpow : (p : ℝ)⁻¹ ^ 7 ≤ (p : ℝ)⁻¹ ^ 2 := by
    exact pow_le_pow_of_le_one (by positivity) hinv (by norm_num)
  have hprime :
      (40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n / (p : ℝ) ^ 7 ≤
        ((40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n) * (p : ℝ)⁻¹ ^ 2 := by
    have hcoef : 0 ≤ (40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n := by positivity
    calc
      (40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n / (p : ℝ) ^ 7 =
          ((40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n) * (p : ℝ)⁻¹ ^ 7 := by
            rw [div_eq_mul_inv, inv_pow]
      _ ≤ ((40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n) * (p : ℝ)⁻¹ ^ 2 :=
        mul_le_mul_of_nonneg_left hinvpow hcoef
  calc
    ‖primeLocalFactor p n T - 1‖ ≤
        (40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n / (p : ℝ) ^ 7 +
          (p : ℝ)⁻¹ ^ 2 := hbase
    _ ≤ ((40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n) * (p : ℝ)⁻¹ ^ 2 +
          (p : ℝ)⁻¹ ^ 2 := add_le_add hprime le_rfl
    _ = (((40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n) + 1) *
        (p : ℝ)⁻¹ ^ 2 := by ring

theorem primeLocalFactor_re_pos_large_of_rpow_two_lt_one
    {p n T : ℕ} [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 33 ≤ n)
    (hsmall : (((40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n) + 1) *
      (p : ℝ)⁻¹ ^ 2 < 1) :
    0 < (primeLocalFactor p n T).re := by
  have hnorm := norm_primeLocalFactor_sub_one_le_rpow_two
    (p := p) (n := n) (T := T) hp hp5 hn
  have hreal : |(primeLocalFactor p n T).re - 1| ≤
      (((40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n) + 1) *
        (p : ℝ)⁻¹ ^ 2 := by
    exact (Complex.abs_re_le_norm (primeLocalFactor p n T - 1)).trans hnorm
  exact primeLocalFactor_re_pos_of_deviation_lt_one (hreal.trans_lt hsmall)

theorem primeLocalFactor_re_pos_of_square_threshold
    {p n T : ℕ} [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 33 ≤ n)
    (hthreshold : (40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n + 1 < (p : ℝ) ^ 2) :
    0 < (primeLocalFactor p n T).re := by
  have hp_pos : (0 : ℝ) < p := by positivity
  have hp_inv_sq : (p : ℝ)⁻¹ ^ 2 = 1 / (p : ℝ) ^ 2 := by
    rw [inv_pow, one_div]
  have hsmall : (((40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n) + 1) *
      (p : ℝ)⁻¹ ^ 2 < 1 := by
    rw [hp_inv_sq]
    rw [mul_one_div]
    apply (div_lt_iff₀ (sq_pos_of_pos hp_pos)).2
    nlinarith
  exact primeLocalFactor_re_pos_large_of_rpow_two_lt_one hp hp5 hn hsmall

theorem exists_square_threshold_cutoff
    {C : ℝ} (hC : 0 ≤ C) :
    ∃ N : ℕ, ∀ p : ℕ, N ≤ p → C < (p : ℝ) ^ 2 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.sqrt C)
  refine ⟨N, ?_⟩
  intro p hpN
  have hpN' : (N : ℝ) ≤ p := by exact_mod_cast hpN
  have hsqrt : Real.sqrt C < (p : ℝ) := hN.trans_le hpN'
  have hsqrt_nonneg : 0 ≤ Real.sqrt C := Real.sqrt_nonneg C
  have hsquare : (Real.sqrt C) ^ 2 = C := Real.sq_sqrt hC
  nlinarith

theorem exists_local_factor_square_threshold_cutoff
    {n : ℕ} (_hn : 33 ≤ n) :
    ∃ N : ℕ, ∀ p : ℕ, N ≤ p →
      (40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n + 1 < (p : ℝ) ^ 2 := by
  apply exists_square_threshold_cutoff
  positivity

theorem norm_primeLocalFactor_sub_one_le_large_prime_denominator_free
    {p n T : ℕ} [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 33 ≤ n) :
    ‖primeLocalFactor p n T - 1‖ ≤
      (40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n / (p : ℝ) ^ 7 +
        2 * (((2 : ℝ) ^ n * ((5 : ℝ) / 4) ^ (n - 1)) *
          (1 + (p : ℝ)) * ((p : ℝ)⁻¹) ^ (n - 2)) := by
  exact norm_primeLocalFactor_sub_one_le_large_prime_of_half_ratio hp hp5 hn
    (inv_pow_le_half_of_prime_large hp5 hn)

end CookMagyarFiniteFourier
end SystolicGrowth
