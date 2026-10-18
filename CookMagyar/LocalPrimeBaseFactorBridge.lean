module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.PrimePowerStationaryPhase
public import CookMagyar.LocalLargePrimeCounts
public import CookMagyar.LocalFactorBridge

@[expose] public section

namespace SystolicGrowth
namespace CookMagyarFiniteFourier

/-! # The prime-level local factor from nonsingular solutions

The first two terms of the prime local factor are exactly the normalized
prime-modulus solution count.  The nonsingular modular solution gives an
explicit positive lower bound for this truncation, uniformly in the target.
-/

/-- At every prime, the first singular-series truncation is the actual
normalized prime-modulus count. -/
theorem one_add_singularSeriesTerm_prime_eq_normalizedUnitCubicCount
    {p n T : ℕ} (hp : p.Prime) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    (1 : ℂ) + singularSeriesTerm n T p =
      (normalizedUnitCubicCount n (T : ZMod p) : ℂ) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [singularSeriesTerm_of_pos n T hp.pos,
    CookMagyarPrimePower.singularSeriesCoefficient_prime_eq_normalized_sub_one_general hp,
    complexNormalizedUnitCubicCount_of_real]
  ring

/-- A nonsingular unit solution at a prime at least five makes the first
local-factor truncation positive, uniformly in the target. -/
theorem one_add_singularSeriesTerm_prime_re_pos
    {p n T : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn5 : 5 ≤ n) :
    0 < ((1 : ℂ) + singularSeriesTerm n T p).re := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [one_add_singularSeriesTerm_prime_eq_normalizedUnitCubicCount hp,
    Complex.ofReal_re]
  apply normalizedUnitCubicCount_pos (q := p) (by omega)
  exact unitCubicSolutionCount_pos_of_prime_ge_five hp hp5 hn5 _

/-- The iterated nonsingular lifts give the explicit prime-level lower
bound `p/(p-1)^n` for the first local-factor truncation. -/
theorem one_add_singularSeriesTerm_prime_re_ge_lift_bound
    {p n T : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn5 : 5 ≤ n) :
    (p : ℝ) / ((p - 1 : ℕ) : ℝ) ^ n ≤
      ((1 : ℂ) + singularSeriesTerm n T p).re := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [one_add_singularSeriesTerm_prime_eq_normalizedUnitCubicCount hp,
    Complex.ofReal_re]
  have hcount : (1 : ℝ) ≤ unitCubicSolutionCount n (T : ZMod p) := by
    exact_mod_cast unitCubicSolutionCount_pos_of_prime_ge_five hp hp5 hn5
      (T : ZMod p)
  have hphi : Nat.totient p = p - 1 := Nat.totient_prime hp
  have hden : 0 < (((p - 1 : ℕ) : ℝ) ^ n) := by
    have hsub : 0 < p - 1 := by omega
    exact pow_pos (by exact_mod_cast hsub) n
  unfold normalizedUnitCubicCount
  rw [hphi]
  apply (div_le_div_iff_of_pos_right hden).2
  simpa using mul_le_mul_of_nonneg_left hcount
    (by positivity : 0 ≤ (p : ℝ))

/-- Any limiting local density at a prime at least five inherits the same
strictly positive target-uniform bound from the nonsingular lift family. -/
theorem primeLocalDensity_ge_lift_bound_of_hasPrimeLocalDensity
    {p n T : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn5 : 5 ≤ n)
    {mu : ℝ} (hmu : HasPrimeLocalDensity p n T hp mu) :
    (p : ℝ) / ((p - 1 : ℕ) : ℝ) ^ n ≤ mu := by
  apply ge_of_tendsto hmu
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk
  simpa [primePowerLocalDensityApproximation] using
    (CookMagyarLocal.normalizedUnitCubicCount_primePower_uniform_lower_bound
      hp hp5 hn5 T k hk)

/-- In particular, an existing local density at a prime at least five is
strictly positive. -/
theorem primeLocalDensity_pos_of_hasPrimeLocalDensity
    {p n T : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn5 : 5 ≤ n)
    {mu : ℝ} (hmu : HasPrimeLocalDensity p n T hp mu) :
    0 < mu := by
  have hbound := primeLocalDensity_ge_lift_bound_of_hasPrimeLocalDensity
    hp hp5 hn5 hmu
  have hpositive : 0 < (p : ℝ) / ((p - 1 : ℕ) : ℝ) ^ n := by
    have hp_sub : 0 < p - 1 := by omega
    exact div_pos (by exact_mod_cast hp.pos)
      (pow_pos (by exact_mod_cast hp_sub) n)
  exact hpositive.trans_le hbound

/-- The full local factor is bounded below by the nonsingular prime-level
count minus the norm of the higher-prime-power tail.  This identifies the
exact extra estimate needed when treating finitely many primes by bounds. -/
theorem primeLocalFactor_re_ge_lift_bound_sub_higherTail_norm
    {p n T : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 33 ≤ n) :
    (p : ℝ) / ((p - 1 : ℕ) : ℝ) ^ n -
        ‖∑' k : ℕ, singularSeriesTerm n T (p ^ (k + 2))‖ ≤
      (primeLocalFactor p n T).re := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hbase := one_add_singularSeriesTerm_prime_re_ge_lift_bound
    hp hp5 (by omega : 5 ≤ n) (T := T)
  let tail : ℂ := ∑' k : ℕ, singularSeriesTerm n T (p ^ (k + 2))
  have htail : -‖tail‖ ≤ tail.re := by
    have hnorm := Complex.abs_re_le_norm tail
    exact (neg_le_neg hnorm).trans (neg_abs_le _)
  rw [primeLocalFactor_eq_prime_add_higherTail_of_large_prime hp hp5 hn]
  change (p : ℝ) / ((p - 1 : ℕ) : ℝ) ^ n - ‖tail‖ ≤
    ((1 : ℂ) + singularSeriesTerm n T p + tail).re
  rw [Complex.add_re]
  linarith

/-- A tail estimate smaller than the explicit nonsingular lift bound makes
the completed local factor positive. -/
theorem primeLocalFactor_re_pos_of_higherTail_norm_lt_lift_bound
    {p n T : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 33 ≤ n)
    (htail : ‖∑' k : ℕ, singularSeriesTerm n T (p ^ (k + 2))‖ <
      (p : ℝ) / ((p - 1 : ℕ) : ℝ) ^ n) :
    0 < (primeLocalFactor p n T).re := by
  have hbound := primeLocalFactor_re_ge_lift_bound_sub_higherTail_norm
    hp hp5 hn (T := T)
  linarith

end CookMagyarFiniteFourier
end SystolicGrowth
