module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.PrimePowerStationaryPhase

@[expose] public section

open scoped BigOperators

namespace SystolicGrowth
namespace CookMagyarPrimePower

open CookMagyarFiniteFourier

/-! # Summable higher prime-power tails

For primes at least five, the stationary-phase bounds at the balanced
prime-power blocks give a geometric majorant for every level above the
prime modulus.  This file turns those termwise bounds into an explicit,
target-uniform summable tail when the number of variables is at least 33.
-/

/-- At an even prime-power level, stationary phase gives the geometric
decay needed for the higher-level singular-series tail. -/
theorem norm_singularSeriesTerm_primePower_even_le_geometric
    {p m n T : ℕ} [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p)
    (hm : 1 ≤ m) (hn : 33 ≤ n) :
    ‖singularSeriesTerm n T (p ^ (2 * m))‖ ≤
      (2 : ℝ) ^ n * ((5 : ℝ) / 4) ^ (n - 1) /
        (p : ℝ) ^ (m * (n - 2)) := by
  have h := norm_singularSeriesTerm_primePower_even_le
    (p := p) (m := m) (n := n) (T := T) hp hp5 hm
  rw [Nat.totient_prime_pow hp (by omega : 0 < 2 * m)] at h
  have hpR : 0 < (p : ℝ) := by
    exact_mod_cast NeZero.pos p
  have hpm1R : 0 < (p : ℝ) - 1 := by
    rw [← Nat.cast_one, ← Nat.cast_sub (by omega : 1 ≤ p)]
    exact_mod_cast (show 0 < p - 1 by omega)
  have htotR : 0 < (p : ℝ) ^ (2 * m - 1) * ((p : ℝ) - 1) := by positivity
  have hnorminv :
      ‖((↑(p ^ (2 * m - 1) * (p - 1)) : ℂ)⁻¹)‖ =
        ((p : ℝ) ^ (2 * m - 1) * ((p : ℝ) - 1))⁻¹ := by
    calc
      ‖((↑(p ^ (2 * m - 1) * (p - 1)) : ℂ)⁻¹)‖ =
          (↑(p ^ (2 * m - 1) * (p - 1)) : ℝ)⁻¹ := by simp [norm_inv]
      _ = ((p : ℝ) ^ (2 * m - 1) * ((p : ℝ) - 1))⁻¹ := by
        rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub (by omega : 1 ≤ p)]
        norm_num
  rw [hnorminv] at h
  have htotcast :
      (↑(p ^ (2 * m - 1) * (p - 1)) : ℝ) =
        (p : ℝ) ^ (2 * m - 1) * ((p : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub (by omega : 1 ≤ p)]
    norm_num
  rw [htotcast] at h
  have hratio : (p : ℝ) / ((p : ℝ) - 1) ≤ (5 : ℝ) / 4 := by
    rw [div_le_iff₀ hpm1R]
    have hp5R : (5 : ℝ) ≤ p := by exact_mod_cast hp5
    linarith
  have hratio_pow := pow_le_pow_left₀
    (by positivity : 0 ≤ (p : ℝ) / ((p : ℝ) - 1)) hratio (n - 1)
  have hform :
      ((p : ℝ) ^ (2 * m - 1) * ((p : ℝ) - 1))⁻¹ ^ n *
          ((p : ℝ) ^ (2 * m - 1) * ((p : ℝ) - 1)) *
          (2 * (p : ℝ) ^ m) ^ n =
        (2 : ℝ) ^ n * ((p : ℝ) / ((p : ℝ) - 1)) ^ (n - 1) /
          (p : ℝ) ^ (m * (n - 2)) := by
    rw [inv_pow, mul_pow, mul_pow, div_pow]
    have hexp :
        m * n + m * (n - 2) + (m * 2 - 1) =
          (m * 2 - 1) * n + (n - 1) := by
      apply Nat.cast_injective (R := ℤ)
      push_cast
      rw [Nat.cast_sub (by omega : 2 ≤ n),
        Nat.cast_sub (by omega : 1 ≤ m * 2),
        Nat.cast_sub (by omega : 1 ≤ n)]
      push_cast
      ring
    have hpows :
        (p : ℝ) ^ (m * n) * (p : ℝ) ^ (m * (n - 2)) *
            (p : ℝ) ^ (m * 2 - 1) =
          (p : ℝ) ^ ((m * 2 - 1) * n) * (p : ℝ) ^ (n - 1) := by
      calc
        (p : ℝ) ^ (m * n) * (p : ℝ) ^ (m * (n - 2)) *
            (p : ℝ) ^ (m * 2 - 1) =
            (p : ℝ) ^ (m * n + m * (n - 2) + (m * 2 - 1)) := by
              rw [← pow_add, ← pow_add]
        _ = (p : ℝ) ^ (((m * 2 - 1) * n) + (n - 1)) := by rw [hexp]
        _ = (p : ℝ) ^ ((m * 2 - 1) * n) * (p : ℝ) ^ (n - 1) := by
              rw [pow_add]
    have hsubpow : ((p : ℝ) - 1) ^ (n - 1) * ((p : ℝ) - 1) =
        ((p : ℝ) - 1) ^ n := by
      calc
        ((p : ℝ) - 1) ^ (n - 1) * ((p : ℝ) - 1) =
            ((p : ℝ) - 1) ^ (n - 1) * ((p : ℝ) - 1) ^ 1 := by
              rw [pow_one]
        _ = ((p : ℝ) - 1) ^ ((n - 1) + 1) := by rw [pow_add]
        _ = ((p : ℝ) - 1) ^ n := by
              rw [show (n - 1) + 1 = n by omega]
    field_simp [htotR.ne', hpR.ne', hpm1R.ne']
    calc
      _ = ((p : ℝ) - 1) *
          ((p : ℝ) ^ (m * n) * (p : ℝ) ^ (m * (n - 2)) *
            (p : ℝ) ^ (m * 2 - 1) * ((p : ℝ) - 1) ^ (n - 1)) := by ring_nf
      _ = ((p : ℝ) - 1) *
          ((p : ℝ) ^ ((m * 2 - 1) * n) * (p : ℝ) ^ (n - 1) *
            ((p : ℝ) - 1) ^ (n - 1)) := by rw [hpows]
      _ = _ := by
        rw [show ((p : ℝ) - 1) *
            ((p : ℝ) ^ ((m * 2 - 1) * n) * (p : ℝ) ^ (n - 1) *
              ((p : ℝ) - 1) ^ (n - 1)) =
            (p : ℝ) ^ ((m * 2 - 1) * n) * (p : ℝ) ^ (n - 1) *
              (((p : ℝ) - 1) ^ (n - 1) * ((p : ℝ) - 1)) by ring]
        rw [hsubpow, pow_mul]
        have hm2 : m * 2 - 1 = 2 * m - 1 := by omega
        rw [hm2]
        ring
  rw [hform] at h
  apply h.trans
  apply div_le_div_of_nonneg_right
  · exact mul_le_mul_of_nonneg_left hratio_pow (by positivity)
  · positivity

/-- The odd levels have the same geometric factor, with one unavoidable
extra factor of the prime. -/
theorem norm_singularSeriesTerm_primePower_odd_le_geometric
    {p m n T : ℕ} [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p)
    (hm : 1 ≤ m) (hn : 33 ≤ n) :
    ‖singularSeriesTerm n T (p ^ (2 * m + 1))‖ ≤
      (2 : ℝ) ^ n * ((5 : ℝ) / 4) ^ (n - 1) /
        (p : ℝ) ^ (m * (n - 2) - 1) := by
  have h := norm_singularSeriesTerm_primePower_odd_le
    (p := p) (m := m) (n := n) (T := T) hp hp5 hm
  rw [Nat.totient_prime_pow hp (by omega : 0 < 2 * m + 1)] at h
  have htwo : 2 * m + 1 - 1 = 2 * m := by omega
  rw [htwo] at h
  have hpR : 0 < (p : ℝ) := by
    exact_mod_cast NeZero.pos p
  have hpm1R : 0 < (p : ℝ) - 1 := by
    rw [← Nat.cast_one, ← Nat.cast_sub (by omega : 1 ≤ p)]
    exact_mod_cast (show 0 < p - 1 by omega)
  have htotR : 0 < (p : ℝ) ^ (2 * m) * ((p : ℝ) - 1) := by positivity
  have hnorminv :
      ‖((↑(p ^ (2 * m) * (p - 1)) : ℂ)⁻¹)‖ =
        ((p : ℝ) ^ (2 * m) * ((p : ℝ) - 1))⁻¹ := by
    calc
      ‖((↑(p ^ (2 * m) * (p - 1)) : ℂ)⁻¹)‖ =
          (↑(p ^ (2 * m) * (p - 1)) : ℝ)⁻¹ := by simp [norm_inv]
      _ = ((p : ℝ) ^ (2 * m) * ((p : ℝ) - 1))⁻¹ := by
        rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub (by omega : 1 ≤ p)]
        norm_num
  rw [hnorminv] at h
  have htotcast :
      (↑(p ^ (2 * m) * (p - 1)) : ℝ) =
        (p : ℝ) ^ (2 * m) * ((p : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub (by omega : 1 ≤ p)]
    norm_num
  rw [htotcast] at h
  have hratio : (p : ℝ) / ((p : ℝ) - 1) ≤ (5 : ℝ) / 4 := by
    rw [div_le_iff₀ hpm1R]
    have hp5R : (5 : ℝ) ≤ p := by exact_mod_cast hp5
    linarith
  have hratio_pow := pow_le_pow_left₀
    (by positivity : 0 ≤ (p : ℝ) / ((p : ℝ) - 1)) hratio (n - 1)
  have hform :
      ((p : ℝ) ^ (2 * m) * ((p : ℝ) - 1))⁻¹ ^ n *
          ((p : ℝ) ^ (2 * m) * ((p : ℝ) - 1)) *
          (2 * (p : ℝ) ^ (m + 1)) ^ n =
        (2 : ℝ) ^ n * ((p : ℝ) / ((p : ℝ) - 1)) ^ (n - 1) /
          (p : ℝ) ^ (m * (n - 2) - 1) := by
    rw [inv_pow, mul_pow, mul_pow, div_pow]
    have hmexp : 1 ≤ m * (n - 2) := by
      have hpos : 0 < m * (n - 2) :=
        Nat.mul_pos (by omega) (by omega)
      omega
    have hexp :
        (m + 1) * n + (m * (n - 2) - 1) + 2 * m =
          (2 * m) * n + (n - 1) := by
      apply Nat.cast_injective (R := ℤ)
      push_cast
      rw [Nat.cast_sub hmexp, Nat.cast_sub (by omega : 1 ≤ n)]
      push_cast
      rw [Nat.cast_sub (by omega : 2 ≤ n)]
      push_cast
      ring
    have hpows :
        (p : ℝ) ^ ((m + 1) * n) * (p : ℝ) ^ (m * (n - 2) - 1) *
            (p : ℝ) ^ (2 * m) =
          (p : ℝ) ^ ((2 * m) * n) * (p : ℝ) ^ (n - 1) := by
      calc
        (p : ℝ) ^ ((m + 1) * n) * (p : ℝ) ^ (m * (n - 2) - 1) *
            (p : ℝ) ^ (2 * m) =
            (p : ℝ) ^ ((m + 1) * n + (m * (n - 2) - 1) + 2 * m) := by
              rw [← pow_add, ← pow_add]
        _ = (p : ℝ) ^ ((2 * m) * n + (n - 1)) := by rw [hexp]
        _ = (p : ℝ) ^ ((2 * m) * n) * (p : ℝ) ^ (n - 1) := by
              rw [pow_add]
    have hsubpow : ((p : ℝ) - 1) ^ (n - 1) * ((p : ℝ) - 1) =
        ((p : ℝ) - 1) ^ n := by
      calc
        ((p : ℝ) - 1) ^ (n - 1) * ((p : ℝ) - 1) =
            ((p : ℝ) - 1) ^ (n - 1) * ((p : ℝ) - 1) ^ 1 := by
              rw [pow_one]
        _ = ((p : ℝ) - 1) ^ ((n - 1) + 1) := by rw [pow_add]
        _ = ((p : ℝ) - 1) ^ n := by
              rw [show (n - 1) + 1 = n by omega]
    field_simp [htotR.ne', hpR.ne', hpm1R.ne']
    calc
      _ = ((p : ℝ) - 1) *
          ((p : ℝ) ^ ((m + 1) * n) * (p : ℝ) ^ (m * (n - 2) - 1) *
            (p : ℝ) ^ (2 * m) * ((p : ℝ) - 1) ^ (n - 1)) := by ring
      _ = ((p : ℝ) - 1) *
          ((p : ℝ) ^ ((2 * m) * n) * (p : ℝ) ^ (n - 1) *
            ((p : ℝ) - 1) ^ (n - 1)) := by rw [hpows]
      _ = _ := by
        rw [show ((p : ℝ) - 1) *
            ((p : ℝ) ^ ((2 * m) * n) * (p : ℝ) ^ (n - 1) *
              ((p : ℝ) - 1) ^ (n - 1)) =
            (p : ℝ) ^ ((2 * m) * n) * (p : ℝ) ^ (n - 1) *
              (((p : ℝ) - 1) ^ (n - 1) * ((p : ℝ) - 1)) by ring]
        rw [hsubpow, pow_mul]
        ring
  rw [hform] at h
  apply h.trans
  apply div_le_div_of_nonneg_right
  · exact mul_le_mul_of_nonneg_left hratio_pow (by positivity)
  · positivity

noncomputable def Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant (n : ℕ) : ℝ :=
  (2 : ℝ) ^ n * ((5 : ℝ) / 4) ^ (n - 1)

noncomputable def Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio (p n : ℕ) : ℝ :=
  ((p : ℝ)⁻¹) ^ (n - 2)

private theorem higherPrimePowerTail_ratio_nonneg_lt_one
    {p n : ℕ} (hp : p.Prime) (hn : 33 ≤ n) :
    0 ≤ Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n ∧ Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n < 1 := by
  have hpR : 0 < (p : ℝ) := by
    exact_mod_cast hp.pos
  have hpone : (1 : ℝ) < p := by
    exact_mod_cast hp.one_lt
  constructor
  · exact pow_nonneg (inv_nonneg.mpr hpR.le) _
  · apply pow_lt_one₀ (inv_nonneg.mpr hpR.le)
      (inv_lt_one_of_one_lt₀ hpone)
    omega

private theorem higherPrimePowerTail_even_rewrite (p m n : ℕ) :
    Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant n / (p : ℝ) ^ (m * (n - 2)) =
      Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant n * Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n ^ m := by
  dsimp [Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant, Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio]
  rw [← pow_mul, inv_pow]
  congr 2
  rw [Nat.mul_comm m (n - 2)]

private theorem higherPrimePowerTail_odd_rewrite
    {p m n : ℕ} [NeZero p] (hm : 1 ≤ m) (hn : 33 ≤ n) :
    Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant n / (p : ℝ) ^ (m * (n - 2) - 1) =
      Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant n * (p : ℝ) *
        Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n ^ m := by
  have hpR : 0 < (p : ℝ) := by
    exact_mod_cast NeZero.pos p
  dsimp [Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant, Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio]
  rw [← pow_mul, inv_pow]
  have hpos : 1 ≤ m * (n - 2) := by
    have : 0 < m * (n - 2) := Nat.mul_pos (by omega) (by omega)
    omega
  have hpow : (p : ℝ) ^ (m * (n - 2)) =
      (p : ℝ) ^ (m * (n - 2) - 1) * (p : ℝ) := by
    calc
      (p : ℝ) ^ (m * (n - 2)) =
          (p : ℝ) ^ ((m * (n - 2) - 1) + 1) := by
            exact congrArg (fun e : ℕ ↦ (p : ℝ) ^ e)
              (show m * (n - 2) = (m * (n - 2) - 1) + 1 by omega)
      _ = (p : ℝ) ^ (m * (n - 2) - 1) * (p : ℝ) ^ 1 := by rw [pow_add]
      _ = (p : ℝ) ^ (m * (n - 2) - 1) * (p : ℝ) := by rw [pow_one]
  have hpow' : (p : ℝ) ^ ((n - 2) * m) =
      (p : ℝ) ^ (m * (n - 2) - 1) * (p : ℝ) := by
    rw [Nat.mul_comm (n - 2) m]
    exact hpow
  rw [hpow']
  field_simp [hpR.ne']

private theorem norm_singularSeriesTerm_primePower_even_le_tailMajorant
    {p m n T : ℕ} [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 33 ≤ n) :
    ‖singularSeriesTerm n T (p ^ (2 * (m + 1)))‖ ≤
      Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant n * Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n ^ (m + 1) := by
  rw [← higherPrimePowerTail_even_rewrite]
  exact norm_singularSeriesTerm_primePower_even_le_geometric hp hp5 (by omega) hn

private theorem norm_singularSeriesTerm_primePower_odd_le_tailMajorant
    {p m n T : ℕ} [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 33 ≤ n) :
    ‖singularSeriesTerm n T (p ^ (2 * (m + 1) + 1))‖ ≤
      Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant n * (p : ℝ) *
        Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n ^ (m + 1) := by
  rw [← higherPrimePowerTail_odd_rewrite (m := m + 1) (by omega) hn]
  exact norm_singularSeriesTerm_primePower_odd_le_geometric hp hp5 (by omega) hn

private theorem singularSeriesTermNormMaximum_primePower_even_le_tailMajorant
    {p m n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 33 ≤ n) :
    singularSeriesTermNormMaximum n (p ^ (2 * (m + 1))) ≤
      Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant n * Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n ^ (m + 1) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hq : 0 < p ^ (2 * (m + 1)) := Nat.pow_pos hp.pos
  obtain ⟨t, ht⟩ := singularSeriesTermNormMaximum_attained n
    (p ^ (2 * (m + 1))) hq
  rw [ht]
  rw [← higherPrimePowerTail_even_rewrite]
  exact norm_singularSeriesTerm_primePower_even_le_geometric
    (T := t.val) hp hp5 (by omega) hn

private theorem singularSeriesTermNormMaximum_primePower_odd_le_tailMajorant
    {p m n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 33 ≤ n) :
    singularSeriesTermNormMaximum n (p ^ (2 * (m + 1) + 1)) ≤
      Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant n * (p : ℝ) *
        Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n ^ (m + 1) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hq : 0 < p ^ (2 * (m + 1) + 1) := Nat.pow_pos hp.pos
  obtain ⟨t, ht⟩ := singularSeriesTermNormMaximum_attained n
    (p ^ (2 * (m + 1) + 1)) hq
  rw [ht]
  rw [← higherPrimePowerTail_odd_rewrite (m := m + 1) (by omega) hn]
  exact norm_singularSeriesTerm_primePower_odd_le_geometric
    (T := t.val) hp hp5 (by omega) hn

private theorem summable_higherPrimePowerTail_evenMajorant
    {p n : ℕ} (hp : p.Prime) (hn : 33 ≤ n) :
    Summable fun m : ℕ ↦
      Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant n * Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n ^ (m + 1) := by
  rcases higherPrimePowerTail_ratio_nonneg_lt_one hp hn with ⟨hr_nonneg, hr_lt⟩
  have hgeom : Summable fun m : ℕ ↦ Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n ^ m :=
    summable_geometric_of_lt_one hr_nonneg hr_lt
  exact Summable.congr
    (Summable.mul_left
      (Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant n * Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n) hgeom)
    (fun m ↦ by rw [pow_succ]; ring)

private theorem summable_higherPrimePowerTail_oddMajorant
    {p n : ℕ} (hp : p.Prime) (hn : 33 ≤ n) :
    Summable fun m : ℕ ↦
      Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant n * (p : ℝ) *
        Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n ^ (m + 1) := by
  rcases higherPrimePowerTail_ratio_nonneg_lt_one hp hn with ⟨hr_nonneg, hr_lt⟩
  have hgeom : Summable fun m : ℕ ↦ Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n ^ m :=
    summable_geometric_of_lt_one hr_nonneg hr_lt
  exact Summable.congr
    (Summable.mul_left
      (Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant n * (p : ℝ) * Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n) hgeom)
    (fun m ↦ by rw [pow_succ]; ring)

private theorem summable_singularSeriesTermNormMaximum_higherPrimePower_evenPart
    {p n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 33 ≤ n) :
    Summable fun m : ℕ ↦
      singularSeriesTermNormMaximum n (p ^ (2 * (m + 1))) := by
  have hnonneg (m : ℕ) :
      0 ≤ singularSeriesTermNormMaximum n (p ^ (2 * (m + 1))) := by
    obtain ⟨t, ht⟩ := singularSeriesTermNormMaximum_attained n
      (p ^ (2 * (m + 1))) (Nat.pow_pos hp.pos)
    rw [ht]
    exact norm_nonneg _
  exact (summable_higherPrimePowerTail_evenMajorant hp hn).of_nonneg_of_le
    hnonneg
    (fun m ↦ singularSeriesTermNormMaximum_primePower_even_le_tailMajorant hp hp5 hn)

private theorem summable_singularSeriesTermNormMaximum_higherPrimePower_oddPart
    {p n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 33 ≤ n) :
    Summable fun m : ℕ ↦
      singularSeriesTermNormMaximum n (p ^ (2 * (m + 1) + 1)) := by
  have hnonneg (m : ℕ) :
      0 ≤ singularSeriesTermNormMaximum n (p ^ (2 * (m + 1) + 1)) := by
    obtain ⟨t, ht⟩ := singularSeriesTermNormMaximum_attained n
      (p ^ (2 * (m + 1) + 1)) (Nat.pow_pos hp.pos)
    rw [ht]
    exact norm_nonneg _
  exact (summable_higherPrimePowerTail_oddMajorant hp hn).of_nonneg_of_le
    hnonneg
    (fun m ↦ singularSeriesTermNormMaximum_primePower_odd_le_tailMajorant hp hp5 hn)

private theorem summable_singularSeriesTermNormMaximum_higherPrimePower_tail
    {p n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 33 ≤ n) :
    Summable fun k : ℕ ↦ singularSeriesTermNormMaximum n (p ^ (k + 2)) := by
  apply Summable.even_add_odd
  · convert summable_singularSeriesTermNormMaximum_higherPrimePower_evenPart hp hp5 hn using 1
  · convert summable_singularSeriesTermNormMaximum_higherPrimePower_oddPart hp hp5 hn using 1

/-- The maximum coefficient norms above the prime level form a summable
prime-power tail, uniformly over all target residues. -/
theorem summable_singularSeriesTermNormMaximum_higherPrimePower
    {p n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 33 ≤ n) :
    Summable fun k : ℕ ↦ singularSeriesTermNormMaximum n (p ^ (k + 2)) :=
  summable_singularSeriesTermNormMaximum_higherPrimePower_tail hp hp5 hn

private theorem summable_norm_singularSeriesTerm_higherPrimePower_evenPart
    {p n T : ℕ} [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 33 ≤ n) :
    Summable fun m : ℕ ↦ ‖singularSeriesTerm n T (p ^ (2 * (m + 1)))‖ := by
  exact (summable_higherPrimePowerTail_evenMajorant hp hn).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _)
    (fun m ↦ norm_singularSeriesTerm_primePower_even_le_tailMajorant
      (p := p) (m := m) (n := n) (T := T) hp hp5 hn)

private theorem summable_norm_singularSeriesTerm_higherPrimePower_oddPart
    {p n T : ℕ} [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 33 ≤ n) :
    Summable fun m : ℕ ↦ ‖singularSeriesTerm n T (p ^ (2 * (m + 1) + 1))‖ := by
  exact (summable_higherPrimePowerTail_oddMajorant hp hn).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _)
    (fun m ↦ norm_singularSeriesTerm_primePower_odd_le_tailMajorant
      (p := p) (m := m) (n := n) (T := T) hp hp5 hn)

private theorem summable_norm_singularSeriesTerm_higherPrimePower_tail
    {p n T : ℕ} [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 33 ≤ n) :
    Summable fun k : ℕ ↦ ‖singularSeriesTerm n T (p ^ (k + 2))‖ := by
  apply Summable.even_add_odd
  · convert summable_norm_singularSeriesTerm_higherPrimePower_evenPart hp hp5 hn using 1
  · convert summable_norm_singularSeriesTerm_higherPrimePower_oddPart hp hp5 hn using 1

private theorem tsum_shifted_even_add_odd
    (f : ℕ → ℝ)
    (hEven : Summable fun m : ℕ ↦ f (2 * (m + 1)))
    (hOdd : Summable fun m : ℕ ↦ f (2 * (m + 1) + 1)) :
    (∑' k : ℕ, f (k + 2)) =
      (∑' m : ℕ, f (2 * (m + 1))) +
        ∑' m : ℕ, f (2 * (m + 1) + 1) := by
  have hEvenEq :
      (fun m : ℕ ↦ (fun k : ℕ ↦ f (k + 2)) (2 * m)) =
        fun m : ℕ ↦ f (2 * (m + 1)) := by
    funext m
    exact congrArg f (by omega)
  have hOddEq :
      (fun m : ℕ ↦ (fun k : ℕ ↦ f (k + 2)) (2 * m + 1)) =
        fun m : ℕ ↦ f (2 * (m + 1) + 1) := by
    funext m
    exact congrArg f (by omega)
  have hEven' : Summable fun m : ℕ ↦ (fun k : ℕ ↦ f (k + 2)) (2 * m) := by
    rw [hEvenEq]
    exact hEven
  have hOdd' : Summable fun m : ℕ ↦ (fun k : ℕ ↦ f (k + 2)) (2 * m + 1) := by
    rw [hOddEq]
    exact hOdd
  have hsum : HasSum (fun k : ℕ ↦ f (k + 2))
      ((∑' m : ℕ, f (2 * (m + 1))) +
        ∑' m : ℕ, f (2 * (m + 1) + 1)) := by
    rw [← hEvenEq, ← hOddEq]
    exact hEven'.hasSum.even_add_odd hOdd'.hasSum
  exact hsum.tsum_eq

private theorem tsum_higherPrimePowerTail_evenMajorant
    {p n : ℕ} (hp : p.Prime) (hn : 33 ≤ n) :
    (∑' m : ℕ,
      Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant n * Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n ^ (m + 1)) =
        Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant n * Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n /
          (1 - Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n) := by
  rcases higherPrimePowerTail_ratio_nonneg_lt_one hp hn with ⟨hr_nonneg, hr_lt⟩
  calc
    (∑' m : ℕ,
      Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant n * Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n ^ (m + 1)) =
        ∑' m : ℕ,
          (Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant n * Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n) *
            Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n ^ m := by
              apply tsum_congr
              intro m
              rw [pow_succ]
              ring
    _ = (Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant n * Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n) *
          ∑' m : ℕ, Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n ^ m := tsum_mul_left
    _ = Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant n * Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n /
          (1 - Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n) := by
            rw [tsum_geometric_of_lt_one hr_nonneg hr_lt]
            ring

private theorem tsum_higherPrimePowerTail_oddMajorant
    {p n : ℕ} (hp : p.Prime) (hn : 33 ≤ n) :
    (∑' m : ℕ,
      Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant n * (p : ℝ) *
        Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n ^ (m + 1)) =
        Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant n * (p : ℝ) * Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n /
          (1 - Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n) := by
  rcases higherPrimePowerTail_ratio_nonneg_lt_one hp hn with ⟨hr_nonneg, hr_lt⟩
  calc
    (∑' m : ℕ,
      Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant n * (p : ℝ) *
        Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n ^ (m + 1)) =
        ∑' m : ℕ,
          (Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant n * (p : ℝ) * Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n) *
            Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n ^ m := by
              apply tsum_congr
              intro m
              rw [pow_succ]
              ring
    _ = (Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant n * (p : ℝ) * Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n) *
          ∑' m : ℕ, Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n ^ m := tsum_mul_left
    _ = Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant n * (p : ℝ) * Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n /
          (1 - Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n) := by
            rw [tsum_geometric_of_lt_one hr_nonneg hr_lt]
            ring

private theorem tsum_singularSeriesTermNormMaximum_higherPrimePower_evenPart_le
    {p n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 33 ≤ n) :
    (∑' m : ℕ,
      singularSeriesTermNormMaximum n (p ^ (2 * (m + 1)))) ≤
        Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant n * Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n /
          (1 - Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n) := by
  calc
    (∑' m : ℕ,
      singularSeriesTermNormMaximum n (p ^ (2 * (m + 1)))) ≤
        ∑' m : ℕ,
          Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant n * Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n ^ (m + 1) :=
      Summable.tsum_le_tsum
        (fun m ↦ singularSeriesTermNormMaximum_primePower_even_le_tailMajorant hp hp5 hn)
        (summable_singularSeriesTermNormMaximum_higherPrimePower_evenPart hp hp5 hn)
        (summable_higherPrimePowerTail_evenMajorant hp hn)
    _ = Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant n * Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n /
          (1 - Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n) :=
      tsum_higherPrimePowerTail_evenMajorant hp hn

private theorem tsum_singularSeriesTermNormMaximum_higherPrimePower_oddPart_le
    {p n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 33 ≤ n) :
    (∑' m : ℕ,
      singularSeriesTermNormMaximum n (p ^ (2 * (m + 1) + 1))) ≤
        Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant n * (p : ℝ) * Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n /
          (1 - Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n) := by
  calc
    (∑' m : ℕ,
      singularSeriesTermNormMaximum n (p ^ (2 * (m + 1) + 1))) ≤
        ∑' m : ℕ,
          Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant n * (p : ℝ) *
            Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n ^ (m + 1) :=
      Summable.tsum_le_tsum
        (fun m ↦ singularSeriesTermNormMaximum_primePower_odd_le_tailMajorant hp hp5 hn)
        (summable_singularSeriesTermNormMaximum_higherPrimePower_oddPart hp hp5 hn)
        (summable_higherPrimePowerTail_oddMajorant hp hn)
    _ = Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant n * (p : ℝ) * Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n /
          (1 - Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n) :=
      tsum_higherPrimePowerTail_oddMajorant hp hn

/-- A target-uniform geometric bound for the sum of the higher prime-power
coefficient maxima. -/
theorem tsum_singularSeriesTermNormMaximum_higherPrimePower_le
    {p n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 33 ≤ n) :
    (∑' k : ℕ, singularSeriesTermNormMaximum n (p ^ (k + 2))) ≤
      ((2 : ℝ) ^ n * ((5 : ℝ) / 4) ^ (n - 1)) *
        (1 + (p : ℝ)) * ((p : ℝ)⁻¹) ^ (n - 2) /
          (1 - ((p : ℝ)⁻¹) ^ (n - 2)) := by
  have hEven := tsum_singularSeriesTermNormMaximum_higherPrimePower_evenPart_le hp hp5 hn
  have hOdd := tsum_singularSeriesTermNormMaximum_higherPrimePower_oddPart_le hp hp5 hn
  calc
    (∑' k : ℕ, singularSeriesTermNormMaximum n (p ^ (k + 2))) =
        (∑' m : ℕ, singularSeriesTermNormMaximum n (p ^ (2 * (m + 1)))) +
          ∑' m : ℕ, singularSeriesTermNormMaximum n (p ^ (2 * (m + 1) + 1)) := by
            exact tsum_shifted_even_add_odd
              (fun q ↦ singularSeriesTermNormMaximum n (p ^ q))
              (summable_singularSeriesTermNormMaximum_higherPrimePower_evenPart hp hp5 hn)
              (summable_singularSeriesTermNormMaximum_higherPrimePower_oddPart hp hp5 hn)
    _ ≤ Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant n * Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n /
          (1 - Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n) +
        Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant n * (p : ℝ) * Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n /
          (1 - Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n) := add_le_add hEven hOdd
    _ = ((2 : ℝ) ^ n * ((5 : ℝ) / 4) ^ (n - 1)) *
          (1 + (p : ℝ)) * ((p : ℝ)⁻¹) ^ (n - 2) /
            (1 - ((p : ℝ)⁻¹) ^ (n - 2)) := by
              simp only [Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant, Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio]
              ring

private theorem tsum_norm_singularSeriesTerm_higherPrimePower_evenPart_le
    {p n T : ℕ} [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 33 ≤ n) :
    (∑' m : ℕ, ‖singularSeriesTerm n T (p ^ (2 * (m + 1)))‖) ≤
      Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant n * Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n /
        (1 - Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n) := by
  calc
    (∑' m : ℕ, ‖singularSeriesTerm n T (p ^ (2 * (m + 1)))‖) ≤
        ∑' m : ℕ,
          Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant n * Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n ^ (m + 1) :=
            Summable.tsum_le_tsum
              (fun m ↦ norm_singularSeriesTerm_primePower_even_le_tailMajorant
                (p := p) (m := m) (n := n) (T := T) hp hp5 hn)
              (summable_norm_singularSeriesTerm_higherPrimePower_evenPart hp hp5 hn)
              (summable_higherPrimePowerTail_evenMajorant hp hn)
    _ = Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant n * Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n /
          (1 - Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n) :=
            tsum_higherPrimePowerTail_evenMajorant hp hn

private theorem tsum_norm_singularSeriesTerm_higherPrimePower_oddPart_le
    {p n T : ℕ} [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 33 ≤ n) :
    (∑' m : ℕ, ‖singularSeriesTerm n T (p ^ (2 * (m + 1) + 1))‖) ≤
      Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant n * (p : ℝ) * Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n /
        (1 - Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n) := by
  calc
    (∑' m : ℕ, ‖singularSeriesTerm n T (p ^ (2 * (m + 1) + 1))‖) ≤
        ∑' m : ℕ,
          Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant n * (p : ℝ) *
            Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n ^ (m + 1) :=
            Summable.tsum_le_tsum
              (fun m ↦ norm_singularSeriesTerm_primePower_odd_le_tailMajorant
                (p := p) (m := m) (n := n) (T := T) hp hp5 hn)
              (summable_norm_singularSeriesTerm_higherPrimePower_oddPart hp hp5 hn)
              (summable_higherPrimePowerTail_oddMajorant hp hn)
    _ = Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant n * (p : ℝ) * Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n /
          (1 - Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n) :=
            tsum_higherPrimePowerTail_oddMajorant hp hn

private theorem tsum_norm_singularSeriesTerm_higherPrimePower_tail_le
    {p n T : ℕ} [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 33 ≤ n) :
    (∑' k : ℕ, ‖singularSeriesTerm n T (p ^ (k + 2))‖) ≤
      Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant n * (1 + (p : ℝ)) * Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n /
        (1 - Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n) := by
  have hEven := tsum_norm_singularSeriesTerm_higherPrimePower_evenPart_le
    (p := p) (n := n) (T := T) hp hp5 hn
  have hOdd := tsum_norm_singularSeriesTerm_higherPrimePower_oddPart_le
    (p := p) (n := n) (T := T) hp hp5 hn
  calc
    (∑' k : ℕ, ‖singularSeriesTerm n T (p ^ (k + 2))‖) =
        (∑' m : ℕ, ‖singularSeriesTerm n T (p ^ (2 * (m + 1)))‖) +
          ∑' m : ℕ, ‖singularSeriesTerm n T (p ^ (2 * (m + 1) + 1))‖ := by
            exact tsum_shifted_even_add_odd
              (fun q ↦ ‖singularSeriesTerm n T (p ^ q)‖)
              (summable_norm_singularSeriesTerm_higherPrimePower_evenPart hp hp5 hn)
              (summable_norm_singularSeriesTerm_higherPrimePower_oddPart hp hp5 hn)
    _ ≤
        Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant n * Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n /
            (1 - Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n) +
          Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant n * (p : ℝ) * Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n /
            (1 - Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n) := add_le_add hEven hOdd
    _ = Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant n * (1 + (p : ℝ)) *
          Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n /
            (1 - Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio p n) := by ring

/-- Absolute summability of all terms at powers `p^k` with `k ≥ 2`. -/
theorem summable_norm_singularSeriesTerm_higherPrimePower
    {p n T : ℕ} [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 33 ≤ n) :
    Summable fun k : ℕ ↦ ‖singularSeriesTerm n T (p ^ (k + 2))‖ :=
  summable_norm_singularSeriesTerm_higherPrimePower_tail hp hp5 hn

/-- An explicit target-uniform bound for the full tail above the prime
modulus.  Its ratio is `p⁻(n-2)`, hence is summable with substantial room
when `n ≥ 33`. -/
theorem tsum_norm_singularSeriesTerm_higherPrimePower_le
    {p n T : ℕ} [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 33 ≤ n) :
    (∑' k : ℕ, ‖singularSeriesTerm n T (p ^ (k + 2))‖) ≤
      ((2 : ℝ) ^ n * ((5 : ℝ) / 4) ^ (n - 1)) *
        (1 + (p : ℝ)) * ((p : ℝ)⁻¹) ^ (n - 2) /
          (1 - ((p : ℝ)⁻¹) ^ (n - 2)) :=
  by
    simpa [Internal.PrimePowerTailHelpers.higherPrimePowerTailConstant, Internal.PrimePowerTailHelpers.higherPrimePowerTailRatio] using
      (tsum_norm_singularSeriesTerm_higherPrimePower_tail_le hp hp5 hn)

end CookMagyarPrimePower
end SystolicGrowth

#print axioms SystolicGrowth.CookMagyarPrimePower.summable_singularSeriesTermNormMaximum_higherPrimePower
