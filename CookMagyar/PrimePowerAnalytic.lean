module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.PrimePowerRemoval

@[expose] public section

open MeasureTheory
open scoped ArithmeticFunction BigOperators

namespace SystolicGrowth
namespace CookMagyarCircle

/-! # Analytic bookkeeping for removing prime powers

This file separates the cubic von--Mangoldt exponential sum into its
odd-prime and non-odd-prime parts.  It also proves the elementary estimates
used in the prime-power-removal step.  The only genuinely analytic datum in
the final estimate is a uniform bound for the bad sum; no asymptotic estimate
is assumed or proved here.
-/

/-- The part of the cubic exponential sum supported on odd primes. -/
noncomputable def cubicOddPrimeExpSum (α : ℝ) (N : ℕ) : ℂ := by
  classical
  exact ∑ x : Fin (N + 1),
    if IsOddPrime (x : ℕ) then
      (ArithmeticFunction.vonMangoldt x : ℂ) * addChar α (primeCubic x)
    else 0

/-- The complementary part, supported on prime powers which are not odd
primes (and harmless zero-weight integers). -/
noncomputable def cubicBadPrimePowerExpSum (α : ℝ) (N : ℕ) : ℂ := by
  classical
  exact ∑ x : Fin (N + 1),
    if ¬IsOddPrime (x : ℕ) then
      (ArithmeticFunction.vonMangoldt x : ℂ) * addChar α (primeCubic x)
    else 0

/-- Exact pointwise decomposition `S = P + E`. -/
theorem cubicVonMangoldtExpSum_eq_oddPrime_add_bad (α : ℝ) (N : ℕ) :
    cubicVonMangoldtExpSum α N =
      cubicOddPrimeExpSum α N + cubicBadPrimePowerExpSum α N := by
  classical
  unfold cubicVonMangoldtExpSum cubicOddPrimeExpSum cubicBadPrimePowerExpSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _hx
  by_cases hp : IsOddPrime (x : ℕ) <;> simp [hp]

/-- The total von--Mangoldt mass on the summation interval. -/
noncomputable def cubicVonMangoldtMass (N : ℕ) : ℝ :=
  ∑ x : Fin (N + 1), ArithmeticFunction.vonMangoldt x

/-- The mass of the non-odd-prime part.  It is an elementary explicit
upper bound for the `L∞` norm of `E`. -/
noncomputable def cubicBadPrimePowerMass (N : ℕ) : ℝ := by
  classical
  exact ∑ x : Fin (N + 1),
    if ¬IsOddPrime (x : ℕ) then ArithmeticFunction.vonMangoldt x else 0

theorem cubicVonMangoldtMass_nonneg (N : ℕ) :
    0 ≤ cubicVonMangoldtMass N := by
  unfold cubicVonMangoldtMass
  exact Finset.sum_nonneg fun x _hx ↦ ArithmeticFunction.vonMangoldt_nonneg

theorem cubicBadPrimePowerMass_nonneg (N : ℕ) :
    0 ≤ cubicBadPrimePowerMass N := by
  classical
  unfold cubicBadPrimePowerMass
  exact Finset.sum_nonneg fun x _hx ↦ by
    by_cases hp : ¬IsOddPrime (x : ℕ)
    · simp only [hp]
      exact ArithmeticFunction.vonMangoldt_nonneg
    · simp [hp]

private theorem norm_vonMangoldt_mul_addChar (α : ℝ) (x : ℕ) :
    ‖(ArithmeticFunction.vonMangoldt x : ℂ) * addChar α (primeCubic x)‖ =
      ArithmeticFunction.vonMangoldt x := by
  rw [norm_mul, norm_addChar]
  simp only [mul_one, Complex.norm_real]
  exact abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg

/-- The elementary `L∞` bound for the full cubic sum. -/
theorem norm_cubicVonMangoldtExpSum_le_mass (α : ℝ) (N : ℕ) :
    ‖cubicVonMangoldtExpSum α N‖ ≤ cubicVonMangoldtMass N := by
  unfold cubicVonMangoldtExpSum cubicVonMangoldtMass
  calc
    ‖∑ x : Fin (N + 1),
        (ArithmeticFunction.vonMangoldt x : ℂ) * addChar α (primeCubic x)‖
        ≤ ∑ x : Fin (N + 1),
            ‖(ArithmeticFunction.vonMangoldt x : ℂ) *
              addChar α (primeCubic x)‖ := norm_sum_le _ _
    _ = ∑ x : Fin (N + 1), ArithmeticFunction.vonMangoldt x := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact norm_vonMangoldt_mul_addChar α x

/-- The same mass bound for the odd-prime part. -/
theorem norm_cubicOddPrimeExpSum_le_mass (α : ℝ) (N : ℕ) :
    ‖cubicOddPrimeExpSum α N‖ ≤ cubicVonMangoldtMass N := by
  classical
  unfold cubicOddPrimeExpSum cubicVonMangoldtMass
  calc
    ‖∑ x : Fin (N + 1),
        if IsOddPrime (x : ℕ) then
          (ArithmeticFunction.vonMangoldt x : ℂ) * addChar α (primeCubic x)
        else 0‖
        ≤ ∑ x : Fin (N + 1),
            ‖if IsOddPrime (x : ℕ) then
                (ArithmeticFunction.vonMangoldt x : ℂ) *
                  addChar α (primeCubic x)
              else 0‖ := norm_sum_le _ _
    _ ≤ ∑ x : Fin (N + 1), ArithmeticFunction.vonMangoldt x := by
      apply Finset.sum_le_sum
      intro x _hx
      by_cases hp : IsOddPrime (x : ℕ)
      · simp only [hp, if_true]
        rw [norm_vonMangoldt_mul_addChar]
      · simp [hp, ArithmeticFunction.vonMangoldt_nonneg]

/-- The coefficient mass is a uniform bound for the bad exponential sum. -/
theorem norm_cubicBadPrimePowerExpSum_le_mass (α : ℝ) (N : ℕ) :
    ‖cubicBadPrimePowerExpSum α N‖ ≤ cubicBadPrimePowerMass N := by
  classical
  unfold cubicBadPrimePowerExpSum cubicBadPrimePowerMass
  calc
    ‖∑ x : Fin (N + 1),
        if ¬IsOddPrime (x : ℕ) then
          (ArithmeticFunction.vonMangoldt x : ℂ) * addChar α (primeCubic x)
        else 0‖
        ≤ ∑ x : Fin (N + 1),
            ‖if ¬IsOddPrime (x : ℕ) then
                (ArithmeticFunction.vonMangoldt x : ℂ) *
                  addChar α (primeCubic x)
              else 0‖ := norm_sum_le _ _
    _ = ∑ x : Fin (N + 1),
          if ¬IsOddPrime (x : ℕ) then ArithmeticFunction.vonMangoldt x else 0 := by
      apply Finset.sum_congr rfl
      intro x _hx
      by_cases hp : IsOddPrime (x : ℕ)
      · simp [hp]
      · simp [hp]

/-- Exact telescoping factorization of the difference between the full and
odd-prime powers. -/
theorem cubic_power_sub_oddPrime_power (α : ℝ) (N n : ℕ) :
    (cubicVonMangoldtExpSum α N) ^ n - (cubicOddPrimeExpSum α N) ^ n =
      cubicBadPrimePowerExpSum α N *
        ∑ j ∈ Finset.range n,
          (cubicVonMangoldtExpSum α N) ^ j *
            (cubicOddPrimeExpSum α N) ^ (n - 1 - j) := by
  let S := cubicVonMangoldtExpSum α N
  let P := cubicOddPrimeExpSum α N
  let E := cubicBadPrimePowerExpSum α N
  have hsplit : S = P + E := cubicVonMangoldtExpSum_eq_oddPrime_add_bad α N
  have hgeom := geom_sum₂_mul S P n
  dsimp only [S, P, E] at hgeom ⊢
  calc
    cubicVonMangoldtExpSum α N ^ n - cubicOddPrimeExpSum α N ^ n =
        (∑ j ∈ Finset.range n,
            cubicVonMangoldtExpSum α N ^ j *
              cubicOddPrimeExpSum α N ^ (n - 1 - j)) *
          (cubicVonMangoldtExpSum α N -
            cubicOddPrimeExpSum α N) := hgeom.symm
    _ = cubicBadPrimePowerExpSum α N *
        ∑ j ∈ Finset.range n,
          cubicVonMangoldtExpSum α N ^ j *
            cubicOddPrimeExpSum α N ^ (n - 1 - j) := by
          rw [cubicVonMangoldtExpSum_eq_oddPrime_add_bad]
          ring

/-- Quantitative telescoping bound.  Both good and full sums are bounded by
the same coefficient mass. -/
theorem norm_cubic_power_sub_oddPrime_power_le (α : ℝ) (N n : ℕ) :
    ‖(cubicVonMangoldtExpSum α N) ^ n -
        (cubicOddPrimeExpSum α N) ^ n‖ ≤
      ‖cubicBadPrimePowerExpSum α N‖ *
        ((n : ℝ) * (cubicVonMangoldtMass N) ^ (n - 1)) := by
  rw [cubic_power_sub_oddPrime_power, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    ‖∑ j ∈ Finset.range n,
        cubicVonMangoldtExpSum α N ^ j *
          cubicOddPrimeExpSum α N ^ (n - 1 - j)‖
        ≤ ∑ j ∈ Finset.range n,
            ‖cubicVonMangoldtExpSum α N ^ j *
              cubicOddPrimeExpSum α N ^ (n - 1 - j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range n,
          (cubicVonMangoldtMass N) ^ (n - 1) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul, norm_pow, norm_pow]
      have hjlt : j < n := Finset.mem_range.mp hj
      have hS : ‖cubicVonMangoldtExpSum α N‖ ^ j ≤
          (cubicVonMangoldtMass N) ^ j :=
        pow_le_pow_left₀ (norm_nonneg _)
          (norm_cubicVonMangoldtExpSum_le_mass α N) j
      have hP : ‖cubicOddPrimeExpSum α N‖ ^ (n - 1 - j) ≤
          (cubicVonMangoldtMass N) ^ (n - 1 - j) :=
        pow_le_pow_left₀ (norm_nonneg _)
          (norm_cubicOddPrimeExpSum_le_mass α N) (n - 1 - j)
      calc
        ‖cubicVonMangoldtExpSum α N‖ ^ j *
              ‖cubicOddPrimeExpSum α N‖ ^ (n - 1 - j)
            ≤ (cubicVonMangoldtMass N) ^ j *
                (cubicVonMangoldtMass N) ^ (n - 1 - j) := by
              exact mul_le_mul hS hP (pow_nonneg (norm_nonneg _) _)
                (pow_nonneg (cubicVonMangoldtMass_nonneg N) _)
        _ = (cubicVonMangoldtMass N) ^ (n - 1) := by
          rw [← pow_add]
          congr 1
          omega
    _ = (n : ℝ) * (cubicVonMangoldtMass N) ^ (n - 1) := by simp

/-- The eighth moment of the full cubic von--Mangoldt exponential sum over
one period. -/
noncomputable def cubicVonMangoldtEighthMoment (N : ℕ) : ℝ :=
  ∫ α in Set.Icc (0 : ℝ) 1, ‖cubicVonMangoldtExpSum α N‖ ^ 8

private theorem continuous_cubicVonMangoldtExpSum (N : ℕ) :
    Continuous fun α : ℝ ↦ cubicVonMangoldtExpSum α N := by
  unfold cubicVonMangoldtExpSum addChar
  fun_prop

private theorem continuous_cubicBadPrimePowerExpSum (N : ℕ) :
    Continuous fun α : ℝ ↦ cubicBadPrimePowerExpSum α N := by
  classical
  unfold cubicBadPrimePowerExpSum
  apply continuous_finsetSum
  intro x _hx
  by_cases hp : IsOddPrime (x : ℕ)
  · simp only [hp, not_true_eq_false, if_false]
    exact continuous_const
  · simp only [hp, not_false_eq_true, if_true]
    unfold addChar
    fun_prop

/-- The basic eighth-moment error estimate.  If `ε` is a uniform bound for
the bad sum `E`, then for `n ≥ 9` the remaining `n-9` full-sum factors are
paid for using the elementary coefficient-mass bound. -/
theorem integral_norm_bad_mul_full_pow_le_eighthMoment
    {n N : ℕ} (hn : 9 ≤ n) {ε : ℝ} (hε : 0 ≤ ε)
    (hE : ∀ α : ℝ, ‖cubicBadPrimePowerExpSum α N‖ ≤ ε) :
    (∫ α in Set.Icc (0 : ℝ) 1,
        ‖cubicBadPrimePowerExpSum α N *
          (cubicVonMangoldtExpSum α N) ^ (n - 1)‖) ≤
      ε * (cubicVonMangoldtMass N) ^ (n - 9) *
        cubicVonMangoldtEighthMoment N := by
  let f : ℝ → ℝ := fun α ↦
    ‖cubicBadPrimePowerExpSum α N *
      (cubicVonMangoldtExpSum α N) ^ (n - 1)‖
  let g : ℝ → ℝ := fun α ↦
    (ε * (cubicVonMangoldtMass N) ^ (n - 9)) *
      ‖cubicVonMangoldtExpSum α N‖ ^ 8
  have hf : IntegrableOn f (Set.Icc (0 : ℝ) 1) := by
    apply Continuous.integrableOn_Icc
    dsimp only [f]
    exact (continuous_cubicBadPrimePowerExpSum N).mul
      ((continuous_cubicVonMangoldtExpSum N).pow _ ) |>.norm
  have hg : IntegrableOn g (Set.Icc (0 : ℝ) 1) := by
    apply Continuous.integrableOn_Icc
    dsimp only [g]
    exact continuous_const.mul ((continuous_cubicVonMangoldtExpSum N).norm.pow 8)
  have hpoint : f ≤ g := by
    intro α
    dsimp only [f, g]
    rw [norm_mul, norm_pow]
    have hexp : n - 1 = 8 + (n - 9) := by omega
    rw [hexp, pow_add]
    have hmass : 0 ≤ cubicVonMangoldtMass N := cubicVonMangoldtMass_nonneg N
    calc
      ‖cubicBadPrimePowerExpSum α N‖ *
            (‖cubicVonMangoldtExpSum α N‖ ^ 8 *
              ‖cubicVonMangoldtExpSum α N‖ ^ (n - 9))
          ≤ ε *
            (‖cubicVonMangoldtExpSum α N‖ ^ 8 *
              ‖cubicVonMangoldtExpSum α N‖ ^ (n - 9)) := by
            gcongr
            exact hE α
      _ ≤ ε *
            (‖cubicVonMangoldtExpSum α N‖ ^ 8 *
              (cubicVonMangoldtMass N) ^ (n - 9)) := by
            gcongr
            exact norm_cubicVonMangoldtExpSum_le_mass α N
      _ = (ε * (cubicVonMangoldtMass N) ^ (n - 9)) *
            ‖cubicVonMangoldtExpSum α N‖ ^ 8 := by ring
  calc
    ∫ α in Set.Icc (0 : ℝ) 1,
          ‖cubicBadPrimePowerExpSum α N *
            cubicVonMangoldtExpSum α N ^ (n - 1)‖ =
        ∫ α in Set.Icc (0 : ℝ) 1, f α := rfl
    _ ≤ ∫ α in Set.Icc (0 : ℝ) 1, g α :=
      MeasureTheory.setIntegral_mono hf hg hpoint
    _ = ε * (cubicVonMangoldtMass N) ^ (n - 9) *
          cubicVonMangoldtEighthMoment N := by
      dsimp only [g]
      rw [MeasureTheory.integral_const_mul]
      rfl

/-- Fully explicit version, using the coefficient mass as the `L∞` bound
for the bad sum. -/
theorem integral_norm_bad_mul_full_pow_le_eighthMoment_mass
    {n N : ℕ} (hn : 9 ≤ n) :
    (∫ α in Set.Icc (0 : ℝ) 1,
        ‖cubicBadPrimePowerExpSum α N *
          (cubicVonMangoldtExpSum α N) ^ (n - 1)‖) ≤
      cubicBadPrimePowerMass N *
        (cubicVonMangoldtMass N) ^ (n - 9) *
          cubicVonMangoldtEighthMoment N :=
  integral_norm_bad_mul_full_pow_le_eighthMoment hn
    (cubicBadPrimePowerMass_nonneg N)
    (fun α ↦ norm_cubicBadPrimePowerExpSum_le_mass α N)

end CookMagyarCircle
end SystolicGrowth
