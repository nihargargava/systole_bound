module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.HuaStepEight

@[expose] public section

open scoped BigOperators

namespace SystolicGrowth
namespace CookMagyarCircle

/-! # Division and boundary cases in Hua's step 8

The source pair sum recounts each eligible divisor `s` times. Dividing for
`s > 0` preserves the explicit reciprocal-`s` loss in the repeated-prime
correction. At `s = 0` only the pair family is automatically empty: the
divisor family may contain divisors with no large prime factors.
-/

/-- No pair can have one fewer than zero large prime factors. This does not
assert that the zero-large-factor divisor family is empty. -/
@[simp] theorem huaStepEightPairs_zero (H Y M parity : ℕ) (R : ℕ → Prop) :
    huaStepEightPairs H Y M 0 parity R = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  rintro ⟨p, v⟩ hpair
  have hcount := (mem_huaStepEightPairs_iff.mp hpair).2.2.2.1
  omega

/-- The repeated-prime subfamily is also empty at factor count zero. -/
@[simp] theorem huaStepEightBadPairs_zero (H Y M parity : ℕ) (R : ℕ → Prop) :
    huaStepEightBadPairs H Y M 0 parity R = ∅ := by
  classical
  simp [huaStepEightBadPairs]

/-- A repeated selected cutoff prime forces at least one cutoff factor in
`v`, so the bad branch cannot occur at `s = 1`. No positive-cutoff assumption
is needed: membership already retains `Y ≤ p`. -/
@[simp] theorem huaStepEightBadPairs_one (H Y M parity : ℕ) (R : ℕ → Prop) :
    huaStepEightBadPairs H Y M 1 parity R = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  rintro ⟨p, v⟩ hbad
  rcases Finset.mem_filter.mp hbad with ⟨hpair, hpv⟩
  rcases mem_huaStepEightPairs_iff.mp hpair with
    ⟨hpH, hvH, _, hcount, _, _⟩
  have hp := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hpH).1
  have hYp : Y ≤ p := (Finset.mem_filter.mp hpH).2
  have hvpos : 0 < v := Nat.pos_of_mem_divisors hvH
  have hpcut : p ∈ primeFactorsAtLeastCutoff Y v :=
    Finset.mem_filter.mpr
      ⟨(Nat.mem_primeFactors_of_ne_zero hvpos.ne').mpr ⟨hp, hpv⟩, hYp⟩
  have hcard : 0 < (primeFactorsAtLeastCutoff Y v).card := Finset.card_pos.mpr ⟨p, hpcut⟩
  omega

/-- A zero upper endpoint excludes every positive divisor. -/
@[simp] theorem huaStepEightDivisors_upper_zero (H Y s parity : ℕ) (R : ℕ → Prop) :
    huaStepEightDivisors H Y 0 s parity R = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro d hd
  have hd' := mem_huaStepEightDivisors_iff.mp hd
  have hpos := Nat.pos_of_mem_divisors hd'.1
  omega

/-- Both entries of a source pair are positive, so a zero upper endpoint
also excludes the pair family. -/
@[simp] theorem huaStepEightPairs_upper_zero (H Y s parity : ℕ) (R : ℕ → Prop) :
    huaStepEightPairs H Y 0 s parity R = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  rintro ⟨p, v⟩ hpair
  rcases mem_huaStepEightPairs_iff.mp hpair with ⟨hpH, hvH, hbound, _, _, _⟩
  have hp := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hpH).1
  have hprod := Nat.mul_pos hp.pos (Nat.pos_of_mem_divisors hvH)
  omega

/-- There is no bad branch when the product range is empty. -/
@[simp] theorem huaStepEightBadPairs_upper_zero (H Y s parity : ℕ) (R : ℕ → Prop) :
    huaStepEightBadPairs H Y 0 s parity R = ∅ := by
  classical
  simp [huaStepEightBadPairs]

/-- The zero-large-factor divisor family need not vanish: it contains `1`
whenever the source predicate and upper endpoint allow it. -/
theorem one_mem_huaStepEightDivisors_zero {H Y M : ℕ} {R : ℕ → Prop}
    (hH : H ≠ 0) (hM : 1 ≤ M) (hR : R 1) :
    1 ∈ huaStepEightDivisors H Y M 0 0 R := by
  rw [mem_huaStepEightDivisors_iff]
  exact ⟨Nat.mem_divisors.mpr ⟨one_dvd _, hH⟩, hM,
    by simp [primeFactorsAtLeastCutoff], by simp, hR⟩

/-- A source divisor range with `m > P` is empty; its progression and strict
lower endpoint are retained even in this boundary case. -/
theorem huaSourceStepEightDivisors_of_lt
    (P m Q t s parity : ℕ) (lambda₂ lambda₃ : ℝ) (hPm : P < m) :
    huaStepEightDivisors (huaStepEightSieveProduct P)
      (Nat.ceil (Real.rpow (Real.log P) lambda₃)) (P / m) s parity
      (huaStepEightSourceCondition P m Q t lambda₂) = ∅ := by
  rw [Nat.div_eq_of_lt hPm]
  exact huaStepEightDivisors_upper_zero _ _ _ _ _

/-- The source pair family also vanishes when `m > P`. -/
theorem huaSourceStepEightPairs_of_lt
    (P m Q t s parity : ℕ) (lambda₂ lambda₃ : ℝ) (hPm : P < m) :
    huaStepEightPairs (huaStepEightSieveProduct P)
      (Nat.ceil (Real.rpow (Real.log P) lambda₃)) (P / m) s parity
      (huaStepEightSourceCondition P m Q t lambda₂) = ∅ := by
  rw [Nat.div_eq_of_lt hPm]
  exact huaStepEightPairs_upper_zero _ _ _ _ _

/-- No repeated-prime correction remains outside the source product range. -/
theorem huaSourceStepEightBadPairs_of_lt
    (P m Q t s parity : ℕ) (lambda₂ lambda₃ : ℝ) (hPm : P < m) :
    huaStepEightBadPairs (huaStepEightSieveProduct P)
      (Nat.ceil (Real.rpow (Real.log P) lambda₃)) (P / m) s parity
      (huaStepEightSourceCondition P m Q t lambda₂) = ∅ := by
  rw [Nat.div_eq_of_lt hPm]
  exact huaStepEightBadPairs_upper_zero _ _ _ _ _

/-- With one large factor, the source pairs recount the divisors exactly
and have no repeated-prime correction. -/
theorem sum_huaStepEightPairs_one_eq_divisors
    {A : Type*} [AddCommMonoid A] {H Y M parity : ℕ} {R : ℕ → Prop}
    (hH : Squarefree H) (f : ℕ → A) :
    (∑ z ∈ huaStepEightPairs H Y M 1 parity R, f (z.1 * z.2)) =
      ∑ d ∈ huaStepEightDivisors H Y M 1 parity R, f d := by
  rw [sum_huaStepEightPairs_eq_recount_add_bad hH f]
  simp

/-- Dividing the exact pair identity expresses the original divisor sum
with its signed repeated-prime correction. -/
theorem sum_huaStepEightDivisors_eq_pair_sub_bad_div
    {H Y M s parity : ℕ} {R : ℕ → Prop}
    (hH : Squarefree H) (hs : 0 < s) (f : ℕ → ℂ) :
    (∑ d ∈ huaStepEightDivisors H Y M s parity R, f d) =
      ((∑ z ∈ huaStepEightPairs H Y M s parity R, f (z.1 * z.2)) -
        ∑ z ∈ huaStepEightBadPairs H Y M s parity R, f (z.1 * z.2)) / (s : ℂ) := by
  have hsne : (s : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hs.ne'
  rw [sum_huaStepEightPairs_eq_recount_add_bad hH f, add_sub_cancel_right, nsmul_eq_mul]
  field_simp

/-- The normalized pair-minus-divisor discrepancy is exactly the bad sum
divided by `s`; neither its sign nor the reciprocal factor is discarded. -/
theorem huaStepEightPairs_div_sub_divisors_eq_bad_div
    {H Y M s parity : ℕ} {R : ℕ → Prop}
    (hH : Squarefree H) (hs : 0 < s) (f : ℕ → ℂ) :
    ((∑ z ∈ huaStepEightPairs H Y M s parity R, f (z.1 * z.2)) / (s : ℂ)) -
      (∑ d ∈ huaStepEightDivisors H Y M s parity R, f d) =
        (∑ z ∈ huaStepEightBadPairs H Y M s parity R, f (z.1 * z.2)) / (s : ℂ) := by
  have hsne : (s : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hs.ne'
  rw [sum_huaStepEightPairs_eq_recount_add_bad hH f, nsmul_eq_mul]
  field_simp
  ring

private theorem complex_div_sub_eq_sub_recount_div (pair divisor : ℂ) {s : ℕ}
    (hs : 0 < s) : pair / (s : ℂ) - divisor = (pair - s • divisor) / (s : ℂ) := by
  have hsne : (s : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hs.ne'
  simp only [nsmul_eq_mul]
  field_simp

/-- The reciprocal-square correction retains the extra reciprocal factor
when the pair sum is divided by its positive factor count. -/
theorem norm_huaStepEightPairs_div_sub_divisors_le
    {H Y M s parity : ℕ} {R : ℕ → Prop} (hH : Squarefree H)
    (hY : 0 < Y) (hs : 0 < s) (f : ℕ → ℂ)
    (hf : ∀ z ∈ huaStepEightBadPairs H Y M s parity R, ‖f (z.1 * z.2)‖ ≤ 1) :
    ‖((∑ z ∈ huaStepEightPairs H Y M s parity R, f (z.1 * z.2)) / (s : ℂ)) -
      (∑ d ∈ huaStepEightDivisors H Y M s parity R, f d)‖ ≤
        (2 : ℝ) * M / ((s : ℝ) * Y) := by
  rw [complex_div_sub_eq_sub_recount_div _ _ hs, norm_div, Complex.norm_natCast]
  calc
    _ ≤ ((2 : ℝ) * M / Y) / s :=
      div_le_div_of_nonneg_right (norm_huaStepEightPairs_sub_recount_le hH hY f hf)
        (Nat.cast_nonneg s)
    _ = (2 : ℝ) * M / ((s : ℝ) * Y) := by rw [div_div, mul_comm (Y : ℝ)]

/-- The eventual logarithmic cutoff estimate retains its explicit `1/s`
loss uniformly in all the remaining source parameters. -/
theorem eventually_norm_huaStepEightPairs_div_sub_divisors_logCutoff_le
    {lambda₃ : ℝ} (h₃ : 0 < lambda₃) :
    ∀ᶠ P : ℕ in Filter.atTop,
      1 < P ∧ ∀ H Y M s parity : ℕ, ∀ R : ℕ → Prop,
        Squarefree H → Nat.floor (Real.rpow (Real.log P) lambda₃) ≤ Y → 0 < s →
        ∀ f : ℕ → ℂ,
          (∀ z ∈ huaStepEightBadPairs H Y M s parity R, ‖f (z.1 * z.2)‖ ≤ 1) →
          ‖((∑ z ∈ huaStepEightPairs H Y M s parity R, f (z.1 * z.2)) / (s : ℂ)) -
            (∑ d ∈ huaStepEightDivisors H Y M s parity R, f d)‖ ≤
              (4 : ℝ) * M / ((s : ℝ) * Real.rpow (Real.log P) lambda₃) := by
  filter_upwards [eventually_norm_huaStepEightPairs_sub_recount_logCutoff_le h₃]
    with P hP
  rcases hP with ⟨hP, hbound⟩
  refine ⟨hP, ?_⟩
  intro H Y M s parity R hH hY hs f hf
  rw [complex_div_sub_eq_sub_recount_div _ _ hs, norm_div, Complex.norm_natCast]
  calc
    _ ≤ ((4 : ℝ) * M / Real.rpow (Real.log P) lambda₃) / s :=
      div_le_div_of_nonneg_right (hbound H Y M s parity R hH hY f hf) (Nat.cast_nonneg s)
    _ = (4 : ℝ) * M / ((s : ℝ) * Real.rpow (Real.log P) lambda₃) := by
      rw [div_div, mul_comm (Real.rpow (Real.log P) lambda₃)]

/-- The exact source divisor sum equals the normalized pair sum minus its
normalized bad branch, with the actual ceiling cutoff and progression. -/
theorem sum_huaSourceStepEightDivisors_eq_pair_sub_bad_div
    (P m Q t s parity : ℕ) (lambda₂ lambda₃ : ℝ) (hs : 0 < s) (f : ℕ → ℂ) :
    let H := huaStepEightSieveProduct P
    let Y := Nat.ceil (Real.rpow (Real.log P) lambda₃)
    let R := huaStepEightSourceCondition P m Q t lambda₂
    (∑ d ∈ huaStepEightDivisors H Y (P / m) s parity R, f (m * d)) =
      ((∑ z ∈ huaStepEightPairs H Y (P / m) s parity R, f (m * (z.1 * z.2))) -
        ∑ z ∈ huaStepEightBadPairs H Y (P / m) s parity R,
          f (m * (z.1 * z.2))) / (s : ℂ) :=
  sum_huaStepEightDivisors_eq_pair_sub_bad_div (squarefree_huaStepEightSieveProduct P)
    hs (fun d => f (m * d))

/-- Hua's source correction after division by `s` has the exact scale
`4P/(s*m*(log P)^lambda₃)`. No factor-count denominator is absorbed. -/
theorem eventually_norm_huaSourceStepEight_div_sub_divisors_le
    {lambda₂ lambda₃ : ℝ} (h₃ : 0 < lambda₃) :
    ∀ᶠ P : ℕ in Filter.atTop,
      1 < P ∧ ∀ m Q t s parity : ℕ, 0 < m → 0 < s → ∀ f : ℕ → ℂ,
        let H := huaStepEightSieveProduct P
        let Y := Nat.ceil (Real.rpow (Real.log P) lambda₃)
        let R := huaStepEightSourceCondition P m Q t lambda₂
        (∀ z ∈ huaStepEightBadPairs H Y (P / m) s parity R,
          ‖f (m * (z.1 * z.2))‖ ≤ 1) →
        ‖((∑ z ∈ huaStepEightPairs H Y (P / m) s parity R,
              f (m * (z.1 * z.2))) / (s : ℂ)) -
          (∑ d ∈ huaStepEightDivisors H Y (P / m) s parity R, f (m * d))‖ ≤
            (4 : ℝ) * P / ((s : ℝ) * m * Real.rpow (Real.log P) lambda₃) := by
  filter_upwards [eventually_norm_huaSourceStepEight_sub_recount_le (lambda₂ := lambda₂) h₃]
    with P hP
  rcases hP with ⟨hP, hbound⟩
  refine ⟨hP, ?_⟩
  intro m Q t s parity hm hs f
  dsimp only
  intro hf
  rw [complex_div_sub_eq_sub_recount_div _ _ hs, norm_div, Complex.norm_natCast]
  calc
    _ ≤ ((4 : ℝ) * P / ((m : ℝ) * Real.rpow (Real.log P) lambda₃)) / s :=
      div_le_div_of_nonneg_right (hbound m Q t s parity hm f hf) (Nat.cast_nonneg s)
    _ = (4 : ℝ) * P / ((s : ℝ) * m * Real.rpow (Real.log P) lambda₃) := by
      rw [div_div]
      ring

end CookMagyarCircle
end SystolicGrowth

#print axioms SystolicGrowth.CookMagyarCircle.huaStepEightBadPairs_one
#print axioms SystolicGrowth.CookMagyarCircle.sum_huaStepEightDivisors_eq_pair_sub_bad_div
#print axioms SystolicGrowth.CookMagyarCircle.huaStepEightPairs_div_sub_divisors_eq_bad_div
#print axioms SystolicGrowth.CookMagyarCircle.norm_huaStepEightPairs_div_sub_divisors_le
#print axioms SystolicGrowth.CookMagyarCircle.eventually_norm_huaSourceStepEight_div_sub_divisors_le
