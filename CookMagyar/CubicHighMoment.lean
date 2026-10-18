module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.HuaAsymptotic

@[expose] public section

open MeasureTheory
open scoped ArithmeticFunction BigOperators ComplexConjugate

namespace SystolicGrowth
namespace CookMagyarCircle

/-! # Exact cubic 32nd moment and removal of von--Mangoldt weights -/

/-- Cubic value of an ordered sixteen-tuple. -/
def cubicSixteenTupleValue {N : ℕ} (x : Fin 16 → Fin (N + 1)) : ℕ :=
  ∑ i, primeCubic (x i)

/-- Von--Mangoldt weight of an ordered sixteen-tuple. -/
noncomputable def cubicSixteenTupleWeight {N : ℕ}
    (x : Fin 16 → Fin (N + 1)) : ℝ :=
  ∏ i, ArithmeticFunction.vonMangoldt (x i)

/-- The number of pairs of sixteen-tuples with equal cubic value. -/
def cubicThirtySecondSolutionCount (N : ℕ) : ℕ :=
  ∑ x : Fin 16 → Fin (N + 1), ∑ y : Fin 16 → Fin (N + 1),
    if cubicSixteenTupleValue x = cubicSixteenTupleValue y then 1 else 0

/-- The corresponding nonnegative von--Mangoldt-weighted energy. -/
noncomputable def cubicVonMangoldtThirtySecondEnergy (N : ℕ) : ℝ :=
  ∑ x : Fin 16 → Fin (N + 1), ∑ y : Fin 16 → Fin (N + 1),
    if cubicSixteenTupleValue x = cubicSixteenTupleValue y then
      cubicSixteenTupleWeight x * cubicSixteenTupleWeight y else 0

private theorem negAddChar_sum_sixteen {ι : Type*} [Fintype ι]
    (alpha : ℝ) (f : ι → ℕ) :
    negAddChar alpha (∑ i, f i) = ∏ i, negAddChar alpha (f i) := by
  classical
  calc
    negAddChar alpha (∑ i, f i) = conj (addChar alpha (∑ i, f i)) :=
      (conj_addChar alpha _).symm
    _ = conj (∏ i, addChar alpha (f i)) := by rw [addChar_sum]
    _ = ∏ i, negAddChar alpha (f i) := by
      rw [map_prod]
      simp only [conj_addChar]

private theorem unweighted_pow_sixteen (alpha : ℝ) (N : ℕ) :
    cubicUnweightedExpSum alpha N ^ 16 =
      ∑ x : Fin 16 → Fin (N + 1), addChar alpha (cubicSixteenTupleValue x) := by
  classical
  rw [cubicUnweightedExpSum_eq_finSum, Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro x _
  rw [← addChar_sum]
  rfl

private theorem conj_unweighted_pow_sixteen (alpha : ℝ) (N : ℕ) :
    conj (cubicUnweightedExpSum alpha N) ^ 16 =
      ∑ x : Fin 16 → Fin (N + 1), negAddChar alpha (cubicSixteenTupleValue x) := by
  rw [← map_pow, unweighted_pow_sixteen, map_sum]
  apply Finset.sum_congr rfl
  intro x _
  exact conj_addChar alpha _

private theorem weighted_pow_sixteen (alpha : ℝ) (N : ℕ) :
    cubicVonMangoldtExpSum alpha N ^ 16 =
      ∑ x : Fin 16 → Fin (N + 1),
        (cubicSixteenTupleWeight x : ℂ) * addChar alpha (cubicSixteenTupleValue x) := by
  classical
  rw [cubicVonMangoldtExpSum, Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.prod_mul_distrib, ← addChar_sum]
  unfold cubicSixteenTupleWeight cubicSixteenTupleValue
  push_cast
  rfl

private theorem conj_weighted_pow_sixteen (alpha : ℝ) (N : ℕ) :
    conj (cubicVonMangoldtExpSum alpha N) ^ 16 =
      ∑ x : Fin 16 → Fin (N + 1),
        (cubicSixteenTupleWeight x : ℂ) * negAddChar alpha (cubicSixteenTupleValue x) := by
  classical
  have hconj :
      conj (cubicVonMangoldtExpSum alpha N) =
        ∑ x : Fin (N + 1),
          (ArithmeticFunction.vonMangoldt x : ℂ) *
            negAddChar alpha (primeCubic x) := by
    unfold cubicVonMangoldtExpSum
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [map_mul, conj_addChar]
    simp
  rw [hconj, Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.prod_mul_distrib, ← negAddChar_sum_sixteen]
  unfold cubicSixteenTupleWeight cubicSixteenTupleValue
  push_cast
  rfl

private theorem ofReal_norm_pow_thirtyTwo (z : ℂ) :
    ((‖z‖ ^ 32 : ℝ) : ℂ) = z ^ 16 * conj z ^ 16 := by
  calc
    ((‖z‖ ^ 32 : ℝ) : ℂ) = (((‖z‖ : ℝ) : ℂ) ^ 2) ^ 16 := by
      push_cast
      ring
    _ = (z * conj z) ^ 16 := by rw [Complex.mul_conj']
    _ = z ^ 16 * conj z ^ 16 := by rw [mul_pow]

/-- The unweighted 32nd moment is exactly the ordered sixteen-tuple count. -/
theorem integral_norm_cubicUnweightedExpSum_pow_thirtyTwo_complex (N : ℕ) :
    (∫ alpha in Set.Icc (0 : ℝ) 1,
      ((‖cubicUnweightedExpSum alpha N‖ ^ 32 : ℝ) : ℂ)) =
        (cubicThirtySecondSolutionCount N : ℂ) := by
  classical
  have hpoint : ∀ alpha : ℝ,
      ((‖cubicUnweightedExpSum alpha N‖ ^ 32 : ℝ) : ℂ) =
        ∑ x : Fin 16 → Fin (N + 1), ∑ y : Fin 16 → Fin (N + 1),
          addChar alpha (cubicSixteenTupleValue x) *
            negAddChar alpha (cubicSixteenTupleValue y) := by
    intro alpha
    rw [ofReal_norm_pow_thirtyTwo, unweighted_pow_sixteen,
      conj_unweighted_pow_sixteen, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
  rw [setIntegral_congr_fun measurableSet_Icc (fun alpha _ => hpoint alpha)]
  rw [integral_finsetSum]
  · unfold cubicThirtySecondSolutionCount
    push_cast
    apply Finset.sum_congr rfl
    intro x _
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro y _
      rw [integral_addChar_mul_negAddChar]
    · intro y _
      apply Continuous.integrableOn_Icc
      unfold addChar negAddChar
      fun_prop
  · intro x _
    apply Continuous.integrableOn_Icc
    unfold addChar negAddChar
    fun_prop

/-- Real-valued form of the exact unweighted 32nd-moment identity. -/
theorem integral_norm_cubicUnweightedExpSum_pow_thirtyTwo (N : ℕ) :
    (∫ alpha in Set.Icc (0 : ℝ) 1,
      ‖cubicUnweightedExpSum alpha N‖ ^ 32) =
        (cubicThirtySecondSolutionCount N : ℝ) := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  exact integral_norm_cubicUnweightedExpSum_pow_thirtyTwo_complex N

/-- Exact orthogonality identity for the weighted 32nd moment. -/
theorem integral_norm_cubicVonMangoldtExpSum_pow_thirtyTwo_complex (N : ℕ) :
    (∫ alpha in Set.Icc (0 : ℝ) 1,
      ((‖cubicVonMangoldtExpSum alpha N‖ ^ 32 : ℝ) : ℂ)) =
        (cubicVonMangoldtThirtySecondEnergy N : ℂ) := by
  classical
  have hpoint : ∀ alpha : ℝ,
      ((‖cubicVonMangoldtExpSum alpha N‖ ^ 32 : ℝ) : ℂ) =
        ∑ x : Fin 16 → Fin (N + 1), ∑ y : Fin 16 → Fin (N + 1),
          ((cubicSixteenTupleWeight x * cubicSixteenTupleWeight y : ℝ) : ℂ) *
            (addChar alpha (cubicSixteenTupleValue x) *
              negAddChar alpha (cubicSixteenTupleValue y)) := by
    intro alpha
    rw [ofReal_norm_pow_thirtyTwo, weighted_pow_sixteen,
      conj_weighted_pow_sixteen, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Icc (fun alpha _ => hpoint alpha)]
  rw [integral_finsetSum]
  · unfold cubicVonMangoldtThirtySecondEnergy
    push_cast
    apply Finset.sum_congr rfl
    intro x _
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro y _
      rw [show
          (∫ alpha in Set.Icc (0 : ℝ) 1,
            (cubicSixteenTupleWeight x : ℂ) * (cubicSixteenTupleWeight y : ℂ) *
              (addChar alpha (cubicSixteenTupleValue x) *
                negAddChar alpha (cubicSixteenTupleValue y))) =
            ((cubicSixteenTupleWeight x : ℂ) * (cubicSixteenTupleWeight y : ℂ)) *
              ∫ alpha in Set.Icc (0 : ℝ) 1,
                addChar alpha (cubicSixteenTupleValue x) *
                  negAddChar alpha (cubicSixteenTupleValue y) by
            rw [← integral_indicator measurableSet_Icc,
              ← integral_indicator measurableSet_Icc]
            simp_rw [Set.indicator_const_mul]
            exact MeasureTheory.integral_const_mul _ _]
      rw [integral_addChar_mul_negAddChar]
      split_ifs <;> simp_all
    · intro y _
      apply Continuous.integrableOn_Icc
      unfold addChar negAddChar
      fun_prop
  · intro x _
    apply Continuous.integrableOn_Icc
    unfold addChar negAddChar
    fun_prop

/-- Real-valued form of the exact weighted 32nd-moment identity. -/
theorem integral_norm_cubicVonMangoldtExpSum_pow_thirtyTwo (N : ℕ) :
    (∫ alpha in Set.Icc (0 : ℝ) 1,
      ‖cubicVonMangoldtExpSum alpha N‖ ^ 32) =
        cubicVonMangoldtThirtySecondEnergy N := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  exact integral_norm_cubicVonMangoldtExpSum_pow_thirtyTwo_complex N

/-- Each sixteen-tuple weight is bounded by sixteen endpoint logarithms. -/
theorem cubicSixteenTupleWeight_le_log_pow_sixteen {N : ℕ}
    (x : Fin 16 → Fin (N + 1)) :
    cubicSixteenTupleWeight x ≤ Real.log (N + 1 : ℝ) ^ 16 := by
  unfold cubicSixteenTupleWeight
  calc
    (∏ i, ArithmeticFunction.vonMangoldt (x i).val) ≤
        ∏ _i : Fin 16, Real.log (N + 1 : ℝ) := by
      exact Finset.prod_le_prod₀
        (fun i _ => ArithmeticFunction.vonMangoldt_nonneg)
        (fun i _ => vonMangoldt_fin_le_log_succ (x i))
    _ = Real.log (N + 1 : ℝ) ^ 16 := by simp

theorem cubicSixteenTupleWeight_nonneg {N : ℕ}
    (x : Fin 16 → Fin (N + 1)) : 0 ≤ cubicSixteenTupleWeight x := by
  unfold cubicSixteenTupleWeight
  exact Finset.prod_nonneg fun i _ => ArithmeticFunction.vonMangoldt_nonneg

/-- Integrated removal of the von--Mangoldt weights costs 32 logarithms. -/
theorem cubicVonMangoldtThirtySecondEnergy_le_count (N : ℕ) :
    cubicVonMangoldtThirtySecondEnergy N ≤
      Real.log (N + 1 : ℝ) ^ 32 * cubicThirtySecondSolutionCount N := by
  have hcount_cast : ((cubicThirtySecondSolutionCount N : ℕ) : ℝ) =
      ∑ x : Fin 16 → Fin (N + 1), ∑ y : Fin 16 → Fin (N + 1),
        if cubicSixteenTupleValue x = cubicSixteenTupleValue y then (1 : ℝ) else 0 := by
    unfold cubicThirtySecondSolutionCount
    push_cast
    rfl
  rw [hcount_cast, Finset.mul_sum]
  unfold cubicVonMangoldtThirtySecondEnergy
  apply Finset.sum_le_sum
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y _
  by_cases hxy : cubicSixteenTupleValue x = cubicSixteenTupleValue y
  · simp only [hxy, ite_true, mul_one]
    have hxw := cubicSixteenTupleWeight_le_log_pow_sixteen x
    have hyw := cubicSixteenTupleWeight_le_log_pow_sixteen y
    calc
      cubicSixteenTupleWeight x * cubicSixteenTupleWeight y ≤
          Real.log (N + 1 : ℝ) ^ 16 * Real.log (N + 1 : ℝ) ^ 16 := by
        exact mul_le_mul hxw hyw (cubicSixteenTupleWeight_nonneg y)
          (pow_nonneg (log_succ_nonneg N) 16)
      _ = Real.log (N + 1 : ℝ) ^ 32 := by ring
  · simp [hxy]

/-- Correct integrated comparison; there is no analogous pointwise bound
between the weighted and unweighted exponential sums. -/
theorem integral_norm_cubicVonMangoldtExpSum_pow_thirtyTwo_le (N : ℕ) :
    (∫ alpha in Set.Icc (0 : ℝ) 1,
      ‖cubicVonMangoldtExpSum alpha N‖ ^ 32) ≤
        Real.log (N + 1 : ℝ) ^ 32 *
          (∫ alpha in Set.Icc (0 : ℝ) 1,
            ‖cubicUnweightedExpSum alpha N‖ ^ 32) := by
  rw [integral_norm_cubicVonMangoldtExpSum_pow_thirtyTwo,
    integral_norm_cubicUnweightedExpSum_pow_thirtyTwo]
  exact cubicVonMangoldtThirtySecondEnergy_le_count N

end CookMagyarCircle
end SystolicGrowth
