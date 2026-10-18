module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.PrimePowerAnalytic

@[expose] public section

open MeasureTheory
open scoped ArithmeticFunction BigOperators ComplexConjugate

namespace SystolicGrowth
namespace CookMagyarCircle

/-! # Exact interpretation of the cubic eighth moment

The analytic Hua estimate bounds an eighth moment.  Before any estimate is
made, Fourier orthogonality identifies that moment exactly with a weighted
additive energy: two four-tuples having the same value of
`∑ (x³-x)`.  This file proves that identity.
-/

/-- Cubic value of a four-tuple. -/
def cubicFourTupleValue {N : ℕ} (x : Fin 4 → Fin (N + 1)) : ℕ :=
  ∑ i, primeCubic (x i)

/-- Von--Mangoldt weight of a four-tuple. -/
noncomputable def cubicFourTupleWeight {N : ℕ}
    (x : Fin 4 → Fin (N + 1)) : ℝ :=
  ∏ i, ArithmeticFunction.vonMangoldt (x i)

/-- Weighted additive energy of the cubic values of four-tuples. -/
noncomputable def cubicVonMangoldtEighthEnergy (N : ℕ) : ℝ :=
  ∑ x : Fin 4 → Fin (N + 1), ∑ y : Fin 4 → Fin (N + 1),
    if cubicFourTupleValue x = cubicFourTupleValue y then
      cubicFourTupleWeight x * cubicFourTupleWeight y
    else 0

@[simp] theorem conj_addChar (alpha : ℝ) (k : ℕ) :
    conj (addChar alpha k) = negAddChar alpha k := by
  unfold addChar negAddChar
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, map_natCast, Complex.conj_ofReal,
    Complex.conj_I]
  ring

private theorem negAddChar_add (alpha : ℝ) (a b : ℕ) :
    negAddChar alpha (a + b) = negAddChar alpha a * negAddChar alpha b := by
  unfold negAddChar
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem negAddChar_sum {ι : Type*} [Fintype ι]
    (alpha : ℝ) (f : ι → ℕ) :
    negAddChar alpha (∑ i, f i) = ∏ i, negAddChar alpha (f i) := by
  classical
  have aux : ∀ s : Finset ι,
      negAddChar alpha (∑ i ∈ s, f i) =
        ∏ i ∈ s, negAddChar alpha (f i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.prod_insert ha,
          negAddChar_add, ih]
  simpa using aux Finset.univ

private theorem cubicExpSum_pow_four (alpha : ℝ) (N : ℕ) :
    cubicVonMangoldtExpSum alpha N ^ 4 =
      ∑ x : Fin 4 → Fin (N + 1),
        (cubicFourTupleWeight x : ℂ) *
          addChar alpha (cubicFourTupleValue x) := by
  classical
  rw [cubicVonMangoldtExpSum, Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro x _hx
  rw [Finset.prod_mul_distrib, ← addChar_sum]
  unfold cubicFourTupleWeight cubicFourTupleValue
  push_cast
  rfl

private theorem conj_cubicExpSum_pow_four (alpha : ℝ) (N : ℕ) :
    conj (cubicVonMangoldtExpSum alpha N) ^ 4 =
      ∑ y : Fin 4 → Fin (N + 1),
        (cubicFourTupleWeight y : ℂ) *
          negAddChar alpha (cubicFourTupleValue y) := by
  classical
  have hconj :
      conj (cubicVonMangoldtExpSum alpha N) =
        ∑ x : Fin (N + 1),
          (ArithmeticFunction.vonMangoldt x : ℂ) *
            negAddChar alpha (primeCubic x) := by
    unfold cubicVonMangoldtExpSum
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro x _hx
    rw [map_mul, conj_addChar]
    simp
  rw [hconj, Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro y _hy
  rw [Finset.prod_mul_distrib, ← negAddChar_sum]
  unfold cubicFourTupleWeight cubicFourTupleValue
  push_cast
  rfl

private theorem ofReal_norm_pow_eight (z : ℂ) :
    ((‖z‖ ^ 8 : ℝ) : ℂ) = z ^ 4 * conj z ^ 4 := by
  calc
    ((‖z‖ ^ 8 : ℝ) : ℂ) = (((‖z‖ : ℝ) : ℂ) ^ 2) ^ 4 := by
      push_cast
      ring
    _ = (z * conj z) ^ 4 := by rw [Complex.mul_conj']
    _ = z ^ 4 * conj z ^ 4 := by rw [mul_pow]

/-- Complex-cast form of the exact eighth-moment identity. -/
theorem integral_norm_cubicExpSum_pow_eight (N : ℕ) :
    (∫ alpha in Set.Icc (0 : ℝ) 1,
        ((‖cubicVonMangoldtExpSum alpha N‖ ^ 8 : ℝ) : ℂ)) =
      (cubicVonMangoldtEighthEnergy N : ℂ) := by
  classical
  have hpoint : ∀ alpha : ℝ,
      ((‖cubicVonMangoldtExpSum alpha N‖ ^ 8 : ℝ) : ℂ) =
        ∑ x : Fin 4 → Fin (N + 1),
          ∑ y : Fin 4 → Fin (N + 1),
            ((cubicFourTupleWeight x * cubicFourTupleWeight y : ℝ) : ℂ) *
              (addChar alpha (cubicFourTupleValue x) *
                negAddChar alpha (cubicFourTupleValue y)) := by
    intro alpha
    rw [ofReal_norm_pow_eight, cubicExpSum_pow_four,
      conj_cubicExpSum_pow_four, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _hx
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _hy
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Icc (fun alpha _ ↦ hpoint alpha)]
  rw [integral_finsetSum]
  · unfold cubicVonMangoldtEighthEnergy
    push_cast
    apply Finset.sum_congr rfl
    intro x _hx
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro y _hy
      rw [show
          (∫ alpha in Set.Icc (0 : ℝ) 1,
            (cubicFourTupleWeight x : ℂ) * (cubicFourTupleWeight y : ℂ) *
              (addChar alpha (cubicFourTupleValue x) *
                negAddChar alpha (cubicFourTupleValue y))) =
            ((cubicFourTupleWeight x : ℂ) * (cubicFourTupleWeight y : ℂ)) *
              ∫ alpha in Set.Icc (0 : ℝ) 1,
                addChar alpha (cubicFourTupleValue x) *
                  negAddChar alpha (cubicFourTupleValue y) by
            rw [← integral_indicator measurableSet_Icc,
              ← integral_indicator measurableSet_Icc]
            simp_rw [Set.indicator_const_mul]
            exact MeasureTheory.integral_const_mul _ _]
      rw [integral_addChar_mul_negAddChar]
      split_ifs <;> simp_all
    · intro y _hy
      apply Continuous.integrableOn_Icc
      unfold addChar negAddChar
      fun_prop
  · intro x _hx
    apply Continuous.integrableOn_Icc
    unfold addChar negAddChar
    fun_prop

/-- **Exact Hua-moment identity.** -/
theorem cubicVonMangoldtEighthMoment_eq_energy (N : ℕ) :
    cubicVonMangoldtEighthMoment N = cubicVonMangoldtEighthEnergy N := by
  apply Complex.ofReal_injective
  unfold cubicVonMangoldtEighthMoment
  rw [← integral_complex_ofReal]
  exact integral_norm_cubicExpSum_pow_eight N

end CookMagyarCircle
end SystolicGrowth
