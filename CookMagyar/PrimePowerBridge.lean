module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.PrimePowerAnalytic

@[expose] public section

open MeasureTheory
open scoped ArithmeticFunction BigOperators

namespace SystolicGrowth
namespace CookMagyarCircle

/-! # From the discarded count to the analytic error integral

This file supplies the finite combinatorial and Fourier bridge used in the
prime-power-removal argument.  A discarded tuple is charged to one of its bad
coordinates.  Removing that coordinate leaves a full `(n-1)`-tuple, whose
generating function is `S^(n-1)`; the removed coordinate contributes `E`.
-/

/-- Weighted solutions for which one specified coordinate is not an odd
prime. -/
noncomputable def cubicBadCoordinateRepresentation
    {n : ℕ} (i : Fin n) (N T : ℕ) : ℝ := by
  classical
  exact ∑ x : Fin n → Fin (N + 1),
    if (∑ j, primeCubic (x j)) = T ∧ ¬IsOddPrime (x i : ℕ) then
      tupleVonMangoldtWeight x
    else 0

/-- The same count after splitting off the bad coordinate. -/
noncomputable def cubicBadLeadingRepresentation
    (m N T : ℕ) : ℝ := by
  classical
  exact ∑ a : Fin (N + 1),
    if ¬IsOddPrime (a : ℕ) then
      ∑ y : Fin m → Fin (N + 1),
        if primeCubic a + ∑ j, primeCubic (y j) = T then
          ArithmeticFunction.vonMangoldt a * tupleVonMangoldtWeight y
        else 0
    else 0

theorem cubicBadCoordinateRepresentation_nonneg
    {n : ℕ} (i : Fin n) (N T : ℕ) :
    0 ≤ cubicBadCoordinateRepresentation i N T := by
  classical
  unfold cubicBadCoordinateRepresentation tupleVonMangoldtWeight
  exact Finset.sum_nonneg fun x _hx ↦ by
    split_ifs
    · exact Finset.prod_nonneg fun j _hj ↦
        ArithmeticFunction.vonMangoldt_nonneg
    · exact le_rfl

theorem cubicBadLeadingRepresentation_nonneg (m N T : ℕ) :
    0 ≤ cubicBadLeadingRepresentation m N T := by
  classical
  unfold cubicBadLeadingRepresentation tupleVonMangoldtWeight
  exact Finset.sum_nonneg fun a _ha ↦ by
    by_cases ha : ¬IsOddPrime (a : ℕ)
    · simp only [ha]
      exact Finset.sum_nonneg fun y _hy ↦ by
        by_cases heq : primeCubic a + ∑ j, primeCubic (y j) = T
        · simp only [heq, if_true]
          exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
            (Finset.prod_nonneg fun j _hj ↦
              ArithmeticFunction.vonMangoldt_nonneg)
        · simp [heq]
    · simp [ha]

/-- Coordinate union bound: a tuple which is not entirely odd-prime has at
least one bad coordinate. -/
theorem cubicDiscardedRepresentation_le_sum_badCoordinates
    (n N T : ℕ) :
    cubicDiscardedRepresentation n N T ≤
      ∑ i : Fin n, cubicBadCoordinateRepresentation i N T := by
  classical
  unfold cubicDiscardedRepresentation cubicBadCoordinateRepresentation
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _hx
  by_cases heq : (∑ j, primeCubic (x j)) = T
  · by_cases hall : IsOddPrimeTuple x
    · rw [if_neg]
      · exact Finset.sum_nonneg fun i _hi ↦ by
          by_cases hbad : ¬IsOddPrime (x i : ℕ)
          · exact (hbad (hall i)).elim
          · simp [heq, hbad]
      · intro h
        exact h.2 hall
    · have hbad : ∃ i : Fin n, ¬IsOddPrime (x i : ℕ) := by
        simpa [IsOddPrimeTuple] using hall
      rcases hbad with ⟨i, hi⟩
      have hw : 0 ≤ tupleVonMangoldtWeight x := by
        unfold tupleVonMangoldtWeight
        exact Finset.prod_nonneg fun j _hj ↦
          ArithmeticFunction.vonMangoldt_nonneg
      rw [if_pos ⟨heq, hall⟩]
      let f : Fin n → ℝ := fun j ↦
        if (∑ k, primeCubic (x k)) = T ∧ ¬IsOddPrime (x j : ℕ) then
          tupleVonMangoldtWeight x else 0
      calc
        tupleVonMangoldtWeight x = f i := by simp [f, heq, hi]
        _ ≤ ∑ j : Fin n, f j := by
          apply Finset.single_le_sum (s := Finset.univ)
          · intro j _hj
            by_cases hj : ¬IsOddPrime (x j : ℕ)
            · simp [f, heq, hj, hw]
            · have hj' : IsOddPrime (x j : ℕ) := not_not.mp hj
              simp [f, heq, hj']
          · exact Finset.mem_univ i
        _ = ∑ j : Fin n,
              if (∑ k, primeCubic (x k)) = T ∧ ¬IsOddPrime (x j : ℕ) then
                tupleVonMangoldtWeight x else 0 := rfl
  · simp [heq]

private theorem sum_primeCubic_insertNth
    {m N : ℕ} (i : Fin (m + 1)) (a : Fin (N + 1))
    (y : Fin m → Fin (N + 1)) :
    (∑ j, primeCubic ((Fin.insertNth i a y :
      Fin (m + 1) → Fin (N + 1)) j)) =
      primeCubic a + ∑ j, primeCubic (y j) := by
  rw [Fin.sum_univ_succAbove _ i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

private theorem prod_vonMangoldt_insertNth
    {m N : ℕ} (i : Fin (m + 1)) (a : Fin (N + 1))
    (y : Fin m → Fin (N + 1)) :
    (∏ j, ArithmeticFunction.vonMangoldt
      ((Fin.insertNth i a y : Fin (m + 1) → Fin (N + 1)) j)) =
      ArithmeticFunction.vonMangoldt a *
        ∏ j, ArithmeticFunction.vonMangoldt (y j) := by
  rw [Fin.prod_univ_succAbove _ i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

/-- Splitting off any selected coordinate gives the same leading-coordinate
count. -/
theorem cubicBadCoordinateRepresentation_eq_leading
    {m : ℕ} (i : Fin (m + 1)) (N T : ℕ) :
    cubicBadCoordinateRepresentation i N T =
      cubicBadLeadingRepresentation m N T := by
  classical
  let A := Fin (N + 1)
  let e : A × (Fin m → A) ≃ (Fin (m + 1) → A) :=
    Fin.insertNthEquiv (fun _ : Fin (m + 1) ↦ A) i
  let F : (Fin (m + 1) → A) → ℝ := fun x ↦
    if (∑ j, primeCubic (x j)) = T ∧ ¬IsOddPrime (x i : ℕ) then
      ∏ j, ArithmeticFunction.vonMangoldt (x j)
    else 0
  calc
    cubicBadCoordinateRepresentation i N T = ∑ x, F x := by
      rfl
    _ = ∑ z, F (e z) := (e.sum_comp F).symm
    _ = cubicBadLeadingRepresentation m N T := by
      unfold cubicBadLeadingRepresentation tupleVonMangoldtWeight
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a _ha
      by_cases ha : ¬IsOddPrime (a : ℕ)
      · rw [if_pos ha]
        apply Finset.sum_congr rfl
        intro y _hy
        dsimp only [F]
        have he : e (a, y) =
            (Fin.insertNth i a y : Fin (m + 1) → Fin (N + 1)) := rfl
        rw [he]
        rw [sum_primeCubic_insertNth, prod_vonMangoldt_insertNth,
          Fin.insertNth_apply_same]
        simp [ha]
      · rw [if_neg ha]
        apply Finset.sum_eq_zero
        intro y _hy
        dsimp only [F]
        have he : e (a, y) =
            (Fin.insertNth i a y : Fin (m + 1) → Fin (N + 1)) := rfl
        rw [he]
        rw [sum_primeCubic_insertNth, prod_vonMangoldt_insertNth,
          Fin.insertNth_apply_same]
        simp [ha]

private theorem product_weighted_addChar_bridge
    {m N : ℕ} (α : ℝ) (y : Fin m → Fin (N + 1)) :
    (∏ j,
        (ArithmeticFunction.vonMangoldt (y j) : ℂ) *
          addChar α (primeCubic (y j))) =
      (tupleVonMangoldtWeight y : ℂ) *
        addChar α (∑ j, primeCubic (y j)) := by
  rw [Finset.prod_mul_distrib, ← addChar_sum]
  simp only [tupleVonMangoldtWeight]
  push_cast
  rfl

/-- Fourier coefficient identity for one distinguished bad coordinate. -/
theorem integral_bad_mul_full_pow (m N T : ℕ) :
    (∫ α in Set.Icc (0 : ℝ) 1,
        cubicBadPrimePowerExpSum α N *
          (cubicVonMangoldtExpSum α N) ^ m * negAddChar α T) =
      (cubicBadLeadingRepresentation m N T : ℂ) := by
  classical
  have hpoint : ∀ α : ℝ,
      cubicBadPrimePowerExpSum α N *
          (cubicVonMangoldtExpSum α N) ^ m * negAddChar α T =
        ∑ a : Fin (N + 1),
          if ¬IsOddPrime (a : ℕ) then
            ∑ y : Fin m → Fin (N + 1),
              ((ArithmeticFunction.vonMangoldt a *
                  tupleVonMangoldtWeight y : ℝ) : ℂ) *
                (addChar α (primeCubic a + ∑ j, primeCubic (y j)) *
                  negAddChar α T)
          else 0 := by
    intro α
    unfold cubicBadPrimePowerExpSum cubicVonMangoldtExpSum
    rw [Fintype.sum_pow]
    simp_rw [product_weighted_addChar_bridge]
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _ha
    by_cases ha : ¬IsOddPrime (a : ℕ)
    · simp only [ha, not_false_eq_true, if_true]
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro y _hy
      rw [addChar_add]
      push_cast
      ring
    · simp [ha]

  rw [setIntegral_congr_fun measurableSet_Icc (fun α _hα ↦ hpoint α)]
  rw [integral_finsetSum]
  · rw [cubicBadLeadingRepresentation]
    push_cast
    apply Finset.sum_congr rfl
    intro a _ha
    by_cases ha : ¬IsOddPrime (a : ℕ)
    · simp only [ha, not_false_eq_true, if_true]
      push_cast
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro y _hy
        rw [show
            (∫ α in Set.Icc (0 : ℝ) 1,
                (ArithmeticFunction.vonMangoldt a : ℂ) *
                  (tupleVonMangoldtWeight y : ℂ) *
                  (addChar α (primeCubic a + ∑ j, primeCubic (y j)) *
                    negAddChar α T)) =
              ((ArithmeticFunction.vonMangoldt a : ℂ) *
                  (tupleVonMangoldtWeight y : ℂ)) *
                ∫ α in Set.Icc (0 : ℝ) 1,
                  addChar α (primeCubic a + ∑ j, primeCubic (y j)) *
                    negAddChar α T by
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
    · simp [ha]
  · intro a _ha
    by_cases ha : ¬IsOddPrime (a : ℕ)
    · simp only [ha, not_false_eq_true, if_true]
      apply integrable_finsetSum
      intro y _hy
      apply Continuous.integrableOn_Icc
      unfold addChar negAddChar
      fun_prop
    · simp [ha]

/-- One distinguished bad-coordinate count is bounded by the absolute
analytic error integral. -/
theorem cubicBadLeadingRepresentation_le_integral_norm
    (m N T : ℕ) :
    cubicBadLeadingRepresentation m N T ≤
      ∫ α in Set.Icc (0 : ℝ) 1,
        ‖cubicBadPrimePowerExpSum α N *
          (cubicVonMangoldtExpSum α N) ^ m‖ := by
  have hnonneg := cubicBadLeadingRepresentation_nonneg m N T
  calc
    cubicBadLeadingRepresentation m N T =
        ‖(cubicBadLeadingRepresentation m N T : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    _ = ‖∫ α in Set.Icc (0 : ℝ) 1,
          cubicBadPrimePowerExpSum α N *
            (cubicVonMangoldtExpSum α N) ^ m * negAddChar α T‖ := by
      rw [integral_bad_mul_full_pow]
    _ ≤ ∫ α in Set.Icc (0 : ℝ) 1,
          ‖cubicBadPrimePowerExpSum α N *
            (cubicVonMangoldtExpSum α N) ^ m * negAddChar α T‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ α in Set.Icc (0 : ℝ) 1,
          ‖cubicBadPrimePowerExpSum α N *
            (cubicVonMangoldtExpSum α N) ^ m‖ := by
      apply integral_congr_ae
      filter_upwards with α
      rw [norm_mul, norm_negAddChar, mul_one]

/-- Appendix-B coordinate union bound.  Every discarded tuple is charged to
one bad coordinate, and each coordinate has Fourier coefficient `E*S^(n-1)`.
-/
theorem cubicDiscardedRepresentation_le_n_mul_integral_norm_bad
    {n N T : ℕ} (hn : 1 ≤ n) :
    cubicDiscardedRepresentation n N T ≤
      (n : ℝ) *
        ∫ α in Set.Icc (0 : ℝ) 1,
          ‖cubicBadPrimePowerExpSum α N *
            (cubicVonMangoldtExpSum α N) ^ (n - 1)‖ := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
  have hn' : n = m + 1 := by omega
  rw [hn']
  calc
    cubicDiscardedRepresentation (m + 1) N T ≤
        ∑ i : Fin (m + 1), cubicBadCoordinateRepresentation i N T :=
      cubicDiscardedRepresentation_le_sum_badCoordinates (m + 1) N T
    _ = ∑ _i : Fin (m + 1), cubicBadLeadingRepresentation m N T := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact cubicBadCoordinateRepresentation_eq_leading i N T
    _ ≤ ∑ _i : Fin (m + 1),
          ∫ α in Set.Icc (0 : ℝ) 1,
            ‖cubicBadPrimePowerExpSum α N *
              (cubicVonMangoldtExpSum α N) ^ m‖ := by
      apply Finset.sum_le_sum
      intro i _hi
      exact cubicBadLeadingRepresentation_le_integral_norm m N T
    _ = ((m + 1 : ℕ) : ℝ) *
          ∫ α in Set.Icc (0 : ℝ) 1,
            ‖cubicBadPrimePowerExpSum α N *
              (cubicVonMangoldtExpSum α N) ^ ((m + 1) - 1)‖ := by
      simp

/-- The completed elementary prime-power-removal estimate: for `n ≥ 9`, the
discarded weighted representation count is bounded by the bad coefficient
mass, the elementary full-sum mass bound, and the eighth moment of `S`. -/
theorem cubicDiscardedRepresentation_le_eighthMoment_error
    {n N T : ℕ} (hn : 9 ≤ n) :
    cubicDiscardedRepresentation n N T ≤
      (n : ℝ) *
        (cubicBadPrimePowerMass N *
          (cubicVonMangoldtMass N) ^ (n - 9) *
            cubicVonMangoldtEighthMoment N) := by
  calc
    cubicDiscardedRepresentation n N T ≤
        (n : ℝ) *
          ∫ α in Set.Icc (0 : ℝ) 1,
            ‖cubicBadPrimePowerExpSum α N *
              (cubicVonMangoldtExpSum α N) ^ (n - 1)‖ :=
      cubicDiscardedRepresentation_le_n_mul_integral_norm_bad (by omega)
    _ ≤ (n : ℝ) *
        (cubicBadPrimePowerMass N *
          (cubicVonMangoldtMass N) ^ (n - 9) *
            cubicVonMangoldtEighthMoment N) := by
      apply mul_le_mul_of_nonneg_left
      · exact integral_norm_bad_mul_full_pow_le_eighthMoment_mass hn
      · positivity

end CookMagyarCircle
end SystolicGrowth
