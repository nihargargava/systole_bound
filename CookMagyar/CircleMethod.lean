module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.

The additive-character and interval-orthogonality proofs in this file are
adapted from Gershon Bialer's `ternary-goldbach-lean`,
`MathExtras.NumberTheory.Vinogradov.CircleMethod` (Apache-2.0).  The
arbitrary-arity cubic coefficient extraction is new to this project.
-/
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory
open scoped ArithmeticFunction BigOperators

namespace SystolicGrowth

/-! # Exact circle-method identities for `x^3 - x`

This file contains the algebraic and Fourier-analytic part of the
Cook--Magyar specialization.  There are no asymptotic estimates here: the
main result, `integral_cubicVonMangoldtExpSum_pow`, is the exact identity
which turns a Fourier integral into the von-Mangoldt-weighted number of
representations of a target by `n` values of `x^3-x`.
-/

/-- The cubic polynomial used throughout the arithmetic construction. -/
def primeCubic (x : ℕ) : ℕ := x ^ 3 - x

namespace CookMagyarCircle

/-- The additive character `e(kα) = exp(2πikα)`. -/
noncomputable def addChar (α : ℝ) (k : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (α : ℂ))

/-- The negative-frequency character `e(-kα)`. -/
noncomputable def negAddChar (α : ℝ) (k : ℕ) : ℂ :=
  Complex.exp (-2 * Real.pi * Complex.I * (α : ℂ) * (k : ℂ))

@[simp] theorem addChar_zero_left (k : ℕ) : addChar 0 k = 1 := by
  simp [addChar]

@[simp] theorem addChar_zero_right (α : ℝ) : addChar α 0 = 1 := by
  simp [addChar]

@[simp] theorem negAddChar_zero_left (k : ℕ) : negAddChar 0 k = 1 := by
  simp [negAddChar]

@[simp] theorem negAddChar_zero_right (α : ℝ) : negAddChar α 0 = 1 := by
  simp [negAddChar]

@[simp] theorem norm_addChar (α : ℝ) (k : ℕ) : ‖addChar α k‖ = 1 := by
  unfold addChar
  have h :
      2 * Real.pi * Complex.I * (k : ℂ) * (α : ℂ) =
        ((2 * Real.pi * k * α : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

@[simp] theorem norm_negAddChar (α : ℝ) (k : ℕ) : ‖negAddChar α k‖ = 1 := by
  unfold negAddChar
  have h :
      -2 * Real.pi * Complex.I * (α : ℂ) * (k : ℂ) =
        ((-2 * Real.pi * α * k : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- Additivity of the frequency becomes multiplication of characters. -/
theorem addChar_add (α : ℝ) (a b : ℕ) :
    addChar α (a + b) = addChar α a * addChar α b := by
  unfold addChar
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The character of a finite sum is the product of the characters. -/
theorem addChar_sum {ι : Type*} [Fintype ι] (α : ℝ) (f : ι → ℕ) :
    addChar α (∑ i, f i) = ∏ i, addChar α (f i) := by
  classical
  have aux : ∀ s : Finset ι,
      addChar α (∑ i ∈ s, f i) = ∏ i ∈ s, addChar α (f i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.prod_insert ha, addChar_add, ih]
  simpa using aux Finset.univ

/-- Orthogonality of integer frequencies on one period. -/
theorem integral_exp_int_frequency (k : ℤ) :
    ∫ α in Set.Icc (0 : ℝ) 1,
        Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (α : ℂ)) =
      if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · simp [hk]
  · have hcoeff_zero :
        fourierCoeffOn (a := (0 : ℝ)) (b := 1) zero_lt_one
          (fun _ : ℝ ↦ (1 : ℂ)) (-k) = 0 := by
      have h := fourierCoeffOn_of_hasDerivAt (hab := zero_lt_one)
        (n := -k) (hn := neg_ne_zero.mpr hk)
        (f := fun _ : ℝ ↦ (1 : ℂ)) (f' := fun _ : ℝ ↦ (0 : ℂ))
        (by
          intro x _hx
          simpa using (hasDerivAt_const (x := x) (c := (1 : ℂ))))
        (by
          simp : IntervalIntegrable (fun _ : ℝ ↦ (0 : ℂ)) volume (0 : ℝ) 1)
      have hz :
          fourierCoeffOn (a := (0 : ℝ)) (b := 1) zero_lt_one
            (fun _ : ℝ ↦ (0 : ℂ)) (-k) = 0 := by
        rw [fourierCoeffOn_eq_integral]
        simp
      rw [hz] at h
      simpa using h
    have hcoeff_int := fourierCoeffOn_eq_integral (a := (0 : ℝ)) (b := 1)
      (f := fun _ : ℝ ↦ (1 : ℂ)) (-k) zero_lt_one
    simp only [sub_zero, one_div, inv_one, one_smul] at hcoeff_int
    rw [intervalIntegral.integral_of_le zero_le_one] at hcoeff_int
    rw [← integral_Icc_eq_integral_Ioc] at hcoeff_int
    have hint_zero :
        ∫ x in Set.Icc (0 : ℝ) 1, fourier k (x : AddCircle (1 : ℝ)) = 0 := by
      simpa [hk] using hcoeff_int.symm.trans hcoeff_zero
    rw [if_neg hk]
    convert hint_zero using 2
    ext x
    rw [fourier_coe_apply]
    push_cast
    ring_nf

/-- Orthogonality in the natural-number frequency convention used below. -/
theorem integral_addChar_mul_negAddChar (m n : ℕ) :
    ∫ α in Set.Icc (0 : ℝ) 1, addChar α m * negAddChar α n =
      if m = n then 1 else 0 := by
  have horth := integral_exp_int_frequency ((m : ℤ) - (n : ℤ))
  have hif :
      (if ((m : ℤ) - (n : ℤ) : ℤ) = 0 then (1 : ℂ) else 0) =
        if m = n then 1 else 0 := by
    split_ifs with h hmn hmn
    · rfl
    · omega
    · omega
    · rfl
  rw [hif] at horth
  rw [← horth]
  apply integral_congr_ae
  filter_upwards with α
  unfold addChar negAddChar
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring_nf

/-- The cubic von-Mangoldt exponential sum at scale `N`.  The indexing type
`Fin (N+1)` represents the closed interval `0 ≤ x ≤ N`. -/
noncomputable def cubicVonMangoldtExpSum (α : ℝ) (N : ℕ) : ℂ :=
  ∑ x : Fin (N + 1),
    (ArithmeticFunction.vonMangoldt x : ℂ) * addChar α (primeCubic x)

/-- The real von-Mangoldt weight of a tuple. -/
noncomputable def tupleVonMangoldtWeight {n N : ℕ}
    (x : Fin n → Fin (N + 1)) : ℝ :=
  ∏ i, ArithmeticFunction.vonMangoldt (x i)

/-- Weighted number of representations
`T = Σ_i (x_i^3-x_i)` with `0 ≤ x_i ≤ N`. -/
noncomputable def cubicVonMangoldtRepresentation
    (n N T : ℕ) : ℝ :=
  ∑ x : Fin n → Fin (N + 1),
    if (∑ i, primeCubic (x i)) = T then tupleVonMangoldtWeight x else 0

private theorem product_weighted_addChar {n N : ℕ}
    (α : ℝ) (x : Fin n → Fin (N + 1)) :
    (∏ i,
        (ArithmeticFunction.vonMangoldt (x i) : ℂ) *
          addChar α (primeCubic (x i))) =
      (tupleVonMangoldtWeight x : ℂ) *
        addChar α (∑ i, primeCubic (x i)) := by
  rw [Finset.prod_mul_distrib]
  rw [← addChar_sum]
  simp only [tupleVonMangoldtWeight]
  push_cast
  rfl

/-- The exact Fourier coefficient identity underlying the specialized circle
method.  This theorem is independent of every major/minor-arc estimate. -/
theorem integral_cubicVonMangoldtExpSum_pow (n N T : ℕ) :
    ∫ α in Set.Icc (0 : ℝ) 1,
        (cubicVonMangoldtExpSum α N) ^ n * negAddChar α T =
      (cubicVonMangoldtRepresentation n N T : ℂ) := by
  classical
  have hpoint : ∀ α : ℝ,
      (cubicVonMangoldtExpSum α N) ^ n * negAddChar α T =
        ∑ x : Fin n → Fin (N + 1),
          (tupleVonMangoldtWeight x : ℂ) *
            (addChar α (∑ i, primeCubic (x i)) * negAddChar α T) := by
    intro α
    rw [cubicVonMangoldtExpSum, Fintype.sum_pow]
    simp_rw [product_weighted_addChar]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _hx
    ring
  rw [setIntegral_congr_fun measurableSet_Icc (fun α _hα ↦ hpoint α)]
  rw [integral_finsetSum]
  · rw [cubicVonMangoldtRepresentation]
    push_cast
    apply Finset.sum_congr rfl
    intro x _hx
    rw [show
        (∫ α in Set.Icc (0 : ℝ) 1,
            (tupleVonMangoldtWeight x : ℂ) *
              (addChar α (∑ i, primeCubic (x i)) * negAddChar α T)) =
          (tupleVonMangoldtWeight x : ℂ) *
            ∫ α in Set.Icc (0 : ℝ) 1,
              addChar α (∑ i, primeCubic (x i)) * negAddChar α T by
        rw [← integral_indicator measurableSet_Icc,
          ← integral_indicator measurableSet_Icc]
        simp_rw [Set.indicator_const_mul]
        exact MeasureTheory.integral_const_mul _ _]
    rw [integral_addChar_mul_negAddChar]
    split_ifs <;> simp_all
  · intro x _hx
    apply Continuous.integrableOn_Icc
    unfold addChar negAddChar
    fun_prop

/-- Every summand in the weighted representation count is nonnegative. -/
theorem cubicVonMangoldtRepresentation_nonneg (n N T : ℕ) :
    0 ≤ cubicVonMangoldtRepresentation n N T := by
  classical
  unfold cubicVonMangoldtRepresentation tupleVonMangoldtWeight
  exact Finset.sum_nonneg fun x _ ↦ by
    split_ifs
    · exact Finset.prod_nonneg fun i _ ↦ ArithmeticFunction.vonMangoldt_nonneg
    · exact le_rfl

/-- A bounded representation by prime powers.  This is exactly what
positivity of the von-Mangoldt-weighted coefficient detects before the
prime-power-removal argument is applied. -/
def IsPrimePowerCubicRepresentation (n N T : ℕ) : Prop :=
  ∃ x : Fin n → Fin (N + 1),
    (∑ i, primeCubic (x i)) = T ∧ ∀ i, IsPrimePow (x i : ℕ)

private theorem tupleVonMangoldtWeight_pos_iff {n N : ℕ}
    (x : Fin n → Fin (N + 1)) :
    0 < tupleVonMangoldtWeight x ↔ ∀ i, IsPrimePow (x i : ℕ) := by
  classical
  constructor
  · intro h i
    have hne : tupleVonMangoldtWeight x ≠ 0 := ne_of_gt h
    have hprod : (∏ j, ArithmeticFunction.vonMangoldt (x j)) ≠ 0 := by
      simpa [tupleVonMangoldtWeight] using hne
    have hall : ∀ j ∈ (Finset.univ : Finset (Fin n)),
        ArithmeticFunction.vonMangoldt (x j) ≠ 0 :=
      Finset.prod_ne_zero_iff.mp hprod
    exact ArithmeticFunction.vonMangoldt_ne_zero_iff.mp (hall i (Finset.mem_univ i))
  · intro h
    unfold tupleVonMangoldtWeight
    exact Finset.prod_pos fun i _ ↦
      ArithmeticFunction.vonMangoldt_pos_iff.mpr (h i)

/-- Positivity of the exact Fourier coefficient is equivalent to the
existence of a bounded prime-power representation. -/
theorem cubicVonMangoldtRepresentation_pos_iff (n N T : ℕ) :
    0 < cubicVonMangoldtRepresentation n N T ↔
      IsPrimePowerCubicRepresentation n N T := by
  classical
  unfold cubicVonMangoldtRepresentation IsPrimePowerCubicRepresentation
  have hnonneg : ∀ x : Fin n → Fin (N + 1),
      0 ≤ if (∑ i, primeCubic (x i)) = T then tupleVonMangoldtWeight x else 0 := by
    intro x
    split_ifs
    · exact Finset.prod_nonneg fun i _ ↦ ArithmeticFunction.vonMangoldt_nonneg
    · exact le_rfl
  rw [Finset.sum_pos_iff_of_nonneg (fun x _hx ↦ hnonneg x)]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, hx⟩
    by_cases heq : (∑ i, primeCubic (x i)) = T
    · refine ⟨x, heq, ?_⟩
      have hwpos : 0 < tupleVonMangoldtWeight x := by simpa [heq] using hx
      exact (tupleVonMangoldtWeight_pos_iff x).mp hwpos
    · simp [heq] at hx
  · rintro ⟨x, heq, hx⟩
    refine ⟨x, ?_⟩
    have hwpos : 0 < tupleVonMangoldtWeight x :=
      (tupleVonMangoldtWeight_pos_iff x).mpr hx
    simpa [heq] using hwpos

end CookMagyarCircle
end SystolicGrowth
