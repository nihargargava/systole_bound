module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-!
# Finite norm-square expansion for Hua's Type-II step

This elementary finite identity is the first algebraic step of the
mean-square estimate in `MinorArcExerciseGaps.lean`. The support of the inner
sum may depend on the outer index. It makes no analytic cancellation claim;
the diagonal, off-diagonal, and divisor-frequency bounds remain separate.
-/

open Finset ComplexConjugate
open scoped BigOperators

namespace SystolicGrowth.CookMagyarCircle

/-- Expand one finite complex norm square into all ordered pairs of summands.
This is the exact expression whose diagonal and off-diagonal terms are
estimated separately in Hua's Type-II argument. -/
theorem norm_sum_sq_eq_sum_pair_real {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 2 =
      ∑ i ∈ s, ∑ j ∈ s, (f i * conj (f j)).re := by
  have hexpand :
      (∑ i ∈ s, f i) * conj (∑ j ∈ s, f j) =
        ∑ i ∈ s, ∑ j ∈ s, f i * conj (f j) := by
    calc
      _ = (∑ i ∈ s, f i) * (∑ j ∈ s, conj (f j)) := by rw [map_sum]
      _ = ∑ i ∈ s, f i * (∑ j ∈ s, conj (f j)) := by rw [Finset.sum_mul]
      _ = _ := by simp only [Finset.mul_sum]
  have hnorm := Complex.mul_conj' (∑ i ∈ s, f i)
  rw [hnorm] at hexpand
  have hre := congrArg Complex.re hexpand
  rw [← Complex.ofReal_pow] at hre
  simpa only [Complex.ofReal_re, Complex.re_sum] using hre

/-- Sum the preceding identity over outer blocks, with an independently
chosen finite inner support at each block. In the Hua application the support
is a fixed divisor set intersected with the interval depending on `u`. -/
theorem sum_norm_sum_sq_eq_sum_triples_real
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (U : Finset ι) (V : ι → Finset κ) (f : ι → κ → ℂ) :
    (∑ u ∈ U, ‖∑ v ∈ V u, f u v‖ ^ 2) =
      ∑ u ∈ U, ∑ v ∈ V u, ∑ w ∈ V u,
        (f u v * conj (f u w)).re := by
  apply Finset.sum_congr rfl
  intro u hu
  exact norm_sum_sq_eq_sum_pair_real (V u) (f u)

/-- Separate equal inner indices from the ordered pairs. The first sum is
nonnegative; all cancellation needed by the Type-II estimate lies in the
second sum, whose inner index is explicitly erased from the finite support. -/
theorem sum_pair_real_eq_diagonal_add_offDiagonal
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℂ) :
    (∑ i ∈ s, ∑ j ∈ s, (f i * conj (f j)).re) =
      (∑ i ∈ s, ‖f i‖ ^ 2) +
        ∑ i ∈ s, ∑ j ∈ s.erase i, (f i * conj (f j)).re := by
  calc
    _ = ∑ i ∈ s, (‖f i‖ ^ 2 +
          ∑ j ∈ s.erase i, (f i * conj (f j)).re) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hsplit := Finset.add_sum_erase s
        (fun j => (f i * conj (f j)).re) hi
      rw [← hsplit]
      rw [Complex.mul_conj']
      rw [← Complex.ofReal_pow]
      simp only [Complex.ofReal_re]
    _ = _ := by rw [Finset.sum_add_distrib]

/-- The diagonal/off-diagonal split, now summed over arbitrary outer blocks.
It can be applied directly to the exact `u`-dependent support in Hua step 9. -/
theorem sum_norm_sum_sq_eq_diagonal_add_offDiagonal
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (U : Finset ι) (V : ι → Finset κ) (f : ι → κ → ℂ) :
    (∑ u ∈ U, ‖∑ v ∈ V u, f u v‖ ^ 2) =
      (∑ u ∈ U, ∑ v ∈ V u, ‖f u v‖ ^ 2) +
        ∑ u ∈ U, ∑ v ∈ V u, ∑ w ∈ (V u).erase v,
          (f u v * conj (f u w)).re := by
  rw [sum_norm_sum_sq_eq_sum_triples_real]
  simp_rw [sum_pair_real_eq_diagonal_add_offDiagonal]
  rw [Finset.sum_add_distrib]

/-- The diagonal needs only a termwise norm bound and a cardinality bound on
each inner support. In Hua's application each phase has norm one; the bound
on the interval support is a separate finite-counting exercise. -/
theorem diagonal_le_card_mul
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (U : Finset ι) (V : ι → Finset κ) (f : ι → κ → ℂ)
    (M : ℝ)
    (hphase : ∀ u ∈ U, ∀ v ∈ V u, ‖f u v‖ ≤ 1)
    (hcard : ∀ u ∈ U, ((V u).card : ℝ) ≤ M) :
    (∑ u ∈ U, ∑ v ∈ V u, ‖f u v‖ ^ 2) ≤ (U.card : ℝ) * M := by
  calc
    _ ≤ ∑ u ∈ U, ∑ _v ∈ V u, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro v hv
      nlinarith [hphase u hu v hv, norm_nonneg (f u v)]
    _ = ∑ u ∈ U, ((V u).card : ℝ) := by simp
    _ ≤ ∑ _u ∈ U, M := by
      apply Finset.sum_le_sum
      intro u hu
      exact hcard u hu
    _ = (U.card : ℝ) * M := by simp

#print axioms norm_sum_sq_eq_sum_pair_real
#print axioms sum_norm_sum_sq_eq_sum_triples_real
#print axioms sum_norm_sum_sq_eq_diagonal_add_offDiagonal
#print axioms diagonal_le_card_mul

end SystolicGrowth.CookMagyarCircle
