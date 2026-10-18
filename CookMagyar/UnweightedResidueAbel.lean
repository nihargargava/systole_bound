module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.UnweightedResidueCount
public import CookMagyar.CubicAbelPhase

@[expose] public section

open Finset MeasureTheory

namespace SystolicGrowth
namespace CookMagyarMajorArc

open CookMagyarCircle

/-! # All-residue cubic Abel approximation

The elementary `1/q` density applies to every residue, not merely to
units. The resulting error bound is uniform in the residue and phase.
-/

/-- Indicator minus uniform density for one residue class. -/
noncomputable def cubicAllResidueErrorCoefficient
    (q r k : ℕ) : ℂ :=
  (if k ≡ r [MOD q] then (1 : ℂ) else 0) - ((1 / (q : ℝ) : ℝ) : ℂ)

/-- The inclusive partial sum of the all-residue error has norm at most
one, uniformly over every positive modulus and every residue. -/
theorem norm_sum_cubicAllResidueErrorCoefficient_le_one
    (q m r : ℕ) (hq : 0 < q) :
    ‖∑ k ∈ Icc 0 m, cubicAllResidueErrorCoefficient q r k‖ ≤ 1 := by
  have hpoint (k : ℕ) :
      cubicAllResidueErrorCoefficient q r k =
        ((((if k ≡ r [MOD q] then (1 : ℝ) else 0) - 1 / (q : ℝ)) : ℝ) : ℂ) := by
    by_cases hk : k ≡ r [MOD q]
    · simp [cubicAllResidueErrorCoefficient, hk]
    · simp [cubicAllResidueErrorCoefficient, hk]
  calc
    ‖∑ k ∈ Icc 0 m, cubicAllResidueErrorCoefficient q r k‖ =
        ‖(((∑ k ∈ Icc 0 m,
            ((if k ≡ r [MOD q] then (1 : ℝ) else 0) - 1 / (q : ℝ))) : ℝ) : ℂ)‖ := by
      congr 1
      rw [Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro k _
      exact hpoint k
    _ = |∑ k ∈ Icc 0 m,
          ((if k ≡ r [MOD q] then (1 : ℝ) else 0) - 1 / (q : ℝ))| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ 1 := abs_sum_cubicAllResidueError_Icc_le_one q m r hq

/-- The unweighted cubic sum over one residue class. -/
noncomputable def cubicUnweightedResidueClassSum
    (q r : ℕ) (beta : ℝ) (N : ℕ) : ℂ :=
  ∑ k ∈ Icc 0 N,
    if k ≡ r [MOD q] then addChar beta (primeCubic k) else 0

/-- The uniform-density model for a single residue class. -/
noncomputable def cubicUnweightedResidueClassModel
    (q : ℕ) (beta : ℝ) (N : ℕ) : ℂ :=
  ((1 / (q : ℝ) : ℝ) : ℂ) *
    ∑ k ∈ Icc 0 N, addChar beta (primeCubic k)

/-- Elementary all-residue Abel estimate. It needs no prime theorem and
holds for arbitrary real `beta` and every positive modulus. -/
theorem norm_cubicUnweightedResidueClassSum_sub_model_le
    (q r : ℕ) (hq : 0 < q) (beta : ℝ) (N : ℕ) (hN : 0 < N) :
    ‖cubicUnweightedResidueClassSum q r beta N -
        cubicUnweightedResidueClassModel q beta N‖ ≤
      1 + (N : ℝ) *
        (2 * Real.pi * |beta| * (3 * (N : ℝ) ^ 2 + 1)) := by
  have hpartial : ∀ t ∈ Set.Ioc (0 : ℝ) N,
      ‖∑ k ∈ Icc 0 ⌊t⌋₊, cubicAllResidueErrorCoefficient q r k‖ ≤ 1 := by
    intro t _
    exact norm_sum_cubicAllResidueErrorCoefficient_le_one q ⌊t⌋₊ r hq
  have habel := norm_sum_addChar_primeCubic_le_partialSumBound
    (cubicAllResidueErrorCoefficient q r) beta N hN (by norm_num) hpartial
  have hsum :
      (∑ k ∈ Icc 0 N,
        addChar beta (primeCubic k) * cubicAllResidueErrorCoefficient q r k) =
        cubicUnweightedResidueClassSum q r beta N -
          cubicUnweightedResidueClassModel q beta N := by
    unfold cubicAllResidueErrorCoefficient
      cubicUnweightedResidueClassSum cubicUnweightedResidueClassModel
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    have hfirst :
        (∑ k ∈ Icc 0 N,
          addChar beta (primeCubic k) *
            (if k ≡ r [MOD q] then (1 : ℂ) else 0)) =
          ∑ k ∈ Icc 0 N,
            if k ≡ r [MOD q] then addChar beta (primeCubic k) else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      split_ifs <;> simp
    rw [hfirst, ← Finset.sum_mul]
    ring
  rw [hsum] at habel
  simpa only [one_mul] using habel

end CookMagyarMajorArc
end SystolicGrowth
