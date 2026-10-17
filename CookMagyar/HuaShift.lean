module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.HuaEstimate
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace SystolicGrowth
namespace CookMagyarCircle

/-! # Finite shift identities for the cubic eighth moment

The second-difference energy is proved in `HuaEstimate`. This module
connects that energy to the unweighted cubic exponential sum. -/

/-- A finite complex sum splits into its diagonal terms and the two
orientations of each strict pair. The triangular sum is written in an
inductive form, ready to be reindexed by a positive shift. -/
theorem sum_range_mul_conj_sum_range (a : ℕ → ℂ) (n : ℕ) :
    (∑ m ∈ Finset.range n, a m) *
        conj (∑ m ∈ Finset.range n, a m) =
      (∑ m ∈ Finset.range n, a m * conj (a m)) +
        ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i,
          (a i * conj (a j) + a j * conj (a i)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [Finset.sum_range_succ]
      have hleft :
          (∑ m ∈ Finset.range n, a m) * conj (a n) =
            ∑ m ∈ Finset.range n, a m * conj (a n) := by
        rw [Finset.sum_mul]
      have hright :
          a n * conj (∑ m ∈ Finset.range n, a m) =
            ∑ m ∈ Finset.range n, a n * conj (a m) := by
        rw [map_sum, Finset.mul_sum]
      calc
        ((∑ m ∈ Finset.range n, a m) + a n) *
            conj ((∑ m ∈ Finset.range n, a m) + a n) =
          (∑ m ∈ Finset.range n, a m) *
              conj (∑ m ∈ Finset.range n, a m) +
            (∑ m ∈ Finset.range n, a m) * conj (a n) +
            a n * conj (∑ m ∈ Finset.range n, a m) +
            a n * conj (a n) := by rw [map_add]; ring
        _ = (∑ m ∈ Finset.range n, a m * conj (a m)) +
              a n * conj (a n) +
            ((∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i,
                (a i * conj (a j) + a j * conj (a i))) +
              ∑ j ∈ Finset.range n,
                (a n * conj (a j) + a j * conj (a n))) := by
              rw [ih, hleft, hright]
              simp only [Finset.sum_add_distrib]
              ring

/-- The two orientations of the strict pairs are conjugates. -/
private theorem sum_strict_pairs_eq_add_conj (a : ℕ → ℂ) (n : ℕ) :
    (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i,
      (a i * conj (a j) + a j * conj (a i))) =
    (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i,
      a i * conj (a j)) +
      conj (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i,
        a i * conj (a j)) := by
  simp only [map_sum, map_mul]
  simp only [Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp [mul_comm]

/-- The real diagonal/off-diagonal identity for an arbitrary finite
complex sequence. -/
theorem norm_sum_range_sq_eq_diagonal_add_pairs (a : ℕ → ℂ) (n : ℕ) :
    ‖∑ m ∈ Finset.range n, a m‖ ^ 2 =
      (∑ m ∈ Finset.range n, ‖a m‖ ^ 2) +
        2 * (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i,
          a i * conj (a j)).re := by
  have h := sum_range_mul_conj_sum_range a n
  rw [sum_strict_pairs_eq_add_conj] at h
  rw [Complex.add_conj] at h
  simp_rw [Complex.mul_conj'] at h
  apply Complex.ofReal_injective
  push_cast
  push_cast at h
  exact h

/-- The unweighted cubic character sum on the closed interval `0 ≤ m ≤ N`. -/
noncomputable def cubicUnweightedExpSum (α : ℝ) (N : ℕ) : ℂ :=
  ∑ m ∈ Finset.range (N + 1), addChar α (primeCubic m)

/-- Ordered strict pairs of indices, before reindexing by positive shifts. -/
noncomputable def cubicStrictPairSum (α : ℝ) (N : ℕ) : ℂ :=
  ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range i,
    addChar α (primeCubic i) * negAddChar α (primeCubic j)

/-- First diagonal/off-diagonal identity for the cubic sum. -/
theorem norm_cubicUnweightedExpSum_sq_eq_strictPairs
    (α : ℝ) (N : ℕ) :
    ‖cubicUnweightedExpSum α N‖ ^ 2 =
      (N + 1 : ℝ) + 2 * (cubicStrictPairSum α N).re := by
  have h := norm_sum_range_sq_eq_diagonal_add_pairs
    (fun m => addChar α (primeCubic m)) (N + 1)
  simp_rw [conj_addChar] at h
  simp only [norm_addChar, one_pow, Finset.sum_const,
    nsmul_eq_mul, mul_one] at h
  simpa [cubicUnweightedExpSum, cubicStrictPairSum] using h

/-- Ordered pairs `j < i` in the cubic summation interval. -/
def strictCubicIndexPairs (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (N + 1)).product (Finset.range (N + 1))).filter
    fun ij => ij.2 < ij.1

/-- The same pairs parameterized by a positive gap and a base point. -/
def positiveCubicShiftPairs (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (N + 1)).product (Finset.range (N + 1))).filter
    fun hm => 0 < hm.1 ∧ hm.2 + hm.1 ≤ N

/-- Rewrite the triangular iterated sum as a sum over strict index pairs. -/
theorem sum_triangle_eq_strictCubicIndexPairs
    (N : ℕ) (g : ℕ → ℕ → ℂ) :
    (∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range i, g i j) =
      ∑ ij ∈ strictCubicIndexPairs N, g ij.1 ij.2 := by
  classical
  rw [strictCubicIndexPairs, Finset.sum_filter]
  change (∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range i, g i j) =
    ∑ a ∈ Finset.range (N + 1) ×ˢ Finset.range (N + 1),
      if a.2 < a.1 then g a.1 a.2 else 0
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i hi
  have hle : i ≤ N + 1 := Nat.le_of_lt (Finset.mem_range.mp hi)
  have hfilter :
      (Finset.range (N + 1)).filter (fun j => j < i) = Finset.range i := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [← hfilter, Finset.sum_filter]

/-- The exact change of variables `(i,j) ↔ (h=i-j,m=j)`. -/
theorem sum_strictCubicIndexPairs_eq_positiveShiftPairs
    (N : ℕ) (g : ℕ → ℕ → ℂ) :
    (∑ ij ∈ strictCubicIndexPairs N, g ij.1 ij.2) =
      ∑ hm ∈ positiveCubicShiftPairs N, g (hm.2 + hm.1) hm.2 := by
  classical
  refine Finset.sum_bij'
    (fun ij _ => (ij.1 - ij.2, ij.2))
    (fun hm _ => (hm.2 + hm.1, hm.2)) ?_ ?_ ?_ ?_ ?_
  · intro ij hij
    rcases (Finset.mem_filter.mp hij).2 with hji
    have hpair := (Finset.mem_filter.mp hij).1
    have hi : ij.1 < N + 1 :=
      Finset.mem_range.mp (Finset.mem_product.mp hpair).1
    have hj : ij.2 < N + 1 :=
      Finset.mem_range.mp (Finset.mem_product.mp hpair).2
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_product.mpr
      constructor <;> exact Finset.mem_range.mpr (by omega)
    · constructor <;> omega
  · intro hm hhm
    rcases (Finset.mem_filter.mp hhm).2 with ⟨hpos, hbound⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_product.mpr
      constructor <;> exact Finset.mem_range.mpr (by omega)
    · omega
  · intro ij hij
    have hji : ij.2 ≤ ij.1 := by
      have hlt := (Finset.mem_filter.mp hij).2
      omega
    apply Prod.ext
    · dsimp; omega
    · rfl
  · intro hm hhm
    apply Prod.ext
    · dsimp; omega
    · rfl
  · intro ij hij
    congr 1
    have hlt := (Finset.mem_filter.mp hij).2
    omega

/-- Group a positive-gap pair sum first by its gap and then by its base. -/
theorem sum_positiveCubicShiftPairs_eq_sum_by_shift
    (N : ℕ) (g : ℕ → ℕ → ℂ) :
    (∑ hm ∈ positiveCubicShiftPairs N, g hm.1 hm.2) =
      ∑ h ∈ Finset.Icc 1 N,
        ∑ m ∈ Finset.range (N + 1 - h), g h m := by
  classical
  have hIcc : Finset.Icc 1 N =
      (Finset.range (N + 1)).filter fun h => 0 < h := by
    ext h
    simp only [Finset.mem_Icc, Finset.mem_filter, Finset.mem_range]
    omega
  unfold positiveCubicShiftPairs
  rw [Finset.sum_filter]
  change (∑ hm ∈ Finset.range (N + 1) ×ˢ Finset.range (N + 1),
    if 0 < hm.1 ∧ hm.2 + hm.1 ≤ N then g hm.1 hm.2 else 0) = _
  rw [Finset.sum_product, hIcc, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro h hh
  by_cases hpos : 0 < h
  · simp only [hpos, true_and, if_true]
    have hfilter :
        (Finset.range (N + 1)).filter (fun m => m + h ≤ N) =
          Finset.range (N + 1 - h) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_range]
      have hle : h ≤ N := by
        have hlt := Finset.mem_range.mp hh
        omega
      omega
    rw [← Finset.sum_filter, hfilter]
  · simp [hpos]

/-- The strict-pair sum written with its positive gap. -/
noncomputable def cubicPositiveShiftSum (α : ℝ) (N : ℕ) : ℂ :=
  ∑ hm ∈ positiveCubicShiftPairs N,
    addChar α (primeCubic (hm.2 + hm.1)) *
      negAddChar α (primeCubic hm.2)

/-- The cubic autocorrelation for one positive shift. -/
noncomputable def cubicFixedShiftSum (α : ℝ) (N h : ℕ) : ℂ :=
  ∑ m ∈ Finset.range (N + 1 - h),
    addChar α (primeCubic (m + h)) * negAddChar α (primeCubic m)

theorem cubicPositiveShiftSum_eq_sum_fixedShift
    (α : ℝ) (N : ℕ) :
    cubicPositiveShiftSum α N =
      ∑ h ∈ Finset.Icc 1 N, cubicFixedShiftSum α N h := by
  unfold cubicPositiveShiftSum cubicFixedShiftSum
  exact sum_positiveCubicShiftPairs_eq_sum_by_shift N
    (fun h m => addChar α (primeCubic (m + h)) *
      negAddChar α (primeCubic m))

theorem cubicStrictPairSum_eq_positiveShiftSum (α : ℝ) (N : ℕ) :
    cubicStrictPairSum α N = cubicPositiveShiftSum α N := by
  unfold cubicStrictPairSum cubicPositiveShiftSum
  rw [sum_triangle_eq_strictCubicIndexPairs]
  exact sum_strictCubicIndexPairs_eq_positiveShiftPairs N
    (fun i j => addChar α (primeCubic i) * negAddChar α (primeCubic j))

/-- First cubic shift identity, with every diagonal and every positive gap
accounted for once. -/
theorem norm_cubicUnweightedExpSum_sq_eq_positiveShiftSum
    (α : ℝ) (N : ℕ) :
    ‖cubicUnweightedExpSum α N‖ ^ 2 =
      (N + 1 : ℝ) + 2 * (cubicPositiveShiftSum α N).re := by
  rw [norm_cubicUnweightedExpSum_sq_eq_strictPairs,
    cubicStrictPairSum_eq_positiveShiftSum]

/-- The off-diagonal term after squaring one fixed-shift sum is exactly a
positive cubic second-difference character. -/
theorem cubicSecondDifference_addChar (α : ℝ) (h k m : ℕ) :
    addChar α (3 * h * k * (2 * m + h + k)) =
      addChar α (primeCubic (m + h + k)) *
        negAddChar α (primeCubic (m + k)) *
        negAddChar α (primeCubic (m + h)) *
        addChar α (primeCubic m) := by
  have hfreqZ : ((3 * h * k * (2 * m + h + k) : ℕ) : ℤ) =
      ((primeCubic (m + h + k) : ℤ) - primeCubic (m + k)) -
        ((primeCubic (m + h) : ℤ) - primeCubic m) := by
    calc
      _ = (h : ℤ) * k * (6 * (m : ℤ) + 3 * h + 3 * k) := by
        push_cast
        ring
      _ = _ := (primeCubic_second_difference h k m).symm
  have hfreqC : ((3 * h * k * (2 * m + h + k) : ℕ) : ℂ) =
      ((primeCubic (m + h + k) : ℂ) - primeCubic (m + k)) -
        ((primeCubic (m + h) : ℂ) - primeCubic m) := by
    exact_mod_cast hfreqZ
  unfold addChar negAddChar
  simp only [← Complex.exp_add]
  congr 1
  rw [hfreqC]
  ring

/-- The conjugate of a negative cubic character is the positive character. -/
private theorem conj_negAddChar (α : ℝ) (n : ℕ) :
    conj (negAddChar α n) = addChar α n := by
  simp [← conj_addChar]

/-- The off-diagonal product for a fixed first shift has the orientation
of the positive second difference. -/
theorem cubicFixedShiftPair_eq_secondDifference
    (α : ℝ) (h k m : ℕ) :
    (addChar α (primeCubic (m + k + h)) *
        negAddChar α (primeCubic (m + k))) *
      conj (addChar α (primeCubic (m + h)) *
        negAddChar α (primeCubic m)) =
      addChar α (3 * h * k * (2 * m + h + k)) := by
  rw [map_mul, conj_addChar, conj_negAddChar]
  rw [cubicSecondDifference_addChar]
  rw [show m + k + h = m + h + k by omega]
  ring

/-- The squared norm of one positive-shift autocorrelation has only its
unit-modulus diagonal and positive second-difference off-diagonal. -/
theorem norm_cubicFixedShiftSum_sq_eq_secondDifferencePairs
    (α : ℝ) (N h : ℕ) (hh : h ≤ N) :
    ‖cubicFixedShiftSum α N h‖ ^ 2 =
      ((N + 1 - h : ℕ) : ℝ) +
        2 * (∑ km ∈ positiveCubicShiftPairs (N - h),
          addChar α (3 * h * km.1 * (2 * km.2 + h + km.1))).re := by
  let a : ℕ → ℂ := fun m =>
    addChar α (primeCubic (m + h)) * negAddChar α (primeCubic m)
  have hlen : N + 1 - h = (N - h) + 1 := by omega
  have hdiag : ∀ m, ‖a m‖ ^ 2 = (1 : ℝ) := by
    intro m
    dsimp [a]
    rw [norm_mul]
    simp [← conj_addChar, norm_addChar]
  have hpairs :
      (∑ i ∈ Finset.range ((N - h) + 1),
        ∑ j ∈ Finset.range i, a i * conj (a j)) =
      ∑ km ∈ positiveCubicShiftPairs (N - h),
        addChar α (3 * h * km.1 * (2 * km.2 + h + km.1)) := by
    rw [sum_triangle_eq_strictCubicIndexPairs]
    calc
      _ = ∑ km ∈ positiveCubicShiftPairs (N - h),
          a (km.2 + km.1) * conj (a km.2) :=
        sum_strictCubicIndexPairs_eq_positiveShiftPairs (N - h)
          (fun i j => a i * conj (a j))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro km hkm
        exact cubicFixedShiftPair_eq_secondDifference α h km.1 km.2
  have hnorm := norm_sum_range_sq_eq_diagonal_add_pairs
    a ((N - h) + 1)
  simp_rw [hdiag] at hnorm
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_range] at hnorm
  rw [hpairs] at hnorm
  simpa only [cubicFixedShiftSum, hlen, a] using hnorm

/-- The iterated positive shifts are exactly the `Fin`-indexed domain used
by the already proved second-difference energy estimate. -/
theorem sum_positiveShiftPairs_eq_secondDifferenceTriples
    (N : ℕ) (g : ℕ → ℕ → ℕ → ℂ) :
    (∑ h ∈ Finset.Icc 1 N,
      ∑ km ∈ positiveCubicShiftPairs (N - h), g h km.1 km.2) =
    ∑ hkm ∈ positiveCubicSecondDifferenceTriples N,
      g hkm.1.val hkm.2.1.val hkm.2.2.val := by
  classical
  rw [Finset.sum_sigma']
  refine Finset.sum_bij'
    (fun x hx =>
      ((⟨x.1, by
          have hh := (Finset.mem_sigma.mp hx).1
          have hle := (Finset.mem_Icc.mp hh).2
          omega⟩ : Fin (N + 1)),
       ((⟨x.2.1, by
          have hx' := (Finset.mem_sigma.mp hx).2
          have hpair := (Finset.mem_filter.mp hx').1
          have hk := (Finset.mem_product.mp hpair).1
          have hle := (Finset.mem_Icc.mp (Finset.mem_sigma.mp hx).1).2
          have hk' := Finset.mem_range.mp hk
          omega⟩ : Fin (N + 1)),
        (⟨x.2.2, by
          have hx' := (Finset.mem_sigma.mp hx).2
          have hpair := (Finset.mem_filter.mp hx').1
          have hm := (Finset.mem_product.mp hpair).2
          have hle := (Finset.mem_Icc.mp (Finset.mem_sigma.mp hx).1).2
          have hm' := Finset.mem_range.mp hm
          omega⟩ : Fin (N + 1)))))
    (fun y _ => ⟨y.1.val, (y.2.1.val, y.2.2.val)⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro x hx
    have hh := (Finset.mem_Icc.mp (Finset.mem_sigma.mp hx).1)
    have hkm := (Finset.mem_filter.mp (Finset.mem_sigma.mp hx).2).2
    simp only [positiveCubicSecondDifferenceTriples, Finset.mem_filter,
      Finset.mem_univ, true_and]
    omega
  · intro y hy
    rcases (Finset.mem_filter.mp hy).2 with ⟨hh, hk, hbound⟩
    have hle : y.1.val ≤ N := by omega
    have hkmle : y.2.2.val + y.2.1.val ≤ N - y.1.val := by omega
    apply Finset.mem_sigma.mpr
    constructor
    · change y.1.val ∈ Finset.Icc 1 N
      exact Finset.mem_Icc.mpr ⟨by omega, hle⟩
    · change (y.2.1.val, y.2.2.val) ∈
        positiveCubicShiftPairs (N - y.1.val)
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_product.mpr
        constructor <;> exact Finset.mem_range.mpr (by omega)
      · constructor <;> omega
  · intro x hx
    apply Sigma.ext
    · rfl
    · rfl
  · intro y hy
    apply Prod.ext
    · rfl
    · apply Prod.ext <;> rfl
  · intro x hx
    rfl

/-- Summing the fixed-shift square identities gives exactly the already
constructed positive second-difference sum. The diagonal remains in a
finite-sum form, avoiding any endpoint convention hidden in a closed form. -/
theorem sum_norm_cubicFixedShiftSum_sq_eq_secondDifference
    (α : ℝ) (N : ℕ) :
    (∑ h ∈ Finset.Icc 1 N, ‖cubicFixedShiftSum α N h‖ ^ 2) =
      (∑ h ∈ Finset.Icc 1 N, ((N + 1 - h : ℕ) : ℝ)) +
        2 * (cubicSecondDifferenceTripleSum α N).re := by
  calc
    _ = ∑ h ∈ Finset.Icc 1 N,
        (((N + 1 - h : ℕ) : ℝ) +
          2 * (∑ km ∈ positiveCubicShiftPairs (N - h),
            addChar α (3 * h * km.1 * (2 * km.2 + h + km.1))).re) := by
          apply Finset.sum_congr rfl
          intro h hh
          exact norm_cubicFixedShiftSum_sq_eq_secondDifferencePairs α N h
            (Finset.mem_Icc.mp hh).2
    _ = (∑ h ∈ Finset.Icc 1 N, ((N + 1 - h : ℕ) : ℝ)) +
          2 * (∑ h ∈ Finset.Icc 1 N,
            ∑ km ∈ positiveCubicShiftPairs (N - h),
              addChar α (3 * h * km.1 * (2 * km.2 + h + km.1))).re := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Complex.re_sum]
    _ = _ := by
      have hsum := sum_positiveShiftPairs_eq_secondDifferenceTriples N
        (fun h k m => addChar α (3 * h * k * (2 * m + h + k)))
      rw [hsum]
      rfl

/-- Closed form for the diagonal count from all positive shifts. -/
theorem cubicShiftDiagonalSum (N : ℕ) :
    (∑ h ∈ Finset.Icc 1 N, ((N + 1 - h : ℕ) : ℝ)) =
      (N : ℝ) * (N + 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hstep :
          (∑ h ∈ Finset.Icc 1 (N + 1),
            (((N + 1) + 1 - h : ℕ) : ℝ)) =
            (∑ h ∈ Finset.Icc 1 N,
              ((N + 1 - h : ℕ) : ℝ)) + (N + 1 : ℝ) := by
        rw [Finset.sum_Icc_succ_top (by omega)]
        have hterms :
            (∑ h ∈ Finset.Icc 1 N,
              (((N + 1) + 1 - h : ℕ) : ℝ)) =
              (∑ h ∈ Finset.Icc 1 N,
                (((N + 1 - h : ℕ) : ℝ) + 1)) := by
          apply Finset.sum_congr rfl
          intro h hh
          have hle := (Finset.mem_Icc.mp hh).2
          have heq : (N + 1) + 1 - h = (N + 1 - h) + 1 := by omega
          simp [heq]
        rw [hterms, Finset.sum_add_distrib]
        simp [Nat.card_Icc]
        ring
      rw [hstep, ih]
      push_cast
      ring

/-- The exact second shift identity: the diagonal is triangular and every
off-diagonal contributes once with each complex orientation. -/
theorem sum_norm_cubicFixedShiftSum_sq_eq_tripleSum
    (α : ℝ) (N : ℕ) :
    (∑ h ∈ Finset.Icc 1 N, ‖cubicFixedShiftSum α N h‖ ^ 2) =
      (N : ℝ) * (N + 1) / 2 +
        2 * (cubicSecondDifferenceTripleSum α N).re := by
  rw [sum_norm_cubicFixedShiftSum_sq_eq_secondDifference,
    cubicShiftDiagonalSum]

/-- Finite Cauchy--Schwarz for the sum over positive cubic shifts. -/
theorem norm_sum_cubicFixedShiftSum_sq_le
    (α : ℝ) (N : ℕ) :
    ‖∑ h ∈ Finset.Icc 1 N, cubicFixedShiftSum α N h‖ ^ 2 ≤
      (N : ℝ) *
        ∑ h ∈ Finset.Icc 1 N, ‖cubicFixedShiftSum α N h‖ ^ 2 := by
  have hnorm :
      ‖∑ h ∈ Finset.Icc 1 N, cubicFixedShiftSum α N h‖ ≤
        ∑ h ∈ Finset.Icc 1 N, ‖cubicFixedShiftSum α N h‖ :=
    norm_sum_le _ _
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := Finset.Icc 1 N)
    (f := fun h => ‖cubicFixedShiftSum α N h‖)
  calc
    _ ≤ (∑ h ∈ Finset.Icc 1 N,
        ‖cubicFixedShiftSum α N h‖) ^ 2 := by
          gcongr
    _ ≤ ((Finset.Icc 1 N).card : ℝ) *
        ∑ h ∈ Finset.Icc 1 N, ‖cubicFixedShiftSum α N h‖ ^ 2 := hcs
    _ = _ := by simp [Nat.card_Icc]

/-- Pointwise fourth-power differencing inequality, with the exact positive
second-difference energy and no zero-shift frequency. -/
theorem norm_cubicUnweightedExpSum_four_le_secondDifference
    (α : ℝ) (N : ℕ) :
    ‖cubicUnweightedExpSum α N‖ ^ 4 ≤
      6 * (N + 1 : ℝ) ^ 3 +
        16 * (N + 1 : ℝ) * ‖cubicSecondDifferenceTripleSum α N‖ := by
  let S : ℂ := ∑ h ∈ Finset.Icc 1 N, cubicFixedShiftSum α N h
  let D : ℂ := cubicSecondDifferenceTripleSum α N
  let X : ℝ := N + 1
  have hfirst : ‖cubicUnweightedExpSum α N‖ ^ 2 = X + 2 * S.re := by
    rw [norm_cubicUnweightedExpSum_sq_eq_positiveShiftSum,
      cubicPositiveShiftSum_eq_sum_fixedShift]
  have hre2 : S.re ^ 2 ≤ ‖S‖ ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg S.re) (norm_nonneg S)).2
      (Complex.abs_re_le_norm S)
    simpa only [sq_abs] using h
  have hfour : ‖cubicUnweightedExpSum α N‖ ^ 4 ≤
      2 * X ^ 2 + 8 * ‖S‖ ^ 2 := by
    calc
      _ = (X + 2 * S.re) ^ 2 := by
        rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hfirst]
      _ ≤ 2 * X ^ 2 + 8 * S.re ^ 2 := by
        nlinarith [sq_nonneg (X - 2 * S.re)]
      _ ≤ 2 * X ^ 2 + 8 * ‖S‖ ^ 2 := by gcongr
  have hcs : ‖S‖ ^ 2 ≤
      (N : ℝ) * ∑ h ∈ Finset.Icc 1 N,
        ‖cubicFixedShiftSum α N h‖ ^ 2 :=
    norm_sum_cubicFixedShiftSum_sq_le α N
  have hsecond :
      (∑ h ∈ Finset.Icc 1 N,
        ‖cubicFixedShiftSum α N h‖ ^ 2) =
      (N : ℝ) * X / 2 + 2 * D.re :=
    sum_norm_cubicFixedShiftSum_sq_eq_tripleSum α N
  have hre : D.re ≤ ‖D‖ := Complex.re_le_norm D
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hX : 1 ≤ X := by dsimp [X]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
  have hnX : (N : ℝ) ≤ X := by dsimp [X]; linarith
  have hpower : (N : ℝ) ^ 2 * X ≤ X ^ 3 := by
    have hsq : (N : ℝ) ^ 2 ≤ X ^ 2 := by gcongr
    calc
      (N : ℝ) ^ 2 * X ≤ X ^ 2 * X := by gcongr
      _ = X ^ 3 := by ring
  have hXpower : X ^ 2 ≤ X ^ 3 := by
    calc
      X ^ 2 = X ^ 2 * 1 := by ring
      _ ≤ X ^ 2 * X := by gcongr
      _ = X ^ 3 := by ring
  calc
    _ ≤ 2 * X ^ 2 + 8 * ‖S‖ ^ 2 := hfour
    _ ≤ 2 * X ^ 2 + 8 * (N : ℝ) *
        (∑ h ∈ Finset.Icc 1 N,
          ‖cubicFixedShiftSum α N h‖ ^ 2) := by nlinarith [hcs]
    _ = 2 * X ^ 2 + 8 * (N : ℝ) *
        ((N : ℝ) * X / 2 + 2 * D.re) := by rw [hsecond]
    _ ≤ 2 * X ^ 2 + 8 * (N : ℝ) *
        ((N : ℝ) * X / 2 + 2 * ‖D‖) := by gcongr
    _ ≤ 6 * X ^ 3 + 16 * X * ‖D‖ := by
      nlinarith [hpower, hXpower, mul_nonneg (sub_nonneg.mpr hnX) (norm_nonneg D)]
    _ = _ := rfl

/-- Pointwise Young's inequality closes the eighth-power estimate with the
same constants as the integral Cauchy--Schwarz argument. -/
theorem norm_cubicUnweightedExpSum_eight_le_secondDifference
    (α : ℝ) (N : ℕ) :
    ‖cubicUnweightedExpSum α N‖ ^ 8 ≤
      12 * (N + 1 : ℝ) ^ 3 * ‖cubicUnweightedExpSum α N‖ ^ 4 +
        256 * (N + 1 : ℝ) ^ 2 *
          ‖cubicSecondDifferenceTripleSum α N‖ ^ 2 := by
  let X : ℝ := N + 1
  let A : ℝ := ‖cubicUnweightedExpSum α N‖ ^ 4
  let B : ℝ := 6 * X ^ 3
  let C : ℝ := 16 * X * ‖cubicSecondDifferenceTripleSum α N‖
  have hA : A ≤ B + C := norm_cubicUnweightedExpSum_four_le_secondDifference α N
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hmul : A * A ≤ (B + C) * A :=
    mul_le_mul_of_nonneg_right hA hA0
  have hsq := sq_nonneg (A - C)
  have hbound : A ^ 2 ≤ 2 * B * A + C ^ 2 := by
    nlinarith [hmul, hsq]
  calc
    _ = A ^ 2 := by dsimp [A]; ring
    _ ≤ 2 * B * A + C ^ 2 := hbound
    _ = _ := by dsimp [A, B, C, X]; ring

/-- Integrating the pointwise Young estimate reduces the unweighted eighth
moment to a fourth moment and the proved second-difference energy. -/
theorem integral_norm_cubicUnweightedExpSum_pow_eight_le
    (N : ℕ) :
    (∫ α in Set.Icc (0 : ℝ) 1,
      ‖cubicUnweightedExpSum α N‖ ^ 8) ≤
      12 * (N + 1 : ℝ) ^ 3 *
        (∫ α in Set.Icc (0 : ℝ) 1,
          ‖cubicUnweightedExpSum α N‖ ^ 4) +
      256 * (N + 1 : ℝ) ^ 2 *
        (∫ α in Set.Icc (0 : ℝ) 1,
          ‖cubicSecondDifferenceTripleSum α N‖ ^ 2) := by
  have hF : Continuous (fun α : ℝ => cubicUnweightedExpSum α N) := by
    unfold cubicUnweightedExpSum addChar
    fun_prop
  have hD : Continuous (fun α : ℝ => cubicSecondDifferenceTripleSum α N) := by
    unfold cubicSecondDifferenceTripleSum addChar
    fun_prop
  let F8 : ℝ → ℝ := fun α => ‖cubicUnweightedExpSum α N‖ ^ 8
  let F4 : ℝ → ℝ := fun α => ‖cubicUnweightedExpSum α N‖ ^ 4
  let D2 : ℝ → ℝ := fun α => ‖cubicSecondDifferenceTripleSum α N‖ ^ 2
  have hF8 : IntegrableOn F8 (Set.Icc (0 : ℝ) 1) := by
    apply Continuous.integrableOn_Icc
    dsimp [F8]
    fun_prop
  have hF4 : IntegrableOn F4 (Set.Icc (0 : ℝ) 1) := by
    apply Continuous.integrableOn_Icc
    dsimp [F4]
    fun_prop
  have hD2 : IntegrableOn D2 (Set.Icc (0 : ℝ) 1) := by
    apply Continuous.integrableOn_Icc
    dsimp [D2]
    fun_prop
  have hR : IntegrableOn
      (fun α => 12 * (N + 1 : ℝ) ^ 3 * F4 α +
        256 * (N + 1 : ℝ) ^ 2 * D2 α)
      (Set.Icc (0 : ℝ) 1) :=
    (hF4.const_mul _).add (hD2.const_mul _)
  calc
    (∫ α in Set.Icc (0 : ℝ) 1, F8 α) ≤
      ∫ α in Set.Icc (0 : ℝ) 1,
        12 * (N + 1 : ℝ) ^ 3 * F4 α +
          256 * (N + 1 : ℝ) ^ 2 * D2 α := by
            apply setIntegral_mono_on hF8 hR measurableSet_Icc
            intro α hα
            exact norm_cubicUnweightedExpSum_eight_le_secondDifference α N
    _ = _ := by
      rw [integral_add (hF4.const_mul _) (hD2.const_mul _),
        integral_const_mul, integral_const_mul]

#print axioms SystolicGrowth.CookMagyarCircle.sum_range_mul_conj_sum_range
#print axioms SystolicGrowth.CookMagyarCircle.norm_sum_range_sq_eq_diagonal_add_pairs
#print axioms SystolicGrowth.CookMagyarCircle.norm_cubicUnweightedExpSum_sq_eq_strictPairs
#print axioms SystolicGrowth.CookMagyarCircle.sum_strictCubicIndexPairs_eq_positiveShiftPairs
#print axioms SystolicGrowth.CookMagyarCircle.cubicPositiveShiftSum_eq_sum_fixedShift
#print axioms SystolicGrowth.CookMagyarCircle.norm_cubicUnweightedExpSum_sq_eq_positiveShiftSum
#print axioms SystolicGrowth.CookMagyarCircle.cubicSecondDifference_addChar
#print axioms SystolicGrowth.CookMagyarCircle.cubicFixedShiftPair_eq_secondDifference
#print axioms SystolicGrowth.CookMagyarCircle.sum_positiveShiftPairs_eq_secondDifferenceTriples
#print axioms SystolicGrowth.CookMagyarCircle.sum_norm_cubicFixedShiftSum_sq_eq_tripleSum
#print axioms SystolicGrowth.CookMagyarCircle.norm_sum_cubicFixedShiftSum_sq_le
#print axioms SystolicGrowth.CookMagyarCircle.norm_cubicUnweightedExpSum_four_le_secondDifference
#print axioms SystolicGrowth.CookMagyarCircle.norm_cubicUnweightedExpSum_eight_le_secondDifference
#print axioms SystolicGrowth.CookMagyarCircle.integral_norm_cubicUnweightedExpSum_pow_eight_le

end CookMagyarCircle
end SystolicGrowth
