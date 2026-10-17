module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.Tactic

@[expose] public section

/-!
# A quantitative von Mangoldt coefficient series bound

The absolutely convergent coefficient series on the near-one Perron line
is bounded explicitly. This is only a coefficient estimate; no contour
exchange or truncated Perron formula is asserted here.
-/

open Finset

namespace SystolicGrowth.CookMagyarCircle

private theorem nat_rpow_neg_one_sub_tsum_le (ε : ℝ) (hε : 0 < ε) :
    (∑' k : ℕ, (k : ℝ) ^ (-1 - ε)) ≤ 1 + 1 / ε := by
  let f : ℕ → ℝ := fun k => (k : ℝ) ^ (-1 - ε)
  have hnonneg (k : ℕ) : 0 ≤ f k := by positivity
  have hzero : f 0 = 0 := by
    simpa only [f, Nat.cast_zero] using
      (Real.zero_rpow (x := -1 - ε) (show -1 - ε ≠ 0 by linarith))
  have hone : f 1 = 1 := by simp [f]
  have hεinv : 0 ≤ ε⁻¹ := inv_nonneg.mpr hε.le
  apply Real.tsum_le_of_sum_range_le hnonneg
  intro N
  by_cases hN : N ≤ 2
  · interval_cases N <;> simp [sum_range_succ, hzero, hone] <;>
      linarith
  · have hN2 : 2 ≤ N := by omega
    obtain ⟨M, rfl⟩ : ∃ M : ℕ, N = M + 2 := ⟨N - 2, by omega⟩
    have hantitone (M : ℕ) : AntitoneOn (fun x : ℝ => x ^ (-1 - ε))
        (Set.Icc (1 : ℝ) (M + 1 : ℕ)) := by
      intro x hx y hy hxy
      exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
    have hcompare := AntitoneOn.sum_le_integral_Ico
      (a := 1) (b := M + 1) (f := fun x : ℝ => x ^ (-1 - ε))
      (by omega) (by simpa only [Nat.cast_one] using hantitone M)
    have hnozero : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (M + 1 : ℕ) := by
      rw [Set.uIcc_of_le (by exact_mod_cast (Nat.succ_pos M))]
      simp
    have hpower :
        (∫ x in (1 : ℝ)..(M + 1 : ℕ), x ^ (-1 - ε)) ≤ 1 / ε := by
      rw [integral_rpow
        (Or.inr ⟨by linarith, hnozero⟩)]
      have hbase : 0 ≤ ((M + 1 : ℕ) : ℝ) ^ (-ε) := by positivity
      simp only [show -1 - ε + 1 = -ε by ring, Real.one_rpow]
      calc
        (((M + 1 : ℕ) : ℝ) ^ (-ε) - 1) / (-ε) =
            (1 - ((M + 1 : ℕ) : ℝ) ^ (-ε)) / ε := by ring
        _ ≤ 1 / ε := by
          apply (div_le_div_iff₀ hε hε).mpr
          nlinarith [hbase]
    have hsum : ∑ k ∈ range (M + 2), f k =
        1 + ∑ i ∈ Ico 1 (M + 1), ((i + 1 : ℕ) : ℝ) ^ (-1 - ε) := by
      rw [show M + 2 = 2 + M by omega, sum_range_add]
      have hfirst : ∑ k ∈ range 2, f k = 1 := by simp [sum_range_succ, hzero, hone]
      rw [hfirst, sum_Ico_eq_sum_range]
      congr 1
      apply sum_congr rfl
      intro i _
      congr 1
      omega
    rw [hsum]
    have htail := hcompare.trans (by simpa only [Nat.cast_one] using hpower)
    linarith

#print axioms nat_rpow_neg_one_sub_tsum_le

/-- The von Mangoldt Dirichlet coefficient series is absolutely convergent
just right of one, with an explicit pole-order-two majorant. -/
theorem vonMangoldt_rpow_series_summable_and_tsum_le
    (σ : ℝ) (hσ : 1 < σ) (hσ₂ : σ ≤ 2) :
    Summable (fun k : ℕ => ArithmeticFunction.vonMangoldt k / (k : ℝ) ^ σ) ∧
      (∑' k : ℕ, ArithmeticFunction.vonMangoldt k / (k : ℝ) ^ σ) ≤
        6 / (σ - 1) ^ 2 := by
  let ε : ℝ := (σ - 1) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hp : Summable (fun k : ℕ => (k : ℝ) ^ (-1 - ε)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hcoeff : 0 ≤ (1 : ℝ) / ε := by positivity
  have hdom : Summable (fun k : ℕ => (1 / ε) * (k : ℝ) ^ (-1 - ε)) :=
    hp.mul_left _
  have hterm (k : ℕ) :
      ArithmeticFunction.vonMangoldt k / (k : ℝ) ^ σ ≤
        (1 / ε) * (k : ℝ) ^ (-1 - ε) := by
    by_cases hk : k = 0
    · subst k
      have hzero : (0 : ℝ) ^ (-1 - ε) = 0 :=
        Real.zero_rpow (show -1 - ε ≠ 0 by linarith)
      simp [ArithmeticFunction.map_zero, hzero]
    · have hkpos : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
      have hΛ : ArithmeticFunction.vonMangoldt k ≤ (k : ℝ) ^ ε / ε :=
        ArithmeticFunction.vonMangoldt_le_log.trans
          (Real.log_le_rpow_div hkpos.le hε)
      calc
        ArithmeticFunction.vonMangoldt k / (k : ℝ) ^ σ ≤
            ((k : ℝ) ^ ε / ε) / (k : ℝ) ^ σ :=
          div_le_div_of_nonneg_right hΛ (Real.rpow_pos_of_pos hkpos σ).le
        _ = (1 / ε) * (k : ℝ) ^ (-1 - ε) := by
          rw [show -1 - ε = ε - σ by dsimp [ε]; ring,
            Real.rpow_sub hkpos]
          ring
  have hnonneg (k : ℕ) :
      0 ≤ ArithmeticFunction.vonMangoldt k / (k : ℝ) ^ σ := by
    exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) σ)
  have hΛsum : Summable
      (fun k : ℕ => ArithmeticFunction.vonMangoldt k / (k : ℝ) ^ σ) :=
    Summable.of_nonneg_of_le hnonneg hterm hdom
  have hsum :
      (∑' k : ℕ, ArithmeticFunction.vonMangoldt k / (k : ℝ) ^ σ) ≤
        (1 / ε) * (∑' k : ℕ, (k : ℝ) ^ (-1 - ε)) := by
    calc
      _ ≤ ∑' k : ℕ, (1 / ε) * (k : ℝ) ^ (-1 - ε) :=
        Summable.tsum_le_tsum hterm hΛsum hdom
      _ = _ := hp.tsum_mul_left _
  have hpbound := nat_rpow_neg_one_sub_tsum_le ε hε
  have hbound :
      (∑' k : ℕ, ArithmeticFunction.vonMangoldt k / (k : ℝ) ^ σ) ≤
        (1 / ε) * (1 + 1 / ε) :=
    hsum.trans (mul_le_mul_of_nonneg_left hpbound hcoeff)
  have hδpos : 0 < σ - 1 := by linarith
  have hδle : σ - 1 ≤ 1 := by linarith
  have hδsq : 0 < (σ - 1) ^ 2 := sq_pos_of_pos hδpos
  have hidentity :
      (1 / ε) * (1 + 1 / ε) = (2 * (σ - 1) + 4) / (σ - 1) ^ 2 := by
    dsimp [ε]
    field_simp
    ring
  refine ⟨hΛsum, hbound.trans ?_⟩
  rw [hidentity]
  apply (div_le_div_iff₀ hδsq hδsq).mpr
  nlinarith

#print axioms vonMangoldt_rpow_series_summable_and_tsum_le

end SystolicGrowth.CookMagyarCircle
