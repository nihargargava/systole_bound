module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.HuaTypeIIFrequencyEnvelope

@[expose] public section

/-!
# Normalized Type-II five-shift frequency estimate

This real-algebra bridge converts the exact tenth-divisor-moment and
sixfold-spacing estimate to the normalization used by Hua's Type-II
mean square. The reduced denominator is compared with the original one,
and the extra spacing block is absorbed using positive integer ranges.
-/

namespace SystolicGrowth.CookMagyarCircle

open CookMagyarArcs

/-- Normalization of the exact positive five-shift frequency envelope.
There is no logarithmic saving premise: the threshold `T` is arbitrary
and positive, and both divisor-rich and rational-spacing terms remain. -/
theorem hua_typeII_cubic_normalized_frequency_envelope_le
    (l D N a q : ℕ) (T : ℝ)
    (hl : 0 < l) (hD : 0 < D) (hN : 0 < N) (hq : 0 < q)
    (hac : Nat.Coprime a q) (hT : 0 < T) :
    let M : ℕ := 36 * l ^ 3 * D ^ 3 * N ^ 2
    (∑ x ∈ huaTypeIICubicShiftBox D N,
      linearDistanceEnvelope (N : ℝ)
        ((a : ℝ) / q * (huaTypeIICubicShiftFrequency l x : ℝ))) /
        ((D : ℝ) ^ 3 * (N : ℝ) ^ 3) ≤
      36 * (l : ℝ) ^ 3 * (1 + Real.log (M : ℝ)) ^ 1023 / T ^ 5 +
        28 * T ^ 5 *
          (36 * (l : ℝ) ^ 3 / q +
            8 * (l : ℝ) ^ 3 * (1 + Real.log (q : ℝ)) / N +
            2 * (q : ℝ) * (1 + Real.log (q : ℝ)) /
              ((D : ℝ) ^ 3 * (N : ℝ) ^ 3)) := by
  dsimp only
  let M : ℕ := 36 * l ^ 3 * D ^ 3 * N ^ 2
  let M₀ : ℕ := 6 * l ^ 3 * D ^ 3 * N ^ 2
  let Q : ℕ := q / Nat.gcd q 6
  let E : ℝ := ∑ x ∈ huaTypeIICubicShiftBox D N,
    linearDistanceEnvelope (N : ℝ)
      ((a : ℝ) / q * (huaTypeIICubicShiftFrequency l x : ℝ))
  let LQ : ℝ := 1 + Real.log (Q : ℝ)
  let Lq : ℝ := 1 + Real.log (q : ℝ)
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hlone : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hDone : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hNone : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hfactor : q = Q * Nat.gcd q 6 := by
    exact (Nat.div_mul_cancel (Nat.gcd_dvd_left q 6)).symm
  have hQ : 0 < Q := by
    apply Nat.pos_of_ne_zero
    intro hQzero
    have hqzero : q = 0 := by simpa [hQzero] using hfactor
    exact (Nat.ne_of_gt hq) hqzero
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hQone : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQq : (Q : ℝ) ≤ q := by
    exact_mod_cast Nat.div_le_self q (Nat.gcd q 6)
  have hg6 : Nat.gcd q 6 ≤ 6 :=
    Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_right q 6)
  have hqQ : (q : ℝ) ≤ 6 * (Q : ℝ) := by
    have hnat : q ≤ 6 * Q := by
      rw [hfactor]
      calc
        Q * Nat.gcd q 6 ≤ Q * 6 := Nat.mul_le_mul_left Q hg6
        _ = 6 * Q := Nat.mul_comm _ _
    exact_mod_cast hnat
  have hLQ : 0 ≤ LQ := by
    exact add_nonneg (by norm_num) (Real.log_nonneg hQone)
  have hLq : 1 ≤ Lq := by
    dsimp [Lq]
    linarith [Real.log_nonneg hqone]
  have hLQq : LQ ≤ Lq := by
    exact add_le_add_right (Real.log_le_log hQR hQq) 1
  have hblock : ((((M₀ + 1) / Q + 1 : ℕ) : ℝ)) ≤ (M₀ : ℝ) / Q + 2 := by
    have hdiv := Nat.cast_div_le (α := ℝ) (m := M₀ + 1) (n := Q)
    have hinv : 1 / (Q : ℝ) ≤ 1 := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hQone
    push_cast at hdiv ⊢
    rw [add_div] at hdiv
    linarith
  have hsource : T ^ 5 * E ≤
      (N : ℝ) * (M : ℝ) * (1 + Real.log (M : ℝ)) ^ 1023 +
        T ^ 10 * ((((M₀ + 1) / Q + 1 : ℕ) : ℝ)) *
          (28 * ((N : ℝ) + (Q : ℝ) * LQ)) :=
    hua_typeII_cubic_full_frequency_envelope_le l D N a q (N : ℝ) T
      hl hq hac (by positivity) hT.le
  have hraw : T ^ 5 * E ≤
      (N : ℝ) * (M : ℝ) * (1 + Real.log (M : ℝ)) ^ 1023 +
        T ^ 10 * ((M₀ : ℝ) / Q + 2) *
          (28 * ((N : ℝ) + (Q : ℝ) * LQ)) := by
    apply hsource.trans
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact mul_le_mul_of_nonneg_left hblock (by positivity)
  have hden : (0 : ℝ) < (D : ℝ) ^ 3 * (N : ℝ) ^ 3 := by positivity
  have hnormalized : E / ((D : ℝ) ^ 3 * (N : ℝ) ^ 3) ≤
      36 * (l : ℝ) ^ 3 * (1 + Real.log (M : ℝ)) ^ 1023 / T ^ 5 +
        28 * T ^ 5 *
          (6 * (l : ℝ) ^ 3 / Q + 6 * (l : ℝ) ^ 3 * LQ / N +
            2 / ((D : ℝ) ^ 3 * (N : ℝ) ^ 2) +
            2 * (Q : ℝ) * LQ / ((D : ℝ) ^ 3 * (N : ℝ) ^ 3)) := by
    have hquot : E ≤
        ((N : ℝ) * (M : ℝ) * (1 + Real.log (M : ℝ)) ^ 1023 +
          T ^ 10 * ((M₀ : ℝ) / Q + 2) *
            (28 * ((N : ℝ) + (Q : ℝ) * LQ))) / T ^ 5 := by
      apply (le_div_iff₀ (pow_pos hT 5)).mpr
      simpa only [mul_comm E] using hraw
    calc
      _ ≤
          (((N : ℝ) * (M : ℝ) * (1 + Real.log (M : ℝ)) ^ 1023 +
            T ^ 10 * ((M₀ : ℝ) / Q + 2) *
              (28 * ((N : ℝ) + (Q : ℝ) * LQ))) / T ^ 5) /
              ((D : ℝ) ^ 3 * (N : ℝ) ^ 3) :=
        div_le_div_of_nonneg_right hquot hden.le
      _ = _ := by
        generalize (1 + Real.log (M : ℝ)) ^ 1023 = Z
        have hMc : (M : ℝ) = 36 * (l : ℝ) ^ 3 * (D : ℝ) ^ 3 * (N : ℝ) ^ 2 := by
          simp [M]
        have hM₀c : (M₀ : ℝ) = 6 * (l : ℝ) ^ 3 * (D : ℝ) ^ 3 * (N : ℝ) ^ 2 := by
          simp [M₀]
        rw [hMc, hM₀c]
        field_simp [ne_of_gt hDR, ne_of_gt hNR, ne_of_gt hQR, ne_of_gt hT]
        ring
  have hfirst : 6 * (l : ℝ) ^ 3 / Q ≤ 36 * (l : ℝ) ^ 3 / q := by
    apply (div_le_div_iff₀ hQR hqR).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hqQ
      (show 0 ≤ 6 * (l : ℝ) ^ 3 by positivity)]
  have hsecond : 6 * (l : ℝ) ^ 3 * LQ / N ≤ 6 * (l : ℝ) ^ 3 * Lq / N := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hLQq (by positivity)) hNR.le
  have hDthree : (1 : ℝ) ≤ (D : ℝ) ^ 3 := one_le_pow₀ hDone
  have hlthree : (1 : ℝ) ≤ (l : ℝ) ^ 3 := one_le_pow₀ hlone
  have hNtwo : (N : ℝ) ≤ (N : ℝ) ^ 2 := by
    calc
      (N : ℝ) = (N : ℝ) * 1 := by ring
      _ ≤ (N : ℝ) * N := mul_le_mul_of_nonneg_left hNone hNR.le
      _ = _ := by ring
  have hextra : 2 / ((D : ℝ) ^ 3 * (N : ℝ) ^ 2) ≤
      2 * (l : ℝ) ^ 3 * Lq / N := by
    calc
      _ ≤ 2 / (N : ℝ) := by
        apply div_le_div_of_nonneg_left (by norm_num) hNR
        exact hNtwo.trans (by simpa using
          mul_le_mul_of_nonneg_right hDthree (show 0 ≤ (N : ℝ) ^ 2 by positivity))
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right ?_ hNR.le
        nlinarith only [mul_le_mul hlthree hLq
          (by norm_num : (0 : ℝ) ≤ 1) (by positivity)]
  have hlast : 2 * (Q : ℝ) * LQ / ((D : ℝ) ^ 3 * (N : ℝ) ^ 3) ≤
      2 * (q : ℝ) * Lq / ((D : ℝ) ^ 3 * (N : ℝ) ^ 3) := by
    apply div_le_div_of_nonneg_right ?_ hden.le
    exact mul_le_mul (mul_le_mul_of_nonneg_left hQq (by norm_num)) hLQq hLQ
      (by positivity)
  have hspacing :
      6 * (l : ℝ) ^ 3 / Q + 6 * (l : ℝ) ^ 3 * LQ / N +
        2 / ((D : ℝ) ^ 3 * (N : ℝ) ^ 2) +
        2 * (Q : ℝ) * LQ / ((D : ℝ) ^ 3 * (N : ℝ) ^ 3) ≤
      36 * (l : ℝ) ^ 3 / q + 8 * (l : ℝ) ^ 3 * Lq / N +
        2 * (q : ℝ) * Lq / ((D : ℝ) ^ 3 * (N : ℝ) ^ 3) := by
    calc
      _ ≤ 36 * (l : ℝ) ^ 3 / q + 6 * (l : ℝ) ^ 3 * Lq / N +
          2 * (l : ℝ) ^ 3 * Lq / N +
          2 * (q : ℝ) * Lq / ((D : ℝ) ^ 3 * (N : ℝ) ^ 3) :=
        add_le_add (add_le_add (add_le_add hfirst hsecond) hextra) hlast
      _ = _ := by ring
  exact hnormalized.trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hspacing (by positivity)))

#print axioms hua_typeII_cubic_normalized_frequency_envelope_le

end SystolicGrowth.CookMagyarCircle
