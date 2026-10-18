module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib

@[expose] public section

/-!
# Counting the positive indices in a Type-II inner support

This finite lemma is independent of Hua's oscillatory estimate. It isolates
the only integer-counting step needed to bound a diagonal after expanding a
mean square: a set of positive integers below a real upper endpoint has at
most that endpoint many elements.
-/

namespace SystolicGrowth.CookMagyarCircle

/-- A finite set of positive integers with a real upper bound has cardinality
at most that upper bound. The proof passes through the natural floor, so no
assumption that the real endpoint is itself an integer is needed. -/
theorem card_pos_nat_le_real_upper (V : Finset ℕ) (R : ℝ)
    (hR : 0 ≤ R) (hV : ∀ v ∈ V, 0 < v ∧ (v : ℝ) ≤ R) :
    (V.card : ℝ) ≤ R := by
  have hsub : V ⊆ Finset.Icc 1 (Nat.floor R) := by
    intro v hv
    exact Finset.mem_Icc.mpr ⟨(hV v hv).1, (Nat.le_floor_iff hR).2 (hV v hv).2⟩
  have hcard : V.card ≤ Nat.floor R := by
    have h := Finset.card_le_card hsub
    simp only [Nat.card_Icc] at h
    omega
  exact (Nat.cast_le.mpr hcard).trans (Nat.floor_le hR)

/-- The exact variable-endpoint support used in Hua's `Q=1` Type-II block
has at most `P/(lD)` elements whenever the outer variable exceeds `D`.
The strict lower endpoint `P'/u < v` is retained but is not needed for this
upper count; dropping it here cannot enlarge the final mean square. -/
theorem card_hua_typeII_interval_support_le
    (P l D u : ℕ) (P' : ℝ) (V : Finset ℕ)
    (hl : 0 < l) (hD : 0 < D) (hDu : D < u) :
    ((V.filter (fun v : ℕ =>
      0 < v ∧ P' / (u : ℝ) < (v : ℝ) ∧
        (v : ℝ) ≤ ((P : ℝ) / l) / u)).card : ℝ) ≤
      ((P : ℝ) / l) / D := by
  classical
  have hl' : 0 < (l : ℝ) := by exact_mod_cast hl
  have hD' : 0 < (D : ℝ) := by exact_mod_cast hD
  have hu' : 0 < (u : ℝ) := by exact_mod_cast (lt_trans hD hDu)
  have hcount :
      ((V.filter (fun v : ℕ =>
        0 < v ∧ P' / (u : ℝ) < (v : ℝ) ∧
          (v : ℝ) ≤ ((P : ℝ) / l) / u)).card : ℝ) ≤
        ((P : ℝ) / l) / u := by
    apply card_pos_nat_le_real_upper
    · positivity
    · intro v hv
      rcases Finset.mem_filter.mp hv with ⟨_, hv0, _, hvle⟩
      exact ⟨hv0, hvle⟩
  apply hcount.trans
  apply (div_le_div_iff₀ hu' hD').2
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_of_lt hDu)
    (div_nonneg (Nat.cast_nonneg P) hl'.le)

/-- Every supported inner index on a dyadic block lies in the same positive
interval, independent of the outer index. This justifies clipping an arbitrary
fixed `V` before applying the full-interval eighth-moment envelope. -/
theorem hua_typeII_interval_support_subset_positive_Icc
    (P l D u : ℕ) (P' : ℝ) (V : Finset ℕ)
    (hl : 0 < l) (hD : 0 < D) (hDu : D < u) :
    V.filter (fun v : ℕ =>
      0 < v ∧ P' / (u : ℝ) < (v : ℝ) ∧
        (v : ℝ) ≤ ((P : ℝ) / l) / u) ⊆
      Finset.Icc 1 (Nat.floor (((P : ℝ) / l) / D)) := by
  intro v hv
  obtain ⟨_, hvpos, _, hvupper⟩ := Finset.mem_filter.mp hv
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have huR : (0 : ℝ) < u := by exact_mod_cast (lt_trans hD hDu)
  have hbudget : ((P : ℝ) / l) / u ≤ ((P : ℝ) / l) / D := by
    apply (div_le_div_iff₀ huR hDR).2
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_of_lt hDu)
      (div_nonneg (Nat.cast_nonneg P) hlR.le)
  have hR : 0 ≤ ((P : ℝ) / l) / D := by positivity
  exact Finset.mem_Icc.mpr
    ⟨hvpos, (Nat.le_floor_iff hR).2 (hvupper.trans hbudget)⟩

#print axioms card_pos_nat_le_real_upper
#print axioms card_hua_typeII_interval_support_le
#print axioms hua_typeII_interval_support_subset_positive_Icc

/-- Under the source upper dyadic gate, the clipped inner endpoint is
positive and comparable to the real interval length. Its logarithmic lower
bound is uniform in both `l` and `D`; no integer rounding is suppressed. -/
theorem hua_typeII_floor_inner_endpoint_bounds
    (P l D sigma3 sigma6 : ℕ) (L : ℝ)
    (hl : 0 < l) (hD : 0 < D) (hL : 2 ≤ L)
    (hexp : sigma3 + 1 ≤ sigma6)
    (hlupper : (l : ℝ) ≤ L ^ sigma3)
    (hDupper : (D : ℝ) < (P : ℝ) / L ^ sigma6) :
    let N := Nat.floor (((P : ℝ) / l) / D)
    1 ≤ N ∧ L ^ (sigma6 - sigma3) / 2 ≤ (N : ℝ) ∧
      (((P : ℝ) / l) / D) / 2 ≤ (N : ℝ) ∧
      (N : ℝ) ≤ ((P : ℝ) / l) / D := by
  dsimp only
  let R := ((P : ℝ) / l) / D
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hLpos : 0 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  have hadd : sigma3 + (sigma6 - sigma3) = sigma6 := by omega
  have hscale : (l : ℝ) * D * L ^ (sigma6 - sigma3) < P := by
    calc
      (l : ℝ) * D * L ^ (sigma6 - sigma3) =
          (D : ℝ) * ((l : ℝ) * L ^ (sigma6 - sigma3)) := by ring
      _ ≤ (D : ℝ) * (L ^ sigma3 * L ^ (sigma6 - sigma3)) := by
        gcongr
      _ = (D : ℝ) * L ^ sigma6 := by rw [← pow_add, hadd]
      _ < P := (lt_div_iff₀ (pow_pos hLpos _)).mp hDupper
  have hlength : L ^ (sigma6 - sigma3) < R := by
    apply (lt_div_iff₀ hDR).mpr
    apply (lt_div_iff₀ hlR).mpr
    nlinarith only [hscale]
  have hpow : 2 ≤ L ^ (sigma6 - sigma3) := by
    calc
      2 ≤ L := hL
      _ = L ^ 1 := (pow_one L).symm
      _ ≤ L ^ (sigma6 - sigma3) := pow_le_pow_right₀ hLone (by omega)
  have hR : 2 < R := hpow.trans_lt hlength
  have hN : 1 ≤ Nat.floor R :=
    (Nat.le_floor_iff (by linarith : 0 ≤ R)).mpr (by norm_num; linarith)
  have hNR : (1 : ℝ) ≤ Nat.floor R := by exact_mod_cast hN
  have hfloor := Nat.lt_floor_add_one R
  have hhalf : R / 2 ≤ (Nat.floor R : ℝ) := by linarith
  exact ⟨hN, (by linarith), hhalf, Nat.floor_le (by linarith)⟩

#print axioms hua_typeII_floor_inner_endpoint_bounds

/-- Both scalar diagonal losses in the normalized thirty-second moment
have the required saving under the unchanged source dyadic gates. -/
theorem hua_typeII_scalar_diagonal_log_saving
    (saving sigma3 sigma5 sigma6 P l D : ℕ) (L : ℝ)
    (h5 : 64 * saving ≤ sigma5)
    (h6 : 7 * sigma3 + 128 * saving + 32768 ≤ sigma6)
    (hl : 0 < l) (hD : 0 < D) (hL : 2 ≤ L)
    (hlupper : (l : ℝ) ≤ L ^ sigma3)
    (hDlower : L ^ sigma5 < (D : ℝ))
    (hDupper : (D : ℝ) < (P : ℝ) / L ^ sigma6) :
    let N := Nat.floor (((P : ℝ) / l) / D)
    1 / (D : ℝ) ^ 4 + 1 / (N : ℝ) ≤ 3 / L ^ (64 * saving) := by
  dsimp only
  let N := Nat.floor (((P : ℝ) / l) / D)
  have hLpos : 0 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  have hDone : (1 : ℝ) ≤ D := by exact_mod_cast hD
  obtain ⟨hN, hNlog, _, _⟩ := hua_typeII_floor_inner_endpoint_bounds
    P l D sigma3 sigma6 L hl hD hL (by omega) hlupper hDupper
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hDpow : L ^ (64 * saving) ≤ (D : ℝ) ^ 4 := by
    calc
      L ^ (64 * saving) ≤ L ^ sigma5 := pow_le_pow_right₀ hLone h5
      _ ≤ (D : ℝ) := hDlower.le
      _ ≤ (D : ℝ) ^ 4 := by
        simpa using pow_le_pow_right₀ hDone (show 1 ≤ 4 by norm_num)
  have hNscaled : L ^ (64 * saving) ≤ 2 * (N : ℝ) := by
    have hpow := pow_le_pow_right₀ hLone (show 64 * saving ≤ sigma6 - sigma3 by omega)
    linarith
  have hfirst : 1 / (D : ℝ) ^ 4 ≤ 1 / L ^ (64 * saving) :=
    one_div_le_one_div_of_le (pow_pos hLpos _) hDpow
  have hsecond : 1 / (N : ℝ) ≤ 2 / L ^ (64 * saving) :=
    (div_le_div_iff₀ hNR (pow_pos hLpos _)).mpr (by simpa using hNscaled)
  calc
    _ ≤ 1 / L ^ (64 * saving) + 2 / L ^ (64 * saving) := add_le_add hfirst hsecond
    _ = _ := by ring

#print axioms hua_typeII_scalar_diagonal_log_saving

end SystolicGrowth.CookMagyarCircle
