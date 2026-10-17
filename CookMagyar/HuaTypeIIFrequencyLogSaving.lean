module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.HuaTypeIIFrequencyNormalized
public import CookMagyar.HuaTypeIISupportCount

@[expose] public section

/-!
# Uniform logarithmic saving for the Type-II five-shift envelope

The threshold in the tenth divisor moment is an integer power of `log P`.
The exact floor endpoint and the unchanged denominator gates absorb all
four terms in the normalized frequency estimate, uniformly in `l,D,a,q`.
-/

namespace SystolicGrowth.CookMagyarCircle

open CookMagyarArcs

/-- The full positive five-shift envelope has the logarithmic saving needed
by the source Type-II estimate. No saving estimate is assumed; the only
inputs are the dyadic upper gate and the original rational-denominator gates.
The lower dyadic gate is unnecessary for this frequency contribution. -/
theorem hua_typeII_cubic_frequency_log_saving
    (saving sigma3 sigma6 sigma : ℕ)
    (h6 : 7 * sigma3 + 128 * saving + 32768 ≤ sigma6)
    (hsigma : 6 * sigma3 + 128 * saving + 32768 < sigma) :
    ∃ K : ℝ, 0 < K ∧ ∀ P l D a q : ℕ,
      2 ≤ Real.log (P : ℝ) →
      0 < l → (l : ℝ) ≤ Real.log (P : ℝ) ^ sigma3 →
      0 < D → (D : ℝ) < (P : ℝ) / Real.log (P : ℝ) ^ sigma6 →
      Nat.Coprime a q →
      Real.log (P : ℝ) ^ sigma < q →
      (q : ℝ) < (P : ℝ) ^ 3 / Real.log (P : ℝ) ^ sigma →
      let N := Nat.floor (((P : ℝ) / l) / D)
      (∑ x ∈ huaTypeIICubicShiftBox D N,
        linearDistanceEnvelope (N : ℝ)
          ((a : ℝ) / q * (huaTypeIICubicShiftFrequency l x : ℝ))) /
          ((D : ℝ) ^ 3 * (N : ℝ) ^ 3) ≤
        K / Real.log (P : ℝ) ^ (64 * saving) := by
  let C : ℝ := (4 + Real.log 36) ^ 1023
  have hC : 0 < C := by
    have hlog36 : 0 ≤ Real.log (36 : ℝ) := Real.log_nonneg (by norm_num)
    dsimp only [C]
    positivity
  refine ⟨36 * C + 28 * (36 + 64 + 64), by positivity, ?_⟩
  intro P l D a q hlog hl hlupper hD hDupper hac hqlower hqupper
  let L : ℝ := Real.log (P : ℝ)
  let s : ℕ := 64 * saving
  let tau : ℕ := (3 * sigma3 + 64 * saving + 2052) / 5
  let T : ℝ := L ^ tau
  let N : ℕ := Nat.floor (((P : ℝ) / l) / D)
  let M : ℕ := 36 * l ^ 3 * D ^ 3 * N ^ 2
  let B : ℝ := (1 + Real.log (M : ℝ)) ^ 1023
  let H : ℝ := 1 + Real.log (q : ℝ)
  let E : ℝ := ∑ x ∈ huaTypeIICubicShiftBox D N,
    linearDistanceEnvelope (N : ℝ)
      ((a : ℝ) / q * (huaTypeIICubicShiftFrequency l x : ℝ))
  change E / ((D : ℝ) ^ 3 * (N : ℝ) ^ 3) ≤
    (36 * C + 28 * (36 + 64 + 64)) / L ^ s
  have hL : 2 ≤ L := hlog
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hLone : 1 ≤ L := (by norm_num : (1 : ℝ) ≤ 2).trans hL
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hP : 0 < P := by
    by_contra h
    have hPzero : P = 0 := by omega
    norm_num [hPzero] at hlog
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP
  have hqR : (0 : ℝ) < q := (pow_pos hLpos sigma).trans hqlower
  have hq : 0 < q := by exact_mod_cast hqR
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hT : 0 < T := pow_pos hLpos tau
  obtain ⟨hN, hNlog, hNhalf, hNupper⟩ :=
    hua_typeII_floor_inner_endpoint_bounds P l D sigma3 sigma6 L hl hD hL
      (by omega) hlupper hDupper
  change 1 ≤ N at hN
  change L ^ (sigma6 - sigma3) / 2 ≤ (N : ℝ) at hNlog
  change (((P : ℝ) / l) / D) / 2 ≤ (N : ℝ) at hNhalf
  change (N : ℝ) ≤ ((P : ℝ) / l) / D at hNupper
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hden : (0 : ℝ) < (D : ℝ) ^ 3 * (N : ℝ) ^ 3 := by positivity
  obtain ⟨hrichBudget, hinnerBudget, hqBudget⟩ :=
    hua_typeII_divisor_threshold_exponent_budget saving sigma3 sigma6 sigma h6 hsigma
  change 3 * sigma3 + 1023 + s < 5 * tau at hrichBudget
  change 5 * tau + 4 * sigma3 + 1 + s < sigma6 at hinnerBudget
  change 5 * tau + 3 * sigma3 + 1 + s < sigma at hqBudget
  have hrichExp : 3 * sigma3 + 1023 + s ≤ 5 * tau := by omega
  have hinnerExp : 5 * tau + 3 * sigma3 + 1 + s ≤ sigma6 - sigma3 := by omega
  have hqExp : 5 * tau + 3 * sigma3 + 1 + s ≤ sigma := by omega
  have hqFirstExp : 5 * tau + 3 * sigma3 + s ≤ sigma := by omega
  have hTfive : T ^ 5 = L ^ (5 * tau) := by
    dsimp only [T]
    rw [← pow_mul]
    congr 1
    omega
  have hlthree : (l : ℝ) ^ 3 ≤ L ^ (3 * sigma3) := by
    calc
      (l : ℝ) ^ 3 ≤ (L ^ sigma3) ^ 3 := pow_le_pow_left₀ hlR.le hlupper 3
      _ = L ^ (3 * sigma3) := by
        rw [← pow_mul]
        congr 1
        omega
  have hM : 0 < M := by dsimp only [M]; positivity
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hBnonneg : 0 ≤ B := by
    exact pow_nonneg (add_nonneg (by norm_num) (Real.log_nonneg hMone)) 1023
  have hB : B ≤ C * L ^ 1023 :=
    hua_typeII_cubic_frequency_log_envelope_le P l D N 1023 hl hD hNpos hNupper hLone
  have hnormalized := hua_typeII_cubic_normalized_frequency_envelope_le
    l D N a q T hl hD hNpos hq hac hT
  change E / ((D : ℝ) ^ 3 * (N : ℝ) ^ 3) ≤
    36 * (l : ℝ) ^ 3 * B / T ^ 5 +
      28 * T ^ 5 * (36 * (l : ℝ) ^ 3 / q + 8 * (l : ℝ) ^ 3 * H / N +
        2 * (q : ℝ) * H / ((D : ℝ) ^ 3 * (N : ℝ) ^ 3)) at hnormalized
  -- Keep the fixed tenth-moment powers out of polynomial normalization.
  clear_value B C
  have hqsigma : (q : ℝ) * L ^ sigma ≤ (P : ℝ) ^ 3 :=
    ((lt_div_iff₀ (pow_pos hLpos sigma)).mp hqupper).le
  have hqcube : (q : ℝ) ≤ (P : ℝ) ^ 3 := by
    calc
      (q : ℝ) = (q : ℝ) * 1 := by ring
      _ ≤ (q : ℝ) * L ^ sigma :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hLone) hqR.le
      _ ≤ (P : ℝ) ^ 3 := hqsigma
  have hH : H ≤ 4 * L := by
    have hlogq := Real.log_le_log hqR hqcube
    rw [Real.log_pow] at hlogq
    change Real.log (q : ℝ) ≤ 3 * L at hlogq
    dsimp only [H]
    linarith only [hlogq, hLone]
  have hHnonneg : 0 ≤ H := by
    exact add_nonneg (by norm_num) (Real.log_nonneg hqone)
  have hcube : (P : ℝ) ^ 3 ≤
      8 * (l : ℝ) ^ 3 * (D : ℝ) ^ 3 * (N : ℝ) ^ 3 := by
    have hlength : (P : ℝ) ≤ 2 * (l : ℝ) * D * N := by
      calc
        (P : ℝ) = ((((P : ℝ) / l) / D) / 2) * (2 * (l : ℝ) * D) := by
          field_simp [ne_of_gt hlR, ne_of_gt hDR]
        _ ≤ (N : ℝ) * (2 * (l : ℝ) * D) :=
          mul_le_mul_of_nonneg_right hNhalf (by positivity)
        _ = _ := by ring
    calc
      (P : ℝ) ^ 3 ≤ (2 * (l : ℝ) * D * N) ^ 3 :=
        pow_le_pow_left₀ hPR.le hlength 3
      _ = _ := by ring
  have hrichScaled : (36 * (l : ℝ) ^ 3 * B / T ^ 5) * L ^ s ≤ 36 * C := by
    calc
      _ = (36 * (l : ℝ) ^ 3 * B * L ^ s) / T ^ 5 := by ring
      _ ≤ 36 * C := by
        apply (div_le_iff₀ (pow_pos hT 5)).mpr
        calc
          36 * (l : ℝ) ^ 3 * B * L ^ s ≤
              36 * L ^ (3 * sigma3) * (C * L ^ 1023) * L ^ s := by gcongr
          _ = 36 * C * L ^ (3 * sigma3 + 1023 + s) := by
            rw [pow_add, pow_add]
            ring
          _ ≤ 36 * C * L ^ (5 * tau) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hLone hrichExp) (by positivity)
          _ = 36 * C * T ^ 5 := by rw [hTfive]
  have hfirstScaled : T ^ 5 * (36 * (l : ℝ) ^ 3 / q) * L ^ s ≤ 36 := by
    calc
      _ = (36 * T ^ 5 * (l : ℝ) ^ 3 * L ^ s) / q := by ring
      _ ≤ 36 := by
        apply (div_le_iff₀ hqR).mpr
        calc
          36 * T ^ 5 * (l : ℝ) ^ 3 * L ^ s ≤
              36 * L ^ (5 * tau) * L ^ (3 * sigma3) * L ^ s := by
            rw [hTfive]
            gcongr
          _ = 36 * L ^ (5 * tau + 3 * sigma3 + s) := by
            rw [pow_add, pow_add]
            ring
          _ ≤ 36 * L ^ sigma :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hLone hqFirstExp) (by norm_num)
          _ ≤ 36 * (q : ℝ) := mul_le_mul_of_nonneg_left hqlower.le (by norm_num)
  have hsecondScaled : T ^ 5 * (8 * (l : ℝ) ^ 3 * H / N) * L ^ s ≤ 64 := by
    calc
      _ = (8 * T ^ 5 * (l : ℝ) ^ 3 * H * L ^ s) / N := by ring
      _ ≤ 64 := by
        apply (div_le_iff₀ hNR).mpr
        calc
          8 * T ^ 5 * (l : ℝ) ^ 3 * H * L ^ s ≤
              8 * L ^ (5 * tau) * L ^ (3 * sigma3) * (4 * L) * L ^ s := by
            rw [hTfive]
            gcongr
          _ = 32 * L ^ (5 * tau + 3 * sigma3 + 1 + s) := by
            rw [pow_add, pow_add, pow_add, pow_one]
            ring
          _ ≤ 32 * L ^ (sigma6 - sigma3) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hLone hinnerExp) (by norm_num)
          _ ≤ 64 * (N : ℝ) := by linarith only [hNlog]
  have hthirdScaled :
      T ^ 5 * (2 * (q : ℝ) * H / ((D : ℝ) ^ 3 * (N : ℝ) ^ 3)) * L ^ s ≤ 64 := by
    calc
      _ = (2 * T ^ 5 * (q : ℝ) * H * L ^ s) /
          ((D : ℝ) ^ 3 * (N : ℝ) ^ 3) := by ring
      _ ≤ 64 := by
        apply (div_le_iff₀ hden).mpr
        apply (mul_le_mul_iff_left₀ (pow_pos hlR 3)).mp
        calc
          (2 * T ^ 5 * (q : ℝ) * H * L ^ s) * (l : ℝ) ^ 3 ≤
              2 * L ^ (5 * tau) * (q : ℝ) * (4 * L) * L ^ s * L ^ (3 * sigma3) := by
            rw [hTfive]
            gcongr
          _ = 8 * (q : ℝ) * L ^ (5 * tau + 3 * sigma3 + 1 + s) := by
            rw [pow_add, pow_add, pow_add, pow_one]
            ring
          _ ≤ 8 * (q : ℝ) * L ^ sigma :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hLone hqExp) (by positivity)
          _ ≤ 8 * (P : ℝ) ^ 3 := by nlinarith only [hqsigma]
          _ ≤ (64 * ((D : ℝ) ^ 3 * (N : ℝ) ^ 3)) * (l : ℝ) ^ 3 := by
            nlinarith only [hcube]
  apply (le_div_iff₀ (pow_pos hLpos s)).mpr
  calc
    E / ((D : ℝ) ^ 3 * (N : ℝ) ^ 3) * L ^ s ≤
        (36 * (l : ℝ) ^ 3 * B / T ^ 5 +
          28 * T ^ 5 * (36 * (l : ℝ) ^ 3 / q + 8 * (l : ℝ) ^ 3 * H / N +
            2 * (q : ℝ) * H / ((D : ℝ) ^ 3 * (N : ℝ) ^ 3))) * L ^ s :=
      mul_le_mul_of_nonneg_right hnormalized (by positivity)
    _ = (36 * (l : ℝ) ^ 3 * B / T ^ 5) * L ^ s +
        28 * (T ^ 5 * (36 * (l : ℝ) ^ 3 / q) * L ^ s +
          T ^ 5 * (8 * (l : ℝ) ^ 3 * H / N) * L ^ s +
          T ^ 5 * (2 * (q : ℝ) * H / ((D : ℝ) ^ 3 * (N : ℝ) ^ 3)) * L ^ s) := by ring
    _ ≤ 36 * C + 28 * (36 + 64 + 64) := by gcongr

#print axioms hua_typeII_cubic_frequency_log_saving

end SystolicGrowth.CookMagyarCircle
