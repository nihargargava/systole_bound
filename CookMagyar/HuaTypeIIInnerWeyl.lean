module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.GeneralCubicWeyl

@[expose] public section

/-!
# Endpoint-uniform cubic inner sums for Hua Type II

An actual interval `Icc lo hi` contained in `Icc 1 P₀` has the same cubic
fourth-power bound as a prefix, with arbitrary lower coefficients retained.
Translation preserves the leading coefficient; two inner differences give
frequency `6*theta*η₁*η₂`. Only nonnegative envelopes are extended to `P₀`.
This result does not assert cancellation on arbitrary finite supports.
-/

open scoped BigOperators ComplexConjugate

namespace SystolicGrowth.CookMagyarCircle

/-- Unpadded second-difference envelope, retaining the exact cap `N+1`.
Unlike the progression-padding interface, this can be embedded in a length-`P₀`
interval without an unnecessary `P₀+1` cap. -/
theorem norm_generalCubicSecondDifferenceSum_le_unpaddedPairEnvelope
    (theta b c d : ℝ) (N : ℕ) :
    ‖unitSequenceSecondDifferenceSum (generalCubicPhase theta b c d) N‖ ≤
      ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        linearDistanceEnvelope (N + 1 : ℝ) (6 * theta * (h * k : ℕ)) := by
  let u := generalCubicPhase theta b c d
  have hdecomp : unitSequenceSecondDifferenceSum u N =
      ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 (N - h),
        ∑ m ∈ Finset.range (N - h + 1 - k),
          u (m + h + k) * conj (u (m + k)) * conj (u (m + h)) * u m := by
    unfold unitSequenceSecondDifferenceSum
    apply Finset.sum_congr rfl
    intro h hh
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      sum_positiveCubicShiftPairs_eq_sum_by_shift (N - h)
        (fun k m => u (m + h + k) * conj (u (m + k)) * conj (u (m + h)) * u m)
  rw [hdecomp]
  calc
    _ ≤ ∑ h ∈ Finset.Icc 1 N,
        ‖∑ k ∈ Finset.Icc 1 (N - h), ∑ m ∈ Finset.range (N - h + 1 - k),
          u (m + h + k) * conj (u (m + k)) * conj (u (m + h)) * u m‖ :=
      norm_sum_le _ _
    _ ≤ ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 (N - h),
        ‖∑ m ∈ Finset.range (N - h + 1 - k),
          u (m + h + k) * conj (u (m + k)) * conj (u (m + h)) * u m‖ := by
      apply Finset.sum_le_sum
      intro h hh
      exact norm_sum_le _ _
    _ ≤ ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 (N - h),
        linearDistanceEnvelope (N + 1 : ℝ) (6 * theta * (h * k : ℕ)) := by
      apply Finset.sum_le_sum
      intro h hh
      apply Finset.sum_le_sum
      intro k hk
      exact norm_generalCubicSecondDifferenceInner_le_envelope theta b c d N h k
        (Finset.mem_Icc.mp hh).2 (Finset.mem_Icc.mp hk).2
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro h hh
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Icc_subset_Icc_right (by omega))
      intro k hk hnot
      exact linearDistanceEnvelope_nonneg (by positivity)

/-- Every natural cubic interval lying in `Icc 1 P₀` obeys the exact
fourth-power inner Weyl envelope, uniformly in endpoints and lower coefficients. -/
theorem norm_generalCubicPhase_sum_Icc_four_le_innerWeyl_envelope
    (theta b c d : ℝ) (lo hi P₀ : ℕ) (hlo : 1 ≤ lo) (hhi : hi ≤ P₀) :
    ‖∑ v ∈ Finset.Icc lo hi, generalCubicPhase theta b c d v‖ ^ 4 ≤
      6 * (P₀ : ℝ) ^ 3 + 16 * (P₀ : ℝ) *
        (∑ η₁ ∈ Finset.Icc 1 P₀, ∑ η₂ ∈ Finset.Icc 1 P₀,
          linearDistanceEnvelope (P₀ : ℝ) (6 * theta * (η₁ * η₂ : ℕ))) := by
  have henvNonneg : 0 ≤
      ∑ η₁ ∈ Finset.Icc 1 P₀, ∑ η₂ ∈ Finset.Icc 1 P₀,
        linearDistanceEnvelope (P₀ : ℝ) (6 * theta * (η₁ * η₂ : ℕ)) := by
    apply Finset.sum_nonneg
    intro η₁ hη₁
    apply Finset.sum_nonneg
    intro η₂ hη₂
    exact linearDistanceEnvelope_nonneg (Nat.cast_nonneg P₀)
  by_cases hlohi : lo ≤ hi
  · let N : ℕ := hi - lo
    let b' : ℝ := 3 * theta * lo + b
    let c' : ℝ := 3 * theta * (lo : ℝ) ^ 2 + 2 * b * lo + c
    let d' : ℝ := theta * (lo : ℝ) ^ 3 + b * (lo : ℝ) ^ 2 + c * lo + d
    have hlen : N + 1 ≤ P₀ := by dsimp [N]; omega
    have hlenR : (N + 1 : ℝ) ≤ (P₀ : ℝ) := by exact_mod_cast hlen
    have hNP : N ≤ P₀ := by omega
    have hset : Finset.Icc lo hi = Finset.Ico lo (hi + 1) := by
      ext v
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    have hcount : hi + 1 - lo = N + 1 := by dsimp [N]; omega
    have hsum : (∑ v ∈ Finset.Icc lo hi, generalCubicPhase theta b c d v) =
        generalCubicExpSum theta b' c' d' N := by
      rw [hset, Finset.sum_Ico_eq_sum_range, hcount]
      unfold generalCubicExpSum
      apply Finset.sum_congr rfl
      intro v hv
      simpa only [b', c', d', Nat.one_mul, Nat.cast_one, one_pow, mul_one] using
        generalCubicPhase_affineChange theta b c d lo 1 v
    have hpair : ‖unitSequenceSecondDifferenceSum (generalCubicPhase theta b' c' d') N‖ ≤
        ∑ η₁ ∈ Finset.Icc 1 P₀, ∑ η₂ ∈ Finset.Icc 1 P₀,
          linearDistanceEnvelope (P₀ : ℝ) (6 * theta * (η₁ * η₂ : ℕ)) := by
      calc
        _ ≤ ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
            linearDistanceEnvelope (N + 1 : ℝ) (6 * theta * (h * k : ℕ)) :=
          norm_generalCubicSecondDifferenceSum_le_unpaddedPairEnvelope theta b' c' d' N
        _ ≤ ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
            linearDistanceEnvelope (P₀ : ℝ) (6 * theta * (h * k : ℕ)) := by
          apply Finset.sum_le_sum
          intro h hh
          apply Finset.sum_le_sum
          intro k hk
          exact linearDistanceEnvelope_mono hlenR
        _ ≤ ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 P₀,
            linearDistanceEnvelope (P₀ : ℝ) (6 * theta * (h * k : ℕ)) := by
          apply Finset.sum_le_sum
          intro h hh
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.Icc_subset_Icc_right hNP) (fun k hk hnot =>
              linearDistanceEnvelope_nonneg (Nat.cast_nonneg P₀))
        _ ≤ _ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hNP)
          intro h hh hnot
          exact Finset.sum_nonneg (fun k hk =>
            linearDistanceEnvelope_nonneg (Nat.cast_nonneg P₀))
    rw [hsum]
    calc
      _ ≤ 6 * (N + 1 : ℝ) ^ 3 + 16 * (N + 1 : ℝ) *
          ‖unitSequenceSecondDifferenceSum (generalCubicPhase theta b' c' d') N‖ :=
        norm_generalCubicExpSum_four_le_secondDifference theta b' c' d' N
      _ ≤ 6 * (N + 1 : ℝ) ^ 3 + 16 * (N + 1 : ℝ) *
          (∑ η₁ ∈ Finset.Icc 1 P₀, ∑ η₂ ∈ Finset.Icc 1 P₀,
            linearDistanceEnvelope (P₀ : ℝ) (6 * theta * (η₁ * η₂ : ℕ))) := by
        gcongr
      _ ≤ _ := by gcongr
  · have hempty : Finset.Icc lo hi = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
    rw [hempty]
    simp only [Finset.sum_empty, norm_zero, zero_pow (by decide : 4 ≠ 0)]
    exact add_nonneg (by positivity) (mul_nonneg (by positivity) henvNonneg)

end SystolicGrowth.CookMagyarCircle

#print axioms SystolicGrowth.CookMagyarCircle.norm_generalCubicSecondDifferenceSum_le_unpaddedPairEnvelope
#print axioms SystolicGrowth.CookMagyarCircle.norm_generalCubicPhase_sum_Icc_four_le_innerWeyl_envelope
