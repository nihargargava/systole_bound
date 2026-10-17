module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.HuaStepEightDivision
public import CookMagyar.HuaStepEightCharacter

@[expose] public section

open scoped BigOperators

namespace SystolicGrowth
namespace CookMagyarCircle

open CookMagyarArcs

/-! # Divided source corrections for actual cubic characters

For positive factor count, Hua's normalized pair sum differs from the
original divisor sum by at most `4P/(s*m*(log P)^lambda₃)`. The exact ceiling
cutoff, strict lower endpoint, progression, and parity are preserved. The
displayed phases have proved unit modulus, so no norm-bound input remains.
-/

/-- The normalized source correction for arbitrary real cubic coefficients
retains the reciprocal factor-count loss explicitly. -/
theorem eventually_norm_huaSourceStepEight_generalCubic_div_sub_divisors_le
    {lambda₂ lambda₃ : ℝ} (h₃ : 0 < lambda₃) :
    ∀ᶠ P : ℕ in Filter.atTop,
      1 < P ∧ ∀ m Q t s parity : ℕ, 0 < m → 0 < s → ∀ a b c d : ℝ,
        let H := huaStepEightSieveProduct P
        let Y := Nat.ceil (Real.rpow (Real.log P) lambda₃)
        let R := huaStepEightSourceCondition P m Q t lambda₂
        ‖((∑ z ∈ huaStepEightPairs H Y (P / m) s parity R,
              generalCubicPhase a b c d (m * (z.1 * z.2))) / (s : ℂ)) -
          (∑ v ∈ huaStepEightDivisors H Y (P / m) s parity R,
            generalCubicPhase a b c d (m * v))‖ ≤
          (4 : ℝ) * P / ((s : ℝ) * m * Real.rpow (Real.log P) lambda₃) := by
  filter_upwards [eventually_norm_huaSourceStepEight_div_sub_divisors_le h₃]
    with P hP
  refine ⟨hP.1, ?_⟩
  intro m Q t s parity hm hs a b c d
  exact hP.2 m Q t s parity hm hs (generalCubicPhase a b c d)
    (by intro z hz; simp only [norm_generalCubicPhase, le_refl])

/-- Rational-leading cubic specialization, uniform in all lower
coefficients and with no artificial phase-norm hypothesis. -/
theorem eventually_norm_huaSourceStepEight_rationalGeneralCubic_div_sub_divisors_le
    {lambda₂ lambda₃ : ℝ} (h₃ : 0 < lambda₃) :
    ∀ᶠ P : ℕ in Filter.atTop,
      1 < P ∧ ∀ m Q t s parity : ℕ, 0 < m → 0 < s →
        ∀ a q : ℕ, ∀ b c d : ℝ,
        let H := huaStepEightSieveProduct P
        let Y := Nat.ceil (Real.rpow (Real.log P) lambda₃)
        let R := huaStepEightSourceCondition P m Q t lambda₂
        ‖((∑ z ∈ huaStepEightPairs H Y (P / m) s parity R,
              generalCubicPhase (rationalCenter a q) b c d (m * (z.1 * z.2))) /
              (s : ℂ)) -
          (∑ v ∈ huaStepEightDivisors H Y (P / m) s parity R,
            generalCubicPhase (rationalCenter a q) b c d (m * v))‖ ≤
          (4 : ℝ) * P / ((s : ℝ) * m * Real.rpow (Real.log P) lambda₃) := by
  filter_upwards [eventually_norm_huaSourceStepEight_generalCubic_div_sub_divisors_le h₃]
    with P hP
  refine ⟨hP.1, ?_⟩
  intro m Q t s parity hm hs a q b c d
  exact hP.2 m Q t s parity hm hs (rationalCenter a q) b c d

/-- The divided correction for the actual polynomial `x³-x`, at its
original real frequency. -/
theorem eventually_norm_huaSourceStepEight_primeCubic_div_sub_divisors_le
    {lambda₂ lambda₃ : ℝ} (h₃ : 0 < lambda₃) :
    ∀ᶠ P : ℕ in Filter.atTop,
      1 < P ∧ ∀ m Q t s parity : ℕ, 0 < m → 0 < s → ∀ alpha : ℝ,
        let H := huaStepEightSieveProduct P
        let Y := Nat.ceil (Real.rpow (Real.log P) lambda₃)
        let R := huaStepEightSourceCondition P m Q t lambda₂
        ‖((∑ z ∈ huaStepEightPairs H Y (P / m) s parity R,
              addChar alpha (primeCubic (m * (z.1 * z.2)))) / (s : ℂ)) -
          (∑ v ∈ huaStepEightDivisors H Y (P / m) s parity R,
            addChar alpha (primeCubic (m * v)))‖ ≤
          (4 : ℝ) * P / ((s : ℝ) * m * Real.rpow (Real.log P) lambda₃) := by
  filter_upwards [eventually_norm_huaSourceStepEight_generalCubic_div_sub_divisors_le h₃]
    with P hP
  refine ⟨hP.1, ?_⟩
  intro m Q t s parity hm hs alpha
  simpa only [← addChar_primeCubic_eq_generalCubicPhase] using
    hP.2 m Q t s parity hm hs alpha 0 (-alpha) 0

/-- Wrapped-frequency form of the divided actual-character correction.
The integer wrap stays in the original character; no smoothing or endpoint
replacement is performed in this repeated-prime estimate. -/
theorem eventually_norm_huaSourceStepEight_wrappedPrimeCubic_div_sub_divisors_le
    {lambda₂ lambda₃ : ℝ} (h₃ : 0 < lambda₃) :
    ∀ᶠ P : ℕ in Filter.atTop,
      1 < P ∧ ∀ m Q t s parity : ℕ, 0 < m → 0 < s →
        ∀ a q : ℕ, ∀ beta : ℝ, ∀ z : ℤ,
        let H := huaStepEightSieveProduct P
        let Y := Nat.ceil (Real.rpow (Real.log P) lambda₃)
        let R := huaStepEightSourceCondition P m Q t lambda₂
        ‖((∑ pair ∈ huaStepEightPairs H Y (P / m) s parity R,
              addChar (rationalCenter a q + beta + z)
                (primeCubic (m * (pair.1 * pair.2)))) / (s : ℂ)) -
          (∑ v ∈ huaStepEightDivisors H Y (P / m) s parity R,
            addChar (rationalCenter a q + beta + z) (primeCubic (m * v)))‖ ≤
          (4 : ℝ) * P / ((s : ℝ) * m * Real.rpow (Real.log P) lambda₃) := by
  filter_upwards [eventually_norm_huaSourceStepEight_primeCubic_div_sub_divisors_le h₃]
    with P hP
  refine ⟨hP.1, ?_⟩
  intro m Q t s parity hm hs a q beta z
  exact hP.2 m Q t s parity hm hs (rationalCenter a q + beta + z)

end CookMagyarCircle
end SystolicGrowth

#print axioms SystolicGrowth.CookMagyarCircle.eventually_norm_huaSourceStepEight_generalCubic_div_sub_divisors_le
#print axioms SystolicGrowth.CookMagyarCircle.eventually_norm_huaSourceStepEight_rationalGeneralCubic_div_sub_divisors_le
#print axioms SystolicGrowth.CookMagyarCircle.eventually_norm_huaSourceStepEight_primeCubic_div_sub_divisors_le
#print axioms SystolicGrowth.CookMagyarCircle.eventually_norm_huaSourceStepEight_wrappedPrimeCubic_div_sub_divisors_le
