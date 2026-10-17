module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.HuaStepEight
public import CookMagyar.GeneralCubicWeyl

@[expose] public section

open scoped BigOperators

namespace SystolicGrowth
namespace CookMagyarCircle

open CookMagyarArcs

/-! # Actual cubic phases in Hua's step-eight correction

The exact source sieve product, ceiling cutoff, product interval,
progression, and parity remain unchanged. Unit modulus is proved for the
displayed cubic phases, rather than supplied as an extra estimate input.
-/

/-- Hua's exact source repeated-prime error for every real cubic polynomial,
uniformly in all four coefficients. -/
theorem eventually_norm_huaSourceStepEight_generalCubic_sub_recount_le
    {lambda₂ lambda₃ : ℝ} (h₃ : 0 < lambda₃) :
    ∀ᶠ P : ℕ in Filter.atTop,
      1 < P ∧ ∀ m Q t s parity : ℕ, 0 < m → ∀ a b c d : ℝ,
        let H := huaStepEightSieveProduct P
        let Y := Nat.ceil (Real.rpow (Real.log P) lambda₃)
        let R := huaStepEightSourceCondition P m Q t lambda₂
        ‖(∑ z ∈ huaStepEightPairs H Y (P / m) s parity R,
            generalCubicPhase a b c d (m * (z.1 * z.2))) -
          s • (∑ v ∈ huaStepEightDivisors H Y (P / m) s parity R,
            generalCubicPhase a b c d (m * v))‖ ≤
          (4 : ℝ) * P / ((m : ℝ) * Real.rpow (Real.log P) lambda₃) := by
  filter_upwards [eventually_norm_huaSourceStepEight_sub_recount_le h₃] with P hP
  refine ⟨hP.1, ?_⟩
  intro m Q t s parity hm a b c d
  exact hP.2 m Q t s parity hm (generalCubicPhase a b c d)
    (by intro z hz; simp only [norm_generalCubicPhase, le_refl])

/-- Rational-leading specialization with arbitrary real lower coefficients.
No denominator or approximation hypothesis is needed for this combinatorial
correction: its only phase input is the proved unit modulus. -/
theorem eventually_norm_huaSourceStepEight_rationalGeneralCubic_sub_recount_le
    {lambda₂ lambda₃ : ℝ} (h₃ : 0 < lambda₃) :
    ∀ᶠ P : ℕ in Filter.atTop,
      1 < P ∧ ∀ m Q t s parity : ℕ, 0 < m → ∀ a q : ℕ, ∀ b c d : ℝ,
        let H := huaStepEightSieveProduct P
        let Y := Nat.ceil (Real.rpow (Real.log P) lambda₃)
        let R := huaStepEightSourceCondition P m Q t lambda₂
        ‖(∑ z ∈ huaStepEightPairs H Y (P / m) s parity R,
            generalCubicPhase (rationalCenter a q) b c d (m * (z.1 * z.2))) -
          s • (∑ v ∈ huaStepEightDivisors H Y (P / m) s parity R,
            generalCubicPhase (rationalCenter a q) b c d (m * v))‖ ≤
          (4 : ℝ) * P / ((m : ℝ) * Real.rpow (Real.log P) lambda₃) := by
  filter_upwards [eventually_norm_huaSourceStepEight_generalCubic_sub_recount_le h₃]
    with P hP
  refine ⟨hP.1, ?_⟩
  intro m Q t s parity hm a q b c d
  exact hP.2 m Q t s parity hm (rationalCenter a q) b c d

/-- The correction for the actual displaced cubic `x³-x`, at the original
real frequency, follows from its exact general-cubic identification. -/
theorem eventually_norm_huaSourceStepEight_primeCubic_sub_recount_le
    {lambda₂ lambda₃ : ℝ} (h₃ : 0 < lambda₃) :
    ∀ᶠ P : ℕ in Filter.atTop,
      1 < P ∧ ∀ m Q t s parity : ℕ, 0 < m → ∀ alpha : ℝ,
        let H := huaStepEightSieveProduct P
        let Y := Nat.ceil (Real.rpow (Real.log P) lambda₃)
        let R := huaStepEightSourceCondition P m Q t lambda₂
        ‖(∑ z ∈ huaStepEightPairs H Y (P / m) s parity R,
            addChar alpha (primeCubic (m * (z.1 * z.2)))) -
          s • (∑ v ∈ huaStepEightDivisors H Y (P / m) s parity R,
            addChar alpha (primeCubic (m * v)))‖ ≤
          (4 : ℝ) * P / ((m : ℝ) * Real.rpow (Real.log P) lambda₃) := by
  filter_upwards [eventually_norm_huaSourceStepEight_generalCubic_sub_recount_le h₃]
    with P hP
  refine ⟨hP.1, ?_⟩
  intro m Q t s parity hm alpha
  simpa only [← addChar_primeCubic_eq_generalCubicPhase] using
    hP.2 m Q t s parity hm alpha 0 (-alpha) 0

/-- Wrapped-frequency form of the actual `x³-x` correction. The integer
wrap is kept in the original character, and all source restrictions and
the source-scale error remain intact. -/
theorem eventually_norm_huaSourceStepEight_wrappedPrimeCubic_sub_recount_le
    {lambda₂ lambda₃ : ℝ} (h₃ : 0 < lambda₃) :
    ∀ᶠ P : ℕ in Filter.atTop,
      1 < P ∧ ∀ m Q t s parity : ℕ, 0 < m → ∀ a q : ℕ,
        ∀ beta : ℝ, ∀ z : ℤ,
        let H := huaStepEightSieveProduct P
        let Y := Nat.ceil (Real.rpow (Real.log P) lambda₃)
        let R := huaStepEightSourceCondition P m Q t lambda₂
        ‖(∑ pair ∈ huaStepEightPairs H Y (P / m) s parity R,
            addChar (rationalCenter a q + beta + z)
              (primeCubic (m * (pair.1 * pair.2)))) -
          s • (∑ v ∈ huaStepEightDivisors H Y (P / m) s parity R,
            addChar (rationalCenter a q + beta + z) (primeCubic (m * v)))‖ ≤
          (4 : ℝ) * P / ((m : ℝ) * Real.rpow (Real.log P) lambda₃) := by
  filter_upwards [eventually_norm_huaSourceStepEight_primeCubic_sub_recount_le h₃]
    with P hP
  refine ⟨hP.1, ?_⟩
  intro m Q t s parity hm a q beta z
  exact hP.2 m Q t s parity hm (rationalCenter a q + beta + z)

end CookMagyarCircle
end SystolicGrowth

#print axioms SystolicGrowth.CookMagyarCircle.eventually_norm_huaSourceStepEight_generalCubic_sub_recount_le
#print axioms SystolicGrowth.CookMagyarCircle.eventually_norm_huaSourceStepEight_rationalGeneralCubic_sub_recount_le
#print axioms SystolicGrowth.CookMagyarCircle.eventually_norm_huaSourceStepEight_primeCubic_sub_recount_le
#print axioms SystolicGrowth.CookMagyarCircle.eventually_norm_huaSourceStepEight_wrappedPrimeCubic_sub_recount_le
