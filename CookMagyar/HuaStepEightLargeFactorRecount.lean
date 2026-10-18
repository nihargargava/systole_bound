module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.HuaStepEightFactorPartition
public import CookMagyar.HuaStepEightAggregation

@[expose] public section

open scoped BigOperators

namespace SystolicGrowth
namespace CookMagyarCircle

/-! # The actual large-factor source recount and its correction

The factor-count partition identifies Hua's full positive-large-factor
divisor branch with its normalized pair aggregate, up to the proved
repeated-prime error. The zero-count smooth branch remains separate. These
theorems do not assert cancellation of the Type-II pair aggregate.
-/

/-- The actual normalized pair aggregate minus the original positive
large-factor divisor aggregate, at the source's two logarithmic cutoffs. -/
noncomputable def huaStepEightLargeFactorRecountError (P Q t parity : ℕ)
    (lambda₂ lambda₃ : ℝ) (f : ℕ → ℂ) : ℂ :=
  let H := huaStepEightSieveProduct P
  let Y := Nat.ceil (Real.rpow (Real.log P) lambda₃)
  let M := Nat.floor (Real.rpow (Real.log P) lambda₂)
  let S := Nat.floor (Real.log P)
  (∑ m ∈ Finset.Icc 1 M, ∑ s ∈ Finset.Icc 1 S,
      (∑ pair ∈ huaStepEightPairs H Y (P / m) s parity
          (huaStepEightSourceCondition P m Q t lambda₂),
        f (m * (pair.1 * pair.2))) / (s : ℂ)) -
    ∑ m ∈ Finset.Icc 1 M,
      ∑ d ∈ huaStepEightLargeFactorDivisors H Y (P / m) parity
          (huaStepEightSourceCondition P m Q t lambda₂), f (m * d)

set_option maxHeartbeats 800000 in
/-- The discrepancy for the true positive-large-factor source branch is
exactly the already bounded sum of normalized corrections. Coverage of
the factor-count range is proved, not assumed or truncated by choice. -/
theorem eventually_huaStepEightLargeFactorRecountError_eq_aggregate
    {lambda₂ lambda₃ : ℝ} (h₃ : 0 < lambda₃) :
    ∀ᶠ P : ℕ in Filter.atTop,
      1 < P ∧ ∀ Q t parity : ℕ, ∀ f : ℕ → ℂ,
        huaStepEightLargeFactorRecountError P Q t parity lambda₂ lambda₃ f =
          huaStepEightAggregateError P Q t parity lambda₂ lambda₃
            (Nat.floor (Real.rpow (Real.log P) lambda₂)) (Nat.floor (Real.log P))
            (fun _ _ => 1) f := by
  filter_upwards [eventually_sum_huaSourceStepEightLargeFactorDivisors_eq_count_fibres
    (A := ℂ) (lambda₂ := lambda₂) h₃] with P hP
  refine ⟨hP.1, ?_⟩
  intro Q t parity f
  dsimp only [huaStepEightLargeFactorRecountError, huaStepEightAggregateError,
    huaStepEightSourceError]
  simp only [one_mul, Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  exact hP.2 m Q t parity
    (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hm).1) f

/-- The correction between the actual source large-factor branch and its
normalized pair aggregate has any logarithmic saving below `lambda₃`,
uniformly in progression, parity, and all real cubic coefficients. -/
theorem eventually_norm_huaSourceStepEight_generalCubic_largeFactorRecount_logSaving_le
    {lambda₂ lambda₃ rho : ℝ} (h₂ : 0 ≤ lambda₂) (h₃ : 0 < lambda₃)
    (hrho : rho < lambda₃) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ P : ℕ in Filter.atTop,
      1 < P ∧ ∀ Q t parity : ℕ, ∀ a b c d : ℝ,
        ‖huaStepEightLargeFactorRecountError P Q t parity lambda₂ lambda₃
          (generalCubicPhase a b c d)‖ ≤ K * P / Real.rpow (Real.log P) rho := by
  obtain ⟨K, hK, hbound⟩ :=
    eventually_norm_huaSourceStepEight_generalCubic_aggregate_logSaving_le h₂ h₃ hrho
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbound, eventually_huaStepEightLargeFactorRecountError_eq_aggregate h₃]
    with P hP heq
  refine ⟨hP.1, ?_⟩
  intro Q t parity a b c d
  rw [heq.2 Q t parity (generalCubicPhase a b c d)]
  exact hP.2 Q t parity (fun _ _ => 1) (by intro m hm s hs; simp) a b c d

/-- The same complete positive-large-factor source correction for the
actual `x³-x` character, with no supplied phase-norm estimate. -/
theorem eventually_norm_huaSourceStepEight_primeCubic_largeFactorRecount_logSaving_le
    {lambda₂ lambda₃ rho : ℝ} (h₂ : 0 ≤ lambda₂) (h₃ : 0 < lambda₃)
    (hrho : rho < lambda₃) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ P : ℕ in Filter.atTop,
      1 < P ∧ ∀ Q t parity : ℕ, ∀ alpha : ℝ,
        ‖huaStepEightLargeFactorRecountError P Q t parity lambda₂ lambda₃
          (fun n => addChar alpha (primeCubic n))‖ ≤
            K * P / Real.rpow (Real.log P) rho := by
  obtain ⟨K, hK, hbound⟩ :=
    eventually_norm_huaSourceStepEight_primeCubic_unweighted_logSaving_le h₂ h₃ hrho
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbound, eventually_huaStepEightLargeFactorRecountError_eq_aggregate h₃]
    with P hP heq
  refine ⟨hP.1, ?_⟩
  intro Q t parity alpha
  rw [heq.2 Q t parity (fun n => addChar alpha (primeCubic n))]
  exact hP.2 Q t parity alpha

/-- The complete eligible source branch, including its smooth zero-count
terms, equals the pair aggregate plus an arbitrarily small logarithmic
error. This composes two proved source errors; it does not assume prime
cancellation or discard the zero-count branch. -/
theorem eventually_norm_huaSourceStepEight_eligible_sub_pairs_logSaving_le
    {lambda₂ lambda₃ rho : ℝ} (h₂ : 0 ≤ lambda₂) (h₃ : 0 < lambda₃)
    (hrho : 0 ≤ rho) (hrho₃ : rho < lambda₃) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ P : ℕ in Filter.atTop,
      1 < P ∧ ∀ Q t parity : ℕ, ∀ a b c d : ℝ,
        let H := huaStepEightSieveProduct P
        let Y := Nat.ceil (Real.rpow (Real.log P) lambda₃)
        let M := Nat.floor (Real.rpow (Real.log P) lambda₂)
        let S := Nat.floor (Real.log P)
        let R := fun m => huaStepEightSourceCondition P m Q t lambda₂
        ‖(∑ m ∈ Finset.Icc 1 M,
            ∑ v ∈ huaStepEightEligibleDivisors H (P / m) parity (R m),
              generalCubicPhase a b c d (m * v)) -
          (∑ m ∈ Finset.Icc 1 M, ∑ s ∈ Finset.Icc 1 S,
            (∑ pair ∈ huaStepEightPairs H Y (P / m) s parity (R m),
              generalCubicPhase a b c d (m * (pair.1 * pair.2))) / (s : ℂ))‖ ≤
          K * (P : ℝ) / Real.rpow (Real.log P) rho := by
  obtain ⟨K, hK, herror⟩ :=
    eventually_norm_huaSourceStepEight_generalCubic_largeFactorRecount_logSaving_le
      h₂ h₃ hrho₃
  refine ⟨K + 1, by positivity, ?_⟩
  filter_upwards [herror,
    eventually_norm_huaSourceStepEight_zeroCount_aggregate_logSaving_le h₂ h₃ hrho,
    eventually_sum_huaSourceStepEightEligibleDivisors_eq_zero_add_count_fibres
      (A := ℂ) (lambda₂ := lambda₂) h₃,
    eventually_sum_huaSourceStepEightLargeFactorDivisors_eq_count_fibres
      (A := ℂ) (lambda₂ := lambda₂) h₃] with P he hzero helig hlarge
  refine ⟨he.1, ?_⟩
  intro Q t parity a b c d
  dsimp only
  let H := huaStepEightSieveProduct P
  let Y := Nat.ceil (Real.rpow (Real.log P) lambda₃)
  let M := Nat.floor (Real.rpow (Real.log P) lambda₂)
  let S := Nat.floor (Real.log P)
  let R := fun m => huaStepEightSourceCondition P m Q t lambda₂
  let f := generalCubicPhase a b c d
  let Z : ℂ := ∑ m ∈ Finset.Icc 1 M,
    ∑ v ∈ huaStepEightDivisors H Y (P / m) 0 parity (R m), f (m * v)
  let A : ℂ := ∑ m ∈ Finset.Icc 1 M,
    ∑ v ∈ huaStepEightEligibleDivisors H (P / m) parity (R m), f (m * v)
  let B : ℂ := ∑ m ∈ Finset.Icc 1 M, ∑ s ∈ Finset.Icc 1 S,
    (∑ pair ∈ huaStepEightPairs H Y (P / m) s parity (R m),
      f (m * (pair.1 * pair.2))) / (s : ℂ)
  have hsplit : A = Z +
      ∑ m ∈ Finset.Icc 1 M,
        ∑ v ∈ huaStepEightLargeFactorDivisors H Y (P / m) parity (R m), f (m * v) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    have hmpos : 0 < m := (Finset.mem_Icc.mp hm).1
    rw [hlarge.2 m Q t parity hmpos f]
    exact helig.2 m Q t parity hmpos f
  have hid : A - B = Z - huaStepEightLargeFactorRecountError
      P Q t parity lambda₂ lambda₃ f := by
    rw [hsplit]
    dsimp only [huaStepEightLargeFactorRecountError, B, H, Y, M, S, R]
    abel
  have hZ : ‖Z‖ ≤ (P : ℝ) / Real.rpow (Real.log P) rho :=
    hzero.2 Q t parity f (by intro n; simp only [f, norm_generalCubicPhase, le_refl])
  have hE := he.2 Q t parity a b c d
  change ‖A - B‖ ≤ (K + 1) * (P : ℝ) / Real.rpow (Real.log P) rho
  rw [hid]
  calc
    _ ≤ ‖Z‖ + ‖huaStepEightLargeFactorRecountError P Q t parity lambda₂ lambda₃ f‖ :=
      norm_sub_le _ _
    _ ≤ (P : ℝ) / Real.rpow (Real.log P) rho +
        K * (P : ℝ) / Real.rpow (Real.log P) rho := add_le_add hZ hE
    _ = _ := by ring

end CookMagyarCircle
end SystolicGrowth

#print axioms SystolicGrowth.CookMagyarCircle.eventually_huaStepEightLargeFactorRecountError_eq_aggregate
#print axioms SystolicGrowth.CookMagyarCircle.eventually_norm_huaSourceStepEight_generalCubic_largeFactorRecount_logSaving_le
#print axioms SystolicGrowth.CookMagyarCircle.eventually_norm_huaSourceStepEight_primeCubic_largeFactorRecount_logSaving_le
#print axioms SystolicGrowth.CookMagyarCircle.eventually_norm_huaSourceStepEight_eligible_sub_pairs_logSaving_le
