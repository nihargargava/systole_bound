module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.HuaStepEight
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

open scoped BigOperators

namespace SystolicGrowth
namespace CookMagyarCircle

/-! # Exact factor-count coverage for Hua's source divisors

Every positive cutoff-factor count lies in the actual source range
`1 ≤ s ≤ floor(log P)` once its cutoff is at least three. The zero-count
smooth branch is retained separately; it is not declared empty.
-/

/-- The product of distinct cutoff primes is at least the corresponding
power of the cutoff and divides the original positive integer. -/
theorem cutoff_pow_card_primeFactorsAtLeastCutoff_le {Y d : ℕ} (hd : 0 < d) :
    Y ^ (primeFactorsAtLeastCutoff Y d).card ≤ d := by
  have hprodDvd : (∏ p ∈ primeFactorsAtLeastCutoff Y d, p) ∣ d :=
    dvd_trans (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _))
      (Nat.prod_primeFactors_dvd d)
  calc
    Y ^ (primeFactorsAtLeastCutoff Y d).card =
        ∏ _p ∈ primeFactorsAtLeastCutoff Y d, Y := by simp
    _ ≤ ∏ p ∈ primeFactorsAtLeastCutoff Y d, p := by
      apply Finset.prod_le_prod₀
      · intro p hp
        exact Nat.zero_le Y
      · intro p hp
        exact (Finset.mem_filter.mp hp).2
    _ ≤ d := Nat.le_of_dvd hd hprodDvd

/-- Cutoff three makes each distinct large prime contribute at least one
to the logarithm of the positive integer. -/
theorem card_primeFactorsAtLeastCutoff_le_log {Y d : ℕ}
    (hY : 3 ≤ Y) (hd : 0 < d) :
    ((primeFactorsAtLeastCutoff Y d).card : ℝ) ≤ Real.log d := by
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
  have hlogY : 1 ≤ Real.log (Y : ℝ) :=
    (Real.le_log_iff_exp_le hYpos).mpr
      (Real.exp_one_lt_three.le.trans (by exact_mod_cast hY))
  have hsize : (Y : ℝ) ^ (primeFactorsAtLeastCutoff Y d).card ≤ d := by
    exact_mod_cast cutoff_pow_card_primeFactorsAtLeastCutoff_le (Y := Y) hd
  calc
    ((primeFactorsAtLeastCutoff Y d).card : ℝ) ≤
        ((primeFactorsAtLeastCutoff Y d).card : ℝ) * Real.log Y := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hlogY
          (Nat.cast_nonneg (primeFactorsAtLeastCutoff Y d).card)
    _ = Real.log ((Y : ℝ) ^ (primeFactorsAtLeastCutoff Y d).card) :=
      (Real.log_pow _ _).symm
    _ ≤ Real.log d := Real.log_le_log (pow_pos hYpos _) hsize

/-- The exact natural factor-count range follows by flooring the logarithmic
size bound; no guessed truncation parameter is introduced. -/
theorem card_primeFactorsAtLeastCutoff_le_floor_log {Y d P : ℕ}
    (hY : 3 ≤ Y) (hd : 0 < d) (hdP : d ≤ P) :
    (primeFactorsAtLeastCutoff Y d).card ≤ Nat.floor (Real.log P) := by
  apply Nat.le_floor
  exact (card_primeFactorsAtLeastCutoff_le_log hY hd).trans
    (Real.log_le_log (by exact_mod_cast hd) (by exact_mod_cast hdP))

/-- All source-eligible divisors, before separating their large-factor
count. Range, parity, and the product restriction are unchanged. -/
noncomputable def huaStepEightEligibleDivisors (H M parity : ℕ)
    (R : ℕ → Prop) : Finset ℕ := by
  classical
  exact H.divisors.filter fun d => d ≤ M ∧ d.primeFactors.card % 2 = parity ∧ R d

/-- The eligible branch having a positive number of cutoff prime factors. -/
noncomputable def huaStepEightLargeFactorDivisors (H Y M parity : ℕ)
    (R : ℕ → Prop) : Finset ℕ := by
  classical
  exact (huaStepEightEligibleDivisors H M parity R).filter fun d =>
    0 < (primeFactorsAtLeastCutoff Y d).card

theorem mem_huaStepEightEligibleDivisors_iff {H M parity d : ℕ} {R : ℕ → Prop} :
    d ∈ huaStepEightEligibleDivisors H M parity R ↔
      d ∈ H.divisors ∧ d ≤ M ∧ d.primeFactors.card % 2 = parity ∧ R d := by
  classical
  simp only [huaStepEightEligibleDivisors, Finset.mem_filter]

theorem mem_huaStepEightLargeFactorDivisors_iff {H Y M parity d : ℕ} {R : ℕ → Prop} :
    d ∈ huaStepEightLargeFactorDivisors H Y M parity R ↔
      d ∈ H.divisors ∧ d ≤ M ∧ 0 < (primeFactorsAtLeastCutoff Y d).card ∧
        d.primeFactors.card % 2 = parity ∧ R d := by
  classical
  simp only [huaStepEightLargeFactorDivisors, Finset.mem_filter,
    mem_huaStepEightEligibleDivisors_iff]
  tauto

/-- Each positive-count fiber is exactly the already defined source
divisor family with that factor count. -/
theorem huaStepEightLargeFactorDivisors_filter_count
    (H Y M parity s : ℕ) (R : ℕ → Prop) (hs : 0 < s) :
    (huaStepEightLargeFactorDivisors H Y M parity R).filter
        (fun d => (primeFactorsAtLeastCutoff Y d).card = s) =
      huaStepEightDivisors H Y M s parity R := by
  classical
  ext d
  simp only [Finset.mem_filter, mem_huaStepEightLargeFactorDivisors_iff,
    mem_huaStepEightDivisors_iff]
  constructor
  · rintro ⟨⟨hd, hdM, _, hparity, hR⟩, hcount⟩
    exact ⟨hd, hdM, hcount, hparity, hR⟩
  · rintro ⟨hd, hdM, hcount, hparity, hR⟩
    exact ⟨⟨hd, hdM, by omega, hparity, hR⟩, hcount⟩

/-- The positive large-factor branch is partitioned by every actual source
factor count, with exactly the endpoint `floor(log P)`. -/
theorem sum_huaStepEightLargeFactorDivisors_eq_count_fibres
    {A : Type*} [AddCommMonoid A] {H Y M P parity : ℕ} {R : ℕ → Prop}
    (hY : 3 ≤ Y) (hMP : M ≤ P) (f : ℕ → A) :
    (∑ d ∈ huaStepEightLargeFactorDivisors H Y M parity R, f d) =
      ∑ s ∈ Finset.Icc 1 (Nat.floor (Real.log P)),
        ∑ d ∈ huaStepEightDivisors H Y M s parity R, f d := by
  classical
  have hmaps : ∀ d ∈ huaStepEightLargeFactorDivisors H Y M parity R,
      (primeFactorsAtLeastCutoff Y d).card ∈ Finset.Icc 1 (Nat.floor (Real.log P)) := by
    intro d hd
    rcases mem_huaStepEightLargeFactorDivisors_iff.mp hd with
      ⟨hdH, hdM, hcount, _, _⟩
    exact Finset.mem_Icc.mpr ⟨hcount,
      card_primeFactorsAtLeastCutoff_le_floor_log hY
        (Nat.pos_of_mem_divisors hdH) (hdM.trans hMP)⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps f]
  apply Finset.sum_congr rfl
  intro s hs
  rw [huaStepEightLargeFactorDivisors_filter_count H Y M parity s R
    (Finset.mem_Icc.mp hs).1]

/-- The complete eligible sum splits into the zero-count smooth branch
and the exact positive-count source range. The former is retained. -/
theorem sum_huaStepEightEligibleDivisors_eq_zero_add_count_fibres
    {A : Type*} [AddCommMonoid A] {H Y M P parity : ℕ} {R : ℕ → Prop}
    (hY : 3 ≤ Y) (hMP : M ≤ P) (f : ℕ → A) :
    (∑ d ∈ huaStepEightEligibleDivisors H M parity R, f d) =
      (∑ d ∈ huaStepEightDivisors H Y M 0 parity R, f d) +
        ∑ s ∈ Finset.Icc 1 (Nat.floor (Real.log P)),
          ∑ d ∈ huaStepEightDivisors H Y M s parity R, f d := by
  classical
  have hzero : (huaStepEightEligibleDivisors H M parity R).filter
      (fun d => (primeFactorsAtLeastCutoff Y d).card = 0) =
      huaStepEightDivisors H Y M 0 parity R := by
    ext d
    simp only [Finset.mem_filter, mem_huaStepEightEligibleDivisors_iff,
      mem_huaStepEightDivisors_iff]
    tauto
  have hpositive : (huaStepEightEligibleDivisors H M parity R).filter
      (fun d => ¬(primeFactorsAtLeastCutoff Y d).card = 0) =
      huaStepEightLargeFactorDivisors H Y M parity R := by
    ext d
    simp only [huaStepEightLargeFactorDivisors, Finset.mem_filter, Nat.pos_iff_ne_zero]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (huaStepEightEligibleDivisors H M parity R)
    (fun d => (primeFactorsAtLeastCutoff Y d).card = 0) f
  rw [hzero, hpositive, sum_huaStepEightLargeFactorDivisors_eq_count_fibres hY hMP f]
    at hsplit
  exact hsplit.symm

/-- Hua's exact ceiling cutoff eventually exceeds three for every positive
real cutoff exponent. -/
theorem eventually_three_le_huaStepEightSourceCutoff
    {lambda₃ : ℝ} (h₃ : 0 < lambda₃) :
    ∀ᶠ P : ℕ in Filter.atTop,
      1 < P ∧ 3 ≤ Nat.ceil (Real.rpow (Real.log P) lambda₃) := by
  have hlog : Filter.Tendsto (fun P : ℕ => Real.log (P : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hcutoff := (tendsto_rpow_atTop h₃).comp hlog
  filter_upwards [hcutoff.eventually_ge_atTop (3 : ℝ),
    Filter.eventually_gt_atTop (1 : ℕ)] with P hcutoff hP
  refine ⟨hP, ?_⟩
  have hceil : (3 : ℝ) ≤ (Nat.ceil (Real.rpow (Real.log P) lambda₃) : ℝ) :=
    hcutoff.trans (Nat.le_ceil _)
  exact_mod_cast hceil

/-- Exact count-fiber coverage of the actual source large-factor branch,
including its ceiling cutoff, strict lower endpoint, and progression. -/
theorem eventually_sum_huaSourceStepEightLargeFactorDivisors_eq_count_fibres
    {A : Type*} [AddCommMonoid A] {lambda₂ lambda₃ : ℝ} (h₃ : 0 < lambda₃) :
    ∀ᶠ P : ℕ in Filter.atTop,
      1 < P ∧ ∀ m Q t parity : ℕ, 0 < m → ∀ f : ℕ → A,
        let H := huaStepEightSieveProduct P
        let Y := Nat.ceil (Real.rpow (Real.log P) lambda₃)
        let R := huaStepEightSourceCondition P m Q t lambda₂
        (∑ d ∈ huaStepEightLargeFactorDivisors H Y (P / m) parity R, f (m * d)) =
          ∑ s ∈ Finset.Icc 1 (Nat.floor (Real.log P)),
            ∑ d ∈ huaStepEightDivisors H Y (P / m) s parity R, f (m * d) := by
  filter_upwards [eventually_three_le_huaStepEightSourceCutoff h₃] with P hP
  refine ⟨hP.1, ?_⟩
  intro m Q t parity _hm f
  exact sum_huaStepEightLargeFactorDivisors_eq_count_fibres hP.2
    (Nat.div_le_self P m) (fun d => f (m * d))

/-- Complete source partition with the zero-large-factor smooth term still
displayed separately from the positive factor-count range. -/
theorem eventually_sum_huaSourceStepEightEligibleDivisors_eq_zero_add_count_fibres
    {A : Type*} [AddCommMonoid A] {lambda₂ lambda₃ : ℝ} (h₃ : 0 < lambda₃) :
    ∀ᶠ P : ℕ in Filter.atTop,
      1 < P ∧ ∀ m Q t parity : ℕ, 0 < m → ∀ f : ℕ → A,
        let H := huaStepEightSieveProduct P
        let Y := Nat.ceil (Real.rpow (Real.log P) lambda₃)
        let R := huaStepEightSourceCondition P m Q t lambda₂
        (∑ d ∈ huaStepEightEligibleDivisors H (P / m) parity R, f (m * d)) =
          (∑ d ∈ huaStepEightDivisors H Y (P / m) 0 parity R, f (m * d)) +
            ∑ s ∈ Finset.Icc 1 (Nat.floor (Real.log P)),
              ∑ d ∈ huaStepEightDivisors H Y (P / m) s parity R, f (m * d) := by
  filter_upwards [eventually_three_le_huaStepEightSourceCutoff h₃] with P hP
  refine ⟨hP.1, ?_⟩
  intro m Q t parity _hm f
  exact sum_huaStepEightEligibleDivisors_eq_zero_add_count_fibres hP.2
    (Nat.div_le_self P m) (fun d => f (m * d))

/-- The actual zero-count source branch consists of smooth squarefree
integers in the original large-divisor interval. The ceiling cutoff used
by the pair sum implies the floor cutoff required by the smooth tail. -/
theorem huaStepEightZeroCount_subset_smoothSquarefree
    (P m Q t parity : ℕ) (lambda₂ lambda₃ : ℝ) :
    huaStepEightDivisors (huaStepEightSieveProduct P)
        (Nat.ceil (Real.rpow (Real.log P) lambda₃)) (P / m) 0 parity
        (huaStepEightSourceCondition P m Q t lambda₂) ⊆
      (Finset.Icc 1 P).filter (fun d : ℕ =>
        Squarefree d ∧ d ≠ 0 ∧
          (∀ p ∈ d.primeFactors,
            p ≤ Nat.floor (Real.rpow (Real.log P) lambda₃)) ∧
          (P : ℝ) / Real.rpow (Real.log P) lambda₂ ≤ (d : ℝ)) := by
  classical
  intro d hd
  obtain ⟨hdH, hdM, hcount, _hparity, hsource⟩ :=
    mem_huaStepEightDivisors_iff.mp hd
  have hsq : Squarefree d := (squarefree_huaStepEightSieveProduct P).squarefree_of_dvd
    (Nat.mem_divisors.mp hdH).1
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hdH
  refine Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨hdpos, hdM.trans (Nat.div_le_self P m)⟩,
      hsq, hdpos.ne', ?_, hsource.1.le⟩
  intro p hp
  have hpCut : p < Nat.ceil (Real.rpow (Real.log P) lambda₃) := by
    by_contra h
    have hpLarge : p ∈ primeFactorsAtLeastCutoff
        (Nat.ceil (Real.rpow (Real.log P) lambda₃)) d :=
      Finset.mem_filter.mpr ⟨hp, by omega⟩
    have hempty := Finset.card_eq_zero.mp hcount
    rw [hempty] at hpLarge
    simp at hpLarge
  exact Nat.le_floor (Nat.lt_ceil.mp hpCut).le

/-- Hua's smooth zero-count branch has any prescribed logarithmic saving,
uniformly in the multiplier, progression and factor parity. The estimate
uses the actual source set, not a supplied cardinality hypothesis. -/
theorem eventually_huaSourceStepEight_zeroCount_card_logSaving_le
    {lambda₂ lambda₃ rho : ℝ} (h₂ : 0 ≤ lambda₂) (h₃ : 0 < lambda₃)
    (hrho : 0 ≤ rho) :
    ∀ᶠ P : ℕ in Filter.atTop,
      1 < P ∧ ∀ m Q t parity : ℕ,
        Real.rpow (Real.log P) rho *
          ((huaStepEightDivisors (huaStepEightSieveProduct P)
            (Nat.ceil (Real.rpow (Real.log P) lambda₃)) (P / m) 0 parity
            (huaStepEightSourceCondition P m Q t lambda₂)).card : ℝ) ≤ P := by
  filter_upwards [eventually_hua_truncatedLog_smoothSquarefree_count_le h₂ h₃ hrho]
    with P hP
  refine ⟨hP.1, ?_⟩
  intro m Q t parity
  have hcard := Finset.card_le_card
    (huaStepEightZeroCount_subset_smoothSquarefree P m Q t parity lambda₂ lambda₃)
  have hcardR := (Nat.cast_le (α := ℝ)).mpr hcard
  exact (mul_le_mul_of_nonneg_left hcardR
    (Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast hP.1.le)) _)).trans hP.2

/-- Summing the actual smooth source remainder over all `m ≤ (log P)^lambda₂`
still has any prescribed saving. A stronger smooth tail pays for the full
multiplier count; no cancellation or coefficient estimate is assumed. -/
theorem eventually_norm_huaSourceStepEight_zeroCount_aggregate_logSaving_le
    {lambda₂ lambda₃ rho : ℝ} (h₂ : 0 ≤ lambda₂) (h₃ : 0 < lambda₃)
    (hrho : 0 ≤ rho) :
    ∀ᶠ P : ℕ in Filter.atTop,
      1 < P ∧ ∀ Q t parity : ℕ, ∀ f : ℕ → ℂ,
        (∀ n, ‖f n‖ ≤ 1) →
        ‖∑ m ∈ Finset.Icc 1 (Nat.floor (Real.rpow (Real.log P) lambda₂)),
          ∑ d ∈ huaStepEightDivisors (huaStepEightSieveProduct P)
            (Nat.ceil (Real.rpow (Real.log P) lambda₃)) (P / m) 0 parity
            (huaStepEightSourceCondition P m Q t lambda₂), f (m * d)‖ ≤
          (P : ℝ) / Real.rpow (Real.log P) rho := by
  filter_upwards [eventually_huaSourceStepEight_zeroCount_card_logSaving_le
    h₂ h₃ (add_nonneg hrho h₂)] with P hP
  refine ⟨hP.1, ?_⟩
  intro Q t parity f hf
  let L : ℝ := Real.log P
  let M : ℕ := Nat.floor (Real.rpow L lambda₂)
  let S := fun m => huaStepEightDivisors (huaStepEightSieveProduct P)
    (Nat.ceil (Real.rpow L lambda₃)) (P / m) 0 parity
    (huaStepEightSourceCondition P m Q t lambda₂)
  have hL : 0 < L := Real.log_pos (by exact_mod_cast hP.1)
  have hpow : 0 < Real.rpow L (rho + lambda₂) := Real.rpow_pos_of_pos hL _
  have hcard : (M : ℝ) ≤ Real.rpow L lambda₂ :=
    Nat.floor_le (Real.rpow_nonneg hL.le _)
  have hblock : ∀ m : ℕ, ‖∑ d ∈ S m, f (m * d)‖ ≤
      (P : ℝ) / Real.rpow L (rho + lambda₂) := by
    intro m
    calc
      _ ≤ ∑ d ∈ S m, ‖f (m * d)‖ := norm_sum_le _ _
      _ ≤ ∑ _d ∈ S m, (1 : ℝ) := Finset.sum_le_sum (fun d _ => hf (m * d))
      _ = ((S m).card : ℝ) := by simp
      _ ≤ (P : ℝ) / Real.rpow L (rho + lambda₂) := by
        apply (le_div_iff₀ hpow).mpr
        simpa only [mul_comm] using hP.2 m Q t parity
  change ‖∑ m ∈ Finset.Icc 1 M, ∑ d ∈ S m, f (m * d)‖ ≤
    (P : ℝ) / Real.rpow L rho
  calc
    _ ≤ ∑ m ∈ Finset.Icc 1 M, ‖∑ d ∈ S m, f (m * d)‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ Finset.Icc 1 M,
        (P : ℝ) / Real.rpow L (rho + lambda₂) :=
      Finset.sum_le_sum (fun m _ => hblock m)
    _ = (M : ℝ) * ((P : ℝ) / Real.rpow L (rho + lambda₂)) := by simp
    _ ≤ Real.rpow L lambda₂ * ((P : ℝ) / Real.rpow L (rho + lambda₂)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (P : ℝ) / Real.rpow L rho := by
      change L ^ lambda₂ * ((P : ℝ) / L ^ (rho + lambda₂)) = (P : ℝ) / L ^ rho
      rw [Real.rpow_add hL rho lambda₂]
      field_simp [ne_of_gt (Real.rpow_pos_of_pos hL rho),
        ne_of_gt (Real.rpow_pos_of_pos hL lambda₂)]

end CookMagyarCircle
end SystolicGrowth

#print axioms SystolicGrowth.CookMagyarCircle.cutoff_pow_card_primeFactorsAtLeastCutoff_le
#print axioms SystolicGrowth.CookMagyarCircle.card_primeFactorsAtLeastCutoff_le_floor_log
#print axioms SystolicGrowth.CookMagyarCircle.sum_huaStepEightLargeFactorDivisors_eq_count_fibres
#print axioms SystolicGrowth.CookMagyarCircle.sum_huaStepEightEligibleDivisors_eq_zero_add_count_fibres
#print axioms SystolicGrowth.CookMagyarCircle.eventually_sum_huaSourceStepEightLargeFactorDivisors_eq_count_fibres
#print axioms SystolicGrowth.CookMagyarCircle.eventually_sum_huaSourceStepEightEligibleDivisors_eq_zero_add_count_fibres
#print axioms SystolicGrowth.CookMagyarCircle.huaStepEightZeroCount_subset_smoothSquarefree
#print axioms SystolicGrowth.CookMagyarCircle.eventually_huaSourceStepEight_zeroCount_card_logSaving_le
#print axioms SystolicGrowth.CookMagyarCircle.eventually_norm_huaSourceStepEight_zeroCount_aggregate_logSaving_le
