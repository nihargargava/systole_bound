module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.HuaDivisorBound
public import CookMagyar.HuaSieve

@[expose] public section

open scoped BigOperators

namespace SystolicGrowth
namespace CookMagyarCircle

/-! # The good/repeated-prime decomposition in Hua's step 8

For a squarefree sieve product `H`, retain the product range, progression,
and parity while choosing a large prime factor. The good pairs recount each
eligible divisor exactly `s` times; repeated primes form the explicit error.
The arbitrary predicate `R` records restrictions on the product, such as the
source lower endpoint and the congruence `m*d ≡ t (mod Q)`.
-/

/-- Eligible divisors with exactly `s` large prime factors and the prescribed
parity of the total number of prime factors. -/
noncomputable def huaStepEightDivisors (H Y M s parity : ℕ)
    (R : ℕ → Prop) : Finset ℕ := by
  classical
  exact H.divisors.filter fun d => d ≤ M ∧
    (primeFactorsAtLeastCutoff Y d).card = s ∧
    d.primeFactors.card % 2 = parity ∧ R d

/-- The unrestricted source pairs: a chosen cutoff prime of `H` and a
divisor `v` with one fewer large factor and opposite total-factor parity.
The product need not divide `H`, since a chosen prime may divide `v` again. -/
noncomputable def huaStepEightPairs (H Y M s parity : ℕ)
    (R : ℕ → Prop) : Finset (ℕ × ℕ) := by
  classical
  exact ((primeFactorsAtLeastCutoff Y H) ×ˢ H.divisors).filter fun z =>
    z.1 * z.2 ≤ M ∧ (primeFactorsAtLeastCutoff Y z.2).card + 1 = s ∧
    (z.2.primeFactors.card + 1) % 2 = parity ∧ R (z.1 * z.2)

/-- The repeated-prime branch with all original source restrictions retained. -/
noncomputable def huaStepEightBadPairs (H Y M s parity : ℕ)
    (R : ℕ → Prop) : Finset (ℕ × ℕ) := by
  classical
  exact (huaStepEightPairs H Y M s parity R).filter fun z => z.1 ∣ z.2

theorem mem_huaStepEightDivisors_iff {H Y M s parity d : ℕ} {R : ℕ → Prop} :
    d ∈ huaStepEightDivisors H Y M s parity R ↔
      d ∈ H.divisors ∧ d ≤ M ∧ (primeFactorsAtLeastCutoff Y d).card = s ∧
      d.primeFactors.card % 2 = parity ∧ R d := by
  classical
  simp only [huaStepEightDivisors, Finset.mem_filter]

theorem mem_huaStepEightPairs_iff {H Y M s parity p v : ℕ} {R : ℕ → Prop} :
    (p, v) ∈ huaStepEightPairs H Y M s parity R ↔
      p ∈ primeFactorsAtLeastCutoff Y H ∧ v ∈ H.divisors ∧ p * v ≤ M ∧
      (primeFactorsAtLeastCutoff Y v).card + 1 = s ∧
      (v.primeFactors.card + 1) % 2 = parity ∧ R (p * v) := by
  classical
  simp only [huaStepEightPairs, Finset.mem_filter, Finset.mem_product]
  tauto

/-- The good branch is exactly the factor/quotient representation of the
eligible divisor family, including its range, parity, and product predicate. -/
theorem huaStepEight_goodPairs_eq {H Y M s parity : ℕ} {R : ℕ → Prop}
    (hH : Squarefree H) :
    (huaStepEightPairs H Y M s parity R).filter (fun z => ¬z.1 ∣ z.2) =
      primeFactorQuotientPairs Y (huaStepEightDivisors H Y M s parity R) := by
  classical
  have hDsq : ∀ d ∈ huaStepEightDivisors H Y M s parity R, Squarefree d := by
    intro d hd
    exact hH.squarefree_of_dvd
      (Nat.mem_divisors.mp (mem_huaStepEightDivisors_iff.mp hd).1).1
  ext ⟨p, v⟩
  rw [Finset.mem_filter, mem_primeFactorQuotientPairs_iff_prime_product_mem hDsq]
  constructor
  · rintro ⟨hpair, hnot⟩
    rcases mem_huaStepEightPairs_iff.mp hpair with
      ⟨hpH, hvH, hbound, hcount, hparity, hR⟩
    have hpFac := (Finset.mem_filter.mp hpH).1
    have hp : Nat.Prime p := Nat.prime_of_mem_primeFactors hpFac
    have hYp : Y ≤ p := (Finset.mem_filter.mp hpH).2
    have hpdvd : p ∣ H := Nat.dvd_of_mem_primeFactors hpFac
    have hvdvd : v ∣ H := (Nat.mem_divisors.mp hvH).1
    have hvsq : Squarefree v := hH.squarefree_of_dvd hvdvd
    have hprodH : p * v ∣ H :=
      (hp.coprime_iff_not_dvd.mpr hnot).mul_dvd_of_dvd_of_dvd hpdvd hvdvd
    have hcut := card_primeFactorsAtLeastCutoff_mul_prime hp hvsq.ne_zero hYp hnot
    have hfull : (p * v).primeFactors.card = v.primeFactors.card + 1 := by
      simpa [primeFactorsAtLeastCutoff] using
        (card_primeFactorsAtLeastCutoff_mul_prime (Y := 0)
          hp hvsq.ne_zero (Nat.zero_le p) hnot)
    refine ⟨hp, hYp, mem_huaStepEightDivisors_iff.mpr ?_⟩
    exact ⟨Nat.mem_divisors.mpr ⟨hprodH, hH.ne_zero⟩, hbound,
      hcut.trans hcount, by simpa only [hfull] using hparity, hR⟩
  · rintro ⟨hp, hYp, hproduct⟩
    rcases mem_huaStepEightDivisors_iff.mp hproduct with
      ⟨hprodDiv, hbound, hcount, hparity, hR⟩
    have hprodH : p * v ∣ H := (Nat.mem_divisors.mp hprodDiv).1
    have hprodSq : Squarefree (p * v) := hH.squarefree_of_dvd hprodH
    have hvprod : v ∣ p * v := ⟨p, Nat.mul_comm p v⟩
    have hvsq : Squarefree v := hprodSq.squarefree_of_dvd hvprod
    have hnot : ¬p ∣ v := by
      intro hpv
      have hpsq : p * p ∣ p * v := by
        obtain ⟨w, rfl⟩ := hpv
        exact ⟨w, (Nat.mul_assoc p p w).symm⟩
      exact (Nat.squarefree_iff_prime_squarefree.mp hprodSq) p hp hpsq
    have hpdvdH : p ∣ H := dvd_trans (dvd_mul_right p v) hprodH
    have hpH : p ∈ primeFactorsAtLeastCutoff Y H :=
      Finset.mem_filter.mpr
        ⟨(Nat.mem_primeFactors_of_ne_zero hH.ne_zero).mpr ⟨hp, hpdvdH⟩, hYp⟩
    have hcut := card_primeFactorsAtLeastCutoff_mul_prime hp hvsq.ne_zero hYp hnot
    have hfull : (p * v).primeFactors.card = v.primeFactors.card + 1 := by
      simpa [primeFactorsAtLeastCutoff] using
        (card_primeFactorsAtLeastCutoff_mul_prime (Y := 0)
          hp hvsq.ne_zero (Nat.zero_le p) hnot)
    refine ⟨mem_huaStepEightPairs_iff.mpr ?_, hnot⟩
    exact ⟨hpH, Nat.mem_divisors.mpr ⟨dvd_trans hvprod hprodH, hH.ne_zero⟩,
      hbound, hcut.symm.trans hcount, by simpa only [hfull] using hparity, hR⟩

/-- All actual bad pairs embed in the previously bounded source-shaped
repeated family, without dropping their range or congruence from the sum. -/
theorem huaStepEightBadPairs_subset {H Y M s parity : ℕ} {R : ℕ → Prop}
    (hH : Squarefree H) :
    huaStepEightBadPairs H Y M s parity R ⊆ huaRepeatedStepEightPairs Y M s := by
  classical
  intro z hz
  rcases z with ⟨p, v⟩
  rcases Finset.mem_filter.mp hz with ⟨hpair, hpv⟩
  rcases mem_huaStepEightPairs_iff.mp hpair with
    ⟨hpH, hvH, hbound, hcount, hparity, hR⟩
  have hp : Nat.Prime p :=
    Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hpH).1
  have hYp : Y ≤ p := (Finset.mem_filter.mp hpH).2
  have hvsq : Squarefree v := hH.squarefree_of_dvd (Nat.mem_divisors.mp hvH).1
  apply Finset.mem_filter.mpr
  exact ⟨mem_repeatedPrimeProductPairs_iff.mpr
    ⟨hp, hYp, Nat.pos_of_ne_zero hvsq.ne_zero, hpv, hbound⟩, hvsq, hcount⟩

/-- Exact Hua step-8 identity: the unrestricted pair sum equals `s` copies
of the original divisor sum plus the explicit repeated-prime correction. -/
theorem sum_huaStepEightPairs_eq_recount_add_bad
    {A : Type*} [AddCommMonoid A] {H Y M s parity : ℕ} {R : ℕ → Prop}
    (hH : Squarefree H) (f : ℕ → A) :
    (∑ z ∈ huaStepEightPairs H Y M s parity R, f (z.1 * z.2)) =
      s • (∑ d ∈ huaStepEightDivisors H Y M s parity R, f d) +
        ∑ z ∈ huaStepEightBadPairs H Y M s parity R, f (z.1 * z.2) := by
  classical
  have hcount : ∀ d ∈ huaStepEightDivisors H Y M s parity R,
      (primeFactorsAtLeastCutoff Y d).card = s := by
    intro d hd
    exact (mem_huaStepEightDivisors_iff.mp hd).2.2.1
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (huaStepEightPairs H Y M s parity R) (fun z => ¬z.1 ∣ z.2)
    (fun z => f (z.1 * z.2))
  rw [huaStepEight_goodPairs_eq hH, sum_primeFactorQuotientPairs_eq_recount hcount f]
    at hsplit
  simpa only [not_not, huaStepEightBadPairs, Finset.smul_sum] using hsplit.symm

/-- The difference between the source pair sum and its exact `s`-fold
recount is bounded by the reciprocal-square repeated-prime majorant. -/
theorem norm_huaStepEightPairs_sub_recount_le
    {H Y M s parity : ℕ} {R : ℕ → Prop} (hH : Squarefree H) (hY : 0 < Y)
    (f : ℕ → ℂ)
    (hf : ∀ z ∈ huaStepEightBadPairs H Y M s parity R, ‖f (z.1 * z.2)‖ ≤ 1) :
    ‖(∑ z ∈ huaStepEightPairs H Y M s parity R, f (z.1 * z.2)) -
      s • (∑ d ∈ huaStepEightDivisors H Y M s parity R, f d)‖ ≤
        (2 : ℝ) * M / Y := by
  rw [sum_huaStepEightPairs_eq_recount_add_bad hH f, add_sub_cancel_left]
  have hsubset : huaStepEightBadPairs H Y M s parity R ⊆
      repeatedPrimeProductPairs Y M :=
    (huaStepEightBadPairs_subset hH).trans (Finset.filter_subset _ _)
  exact norm_sum_subset_repeatedPrimeProductPairs_le hY hsubset
    (fun z => f (z.1 * z.2)) hf

/-- Any natural cutoff at least the floor of Hua's real cutoff inherits the
logarithmic error estimate. In particular, this applies to its exact ceiling
cutoff, without equating a floor with the source's real inequality. -/
theorem eventually_norm_huaStepEightPairs_sub_recount_logCutoff_le
    {lambda₃ : ℝ} (h₃ : 0 < lambda₃) :
    ∀ᶠ P : ℕ in Filter.atTop,
      1 < P ∧ ∀ H Y M s parity : ℕ, ∀ R : ℕ → Prop,
        Squarefree H → Nat.floor (Real.rpow (Real.log P) lambda₃) ≤ Y →
        ∀ f : ℕ → ℂ,
          (∀ z ∈ huaStepEightBadPairs H Y M s parity R, ‖f (z.1 * z.2)‖ ≤ 1) →
          ‖(∑ z ∈ huaStepEightPairs H Y M s parity R, f (z.1 * z.2)) -
            s • (∑ d ∈ huaStepEightDivisors H Y M s parity R, f d)‖ ≤
              (4 : ℝ) * M / Real.rpow (Real.log P) lambda₃ := by
  classical
  filter_upwards
    [eventually_norm_sum_subset_repeatedPrimeProductPairs_logCutoff_le h₃]
    with P hP
  rcases hP with ⟨hP, hbound⟩
  refine ⟨hP, ?_⟩
  intro H Y M s parity R hH hY f hf
  have hsubset : huaStepEightBadPairs H Y M s parity R ⊆
      repeatedPrimeProductPairs (Nat.floor (Real.rpow (Real.log P) lambda₃)) M := by
    intro z hz
    rcases z with ⟨p, v⟩
    have hrep := (Finset.mem_filter.mp (huaStepEightBadPairs_subset hH hz)).1
    rcases mem_repeatedPrimeProductPairs_iff.mp hrep with
      ⟨hp, hYp, hvpos, hpv, hprod⟩
    exact mem_repeatedPrimeProductPairs_iff.mpr
      ⟨hp, hY.trans hYp, hvpos, hpv, hprod⟩
  rw [sum_huaStepEightPairs_eq_recount_add_bad hH f, add_sub_cancel_left]
  exact hbound M _ hsubset (fun z => f (z.1 * z.2)) hf

/-- Hua's fixed sieve product, whose prime factors are exactly the primes
not exceeding the square-root endpoint. -/
def huaStepEightSieveProduct (P : ℕ) : ℕ :=
  ∏ p ∈ CookMagyarHuaSieve.smallPrimesUpTo P, p

theorem squarefree_huaStepEightSieveProduct (P : ℕ) :
    Squarefree (huaStepEightSieveProduct P) := by
  apply CookMagyarHuaSieve.subsetProduct_squarefree
  intro p hp
  exact (Finset.mem_filter.mp hp).2

theorem primeFactors_huaStepEightSieveProduct (P : ℕ) :
    (huaStepEightSieveProduct P).primeFactors = CookMagyarHuaSieve.smallPrimesUpTo P := by
  apply Nat.primeFactors_prod
  intro p hp
  exact (Finset.mem_filter.mp hp).2

/-- The strict lower range and progression condition on the product in the
source's step 8. Its upper endpoint is supplied separately by `M=P/m`. -/
def huaStepEightSourceCondition (P m Q t : ℕ) (lambda₂ : ℝ) (d : ℕ) : Prop :=
  (P : ℝ) / Real.rpow (Real.log P) lambda₂ < (d : ℝ) ∧ Nat.ModEq Q (m * d) t

/-- The repeated-prime correction with Hua's actual sieve product, ceiling
prime cutoff, product range, progression, and parity. The bound has the
source scale `P/(m*(log P)^lambda₃)`, uniform in the integer source data. -/
theorem eventually_norm_huaSourceStepEight_sub_recount_le
    {lambda₂ lambda₃ : ℝ} (h₃ : 0 < lambda₃) :
    ∀ᶠ P : ℕ in Filter.atTop,
      1 < P ∧ ∀ m Q t s parity : ℕ, 0 < m → ∀ f : ℕ → ℂ,
        let H := huaStepEightSieveProduct P
        let Y := Nat.ceil (Real.rpow (Real.log P) lambda₃)
        let R := huaStepEightSourceCondition P m Q t lambda₂
        (∀ z ∈ huaStepEightBadPairs H Y (P / m) s parity R,
          ‖f (m * (z.1 * z.2))‖ ≤ 1) →
        ‖(∑ z ∈ huaStepEightPairs H Y (P / m) s parity R,
            f (m * (z.1 * z.2))) -
          s • (∑ d ∈ huaStepEightDivisors H Y (P / m) s parity R, f (m * d))‖ ≤
            (4 : ℝ) * P / ((m : ℝ) * Real.rpow (Real.log P) lambda₃) := by
  filter_upwards [eventually_norm_huaStepEightPairs_sub_recount_logCutoff_le h₃]
    with P hP
  rcases hP with ⟨hP, hbound⟩
  refine ⟨hP, ?_⟩
  intro m Q t s parity _hm f
  dsimp only
  intro hf
  have hbase := hbound (huaStepEightSieveProduct P)
    (Nat.ceil (Real.rpow (Real.log P) lambda₃)) (P / m) s parity
    (huaStepEightSourceCondition P m Q t lambda₂)
    (squarefree_huaStepEightSieveProduct P)
    (Nat.floor_le_ceil (Real.rpow (Real.log P) lambda₃)) (fun d => f (m * d)) hf
  have hden : 0 < Real.rpow (Real.log P) lambda₃ :=
    Real.rpow_pos_of_pos (Real.log_pos (by exact_mod_cast hP)) _
  calc
    _ ≤ (4 : ℝ) * (P / m : ℕ) / Real.rpow (Real.log P) lambda₃ := hbase
    _ ≤ (4 : ℝ) * ((P : ℝ) / m) / Real.rpow (Real.log P) lambda₃ := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left Nat.cast_div_le (by norm_num)) hden.le
    _ = (4 : ℝ) * P / ((m : ℝ) * Real.rpow (Real.log P) lambda₃) := by
      rw [mul_div_assoc, div_div]
      ring

end CookMagyarCircle
end SystolicGrowth

#print axioms SystolicGrowth.CookMagyarCircle.huaStepEight_goodPairs_eq
#print axioms SystolicGrowth.CookMagyarCircle.huaStepEightBadPairs_subset
#print axioms SystolicGrowth.CookMagyarCircle.sum_huaStepEightPairs_eq_recount_add_bad
#print axioms SystolicGrowth.CookMagyarCircle.norm_huaStepEightPairs_sub_recount_le
#print axioms SystolicGrowth.CookMagyarCircle.eventually_norm_huaStepEightPairs_sub_recount_logCutoff_le
#print axioms SystolicGrowth.CookMagyarCircle.squarefree_huaStepEightSieveProduct
#print axioms SystolicGrowth.CookMagyarCircle.primeFactors_huaStepEightSieveProduct
#print axioms SystolicGrowth.CookMagyarCircle.eventually_norm_huaSourceStepEight_sub_recount_le
