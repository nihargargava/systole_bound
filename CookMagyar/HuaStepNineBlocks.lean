module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.HuaStepEight

@[expose] public section

open scoped BigOperators

namespace SystolicGrowth
namespace CookMagyarCircle

/-! # Source-shaped outer-prime fibers for Hua's step 9

The step-eight pair sum is first regrouped by its selected large prime `u`.
This is an exact finite identity preserving the product cutoff, factor-count
condition, parity, and source predicate (including the progression). It is
only the reindexing needed to apply a later uniform estimate to each `u`;
it makes no cancellation or Type-II estimate.
-/

/-- The inner `v`-range for a fixed selected large prime `u`, with every
step-eight source restriction retained. -/
noncomputable def huaStepNineVFiber (H Y M s parity u : ℕ)
    (R : ℕ → Prop) : Finset ℕ := by
  classical
  exact H.divisors.filter fun v =>
    u * v ≤ M ∧ (primeFactorsAtLeastCutoff Y v).card + 1 = s ∧
      (v.primeFactors.card + 1) % 2 = parity ∧ R (u * v)

/-- The outer source variable is an admissible fixed multiplier in Hua's
Lemma 6.3: on the actual `m≤floor((log P)^lambda₂)` range it is positive
and satisfies `m≤(log P)^lambda₂`. -/
theorem huaStepNineOuterMultiplier_source_bound
    (P m : ℕ) (lambda₂ : ℝ) (hP : 1 < P)
    (hm : m ∈ Finset.Icc 1 (Nat.floor (Real.rpow (Real.log P) lambda₂))) :
    0 < m ∧ (m : ℝ) ≤ Real.rpow (Real.log P) lambda₂ := by
  rcases Finset.mem_Icc.mp hm with ⟨hmlo, hmhi⟩
  have hlog : 0 < Real.log (P : ℝ) := Real.log_pos (by exact_mod_cast hP)
  have hrpow : 0 ≤ Real.rpow (Real.log (P : ℝ)) lambda₂ :=
    (Real.rpow_pos_of_pos hlog lambda₂).le
  refine ⟨by omega, ?_⟩
  have hmcast : (m : ℝ) ≤ (Nat.floor (Real.rpow (Real.log (P : ℝ)) lambda₂) : ℝ) := by
    exact_mod_cast hmhi
  exact hmcast.trans (Nat.floor_le hrpow)

/-- The cubic differencing frequency factors into the variable gap and a
positive quadratic factor. This is the divisor-factorization input for the
exceptional reduced-denominator count in Hua's Lemma 6.3. -/
theorem nat_cube_sub_factorization {a b : ℕ} (hba : b ≤ a) :
    a ^ 3 - b ^ 3 = (a - b) * (a ^ 2 + a * b + b ^ 2) := by
  let d := a - b
  have hd : d + b = a := by
    dsimp [d]
    exact Nat.sub_add_cancel hba
  have hpoly : a ^ 3 = d * (a ^ 2 + a * b + b ^ 2) + b ^ 3 := by
    rw [← hd]
    ring
  calc
    a ^ 3 - b ^ 3 = (d * (a ^ 2 + a * b + b ^ 2) + b ^ 3) - b ^ 3 := by rw [hpoly]
    _ = d * (a ^ 2 + a * b + b ^ 2) := Nat.add_sub_cancel_right _ _
    _ = (a - b) * (a ^ 2 + a * b + b ^ 2) := by rfl

/-- The divisor count of the cubic leading-frequency product is bounded by
the product of the divisor counts of its three arithmetic factors. -/
theorem card_divisors_cubicDifference_frequency_le
    {l a b : ℕ} (hl : 0 < l) (hba : b < a) :
    ((l ^ 3 * (a ^ 3 - b ^ 3)).divisors.card : ℕ) ≤
      (l ^ 3).divisors.card * (a - b).divisors.card *
        (a ^ 2 + a * b + b ^ 2).divisors.card := by
  have hfactor :
      l ^ 3 * (a ^ 3 - b ^ 3) =
        (l ^ 3 * (a - b)) * (a ^ 2 + a * b + b ^ 2) := by
    rw [nat_cube_sub_factorization (Nat.le_of_lt hba)]
    ring
  rw [hfactor]
  have hl3 : 0 < l ^ 3 := by positivity
  have hgap : 0 < a - b := Nat.sub_pos_of_lt hba
  have ha : 0 < a := by omega
  have hquad : 0 < a ^ 2 + a * b + b ^ 2 := by positivity
  calc
    _ ≤ (l ^ 3 * (a - b)).divisors.card *
          (a ^ 2 + a * b + b ^ 2).divisors.card :=
      card_divisors_mul_le (mul_ne_zero hl3.ne' hgap.ne') hquad.ne'
    _ ≤ (l ^ 3).divisors.card * (a - b).divisors.card *
          (a ^ 2 + a * b + b ^ 2).divisors.card := by
      exact Nat.mul_le_mul_right _
        (card_divisors_mul_le hl3.ne' hgap.ne')

/-- The sieve cutoff makes every selected outer prime at least
`(log P)^lambda₃`, while retaining the source upper endpoint `sqrt P`. -/
theorem huaStepNineOuterPrime_source_bounds
    (P u : ℕ) (lambda₃ : ℝ)
    (hu : u ∈ primeFactorsAtLeastCutoff
      (Nat.ceil (Real.rpow (Real.log P) lambda₃))
      (huaStepEightSieveProduct P)) :
    Nat.Prime u ∧ Real.rpow (Real.log P) lambda₃ ≤ (u : ℝ) ∧
      u ≤ Nat.sqrt P := by
  rw [primeFactorsAtLeastCutoff, primeFactors_huaStepEightSieveProduct,
    CookMagyarHuaSieve.smallPrimesUpTo] at hu
  simp only [Finset.mem_filter, Finset.mem_Icc] at hu
  rcases hu with ⟨⟨⟨_, hupper⟩, hp⟩, hcutNat⟩
  have hceil :
      (Real.rpow (Real.log P) lambda₃ : ℝ) ≤
        (Nat.ceil (Real.rpow (Real.log P) lambda₃) : ℝ) :=
    Nat.le_ceil _
  have hcut :
      (Nat.ceil (Real.rpow (Real.log P) lambda₃) : ℝ) ≤ (u : ℝ) := by
    exact_mod_cast hcutNat
  exact ⟨hp, hceil.trans hcut, hupper⟩

/-- Hua's actual source fiber has exactly the interval required by Lemma 6.3:
after fixing its small multiplier `m` and dyadic variable `u`, the inner
variable `v` lies strictly above `P/(log P)^lambda₂/u` and at most
`(P/m)/u`. The progression and factor predicates remain part of membership;
this theorem extracts only the interval consequences. -/
theorem huaStepNineSourceVFiber_interval
    (P m Q t s parity : ℕ) (lambda₂ lambda₃ : ℝ) {u v : ℕ}
    (hu : 0 < u)
    (hv : v ∈ huaStepNineVFiber (huaStepEightSieveProduct P)
      (Nat.ceil (Real.rpow (Real.log P) lambda₃)) (P / m) s parity u
      (huaStepEightSourceCondition P m Q t lambda₂)) :
    ((P : ℝ) / Real.rpow (Real.log P) lambda₂) / (u : ℝ) < (v : ℝ) ∧
      (v : ℝ) ≤ ((P / m : ℕ) : ℝ) / (u : ℝ) := by
  classical
  simp only [huaStepNineVFiber, Finset.mem_filter] at hv
  rcases hv with ⟨_, ⟨hupper, _, _, hsource⟩⟩
  simp only [huaStepEightSourceCondition] at hsource
  have huR : 0 < (u : ℝ) := by exact_mod_cast hu
  have hsourceReal :
      (P : ℝ) / Real.rpow (Real.log P) lambda₂ < (u : ℝ) * (v : ℝ) := by
    simpa only [Nat.cast_mul] using hsource.1
  have hupperReal : (u : ℝ) * (v : ℝ) ≤ ((P / m : ℕ) : ℝ) := by
    exact_mod_cast hupper
  constructor
  · apply (div_lt_iff₀ huR).2
    calc
      (P : ℝ) / Real.rpow (Real.log P) lambda₂ < (u : ℝ) * (v : ℝ) :=
        hsourceReal
      _ = (v : ℝ) * (u : ℝ) := by ring
  · apply (le_div_iff₀ huR).2
    calc
      (v : ℝ) * (u : ℝ) = (u : ℝ) * (v : ℝ) := by ring
      _ ≤ ((P / m : ℕ) : ℝ) := hupperReal

/-- The fixed outer multiplier and the selected prime retain the source
progression on the inner variable. -/
theorem huaStepNineSourceVFiber_progression
    (P m Q t s parity : ℕ) (lambda₂ lambda₃ : ℝ) {u v : ℕ}
    (hv : v ∈ huaStepNineVFiber (huaStepEightSieveProduct P)
      (Nat.ceil (Real.rpow (Real.log P) lambda₃)) (P / m) s parity u
      (huaStepEightSourceCondition P m Q t lambda₂)) :
    Nat.ModEq Q (m * (u * v)) t := by
  classical
  simp only [huaStepNineVFiber, Finset.mem_filter] at hv
  rcases hv with ⟨_, ⟨_, _, _, hsource⟩⟩
  simpa only [huaStepEightSourceCondition] using hsource.2

/-- The sieve-product encoding of the chosen prime is exactly Hua's
`Y≤u≤sqrt(P)` prime range; both endpoints are exposed for the dyadic split. -/
theorem mem_huaStepNineOuterPrime_iff
    (P Y u : ℕ) :
    u ∈ primeFactorsAtLeastCutoff Y (huaStepEightSieveProduct P) ↔
      Nat.Prime u ∧ Y ≤ u ∧ u ≤ Nat.sqrt P := by
  rw [primeFactorsAtLeastCutoff, primeFactors_huaStepEightSieveProduct]
  simp only [Finset.mem_filter, CookMagyarHuaSieve.smallPrimesUpTo,
    Finset.mem_Icc, Finset.mem_filter]
  constructor
  · rintro ⟨⟨⟨h₂, hupper⟩, hp⟩, hY⟩
    exact ⟨hp, hY, hupper⟩
  · rintro ⟨hp, hY, hupper⟩
    exact ⟨⟨⟨hp.two_le, hupper⟩, hp⟩, hY⟩

/-- The dyadic block indexed by `k` consists of integers with
`log₂(u-1)=k`; equivalently these lie in `2^k < u ≤ 2^(k+1)` when `u≥2`.
Using this index gives a disjoint partition even at shared endpoints. -/
def huaStepNineDyadicBlock (S : Finset ℕ) (k : ℕ) : Finset ℕ :=
  S.filter fun u => Nat.log 2 (u - 1) = k

/-- Every member of a log-indexed block lies in the corresponding half-open
dyadic interval. -/
theorem mem_huaStepNineDyadicBlock_imp
    {S : Finset ℕ} {u k : ℕ}
    (hu : u ∈ huaStepNineDyadicBlock S k) (hlo : 2 ≤ u) :
    2 ^ k < u ∧ u ≤ 2 ^ (k + 1) := by
  have hlog := (Finset.mem_filter.mp hu).2
  have hpowlo := Nat.pow_log_le_self 2 (by omega : u - 1 ≠ 0)
  rw [hlog] at hpowlo
  have hpowhi := Nat.lt_pow_succ_log_self (by omega : 1 < 2) (u - 1)
  rw [hlog] at hpowhi
  constructor <;> omega

/-- Exact finite decomposition of a set of integers bounded by `R` into
logarithmic blocks. -/
theorem sum_eq_sum_huaStepNineDyadicBlocks
    {S : Finset ℕ} {R : ℕ} (f : ℕ → ℂ)
    (hhi : ∀ u ∈ S, u ≤ R) :
    (∑ u ∈ S, f u) =
      ∑ k ∈ Finset.Icc 0 (Nat.log 2 R),
        ∑ u ∈ huaStepNineDyadicBlock S k, f u := by
  classical
  have hmaps : ∀ u ∈ S, Nat.log 2 (u - 1) ∈ Finset.Icc 0 (Nat.log 2 R) := by
    intro u hu
    refine Finset.mem_Icc.mpr ⟨Nat.zero_le _, ?_⟩
    exact Nat.log_mono_right (le_trans (Nat.sub_le u 1) (hhi u hu))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps f]
  apply Finset.sum_congr rfl
  intro k hk
  rfl

/-- Hua's selected-prime range is partitioned into exact dyadic blocks
`2^k < u ≤ 2^(k+1)`, up to `Nat.sqrt P`. -/
theorem sum_huaStepNineOuterPrimes_eq_sum_dyadicBlocks
    (P Y : ℕ) (f : ℕ → ℂ) :
    (∑ u ∈ primeFactorsAtLeastCutoff Y (huaStepEightSieveProduct P), f u) =
      ∑ k ∈ Finset.Icc 0 (Nat.log 2 (Nat.sqrt P)),
        ∑ u ∈ huaStepNineDyadicBlock
          (primeFactorsAtLeastCutoff Y (huaStepEightSieveProduct P)) k, f u := by
  apply sum_eq_sum_huaStepNineDyadicBlocks f
  intro u hu
  have hmem := mem_huaStepNineOuterPrime_iff P Y u |>.mp hu
  exact hmem.2.2

/-- Regroup the complete step-eight pair aggregate by its chosen outer prime.
The inner sum is exactly Hua's source `v`-fiber for that `u`. -/
theorem sum_huaStepEightPairs_eq_sum_stepNineVFibers
    (H Y M s parity : ℕ) (R : ℕ → Prop) (f : ℕ → ℂ) :
    (∑ pair ∈ huaStepEightPairs H Y M s parity R, f (pair.1 * pair.2)) =
      ∑ u ∈ primeFactorsAtLeastCutoff Y H,
        ∑ v ∈ huaStepNineVFiber H Y M s parity u R, f (u * v) := by
  classical
  simp only [huaStepEightPairs, Finset.sum_filter, Finset.sum_product]
  simp [huaStepNineVFiber, Finset.sum_filter, and_assoc, and_left_comm, and_comm]

/-- The source-instantiated version makes explicit that the `v`-fiber keeps
the exact progression `m*u*v ≡ t (mod Q)` and lower endpoint from step 8. -/
theorem sum_huaStepEightSourcePairs_eq_sum_stepNineSourceVFibers
    (P m Q t s parity : ℕ) (lambda₂ lambda₃ : ℝ)
    (f : ℕ → ℂ) :
    (∑ pair ∈ huaStepEightPairs (huaStepEightSieveProduct P)
        (Nat.ceil (Real.rpow (Real.log P) lambda₃)) (P / m) s parity
        (huaStepEightSourceCondition P m Q t lambda₂),
        f (m * (pair.1 * pair.2))) =
      ∑ u ∈ primeFactorsAtLeastCutoff
          (Nat.ceil (Real.rpow (Real.log P) lambda₃))
          (huaStepEightSieveProduct P),
        ∑ v ∈ huaStepNineVFiber (huaStepEightSieveProduct P)
          (Nat.ceil (Real.rpow (Real.log P) lambda₃)) (P / m) s parity u
          (huaStepEightSourceCondition P m Q t lambda₂),
          f (m * (u * v)) := by
  simpa only [← Nat.mul_assoc] using
    (sum_huaStepEightPairs_eq_sum_stepNineVFibers
      (huaStepEightSieveProduct P) (Nat.ceil (Real.rpow (Real.log P) lambda₃))
      (P / m) s parity (huaStepEightSourceCondition P m Q t lambda₂)
      (fun x => f (m * x)))

/-- Complete exact step-9 organization: first group by the chosen prime,
then by its disjoint dyadic block, keeping the source `v`-sum unchanged. -/
theorem sum_huaStepEightSourcePairs_eq_sum_stepNineDyadicFibers
    (P m Q t s parity : ℕ) (lambda₂ lambda₃ : ℝ) (f : ℕ → ℂ) :
    (∑ pair ∈ huaStepEightPairs (huaStepEightSieveProduct P)
        (Nat.ceil (Real.rpow (Real.log P) lambda₃)) (P / m) s parity
        (huaStepEightSourceCondition P m Q t lambda₂),
        f (m * (pair.1 * pair.2))) =
      ∑ k ∈ Finset.Icc 0 (Nat.log 2 (Nat.sqrt P)),
        ∑ u ∈ huaStepNineDyadicBlock
            (primeFactorsAtLeastCutoff
              (Nat.ceil (Real.rpow (Real.log P) lambda₃))
              (huaStepEightSieveProduct P)) k,
          ∑ v ∈ huaStepNineVFiber (huaStepEightSieveProduct P)
            (Nat.ceil (Real.rpow (Real.log P) lambda₃)) (P / m) s parity u
            (huaStepEightSourceCondition P m Q t lambda₂),
            f (m * (u * v)) := by
  calc
    _ = ∑ u ∈ primeFactorsAtLeastCutoff
          (Nat.ceil (Real.rpow (Real.log P) lambda₃))
          (huaStepEightSieveProduct P),
        ∑ v ∈ huaStepNineVFiber (huaStepEightSieveProduct P)
          (Nat.ceil (Real.rpow (Real.log P) lambda₃)) (P / m) s parity u
          (huaStepEightSourceCondition P m Q t lambda₂),
          f (m * (u * v)) :=
      sum_huaStepEightSourcePairs_eq_sum_stepNineSourceVFibers
        P m Q t s parity lambda₂ lambda₃ f
    _ = _ := sum_huaStepNineOuterPrimes_eq_sum_dyadicBlocks P
      (Nat.ceil (Real.rpow (Real.log P) lambda₃))
      (fun u => ∑ v ∈ huaStepNineVFiber (huaStepEightSieveProduct P)
        (Nat.ceil (Real.rpow (Real.log P) lambda₃)) (P / m) s parity u
        (huaStepEightSourceCondition P m Q t lambda₂), f (m * (u * v)))

end CookMagyarCircle
end SystolicGrowth

#print axioms SystolicGrowth.CookMagyarCircle.sum_huaStepEightPairs_eq_sum_stepNineVFibers
#print axioms SystolicGrowth.CookMagyarCircle.mem_huaStepNineOuterPrime_iff
#print axioms SystolicGrowth.CookMagyarCircle.sum_eq_sum_huaStepNineDyadicBlocks
#print axioms SystolicGrowth.CookMagyarCircle.sum_huaStepNineOuterPrimes_eq_sum_dyadicBlocks
#print axioms SystolicGrowth.CookMagyarCircle.sum_huaStepEightSourcePairs_eq_sum_stepNineDyadicFibers
#print axioms SystolicGrowth.CookMagyarCircle.huaStepNineSourceVFiber_interval
#print axioms SystolicGrowth.CookMagyarCircle.huaStepNineSourceVFiber_progression
#print axioms SystolicGrowth.CookMagyarCircle.huaStepNineOuterMultiplier_source_bound
#print axioms SystolicGrowth.CookMagyarCircle.huaStepNineOuterPrime_source_bounds
