module

/-
Copyright (c) 2026 Gershon Bialer.
Released under Apache 2.0 license.
-/
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius

@[expose] public section

open scoped BigOperators

namespace SystolicGrowth
namespace CookMagyarHuaSieve

/-- Finite inclusion-exclusion over a chosen set of candidate prime divisors.
The signed subset sum is one exactly when none of the selected integers
divides `n`, and cancels to zero when at least one does. For a finite set of
primes this is the combinatorial core of Hua's small-prime-divisor sieve. -/
theorem inclusionExclusion_dvd_indicator (S : Finset ℕ) (n : ℕ) :
    (∑ T ∈ S.powerset,
      if (∀ p ∈ T, p ∣ n) then (-1 : ℤ) ^ T.card else 0) =
      if (S.filter fun p => p ∣ n) = ∅ then 1 else 0 := by
  classical
  let A : Finset ℕ := S.filter fun p => p ∣ n
  have hA : A ⊆ S := Finset.filter_subset _ _
  have hpred (T : Finset ℕ) (hT : T ∈ S.powerset) :
      (∀ p ∈ T, p ∣ n) ↔ T ⊆ A := by
    simp only [Finset.mem_powerset] at hT
    constructor
    · intro h p hp
      exact Finset.mem_filter.mpr ⟨hT hp, h p hp⟩
    · intro h p hp
      exact (Finset.mem_filter.mp (h hp)).2
  have hsum :
      (∑ T ∈ S.powerset,
        if (∀ p ∈ T, p ∣ n) then (-1 : ℤ) ^ T.card else 0) =
      ∑ T ∈ S.powerset, if T ⊆ A then (-1 : ℤ) ^ T.card else 0 := by
    apply Finset.sum_congr rfl
    intro T hT
    by_cases h : ∀ p ∈ T, p ∣ n
    · have h' : T ⊆ A := (hpred T hT).mp h
      simp only [if_pos h, if_pos h']
    · have h' : ¬T ⊆ A := fun hs => h ((hpred T hT).mpr hs)
      simp only [if_neg h, if_neg h']
  have hfilter : S.powerset.filter (fun T => T ⊆ A) = A.powerset := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨fun ⟨_, hTA⟩ => hTA, fun hTA => ⟨hTA.trans hA, hTA⟩⟩
  calc
    (∑ T ∈ S.powerset,
        if (∀ p ∈ T, p ∣ n) then (-1 : ℤ) ^ T.card else 0) =
      ∑ T ∈ S.powerset, if T ⊆ A then (-1 : ℤ) ^ T.card else 0 := hsum
    _ = ∑ T ∈ S.powerset.filter (fun T => T ⊆ A), (-1 : ℤ) ^ T.card := by
      rw [← Finset.sum_filter]
    _ = ∑ T ∈ A.powerset, (-1 : ℤ) ^ T.card := by rw [hfilter]
    _ = if A = ∅ then 1 else 0 := Finset.sum_powerset_neg_one_pow_card
    _ = if (S.filter fun p => p ∣ n) = ∅ then 1 else 0 := by rfl

/-- The finite set of primes not exceeding `sqrt n`. -/
def smallPrimeDivisors (n : ℕ) : Finset ℕ :=
  (Finset.Icc 2 (Nat.sqrt n)).filter fun p => Nat.Prime p

/-- An integer at least two is prime precisely when none of its prime
divisors lies in the complete candidate range up to its square root. -/
theorem smallPrimeDivisors_filter_dvd_eq_empty_iff_prime
    {n : ℕ} (hn : 2 ≤ n) :
    (smallPrimeDivisors n).filter (fun p => p ∣ n) = ∅ ↔ n.Prime := by
  constructor
  · intro hempty
    apply Nat.prime_def_le_sqrt.mpr
    refine ⟨hn, ?_⟩
    intro m hm hmsqrt hmn
    obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
    have hple : p ≤ m := Nat.le_of_dvd (by omega : 0 < m) hpm
    have hpCandidates : p ∈ smallPrimeDivisors n := by
      change p ∈ (Finset.Icc 2 (Nat.sqrt n)).filter (fun q => Nat.Prime q)
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_Icc.mpr ⟨hp.two_le, hple.trans hmsqrt⟩, hp⟩
    have hpActive : p ∈ (smallPrimeDivisors n).filter (fun q => q ∣ n) :=
      Finset.mem_filter.mpr ⟨hpCandidates, hpm.trans hmn⟩
    rw [hempty] at hpActive
    simp at hpActive
  · intro hnprime
    apply Finset.filter_eq_empty_iff.mpr
    intro p hpS
    simp only [smallPrimeDivisors, Finset.mem_filter, Finset.mem_Icc] at hpS
    exact (Nat.prime_def_le_sqrt.mp hnprime).2 p hpS.1.1 hpS.1.2

/-- Pointwise inclusion-exclusion over prime divisors up to `sqrt(n)` gives
the prime indicator for integers at least two. The fixed-parameter version
used in a prime sum appears below. -/
theorem smallPrimeInclusionExclusion_eq_primeIndicator
    {n : ℕ} (hn : 2 ≤ n) :
    (∑ T ∈ (smallPrimeDivisors n).powerset,
      if (∀ p ∈ T, p ∣ n) then (-1 : ℤ) ^ T.card else 0) =
      if n.Prime then 1 else 0 := by
  rw [inclusionExclusion_dvd_indicator]
  by_cases hp : n.Prime
  · have he := (smallPrimeDivisors_filter_dvd_eq_empty_iff_prime hn).mpr hp
    simp [he, hp]
  · have he : (smallPrimeDivisors n).filter (fun p => p ∣ n) ≠ ∅ := by
      intro h
      exact hp ((smallPrimeDivisors_filter_dvd_eq_empty_iff_prime hn).mp h)
    simp [he, hp]

/-- A fixed candidate set for a whole interval: all primes up to `sqrt(P)`. -/
def smallPrimesUpTo (P : ℕ) : Finset ℕ :=
  (Finset.Icc 2 (Nat.sqrt P)).filter fun p => Nat.Prime p

/-- On a finite set of distinct primes, the Möbius value of their product is
the inclusion-exclusion sign. This is the arithmetic-function bridge needed
to rewrite the subset sieve as a divisor sum. -/
theorem moebius_subsetProduct_eq_sign (T : Finset ℕ)
    (hT : ∀ p ∈ T, Nat.Prime p) :
    ArithmeticFunction.moebius (∏ p ∈ T, p) = (-1 : ℤ) ^ T.card := by
  rw [ArithmeticFunction.IsMultiplicative.map_prod_of_prime
    ArithmeticFunction.isMultiplicative_moebius T hT]
  have hprod : (∏ p ∈ T, ArithmeticFunction.moebius p) =
      ∏ p ∈ T, (-1 : ℤ) := by
    apply Finset.prod_congr rfl
    intro p hp
    exact ArithmeticFunction.moebius_apply_prime (hT p hp)
  rw [hprod]
  rw [Finset.prod_const]

/-- Products of distinct primes retain the subset they came from. This is the
injectivity half of the subset/divisor correspondence for the sieve product. -/
theorem subsetProduct_injective_of_prime_subset (S T U : Finset ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p) (hT : T ⊆ S) (hU : U ⊆ S)
    (hprod : (∏ p ∈ T, p) = ∏ p ∈ U, p) : T = U := by
  have hTprime : ∀ p ∈ T, Nat.Prime p := fun p hp => hS p (hT hp)
  have hUprime : ∀ p ∈ U, Nat.Prime p := fun p hp => hS p (hU hp)
  have hfac := congrArg Nat.primeFactors hprod
  rw [Nat.primeFactors_prod hTprime, Nat.primeFactors_prod hUprime] at hfac
  exact hfac

/-- The product attached to a finite set of distinct primes is squarefree. -/
theorem subsetProduct_squarefree (T : Finset ℕ)
    (hT : ∀ p ∈ T, Nat.Prime p) : Squarefree (∏ p ∈ T, p) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
  · intro p hp q hq hpq
    simp only [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (hT p hp) (hT q hq)).mpr hpq
  · intro p hp
    exact (hT p hp).squarefree

/-- Summing Möbius over the divisors of a product of distinct primes gives
the same zero-or-one value as inclusion-exclusion: it is one only for the
empty prime set. -/
theorem moebius_divisor_sum_subsetProduct_eq_empty_indicator (T : Finset ℕ)
    (hT : ∀ p ∈ T, Nat.Prime p) :
    (∑ d ∈ (∏ p ∈ T, p).divisors, ArithmeticFunction.moebius d) =
      if T = ∅ then 1 else 0 := by
  rw [← ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_add_of_squarefree
    ArithmeticFunction.isMultiplicative_moebius (subsetProduct_squarefree T hT)]
  rw [Nat.primeFactors_prod hT]
  by_cases hempty : T = ∅
  · simp [hempty]
  · obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hz : 1 + ArithmeticFunction.moebius p = 0 := by
      rw [ArithmeticFunction.moebius_apply_prime (hT p hp)]
      ring
    rw [Finset.prod_eq_zero hp hz]
    simp [hempty]

/-- The sieve inclusion-exclusion sum is exactly the Möbius divisor sum for
the product of those candidate primes which divide `n`. This is the finite
arithmetic-function form used before replacing the active product by a fixed
cutoff product with a divisibility condition. -/
theorem inclusionExclusion_eq_moebius_activeDivisorSum (S : Finset ℕ) (n : ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p) :
    (∑ T ∈ S.powerset,
      if (∀ p ∈ T, p ∣ n) then (-1 : ℤ) ^ T.card else 0) =
      ∑ d ∈ (∏ p ∈ S.filter (fun p => p ∣ n), p).divisors,
        ArithmeticFunction.moebius d := by
  let A := S.filter (fun p => p ∣ n)
  have hA : ∀ p ∈ A, Nat.Prime p := fun p hp => hS p (Finset.mem_filter.mp hp).1
  rw [inclusionExclusion_dvd_indicator, moebius_divisor_sum_subsetProduct_eq_empty_indicator
    A hA]

/-- Divisors of the active-prime product are exactly the divisors of the
fixed prime product which also divide `n`. Since the fixed product is
squarefree, any such divisor is the product of a subset of primes that all
divide `n`. -/
theorem activeDivisors_eq_fixedProduct_divisors_dvd (S : Finset ℕ) (n : ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p) (hn : n ≠ 0) :
    (∏ p ∈ S.filter (fun p => p ∣ n), p).divisors =
      (∏ p ∈ S, p).divisors.filter (fun d => d ∣ n) := by
  classical
  let A := S.filter (fun p => p ∣ n)
  let H := ∏ p ∈ S, p
  have hH0 : H ≠ 0 := by
    dsimp [H]
    exact Finset.prod_ne_zero_iff.mpr fun p hp => (hS p hp).ne_zero
  have hA0 : (∏ p ∈ A, p) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun p hp =>
      (hS p (Finset.mem_filter.mp hp).1).ne_zero
  have hHsq : Squarefree H := by
    dsimp [H]
    exact subsetProduct_squarefree S hS
  have hA_dvd_H : (∏ p ∈ A, p) ∣ H := by
    dsimp [A, H]
    exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
  have hA_subset_primeFactors : A ⊆ n.primeFactors := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpS, hpn⟩
    exact (Nat.mem_primeFactors_of_ne_zero hn).mpr ⟨hS p hpS, hpn⟩
  have hA_dvd_n : (∏ p ∈ A, p) ∣ n := by
    exact dvd_trans (Finset.prod_dvd_prod_of_subset _ _ _ hA_subset_primeFactors)
      (Nat.prod_primeFactors_dvd n)
  have hH_factors : H.primeFactors = S := by
    dsimp [H]
    exact Nat.primeFactors_prod hS
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨hdA, _⟩
    exact ⟨⟨dvd_trans hdA hA_dvd_H, hH0⟩, dvd_trans hdA hA_dvd_n⟩
  · rintro ⟨⟨hdH, _⟩, hdn⟩
    have hdSq : Squarefree d := hHsq.squarefree_of_dvd hdH
    have hfacH : d.primeFactors ⊆ H.primeFactors := Nat.primeFactors_mono hdH hH0
    have hfacN : d.primeFactors ⊆ n.primeFactors := Nat.primeFactors_mono hdn hn
    have hfacA : d.primeFactors ⊆ A := by
      intro p hp
      have hpS : p ∈ S := by simpa only [hH_factors] using hfacH hp
      have hpN : p ∈ n.primeFactors := hfacN hp
      have hpn : p ∣ n := (Nat.mem_primeFactors_of_ne_zero hn).mp hpN |>.2
      exact Finset.mem_filter.mpr ⟨hpS, hpn⟩
    have hprod : (∏ p ∈ d.primeFactors, p) ∣ ∏ p ∈ A, p :=
      Finset.prod_dvd_prod_of_subset _ _ _ hfacA
    rw [Nat.prod_primeFactors_of_squarefree hdSq] at hprod
    exact ⟨hprod, hA0⟩

/-- The finite sieve is the fixed-cutoff Möbius divisor sum with the
divisibility condition `d ∣ n`. This is the arithmetic identity needed to
sum the sieve uniformly over the large interval. -/
theorem inclusionExclusion_eq_moebius_fixedDivisorSum (S : Finset ℕ) (n : ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p) (hn : n ≠ 0) :
    (∑ T ∈ S.powerset,
      if (∀ p ∈ T, p ∣ n) then (-1 : ℤ) ^ T.card else 0) =
      ∑ d ∈ (∏ p ∈ S, p).divisors.filter (fun d => d ∣ n),
        ArithmeticFunction.moebius d := by
  rw [inclusionExclusion_eq_moebius_activeDivisorSum S n hS,
    activeDivisors_eq_fixedProduct_divisors_dvd S n hS hn]

/-- Above `sqrt(P)`, the fixed sieve by primes up to `sqrt(P)` detects
primality for every `n≤P`. This is the uniform-parameter version needed to
sum the sieve identity over an interval; unlike `smallPrimeDivisors`, its
candidate set does not depend on `n`. -/
theorem smallPrimesUpTo_filter_dvd_eq_empty_iff_prime
    {n P : ℕ} (hn2 : 2 ≤ n) (hnP : n ≤ P) (hlarge : Nat.sqrt P < n) :
    (smallPrimesUpTo P).filter (fun p => p ∣ n) = ∅ ↔ n.Prime := by
  constructor
  · intro hempty
    by_contra hnprime
    have hbad :
        ¬ ∀ m, 2 ≤ m → m ≤ Nat.sqrt n → ¬m ∣ n := by
      intro hall
      exact hnprime (Nat.prime_def_le_sqrt.mpr ⟨hn2, hall⟩)
    push Not at hbad
    obtain ⟨m, hm2, hmsqrt, hmn⟩ := hbad
    obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
    have hple : p ≤ m := Nat.le_of_dvd (by omega : 0 < m) hpm
    have hpsqrt : p ≤ Nat.sqrt P :=
      hple.trans (hmsqrt.trans (Nat.sqrt_le_sqrt hnP))
    have hpCandidates : p ∈ smallPrimesUpTo P := by
      change p ∈ (Finset.Icc 2 (Nat.sqrt P)).filter (fun q => Nat.Prime q)
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_Icc.mpr ⟨hp.two_le, hpsqrt⟩, hp⟩
    have hpActive : p ∈ (smallPrimesUpTo P).filter (fun q => q ∣ n) :=
      Finset.mem_filter.mpr ⟨hpCandidates, hpm.trans hmn⟩
    rw [hempty] at hpActive
    simp at hpActive
  · intro hnprime
    apply Finset.filter_eq_empty_iff.mpr
    intro p hpS
    simp only [smallPrimesUpTo, Finset.mem_filter, Finset.mem_Icc] at hpS
    have hp_lt : p < n := lt_of_le_of_lt hpS.1.2 hlarge
    intro hpdvd
    have hp_eq : p = n :=
      (Nat.prime_dvd_prime_iff_eq hpS.2 hnprime).mp hpdvd
    omega

/-- Uniform small-prime inclusion-exclusion is the prime indicator on the
large part of `[1,P]`. The omitted small primes satisfy `n≤sqrt(P)` and can
be accounted for separately in Hua's `O(sqrt(P))` remainder. -/
theorem smallPrimesUpTo_inclusionExclusion_eq_primeIndicator
    {n P : ℕ} (hn2 : 2 ≤ n) (hnP : n ≤ P) (hlarge : Nat.sqrt P < n) :
    (∑ T ∈ (smallPrimesUpTo P).powerset,
      if (∀ p ∈ T, p ∣ n) then (-1 : ℤ) ^ T.card else 0) =
      if n.Prime then 1 else 0 := by
  rw [inclusionExclusion_dvd_indicator]
  by_cases hp : n.Prime
  · have he :=
      (smallPrimesUpTo_filter_dvd_eq_empty_iff_prime hn2 hnP hlarge).mpr hp
    simp [he, hp]
  · have he : (smallPrimesUpTo P).filter (fun p => p ∣ n) ≠ ∅ := by
      intro h
      exact hp
        ((smallPrimesUpTo_filter_dvd_eq_empty_iff_prime hn2 hnP hlarge).mp h)
    simp [he, hp]

/-- On the large part of `[1,P]`, the prime indicator is the source-style
Möbius sum over divisors of the one fixed product of small primes. -/
theorem smallPrimesUpTo_moebius_sum_eq_primeIndicator
    {n P : ℕ} (hn2 : 2 ≤ n) (hnP : n ≤ P) (hlarge : Nat.sqrt P < n) :
    (∑ d ∈ (∏ p ∈ smallPrimesUpTo P, p).divisors.filter (fun d => d ∣ n),
      ArithmeticFunction.moebius d) = if n.Prime then 1 else 0 := by
  have hS : ∀ p ∈ smallPrimesUpTo P, Nat.Prime p := by
    intro p hp
    change p ∈ (Finset.Icc 2 (Nat.sqrt P)).filter (fun q => Nat.Prime q) at hp
    exact (Finset.mem_filter.mp hp).2
  rw [← inclusionExclusion_eq_moebius_fixedDivisorSum
    (smallPrimesUpTo P) n hS (by omega)]
  exact smallPrimesUpTo_inclusionExclusion_eq_primeIndicator hn2 hnP hlarge

/-- Summing the fixed-cutoff sieve identity over the large interval turns the
prime count into Möbius-weighted counts of multiples of each divisor. -/
theorem sum_smallPrimesUpTo_primeIndicator_eq_moebius_multipleCount (P : ℕ) :
    (∑ n ∈ Finset.Ioc (Nat.sqrt P) P, if n.Prime then (1 : ℤ) else 0) =
      ∑ d ∈ (∏ p ∈ smallPrimesUpTo P, p).divisors,
        (↑((Finset.Ioc (Nat.sqrt P) P).filter (fun n => d ∣ n)).card : ℤ) *
          ArithmeticFunction.moebius d := by
  classical
  let I := Finset.Ioc (Nat.sqrt P) P
  let H := ∏ p ∈ smallPrimesUpTo P, p
  calc
    (∑ n ∈ I, if n.Prime then (1 : ℤ) else 0) =
        ∑ n ∈ I, ∑ d ∈ H.divisors,
          if d ∣ n then ArithmeticFunction.moebius d else 0 := by
      apply Finset.sum_congr rfl
      intro n hnI
      have hnI' : Nat.sqrt P < n ∧ n ≤ P := Finset.mem_Ioc.mp hnI
      have hn_pos : 1 ≤ n := by omega
      have hP_pos : 1 ≤ P := le_trans hn_pos hnI'.2
      have hroot : 1 ≤ Nat.sqrt P := by
        simpa using Nat.sqrt_le_sqrt hP_pos
      have hn2 : 2 ≤ n := by omega
      have hpoint := smallPrimesUpTo_moebius_sum_eq_primeIndicator
        hn2 hnI'.2 hnI'.1
      rw [Finset.sum_filter] at hpoint
      exact hpoint.symm
    _ = ∑ d ∈ H.divisors, ∑ n ∈ I,
          if d ∣ n then ArithmeticFunction.moebius d else 0 := Finset.sum_comm
    _ = ∑ d ∈ H.divisors,
          (↑(I.filter (fun n => d ∣ n)).card : ℤ) *
            ArithmeticFunction.moebius d := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Finset.sum_filter]
      simp [Finset.sum_const]

/-- The number of multiples of `d` in `(a,b]` is the difference of the two
quotients. This evaluates the counting factor in the preceding identity. -/
theorem card_filter_dvd_Ioc_eq_div_sub_div (a b d : ℕ) (hab : a ≤ b) :
    ((Finset.Ioc a b).filter (fun n => d ∣ n)).card = b / d - a / d := by
  have hIcc (N : ℕ) : ((Finset.Icc 1 N).filter (fun n => d ∣ n)).card = N / d := by
    calc
      ((Finset.Icc 1 N).filter (fun n => d ∣ n)).card =
          ((Finset.range N.succ).filter (fun n => n ≠ 0 ∧ d ∣ n)).card := by
        congr 1
        ext n
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
        omega
      _ = N / d := Nat.card_multiples' N d
  have hIoc : Finset.Ioc a b = Finset.Icc 1 b \ Finset.Icc 1 a := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_sdiff, Finset.mem_Icc]
    omega
  have hsub : (Finset.Icc 1 a).filter (fun n => d ∣ n) ⊆
      (Finset.Icc 1 b).filter (fun n => d ∣ n) :=
    Finset.filter_subset_filter (p := fun n => d ∣ n)
      (Finset.Icc_subset_Icc_right hab)
  have hfilter :
      (Finset.Icc 1 b \ Finset.Icc 1 a).filter (fun n => d ∣ n) =
        (Finset.Icc 1 b).filter (fun n => d ∣ n) \
          (Finset.Icc 1 a).filter (fun n => d ∣ n) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    by_cases hdn : d ∣ n <;> simp [hdn, Finset.mem_Icc]
  calc
    ((Finset.Ioc a b).filter (fun n => d ∣ n)).card =
        ((Finset.Icc 1 b).filter (fun n => d ∣ n) \
          (Finset.Icc 1 a).filter (fun n => d ∣ n)).card := by
      rw [hIoc, hfilter]
    _ = ((Finset.Icc 1 b).filter (fun n => d ∣ n)).card -
        ((Finset.Icc 1 a).filter (fun n => d ∣ n)).card :=
      Finset.card_sdiff_of_subset hsub
    _ = b / d - a / d := by rw [hIcc b, hIcc a]

/-- Exact finite prime-counting identity on the large interval, with each
multiple count evaluated as a quotient difference. -/
theorem sum_smallPrimesUpTo_primeIndicator_eq_moebius_quotientSum (P : ℕ) :
    (∑ n ∈ Finset.Ioc (Nat.sqrt P) P, if n.Prime then (1 : ℤ) else 0) =
      ∑ d ∈ (∏ p ∈ smallPrimesUpTo P, p).divisors,
        (↑(P / d - Nat.sqrt P / d) : ℤ) * ArithmeticFunction.moebius d := by
  rw [sum_smallPrimesUpTo_primeIndicator_eq_moebius_multipleCount]
  apply Finset.sum_congr rfl
  intro d hd
  congr 2
  exact card_filter_dvd_Ioc_eq_div_sub_div (Nat.sqrt P) P d (Nat.sqrt_le_self P)

/-- The primes below the square-root cutoff contribute at most the length of
that initial interval. This is Hua's elementary `O(sqrt(P))` remainder. -/
theorem sum_primeIndicator_smallIcc_le_sqrt (P : ℕ) :
    (∑ n ∈ Finset.Icc 1 (Nat.sqrt P), if n.Prime then (1 : ℤ) else 0) ≤
      (Nat.sqrt P : ℤ) := by
  calc
    (∑ n ∈ Finset.Icc 1 (Nat.sqrt P), if n.Prime then (1 : ℤ) else 0) ≤
        ∑ _n ∈ Finset.Icc 1 (Nat.sqrt P), (1 : ℤ) := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hp : n.Prime <;> simp [hp]
    _ = (Finset.Icc 1 (Nat.sqrt P)).card := by simp
    _ = (Nat.sqrt P : ℤ) := by simp

/-- Hua's first decomposition step: the full prime count is the small-prime
remainder plus the fixed-cutoff Möbius quotient sum over the large interval. -/
theorem sum_primeIndicator_Icc_eq_smallRemainder_add_quotientSum (P : ℕ) :
    (∑ n ∈ Finset.Icc 1 P, if n.Prime then (1 : ℤ) else 0) =
      (∑ n ∈ Finset.Icc 1 (Nat.sqrt P), if n.Prime then (1 : ℤ) else 0) +
        ∑ d ∈ (∏ p ∈ smallPrimesUpTo P, p).divisors,
          (↑(P / d - Nat.sqrt P / d) : ℤ) * ArithmeticFunction.moebius d := by
  let small := Finset.Icc 1 (Nat.sqrt P)
  let large := Finset.Ioc (Nat.sqrt P) P
  have hdis : Disjoint small large := by
    apply Finset.disjoint_left.mpr
    intro n hnSmall hnLarge
    exact (not_lt_of_ge (Finset.mem_Icc.mp hnSmall).2) (Finset.mem_Ioc.mp hnLarge).1
  have hrootP : Nat.sqrt P ≤ P := Nat.sqrt_le_self P
  have hunion : small ∪ large = Finset.Icc 1 P := by
    ext n
    simp [small, large, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  calc
    (∑ n ∈ Finset.Icc 1 P, if n.Prime then (1 : ℤ) else 0) =
        ∑ n ∈ small ∪ large, if n.Prime then (1 : ℤ) else 0 := by rw [hunion]
    _ = (∑ n ∈ small, if n.Prime then (1 : ℤ) else 0) +
        ∑ n ∈ large, if n.Prime then (1 : ℤ) else 0 := Finset.sum_union hdis
    _ = (∑ n ∈ Finset.Icc 1 (Nat.sqrt P), if n.Prime then (1 : ℤ) else 0) +
        ∑ d ∈ (∏ p ∈ smallPrimesUpTo P, p).divisors,
          (↑(P / d - Nat.sqrt P / d) : ℤ) * ArithmeticFunction.moebius d := by
      dsimp [small, large]
      rw [sum_smallPrimesUpTo_primeIndicator_eq_moebius_quotientSum]
end CookMagyarHuaSieve
end SystolicGrowth

#print axioms SystolicGrowth.CookMagyarHuaSieve.inclusionExclusion_dvd_indicator
#print axioms SystolicGrowth.CookMagyarHuaSieve.smallPrimeDivisors_filter_dvd_eq_empty_iff_prime
#print axioms SystolicGrowth.CookMagyarHuaSieve.smallPrimeInclusionExclusion_eq_primeIndicator
#print axioms SystolicGrowth.CookMagyarHuaSieve.smallPrimesUpTo_filter_dvd_eq_empty_iff_prime
#print axioms SystolicGrowth.CookMagyarHuaSieve.smallPrimesUpTo_inclusionExclusion_eq_primeIndicator
#print axioms SystolicGrowth.CookMagyarHuaSieve.moebius_subsetProduct_eq_sign
#print axioms SystolicGrowth.CookMagyarHuaSieve.subsetProduct_injective_of_prime_subset
#print axioms SystolicGrowth.CookMagyarHuaSieve.subsetProduct_squarefree
#print axioms SystolicGrowth.CookMagyarHuaSieve.moebius_divisor_sum_subsetProduct_eq_empty_indicator
#print axioms SystolicGrowth.CookMagyarHuaSieve.inclusionExclusion_eq_moebius_activeDivisorSum
#print axioms SystolicGrowth.CookMagyarHuaSieve.activeDivisors_eq_fixedProduct_divisors_dvd
#print axioms SystolicGrowth.CookMagyarHuaSieve.inclusionExclusion_eq_moebius_fixedDivisorSum
#print axioms SystolicGrowth.CookMagyarHuaSieve.smallPrimesUpTo_moebius_sum_eq_primeIndicator
#print axioms SystolicGrowth.CookMagyarHuaSieve.sum_smallPrimesUpTo_primeIndicator_eq_moebius_multipleCount
#print axioms SystolicGrowth.CookMagyarHuaSieve.card_filter_dvd_Ioc_eq_div_sub_div
#print axioms SystolicGrowth.CookMagyarHuaSieve.sum_smallPrimesUpTo_primeIndicator_eq_moebius_quotientSum
#print axioms SystolicGrowth.CookMagyarHuaSieve.sum_primeIndicator_smallIcc_le_sqrt
#print axioms SystolicGrowth.CookMagyarHuaSieve.sum_primeIndicator_Icc_eq_smallRemainder_add_quotientSum
