module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.HuaStepEightFactorPartition

@[expose] public section

/-!
# Complex-weighted prime sieve identity

Hua's fixed small-prime sieve is applied to an arbitrary complex phase.
The square-root remainder is retained explicitly, and the large interval
is an exact Möbius sum over the fixed step-eight sieve product. Positive
quotients reindex each multiple sum without changing either endpoint.
-/

open scoped BigOperators

namespace SystolicGrowth.CookMagyarCircle

open CookMagyarHuaSieve

/-- The pointwise fixed-product Möbius sieve, summed against an arbitrary
complex phase on the actual large interval. -/
theorem hua_primePhase_large_eq_moebius_multiples
    (P : ℕ) (f : ℕ → ℂ) :
    (∑ n ∈ Finset.Ioc (Nat.sqrt P) P, if n.Prime then f n else 0) =
      ∑ d ∈ (huaStepEightSieveProduct P).divisors,
        (ArithmeticFunction.moebius d : ℂ) *
          ∑ n ∈ (Finset.Ioc (Nat.sqrt P) P).filter (fun n => d ∣ n), f n := by
  classical
  let I := Finset.Ioc (Nat.sqrt P) P
  let H := huaStepEightSieveProduct P
  have hpoint (n : ℕ) (hn : n ∈ I) :
      (if n.Prime then f n else 0) =
        ∑ d ∈ H.divisors, if d ∣ n then
          (ArithmeticFunction.moebius d : ℂ) * f n else 0 := by
    have hnI : Nat.sqrt P < n ∧ n ≤ P := Finset.mem_Ioc.mp hn
    have hnpos : 1 ≤ n := by omega
    have hPpos : 1 ≤ P := hnpos.trans hnI.2
    have hroot : 1 ≤ Nat.sqrt P := by
      simpa using Nat.sqrt_le_sqrt hPpos
    have hn2 : 2 ≤ n := by omega
    have hpointInt := smallPrimesUpTo_moebius_sum_eq_primeIndicator hn2 hnI.2 hnI.1
    have hpointC :
        (∑ d ∈ H.divisors.filter (fun d => d ∣ n),
          (ArithmeticFunction.moebius d : ℂ)) =
          if n.Prime then 1 else 0 := by
      exact_mod_cast hpointInt
    calc
      _ = (if n.Prime then (1 : ℂ) else 0) * f n := by
        split <;> simp
      _ = (∑ d ∈ H.divisors.filter (fun d => d ∣ n),
          (ArithmeticFunction.moebius d : ℂ)) * f n := by rw [hpointC]
      _ = _ := by rw [Finset.sum_mul, Finset.sum_filter]
  calc
    _ = ∑ n ∈ I, ∑ d ∈ H.divisors,
        if d ∣ n then (ArithmeticFunction.moebius d : ℂ) * f n else 0 :=
      Finset.sum_congr rfl hpoint
    _ = ∑ d ∈ H.divisors, ∑ n ∈ I,
        if d ∣ n then (ArithmeticFunction.moebius d : ℂ) * f n else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mul_sum, Finset.sum_filter]

/-- The exact first step of the prime-phase decomposition: the original
sum, including endpoint zero, is the small-prime remainder plus the fixed
Möbius divisor sum on `(sqrt(P),P]`. -/
theorem hua_primePhase_eq_smallRemainder_add_moebius_multiples
    (P : ℕ) (f : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 0 P, if n.Prime then f n else 0) =
      (∑ n ∈ Finset.Icc 0 (Nat.sqrt P), if n.Prime then f n else 0) +
        ∑ d ∈ (huaStepEightSieveProduct P).divisors,
          (ArithmeticFunction.moebius d : ℂ) *
            ∑ n ∈ (Finset.Ioc (Nat.sqrt P) P).filter (fun n => d ∣ n), f n := by
  classical
  let small := Finset.Icc 0 (Nat.sqrt P)
  let large := Finset.Ioc (Nat.sqrt P) P
  have hdis : Disjoint small large := by
    apply Finset.disjoint_left.mpr
    intro n hnSmall hnLarge
    exact (not_lt_of_ge (Finset.mem_Icc.mp hnSmall).2) (Finset.mem_Ioc.mp hnLarge).1
  have hunion : small ∪ large = Finset.Icc 0 P := by
    have hrootP := Nat.sqrt_le_self P
    ext n
    simp only [small, large, Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  calc
    _ = ∑ n ∈ small ∪ large, if n.Prime then f n else 0 := by rw [hunion]
    _ = (∑ n ∈ small, if n.Prime then f n else 0) +
        ∑ n ∈ large, if n.Prime then f n else 0 := Finset.sum_union hdis
    _ = _ := by
      dsimp [small, large]
      rw [hua_primePhase_large_eq_moebius_multiples]

/-- The small-prime phase remainder has norm at most `sqrt(P)`. Endpoint
zero contributes nothing because zero is not prime. -/
theorem hua_primePhase_smallRemainder_norm_le_sqrt
    (P : ℕ) (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) :
    ‖∑ n ∈ Finset.Icc 0 (Nat.sqrt P), if n.Prime then f n else 0‖ ≤
      (Nat.sqrt P : ℝ) := by
  classical
  have hsmall :
      (∑ n ∈ Finset.Icc 0 (Nat.sqrt P), if n.Prime then f n else 0) =
        ∑ n ∈ Finset.Icc 1 (Nat.sqrt P), if n.Prime then f n else 0 := by
    symm
    apply Finset.sum_subset (Finset.Icc_subset_Icc (by omega) le_rfl)
    intro n hn hnnot
    have hnzero : n = 0 := by
      simp only [Finset.mem_Icc] at hn hnnot
      omega
    have hnotPrime : ¬Nat.Prime 0 := by
      intro hprime
      have htwo := hprime.two_le
      omega
    simp [hnzero, hnotPrime]
  rw [hsmall]
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 (Nat.sqrt P), ‖if n.Prime then f n else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 (Nat.sqrt P), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hp : n.Prime
      · simpa only [if_pos hp] using hf n
      · simp [hp]
    _ = _ := by simp [Nat.card_Icc]

/-- Multiples in an open-closed natural interval are exactly the positive
quotients in the divided interval. This preserves both source endpoints. -/
theorem hua_sum_multiples_Ioc_eq_sum_quotients
    (A B d : ℕ) (hd : 0 < d) (f : ℕ → ℂ) :
    (∑ n ∈ (Finset.Ioc A B).filter (fun n => d ∣ n), f n) =
      ∑ m ∈ Finset.Ioc (A / d) (B / d), f (d * m) := by
  classical
  apply Finset.sum_bij (fun n _ => n / d)
  · intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnI, hdn⟩
    rcases Finset.mem_Ioc.mp hnI with ⟨hAn, hnB⟩
    apply Finset.mem_Ioc.mpr
    constructor
    · apply (Nat.div_lt_iff_lt_mul hd).mpr
      simpa only [Nat.div_mul_cancel hdn] using hAn
    · exact Nat.div_le_div_right hnB
  · intro n hn m hm hnm
    have hdn := (Finset.mem_filter.mp hn).2
    have hdm := (Finset.mem_filter.mp hm).2
    calc
      n = d * (n / d) := (Nat.mul_div_cancel' hdn).symm
      _ = d * (m / d) := by rw [hnm]
      _ = m := Nat.mul_div_cancel' hdm
  · intro m hm
    rcases Finset.mem_Ioc.mp hm with ⟨hAm, hmB⟩
    refine ⟨d * m, Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨?_, ?_⟩,
      dvd_mul_right d m⟩, ?_⟩
    · simpa only [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hd).mp hAm
    · simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).mp hmB
    · exact Nat.mul_div_cancel_left m hd
  · intro n hn
    rw [Nat.mul_div_cancel' (Finset.mem_filter.mp hn).2]

/-- The same exact prime-phase identity with every multiple sum reindexed
to its actual positive quotient interval. -/
theorem hua_primePhase_eq_smallRemainder_add_moebius_quotients
    (P : ℕ) (f : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 0 P, if n.Prime then f n else 0) =
      (∑ n ∈ Finset.Icc 0 (Nat.sqrt P), if n.Prime then f n else 0) +
        ∑ d ∈ (huaStepEightSieveProduct P).divisors,
          (ArithmeticFunction.moebius d : ℂ) *
            ∑ m ∈ Finset.Ioc (Nat.sqrt P / d) (P / d), f (d * m) := by
  rw [hua_primePhase_eq_smallRemainder_add_moebius_multiples]
  apply congrArg
  apply Finset.sum_congr rfl
  intro d hd
  rw [hua_sum_multiples_Ioc_eq_sum_quotients]
  exact Nat.pos_of_mem_divisors hd

/-- For a squarefree integer, the Möbius sign is determined by the number
of its distinct prime factors, including the empty factor set at one. -/
theorem hua_moebius_eq_primeFactor_sign_of_squarefree
    (d : ℕ) (hd : Squarefree d) :
    ArithmeticFunction.moebius d = (-1 : ℤ) ^ d.primeFactors.card := by
  have hsign := moebius_subsetProduct_eq_sign d.primeFactors
    (fun p hp => Nat.prime_of_mem_primeFactors hp)
  simpa only [Nat.prod_primeFactors_of_squarefree hd] using hsign

/-- The fixed squarefree divisor sum is the even-factor source contribution
minus the odd-factor contribution. The actual upper range and arbitrary
source restriction are retained in both eligible divisor families. -/
theorem hua_moebius_divisor_sum_eq_even_sub_odd
    (H M : ℕ) (R : ℕ → Prop) [DecidablePred R]
    (hH : Squarefree H) (f : ℕ → ℂ) :
    (∑ d ∈ H.divisors.filter (fun d => d ≤ M ∧ R d),
      (ArithmeticFunction.moebius d : ℂ) * f d) =
      (∑ d ∈ huaStepEightEligibleDivisors H M 0 R, f d) -
        ∑ d ∈ huaStepEightEligibleDivisors H M 1 R, f d := by
  classical
  let I := H.divisors.filter (fun d => d ≤ M ∧ R d)
  have hmu (d : ℕ) (hd : d ∈ H.divisors) :
      (ArithmeticFunction.moebius d : ℂ) =
        (-1 : ℂ) ^ (d.primeFactors.card % 2) := by
    have hdsq := hH.squarefree_of_dvd (Nat.mem_divisors.mp hd).1
    have hcast : (ArithmeticFunction.moebius d : ℂ) =
        (-1 : ℂ) ^ d.primeFactors.card := by
      exact_mod_cast hua_moebius_eq_primeFactor_sign_of_squarefree d hdsq
    exact hcast.trans (neg_one_pow_eq_pow_mod_two _)
  have heven : I.filter (fun d => d.primeFactors.card % 2 = 0) =
      huaStepEightEligibleDivisors H M 0 R := by
    ext d
    simp only [I, Finset.mem_filter, mem_huaStepEightEligibleDivisors_iff]
    tauto
  have hodd : I.filter (fun d => ¬d.primeFactors.card % 2 = 0) =
      huaStepEightEligibleDivisors H M 1 R := by
    ext d
    simp only [I, Finset.mem_filter, mem_huaStepEightEligibleDivisors_iff]
    have hparity : (¬d.primeFactors.card % 2 = 0) ↔ d.primeFactors.card % 2 = 1 := by
      omega
    rw [hparity]
    tauto
  have hsumEven :
      (∑ d ∈ I.filter (fun d => d.primeFactors.card % 2 = 0),
        (ArithmeticFunction.moebius d : ℂ) * f d) =
        ∑ d ∈ I.filter (fun d => d.primeFactors.card % 2 = 0), f d := by
    apply Finset.sum_congr rfl
    intro d hd
    rcases Finset.mem_filter.mp hd with ⟨hdI, hparity⟩
    rw [hmu d (Finset.mem_filter.mp hdI).1, hparity]
    simp
  have hsumOdd :
      (∑ d ∈ I.filter (fun d => ¬d.primeFactors.card % 2 = 0),
        (ArithmeticFunction.moebius d : ℂ) * f d) =
        -(∑ d ∈ I.filter (fun d => ¬d.primeFactors.card % 2 = 0), f d) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rcases Finset.mem_filter.mp hd with ⟨hdI, hparity⟩
    have hparityOne : d.primeFactors.card % 2 = 1 := by omega
    rw [hmu d (Finset.mem_filter.mp hdI).1, hparityOne]
    simp
  have hsplit := Finset.sum_filter_add_sum_filter_not I
    (fun d => d.primeFactors.card % 2 = 0)
    (fun d => (ArithmeticFunction.moebius d : ℂ) * f d)
  rw [hsumEven, hsumOdd, heven, hodd] at hsplit
  simpa only [sub_eq_add_neg] using hsplit.symm

/-- A positive quotient from the actual large-divisor branch lies in the
fixed logarithmic outer range. The strict source cutoff is retained. -/
theorem hua_largeDivisor_quotient_le_floor
    (P d m sigma3 : ℕ) (hL : 0 < Real.log (P : ℝ))
    (hd : 0 < d)
    (hlarge : (P : ℝ) / Real.log (P : ℝ) ^ sigma3 < d)
    (hm : m ≤ P / d) :
    m ≤ Nat.floor (Real.log (P : ℝ) ^ sigma3) := by
  have hprod : d * m ≤ P := by
    simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).mp hm
  have hprodR : (d : ℝ) * m ≤ P := by exact_mod_cast hprod
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hstrict : (P : ℝ) < (d : ℝ) * Real.log (P : ℝ) ^ sigma3 :=
    (div_lt_iff₀ (pow_pos hL sigma3)).mp hlarge
  have hmR : (m : ℝ) < Real.log (P : ℝ) ^ sigma3 := by
    nlinarith only [hprodR, hstrict, hdR]
  exact (Nat.le_floor_iff (pow_nonneg hL.le sigma3)).mpr hmR.le

/-- Interchanging Hua's actual large sieve branch yields the exact fixed
outer range and eligible divisor range. The square-root lower endpoint is
removed only after the large-divisor cutoff has been shown to exceed it. -/
theorem hua_largeDivisor_moebius_quotients_eq_source
    (P sigma3 : ℕ) (f : ℕ → ℂ)
    (hL : 0 < Real.log (P : ℝ))
    (hroot : (Nat.sqrt P : ℝ) ≤ (P : ℝ) / Real.log (P : ℝ) ^ sigma3) :
    (∑ d ∈ (huaStepEightSieveProduct P).divisors.filter
        (fun d : ℕ => (P : ℝ) / Real.log (P : ℝ) ^ sigma3 < (d : ℝ)),
      (ArithmeticFunction.moebius d : ℂ) *
        ∑ m ∈ Finset.Ioc (Nat.sqrt P / d) (P / d), f (d * m)) =
      ∑ m ∈ Finset.Icc 1 (Nat.floor (Real.log (P : ℝ) ^ sigma3)),
        ∑ d ∈ (huaStepEightSieveProduct P).divisors.filter
            (fun d => d ≤ P / m ∧
              (P : ℝ) / Real.log (P : ℝ) ^ sigma3 < (d : ℝ)),
          (ArithmeticFunction.moebius d : ℂ) * f (m * d) := by
  classical
  let H := huaStepEightSieveProduct P
  let X : ℝ := (P : ℝ) / Real.log (P : ℝ) ^ sigma3
  let M := Nat.floor (Real.log (P : ℝ) ^ sigma3)
  let D := H.divisors.filter (fun d : ℕ => X < (d : ℝ))
  have hexpand (d : ℕ) (hd : d ∈ D) :
      (ArithmeticFunction.moebius d : ℂ) *
          ∑ m ∈ Finset.Ioc (Nat.sqrt P / d) (P / d), f (d * m) =
        ∑ m ∈ Finset.Icc 1 M,
          if m ≤ P / d then (ArithmeticFunction.moebius d : ℂ) * f (m * d)
          else 0 := by
    have hddiv : d ∈ H.divisors := (Finset.mem_filter.mp hd).1
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hddiv
    have hdlarge : X < (d : ℝ) := (Finset.mem_filter.mp hd).2
    have hrootlt : Nat.sqrt P < d := by
      exact_mod_cast hroot.trans_lt hdlarge
    have hlo : Nat.sqrt P / d = 0 := Nat.div_eq_of_lt hrootlt
    have hinterval : Finset.Ioc 0 (P / d) = Finset.Icc 1 (P / d) := by
      ext m
      simp only [Finset.mem_Ioc, Finset.mem_Icc]
      omega
    have hfilter : (Finset.Icc 1 M).filter (fun m => m ≤ P / d) =
        Finset.Icc 1 (P / d) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · tauto
      · rintro ⟨hmpos, hmupper⟩
        exact ⟨⟨hmpos,
          hua_largeDivisor_quotient_le_floor P d m sigma3 hL hdpos hdlarge hmupper⟩,
          hmupper⟩
    rw [hlo, hinterval, Finset.mul_sum, ← hfilter, Finset.sum_filter]
    simp only [Nat.mul_comm]
  change (∑ d ∈ D, _) = _
  rw [Finset.sum_congr rfl hexpand, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  have hmpos : 0 < m := by have := (Finset.mem_Icc.mp hm).1; omega
  have hfilter : D.filter (fun d => m ≤ P / d) =
      H.divisors.filter (fun d => d ≤ P / m ∧ X < (d : ℝ)) := by
    ext d
    simp only [D, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hddiv, hdlarge⟩, hmupper⟩
      have hdpos := Nat.pos_of_mem_divisors hddiv
      have hprod := (Nat.le_div_iff_mul_le hdpos).mp hmupper
      exact ⟨hddiv, (Nat.le_div_iff_mul_le hmpos).mpr
        (by simpa only [Nat.mul_comm] using hprod), hdlarge⟩
    · rintro ⟨hddiv, hdupper, hdlarge⟩
      have hdpos := Nat.pos_of_mem_divisors hddiv
      have hprod := (Nat.le_div_iff_mul_le hmpos).mp hdupper
      exact ⟨⟨hddiv, hdlarge⟩, (Nat.le_div_iff_mul_le hdpos).mpr
        (by simpa only [Nat.mul_comm] using hprod)⟩
  rw [← Finset.sum_filter, hfilter]

/-- The large sieve contribution is precisely the difference of the two
source parity aggregates, with no Möbius weights or endpoints discarded. -/
theorem hua_largeDivisor_moebius_quotients_eq_source_even_sub_odd
    (P sigma3 : ℕ) (f : ℕ → ℂ)
    (hL : 0 < Real.log (P : ℝ))
    (hroot : (Nat.sqrt P : ℝ) ≤ (P : ℝ) / Real.log (P : ℝ) ^ sigma3) :
    (∑ d ∈ (huaStepEightSieveProduct P).divisors.filter
        (fun d : ℕ => (P : ℝ) / Real.log (P : ℝ) ^ sigma3 < (d : ℝ)),
      (ArithmeticFunction.moebius d : ℂ) *
        ∑ m ∈ Finset.Ioc (Nat.sqrt P / d) (P / d), f (d * m)) =
      (∑ m ∈ Finset.Icc 1
          (Nat.floor (Real.rpow (Real.log P) (sigma3 : ℝ))),
        ∑ d ∈ huaStepEightEligibleDivisors (huaStepEightSieveProduct P)
            (P / m) 0 (huaStepEightSourceCondition P m 1 0 (sigma3 : ℝ)),
          f (m * d)) -
      ∑ m ∈ Finset.Icc 1
          (Nat.floor (Real.rpow (Real.log P) (sigma3 : ℝ))),
        ∑ d ∈ huaStepEightEligibleDivisors (huaStepEightSieveProduct P)
            (P / m) 1 (huaStepEightSourceCondition P m 1 0 (sigma3 : ℝ)),
          f (m * d) := by
  classical
  rw [hua_largeDivisor_moebius_quotients_eq_source P sigma3 f hL hroot,
    ← Finset.sum_sub_distrib]
  simp only [Real.rpow_eq_pow, Real.rpow_natCast]
  apply Finset.sum_congr rfl
  intro m hm
  have hsource (d : ℕ) :
      huaStepEightSourceCondition P m 1 0 (sigma3 : ℝ) d ↔
        (P : ℝ) / Real.log (P : ℝ) ^ sigma3 < (d : ℝ) := by
    simp only [huaStepEightSourceCondition, Real.rpow_eq_pow, Real.rpow_natCast]
    exact and_iff_left (Nat.modEq_one)
  have hfilter :
      (huaStepEightSieveProduct P).divisors.filter
          (fun d => d ≤ P / m ∧ (P : ℝ) / Real.log (P : ℝ) ^ sigma3 < (d : ℝ)) =
        (huaStepEightSieveProduct P).divisors.filter
          (fun d => d ≤ P / m ∧ huaStepEightSourceCondition P m 1 0 (sigma3 : ℝ) d) := by
    ext d
    simp only [Finset.mem_filter, hsource]
  rw [hfilter]
  exact hua_moebius_divisor_sum_eq_even_sub_odd _ _ _
    (squarefree_huaStepEightSieveProduct P) (fun d => f (m * d))

/-- The endpoint justification for the preceding source identity holds
eventually for every fixed multiplier exponent. -/
theorem eventually_hua_largeDivisor_moebius_quotients_eq_source_even_sub_odd
    (sigma3 : ℕ) :
    ∀ᶠ P : ℕ in Filter.atTop, ∀ f : ℕ → ℂ,
      (∑ d ∈ (huaStepEightSieveProduct P).divisors.filter
          (fun d : ℕ => (P : ℝ) / Real.log (P : ℝ) ^ sigma3 < (d : ℝ)),
        (ArithmeticFunction.moebius d : ℂ) *
          ∑ m ∈ Finset.Ioc (Nat.sqrt P / d) (P / d), f (d * m)) =
        (∑ m ∈ Finset.Icc 1
            (Nat.floor (Real.rpow (Real.log P) (sigma3 : ℝ))),
          ∑ d ∈ huaStepEightEligibleDivisors (huaStepEightSieveProduct P)
              (P / m) 0 (huaStepEightSourceCondition P m 1 0 (sigma3 : ℝ)),
            f (m * d)) -
        ∑ m ∈ Finset.Icc 1
            (Nat.floor (Real.rpow (Real.log P) (sigma3 : ℝ))),
          ∑ d ∈ huaStepEightEligibleDivisors (huaStepEightSieveProduct P)
              (P / m) 1 (huaStepEightSourceCondition P m 1 0 (sigma3 : ℝ)),
            f (m * d) := by
  filter_upwards [eventually_natSqrt_le_scale_div_log_pow sigma3] with P hP
  intro f
  exact hua_largeDivisor_moebius_quotients_eq_source_even_sub_odd P sigma3 f
    (Real.log_pos (by exact_mod_cast hP.1)) hP.2

/-- The two fixed logarithmic cutoffs occur in the intended order for
large endpoints. Thus the small, medium and large ranges really partition
every sieve divisor. -/
theorem eventually_hua_divisor_cutoffs_ordered (lambda1 lambda2 : ℕ) :
    ∀ᶠ P : ℕ in Filter.atTop,
      0 < Real.log (P : ℝ) ∧
        Real.log (P : ℝ) ^ lambda1 ≤
          (P : ℝ) / Real.log (P : ℝ) ^ lambda2 := by
  have hlittle :
      (fun x : ℝ => Real.log x ^ (lambda1 + lambda2)) =o[Filter.atTop]
        (fun x => x) := by
    simpa only [Real.rpow_natCast, Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop
        ((lambda1 + lambda2 : ℕ) : ℝ) (by norm_num : (0 : ℝ) < 1))
  have hbound := tendsto_natCast_atTop_atTop.eventually
    (hlittle.bound (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hbound, Filter.eventually_gt_atTop (1 : ℕ)] with P hboundP hP
  have hL : 0 < Real.log (P : ℝ) := Real.log_pos (by exact_mod_cast hP)
  have hpow : Real.log (P : ℝ) ^ (lambda1 + lambda2) ≤ (P : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hL.le _),
      abs_of_nonneg (Nat.cast_nonneg P : (0 : ℝ) ≤ P), one_mul] using hboundP
  refine ⟨hL, (le_div_iff₀ (pow_pos hL lambda2)).mpr ?_⟩
  simpa only [pow_add] using hpow

/-- The exact finite sieve decomposition into the three source divisor
ranges. Both quotient endpoints remain present in all three branches. -/
theorem hua_primePhase_eq_smallRemainder_add_three_divisor_ranges
    (P lambda1 lambda2 : ℕ) (f : ℕ → ℂ)
    (hcutoffs : Real.log (P : ℝ) ^ lambda1 ≤
      (P : ℝ) / Real.log (P : ℝ) ^ lambda2) :
    (∑ n ∈ Finset.Icc 0 P, if n.Prime then f n else 0) =
      (∑ n ∈ Finset.Icc 0 (Nat.sqrt P), if n.Prime then f n else 0) +
      (∑ d ∈ (huaStepEightSieveProduct P).divisors.filter
          (fun d : ℕ => (d : ℝ) ≤ Real.log (P : ℝ) ^ lambda1),
        (ArithmeticFunction.moebius d : ℂ) *
          ∑ m ∈ Finset.Ioc (Nat.sqrt P / d) (P / d), f (d * m)) +
      (∑ d ∈ (huaStepEightSieveProduct P).divisors.filter
          (fun d : ℕ => Real.log (P : ℝ) ^ lambda1 < (d : ℝ) ∧
            (d : ℝ) ≤ (P : ℝ) / Real.log (P : ℝ) ^ lambda2),
        (ArithmeticFunction.moebius d : ℂ) *
          ∑ m ∈ Finset.Ioc (Nat.sqrt P / d) (P / d), f (d * m)) +
      ∑ d ∈ (huaStepEightSieveProduct P).divisors.filter
          (fun d : ℕ => (P : ℝ) / Real.log (P : ℝ) ^ lambda2 < (d : ℝ)),
        (ArithmeticFunction.moebius d : ℂ) *
          ∑ m ∈ Finset.Ioc (Nat.sqrt P / d) (P / d), f (d * m) := by
  classical
  let H := huaStepEightSieveProduct P
  let A : ℝ := Real.log (P : ℝ) ^ lambda1
  let B : ℝ := (P : ℝ) / Real.log (P : ℝ) ^ lambda2
  let w := fun d : ℕ => (ArithmeticFunction.moebius d : ℂ) *
    ∑ m ∈ Finset.Ioc (Nat.sqrt P / d) (P / d), f (d * m)
  have hsmall := Finset.sum_filter_add_sum_filter_not H.divisors
    (fun d : ℕ => (d : ℝ) ≤ A) w
  have hlarge := Finset.sum_filter_add_sum_filter_not
    (H.divisors.filter (fun d : ℕ => ¬(d : ℝ) ≤ A))
    (fun d : ℕ => (d : ℝ) ≤ B) w
  have hmiddle :
      (H.divisors.filter (fun d : ℕ => ¬(d : ℝ) ≤ A)).filter
          (fun d : ℕ => (d : ℝ) ≤ B) =
        H.divisors.filter (fun d : ℕ => A < (d : ℝ) ∧ (d : ℝ) ≤ B) := by
    ext d
    simp only [Finset.mem_filter, not_le]
    tauto
  have hlast :
      (H.divisors.filter (fun d : ℕ => ¬(d : ℝ) ≤ A)).filter
          (fun d : ℕ => ¬(d : ℝ) ≤ B) =
        H.divisors.filter (fun d : ℕ => B < (d : ℝ)) := by
    ext d
    simp only [Finset.mem_filter, not_le]
    constructor
    · tauto
    · rintro ⟨hd, hBd⟩
      exact ⟨⟨hd, hcutoffs.trans_lt hBd⟩, hBd⟩
  rw [hmiddle, hlast] at hlarge
  rw [hua_primePhase_eq_smallRemainder_add_moebius_quotients]
  change _ + (∑ d ∈ H.divisors, w d) = _
  rw [← hsmall, ← hlarge]
  simp only [H, A, B, w]
  ring

/-- Moving the assembled source rate from `log(P)` to the target's
`log(P+2)` costs only the fixed factor `2^decay`. -/
theorem hua_log_rate_le_shifted_log_rate
    (P decay : ℕ) (C : ℝ) (hP : 2 ≤ P) (hC : 0 ≤ C) :
    C * (P : ℝ) / Real.log (P : ℝ) ^ decay ≤
      ((2 : ℝ) ^ decay * C) * P / Real.log ((P : ℝ) + 2) ^ decay := by
  have hPR : (2 : ℝ) ≤ P := by exact_mod_cast hP
  have hPpos : (0 : ℝ) < P := by linarith
  have hL : 0 < Real.log (P : ℝ) := Real.log_pos (by linarith)
  have hL' : 0 < Real.log ((P : ℝ) + 2) := Real.log_pos (by linarith)
  have hquadratic : (P : ℝ) + 2 ≤ (P : ℝ) ^ 2 := by nlinarith
  have hlog : Real.log ((P : ℝ) + 2) ≤ 2 * Real.log (P : ℝ) := by
    calc
      Real.log ((P : ℝ) + 2) ≤ Real.log ((P : ℝ) ^ 2) :=
        Real.log_le_log (by positivity) hquadratic
      _ = _ := by rw [Real.log_pow]; norm_num
  have hpow : Real.log ((P : ℝ) + 2) ^ decay ≤
      (2 : ℝ) ^ decay * Real.log (P : ℝ) ^ decay := by
    simpa only [mul_pow] using pow_le_pow_left₀ hL'.le hlog decay
  apply (div_le_div_iff₀ (pow_pos hL decay) (pow_pos hL' decay)).mpr
  calc
    C * (P : ℝ) * Real.log ((P : ℝ) + 2) ^ decay ≤
        C * P * ((2 : ℝ) ^ decay * Real.log (P : ℝ) ^ decay) :=
      mul_le_mul_of_nonneg_left hpow (mul_nonneg hC (Nat.cast_nonneg P))
    _ = _ := by ring

#print axioms hua_log_rate_le_shifted_log_rate
#print axioms eventually_hua_divisor_cutoffs_ordered
#print axioms hua_primePhase_eq_smallRemainder_add_three_divisor_ranges
#print axioms hua_largeDivisor_moebius_quotients_eq_source_even_sub_odd
#print axioms eventually_hua_largeDivisor_moebius_quotients_eq_source_even_sub_odd
#print axioms hua_primePhase_eq_smallRemainder_add_moebius_multiples
#print axioms hua_primePhase_smallRemainder_norm_le_sqrt
#print axioms hua_sum_multiples_Ioc_eq_sum_quotients
#print axioms hua_primePhase_eq_smallRemainder_add_moebius_quotients
#print axioms hua_moebius_eq_primeFactor_sign_of_squarefree
#print axioms hua_moebius_divisor_sum_eq_even_sub_odd

end SystolicGrowth.CookMagyarCircle
