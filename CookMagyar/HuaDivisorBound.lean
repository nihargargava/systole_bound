module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.PSeries

@[expose] public section

open scoped BigOperators

/-! # Divisor-counting ingredients for Hua's estimate

The sharp Hua bound needs a subpolynomial estimate for the divisor function.
This file records a factor-level estimate and the exact prime-power case,
which are the local ingredients in the Euler-product approach.
-/

namespace SystolicGrowth
namespace CookMagyarCircle

/-- Each local factor in the divisor Euler product is at most `2^k`. -/
theorem succ_le_two_pow (k : ℕ) : k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      calc
        k + 1 + 1 ≤ 2 * (k + 1) := by omega
        _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (k + 1) := by rw [pow_succ]; omega

/-- For primes whose `ε`-power is at least two, the local divisor factor is
absorbed directly by the corresponding prime-power contribution. -/
theorem divisorLocalFactor_le_rpow {p e : ℕ} {ε : ℝ}
    (hthreshold : 2 ≤ Real.rpow (p : ℝ) ε) :
    (e + 1 : ℝ) ≤ Real.rpow (p : ℝ) (ε * (e : ℝ)) := by
  calc
    (e + 1 : ℝ) ≤ (2 : ℝ) ^ e := by exact_mod_cast succ_le_two_pow e
    _ ≤ (Real.rpow (p : ℝ) ε) ^ e := by gcongr
    _ = Real.rpow (p : ℝ) (ε * (e : ℝ)) := by
      exact (Real.rpow_mul_natCast (by positivity) ε e).symm

/-- For each fixed real base strictly larger than one, the linear factor in
the exponent is absorbed by a constant times the corresponding geometric
factor. -/
theorem exists_linear_le_const_mul_pow {x : ℝ} (hx : 1 < x) :
    ∃ C : ℝ, 0 < C ∧ ∀ e : ℕ, (e + 1 : ℝ) ≤ C * x ^ e := by
  obtain ⟨r, hr⟩ := pow_unbounded_of_one_lt (2 : ℝ) hx
  have hrpos : 0 < r := by
    by_contra h
    have : r = 0 := Nat.eq_zero_of_not_pos h
    simp [this] at hr
  refine ⟨r, Nat.cast_pos.mpr hrpos, ?_⟩
  intro e
  let q := e / r
  have hq : q + 1 ≤ 2 ^ q := succ_le_two_pow q
  have hmod : e % r < r := Nat.mod_lt _ hrpos
  have hsplit : e = r * q + e % r := by
    dsimp [q]
    exact (Nat.div_add_mod e r).symm
  have hlinear : e + 1 ≤ r * (q + 1) := by
    rw [hsplit]
    rw [Nat.mul_add]
    omega
  have hgeom : (2 : ℝ) ^ q ≤ (x ^ r) ^ q := by
    gcongr
  have hpowexp : q * r ≤ e := by
    dsimp [q]
    exact Nat.div_mul_le_self e r
  calc
    (e + 1 : ℝ) ≤ (r * (q + 1) : ℕ) := by exact_mod_cast hlinear
    _ ≤ (r : ℝ) * 2 ^ q := by
      exact_mod_cast Nat.mul_le_mul_left r hq
    _ ≤ (r : ℝ) * (x ^ r) ^ q := by gcongr
    _ = (r : ℝ) * x ^ (q * r) := by
      simp [pow_mul, Nat.mul_comm]
    _ ≤ (r : ℝ) * x ^ e := by
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx.le hpowexp)
        (Nat.cast_nonneg r)

/-- For each fixed prime base and positive `ε`, the local divisor factor is
bounded by a constant times the `ε`-power contribution. -/
theorem exists_local_divisor_constant {p : ℕ} {ε : ℝ}
    (hp : 2 ≤ p) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ e : ℕ,
      (e + 1 : ℝ) ≤ C * Real.rpow (p : ℝ) (ε * (e : ℝ)) := by
  have hp' : (1 : ℝ) < p := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hp)
  have hx : 1 < Real.rpow (p : ℝ) ε := by
    simpa using Real.rpow_lt_rpow (by norm_num) hp' hε
  obtain ⟨C, hC, hbound⟩ := exists_linear_le_const_mul_pow hx
  refine ⟨C, hC, fun e ↦ ?_⟩
  calc
    (e + 1 : ℝ) ≤ C * (Real.rpow (p : ℝ) ε) ^ e := hbound e
    _ = C * Real.rpow (p : ℝ) (ε * (e : ℝ)) := by
      exact congrArg (fun z : ℝ => C * z)
        (Real.rpow_mul_natCast (by positivity) ε e).symm

/-- A natural cutoff beyond which the local constant can be taken to be one. -/
theorem exists_divisor_large_prime_cutoff {ε : ℝ} (hε : 0 < ε) :
    ∃ P : ℕ, ∀ p : ℕ, P ≤ p →
      2 ≤ Real.rpow (p : ℝ) ε := by
  obtain ⟨P, hP⟩ := exists_nat_gt (Real.rpow 2 ε⁻¹)
  refine ⟨P, fun p hp ↦ ?_⟩
  have hlt : Real.rpow 2 ε⁻¹ < (p : ℝ) := by
    exact lt_of_lt_of_le (by exact_mod_cast hP) (by exact_mod_cast hp)
  have hpow : Real.rpow (Real.rpow 2 ε⁻¹) ε <
      Real.rpow (p : ℝ) ε := by
    exact Real.rpow_lt_rpow
      (Real.rpow_pos_of_pos (by norm_num) _).le hlt hε
  have hcancel : Real.rpow (Real.rpow 2 ε⁻¹) ε = 2 := by
    simpa using Real.rpow_inv_rpow (by norm_num) hε.ne'
  rw [hcancel] at hpow
  linarith

/-- Chosen local constants, defined for every natural prime candidate. -/
noncomputable def divisorLocalConstant (ε : ℝ) (hε : 0 < ε) (p : ℕ) : ℝ :=
  if hp : 2 ≤ p then Classical.choose (exists_local_divisor_constant hp hε) else 1

theorem divisorLocalConstant_spec {ε : ℝ} (hε : 0 < ε) {p : ℕ}
    (hp : 2 ≤ p) :
    0 < divisorLocalConstant ε hε p ∧
      ∀ e : ℕ, (e + 1 : ℝ) ≤ divisorLocalConstant ε hε p *
        Real.rpow (p : ℝ) (ε * (e : ℝ)) := by
  simp only [divisorLocalConstant, dif_pos hp]
  exact Classical.choose_spec (exists_local_divisor_constant hp hε)

theorem one_le_divisorLocalConstant {ε : ℝ} (hε : 0 < ε) {p : ℕ}
    (hp : 2 ≤ p) : 1 ≤ divisorLocalConstant ε hε p := by
  have h := (divisorLocalConstant_spec hε hp).2 0
  simpa using h

/-- All local constants for primes below the cutoff are dominated by one
constant obtained as a finite Euler product. -/
theorem exists_uniform_small_prime_constant {ε : ℝ} (hε : 0 < ε) :
    ∃ P : ℕ, (∀ p : ℕ, P ≤ p → 2 ≤ Real.rpow (p : ℝ) ε) ∧
      ∃ C : ℝ, 1 ≤ C ∧ ∀ p e : ℕ,
      2 ≤ p → p < P →
      (e + 1 : ℝ) ≤ C * Real.rpow (p : ℝ) (ε * (e : ℝ)) := by
  classical
  obtain ⟨P, hP⟩ := exists_divisor_large_prime_cutoff hε
  let C : ℝ := ∏ p ∈ Finset.Icc 2 P, divisorLocalConstant ε hε p
  have hCone : 1 ≤ C := by
    apply Finset.one_le_prod₀
    intro p hp
    exact one_le_divisorLocalConstant hε (Finset.mem_Icc.mp hp).1
  refine ⟨P, hP, C, hCone, fun p e hp hlt ↦ ?_⟩
  have hpmem : p ∈ Finset.Icc 2 P := Finset.mem_Icc.mpr
    ⟨hp, Nat.le_of_lt hlt⟩
  have hlocal := (divisorLocalConstant_spec hε hp).2 e
  have hconst : divisorLocalConstant ε hε p ≤ C := by
    have hsingle : (∏ q ∈ ({p} : Finset ℕ), divisorLocalConstant ε hε q) ≤
        ∏ q ∈ Finset.Icc 2 P, divisorLocalConstant ε hε q := by
      apply Finset.prod_le_prod_of_subset_of_one_le₀
        (Finset.singleton_subset_iff.mpr hpmem)
      · intro q hq
        have hqp : q = p := Finset.mem_singleton.mp hq
        subst q
        exact (divisorLocalConstant_spec hε hp).1.le
      · intro q hq hqnot
        exact one_le_divisorLocalConstant hε (Finset.mem_Icc.mp hq).1
    simpa [C] using hsingle
  exact hlocal.trans (mul_le_mul_of_nonneg_right hconst
    (Real.rpow_nonneg (by positivity) _))

/-- Uniform subpolynomial growth of the divisor count. -/
theorem exists_divisor_rpow_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, m ≠ 0 →
      (m.divisors.card : ℝ) ≤ C * Real.rpow (m : ℝ) ε := by
  classical
  obtain ⟨P, hcut, C₀, hC₀, hsmall⟩ := exists_uniform_small_prime_constant hε
  let C : ℝ := C₀ ^ P
  refine ⟨C, by positivity, fun m hm ↦ ?_⟩
  let s := m.primeFactors
  let localWeight : ℕ → ℝ := fun p =>
    if p < P then C₀ else 1
  have hlocal : ∀ p ∈ s, ∀ e : ℕ,
      (e + 1 : ℝ) ≤ localWeight p * Real.rpow (p : ℝ) (ε * (e : ℝ)) := by
    intro p hp e
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp2 : 2 ≤ p := hprime.two_le
    by_cases hlt : p < P
    · simpa [localWeight, hlt] using hsmall p e hp2 hlt
    · have hthreshold := hcut p (Nat.le_of_not_gt hlt)
      simpa [localWeight, hlt] using divisorLocalFactor_le_rpow hthreshold
  have heulerNat := Nat.card_divisors hm
  have heuler : (m.divisors.card : ℝ) =
      ∏ p ∈ s, ((m.factorization p + 1 : ℕ) : ℝ) := by
    rw [heulerNat]
    norm_cast
  have hprodLocal :
      (∏ p ∈ s, ((m.factorization p + 1 : ℕ) : ℝ)) ≤
        ∏ p ∈ s, (localWeight p *
          Real.rpow (p : ℝ) (ε * (m.factorization p : ℝ))) := by
    apply Finset.prod_le_prod₀
    · intro p hp
      positivity
    · intro p hp
      simpa [Nat.cast_add] using hlocal p hp (m.factorization p)
  have hsmallProd : (∏ p ∈ s, localWeight p) ≤ C₀ ^ P := by
    rw [← Finset.prod_filter]
    let t := s.filter (fun p => p < P)
    have htSub : t ⊆ Finset.Iio P := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      exact Finset.mem_Iio.mpr hp'.2
    have ht : t.card ≤ P := by
      calc
        t.card ≤ (Finset.Iio P).card := Finset.card_le_card htSub
        _ = P := by simp
    calc
      (∏ p ∈ t, C₀) = C₀ ^ t.card := by simp [Finset.prod_const]
      _ ≤ C₀ ^ P := by gcongr
  have hprodSplit :
      (∏ p ∈ s, (localWeight p *
          Real.rpow (p : ℝ) (ε * (m.factorization p : ℝ)))) =
        (∏ p ∈ s, localWeight p) *
          ∏ p ∈ s, Real.rpow (p : ℝ) (ε * (m.factorization p : ℝ)) := by
    rw [Finset.prod_mul_distrib]
  have hrpowProduct :
      (∏ p ∈ s, Real.rpow (p : ℝ) (ε * (m.factorization p : ℝ))) =
        Real.rpow (m : ℝ) ε := by
    have hsprime : ∀ p ∈ s, p.Prime := fun p hp ↦ Nat.prime_of_mem_primeFactors hp
    have hterm : ∀ p ∈ s,
        Real.rpow (p : ℝ) (ε * (m.factorization p : ℝ)) =
          Real.rpow ((p : ℝ) ^ m.factorization p) ε := by
      intro p hp
      calc
        Real.rpow (p : ℝ) (ε * (m.factorization p : ℝ)) =
            Real.rpow (p : ℝ) ((m.factorization p : ℝ) * ε) := by rw [mul_comm]
        _ = ((p : ℝ) ^ m.factorization p) ^ ε := by
          exact Real.rpow_natCast_mul (x := (p : ℝ)) (by positivity)
            (m.factorization p) ε
        _ = Real.rpow ((p : ℝ) ^ m.factorization p) ε := rfl
    have hprodRpow (u : Finset ℕ) (hu : ∀ p ∈ u, p.Prime) :
        (∏ p ∈ u, Real.rpow ((p : ℝ) ^ m.factorization p) ε) =
          Real.rpow (∏ p ∈ u, ((p : ℝ) ^ m.factorization p)) ε := by
      classical
      induction u using Finset.induction_on with
      | empty => simp
      | @insert p u hpu ih =>
        have hpp := hu p (by simp)
        have hu' : ∀ q ∈ u, q.Prime := fun q hq ↦ hu q (by simp [hq])
        rw [Finset.prod_insert hpu, Finset.prod_insert hpu]
        calc
          Real.rpow ((p : ℝ) ^ m.factorization p) ε *
              ∏ x ∈ u, Real.rpow ((x : ℝ) ^ m.factorization x) ε =
              Real.rpow ((p : ℝ) ^ m.factorization p) ε *
                Real.rpow (∏ x ∈ u, ((x : ℝ) ^ m.factorization x)) ε := by
                  rw [ih hu']
          _ = Real.rpow ((p : ℝ) ^ m.factorization p *
                ∏ x ∈ u, ((x : ℝ) ^ m.factorization x)) ε := by
                  exact (Real.mul_rpow (by positivity) (by positivity)).symm
    have hnat : ∏ p ∈ s, p ^ m.factorization p = m := by
      simpa [Nat.prod_factorization_eq_prod_primeFactors] using
        (Nat.prod_factorization_pow_eq_self hm)
    have hcast : ∏ p ∈ s, ((p : ℝ) ^ m.factorization p) = (m : ℝ) := by
      exact_mod_cast hnat
    calc
      (∏ p ∈ s, Real.rpow (p : ℝ) (ε * (m.factorization p : ℝ))) =
          ∏ p ∈ s, Real.rpow ((p : ℝ) ^ m.factorization p) ε := by
        apply Finset.prod_congr rfl
        intro p hp
        exact hterm p hp
      _ = Real.rpow (∏ p ∈ s, ((p : ℝ) ^ m.factorization p)) ε :=
        hprodRpow s hsprime
      _ = Real.rpow (m : ℝ) ε := by rw [hcast]
  rw [heuler]
  calc
    _ ≤ ∏ p ∈ s, (localWeight p *
        Real.rpow (p : ℝ) (ε * (m.factorization p : ℝ))) := hprodLocal
    _ = (∏ p ∈ s, localWeight p) *
        ∏ p ∈ s, Real.rpow (p : ℝ) (ε * (m.factorization p : ℝ)) := hprodSplit
    _ ≤ C₀ ^ P * Real.rpow (m : ℝ) ε := by
      rw [hrpowProduct]
      exact mul_le_mul_of_nonneg_right hsmallProd
        (Real.rpow_nonneg (by exact_mod_cast Nat.zero_le m) ε)

/-- A prime power has exactly one divisor for each exponent from `0` to `k`. -/
theorem card_divisors_prime_pow {p k : ℕ} (hp : p.Prime) :
    (p ^ k).divisors.card = k + 1 := by
  by_cases hk : k = 0
  · subst k
    simp
  · rw [Nat.card_divisors (pow_ne_zero _ hp.ne_zero)]
    rw [Nat.primeFactors_pow p hk]
    simp [hp.factorization_pow, hp.primeFactors]

/-- The Euler product for the divisor function is bounded factorwise by the
corresponding product of powers of two. -/
theorem card_divisors_le_prod_two_pow {n : ℕ} (hn : n ≠ 0) :
    n.divisors.card ≤ ∏ p ∈ n.primeFactors, 2 ^ n.factorization p := by
  rw [Nat.card_divisors hn]
  apply Finset.prod_le_prod₀
  · intro p hp
    positivity
  · intro p hp
    exact succ_le_two_pow (n.factorization p)

/-- For a squarefree positive integer, each prime factor occurs with
exponent one, so its divisor count is exactly two to the number of distinct
prime factors. This converts a lower bound on the number of factors into a
large-divisor-count threshold. -/
theorem card_divisors_eq_two_pow_card_primeFactors_of_squarefree
    {n : ℕ} (hn : Squarefree n) (hn0 : n ≠ 0) :
    n.divisors.card = 2 ^ n.primeFactors.card := by
  rw [Nat.card_divisors hn0]
  calc
    (∏ p ∈ n.primeFactors, (n.factorization p + 1)) =
        ∏ p ∈ n.primeFactors, 2 := by
          apply Finset.prod_congr rfl
          intro p hp
          have hmem := (Nat.mem_primeFactors_of_ne_zero hn0).mp hp
          rw [Nat.factorization_eq_one_of_squarefree hn hmem.1 hmem.2]
    _ = 2 ^ n.primeFactors.card := by simp

/-- A squarefree integer whose prime factors are all at most `B` is at most
`B` raised to the number of its distinct prime factors. This is the elementary
factor-count inequality used to force many divisors for smooth integers. -/
theorem squarefree_le_primeFactorBound_pow
    {n B : ℕ} (hn : Squarefree n) (hB : ∀ p ∈ n.primeFactors, p ≤ B) :
    n ≤ B ^ n.primeFactors.card := by
  calc
    n = ∏ p ∈ n.primeFactors, p :=
      (Nat.prod_primeFactors_of_squarefree hn).symm
    _ ≤ ∏ _p ∈ n.primeFactors, B := by
      apply Finset.prod_le_prod₀
      · intro p hp
        exact Nat.zero_le p
      · intro p hp
        exact hB p hp
    _ = B ^ n.primeFactors.card := by simp

/-- Logarithmic form of the smooth factor-count inequality. It is the
analytic interface used to compare the size of a smooth integer with its
number of distinct prime factors. -/
theorem log_le_card_primeFactors_mul_log_of_squarefree
    {n B : ℕ} (hn : Squarefree n) (hn0 : n ≠ 0) (hB : 1 < B)
    (hFactors : ∀ p ∈ n.primeFactors, p ≤ B) :
    Real.log (n : ℝ) ≤ (n.primeFactors.card : ℝ) * Real.log B := by
  have hsize := squarefree_le_primeFactorBound_pow hn hFactors
  have hsizeR : (n : ℝ) ≤ (B : ℝ) ^ n.primeFactors.card := by
    exact_mod_cast hsize
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hn0)
  have hBpos : (0 : ℝ) < (B : ℝ) := by
    exact_mod_cast (lt_trans Nat.zero_lt_one hB)
  calc
    Real.log (n : ℝ) ≤ Real.log ((B : ℝ) ^ n.primeFactors.card) :=
      Real.log_le_log hnpos hsizeR
    _ = (n.primeFactors.card : ℝ) * Real.log B := by
      rw [Real.log_pow]

/-- A lower bound for the size of a smooth squarefree integer forces a lower
bound for its number of distinct prime factors. -/
theorem card_primeFactors_ge_log_ratio_of_squarefree
    {n B : ℕ} (hn : Squarefree n) (hn0 : n ≠ 0) (hB : 1 < B)
    (hFactors : ∀ p ∈ n.primeFactors, p ≤ B) {A : ℝ}
    (hA : A ≤ Real.log (n : ℝ)) :
    A / Real.log B ≤ (n.primeFactors.card : ℝ) := by
  have hlogB : 0 < Real.log (B : ℝ) := by
    exact Real.log_pos (by exact_mod_cast hB)
  have hfactorLog := log_le_card_primeFactors_mul_log_of_squarefree
    hn hn0 hB hFactors
  apply (div_le_iff₀ hlogB).2
  linarith

/-- For squarefree `n`, a natural lower bound on the number of distinct
prime factors gives the corresponding exponential lower bound on its divisor
count. -/
theorem two_pow_le_card_divisors_of_squarefree
    {n k : ℕ} (hn : Squarefree n) (hn0 : n ≠ 0)
    (hk : k ≤ n.primeFactors.card) :
    2 ^ k ≤ n.divisors.card := by
  rw [card_divisors_eq_two_pow_card_primeFactors_of_squarefree hn hn0]
  exact Nat.pow_le_pow_right (by omega) hk

/-- Real-power form of the smooth divisor-count lower bound. It avoids
rounding the logarithmic factor-count estimate to an integer and can be used
directly as a real threshold in Hua's divisor-moment tail inequality. -/
theorem rpow_two_log_ratio_le_card_divisors_of_squarefree
    {n B : ℕ} (hn : Squarefree n) (hn0 : n ≠ 0) (hB : 1 < B)
    (hFactors : ∀ p ∈ n.primeFactors, p ≤ B) {A : ℝ}
    (hA : A ≤ Real.log (n : ℝ)) :
    Real.rpow 2 (A / Real.log B) ≤ (n.divisors.card : ℝ) := by
  have hfactor := card_primeFactors_ge_log_ratio_of_squarefree
    hn hn0 hB hFactors hA
  have hpow : Real.rpow 2 (A / Real.log B) ≤
      Real.rpow 2 (n.primeFactors.card : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hfactor
  have hdiv := card_divisors_eq_two_pow_card_primeFactors_of_squarefree hn hn0
  calc
    Real.rpow 2 (A / Real.log B) ≤
        Real.rpow 2 (n.primeFactors.card : ℝ) := hpow
    _ = (2 : ℝ) ^ n.primeFactors.card := Real.rpow_natCast 2 _
    _ ≤ (n.divisors.card : ℝ) := by exact_mod_cast hdiv.symm.le

/-- The divisor-counting function is submultiplicative, without a coprimality
assumption. This is the arithmetic step used to iterate Hua's divisor-moment
estimate. -/
theorem card_divisors_mul_le {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    ((m * n).divisors.card : ℕ) ≤ m.divisors.card * n.divisors.card := by
  classical
  rw [Nat.card_divisors (mul_ne_zero hm hn), Nat.primeFactors_mul hm hn,
    Nat.factorization_mul hm hn, Nat.card_divisors hm, Nat.card_divisors hn]
  let A := m.primeFactors
  let B := n.primeFactors
  have hProdM :
      (∏ p ∈ A, (m.factorization p + 1)) =
        ∏ p ∈ A ∪ B, (m.factorization p + 1) := by
    apply Finset.prod_subset_one_on_sdiff Finset.subset_union_left
    · intro p hp
      rcases Finset.mem_sdiff.mp hp with ⟨hpAB, hpnotA⟩
      rcases Finset.mem_union.mp hpAB with hpA | hpB
      · exact (hpnotA hpA).elim
      · have hpdata := Nat.mem_primeFactors.mp hpB
        have hnotdvd : ¬p ∣ m := fun hdiv ↦
          hpnotA (Nat.mem_primeFactors.mpr ⟨hpdata.1, hdiv, hm⟩)
        simp [Nat.factorization_eq_zero_of_not_dvd hnotdvd]
    · intro p hp
      rfl
  have hProdN :
      (∏ p ∈ B, (n.factorization p + 1)) =
        ∏ p ∈ A ∪ B, (n.factorization p + 1) := by
    apply Finset.prod_subset_one_on_sdiff Finset.subset_union_right
    · intro p hp
      rcases Finset.mem_sdiff.mp hp with ⟨hpAB, hpnotB⟩
      rcases Finset.mem_union.mp hpAB with hpA | hpB
      · have hpdata := Nat.mem_primeFactors.mp hpA
        have hnotdvd : ¬p ∣ n := fun hdiv ↦
          hpnotB (Nat.mem_primeFactors.mpr ⟨hpdata.1, hdiv, hn⟩)
        simp [Nat.factorization_eq_zero_of_not_dvd hnotdvd]
      · exact (hpnotB hpB).elim
    · intro p hp
      rfl
  have hlocal (p : ℕ) :
      m.factorization p + n.factorization p + 1 ≤
        (m.factorization p + 1) * (n.factorization p + 1) := by
    nlinarith [Nat.zero_le (m.factorization p * n.factorization p)]
  calc
    _ ≤ ∏ p ∈ A ∪ B,
        (m.factorization p + 1) * (n.factorization p + 1) := by
          apply Finset.prod_le_prod₀
          · intro p hp
            positivity
          · intro p hp
            exact hlocal p
    _ = (∏ p ∈ A ∪ B, (m.factorization p + 1)) *
        ∏ p ∈ A ∪ B, (n.factorization p + 1) := by
          rw [Finset.prod_mul_distrib]
    _ = (∏ p ∈ A, (m.factorization p + 1)) *
        ∏ p ∈ B, (n.factorization p + 1) := by rw [← hProdM, ← hProdN]

/-- Pointwise convolution inequality for a positive divisor moment. Each
factorization `n = d * (n / d)` contributes at least
`d(n)^(t-1)`, by submultiplicativity of the divisor count. Summing over the
`d(n)` divisors gives the `t`th power. This is the local recurrence behind
Hua's averaged divisor-moment lemma. -/
theorem card_divisors_pow_le_divisorSum {n t : ℕ} (hn : n ≠ 0) (ht : 0 < t) :
    n.divisors.card ^ t ≤
      ∑ d ∈ n.divisors,
        d.divisors.card ^ (t - 1) * (n / d).divisors.card ^ (t - 1) := by
  classical
  let D := n.divisors.card
  have hsum :
      (∑ d ∈ n.divisors, D ^ (t - 1)) ≤
        ∑ d ∈ n.divisors,
          d.divisors.card ^ (t - 1) * (n / d).divisors.card ^ (t - 1) := by
    apply Finset.sum_le_sum
    intro d hd
    have hdiv := Nat.mem_divisors.mp hd
    have hdne : d ≠ 0 := by
      intro heq
      subst d
      simp at hdiv
    have hdq : d * (n / d) = n := Nat.mul_div_cancel' hdiv.1
    have hqne : n / d ≠ 0 := by
      intro hq
      rw [hq, Nat.mul_zero] at hdq
      exact hn hdq.symm
    have hmul := card_divisors_mul_le hdne hqne
    rw [hdq] at hmul
    have hpow := Nat.pow_le_pow_left hmul (t - 1)
    simpa [D, Nat.mul_pow] using hpow
  have hsumEq : (∑ d ∈ n.divisors, D ^ (t - 1)) = D ^ t := by
    calc
      (∑ d ∈ n.divisors, D ^ (t - 1)) = D * D ^ (t - 1) := by
        simp [D, Finset.sum_const]
      _ = D ^ (t - 1) * D := Nat.mul_comm _ _
      _ = D ^ ((t - 1) + 1) := by rw [Nat.pow_succ]
      _ = D ^ t := by rw [Nat.sub_add_cancel ht]
  rw [← hsumEq]
  exact hsum

/-- Summing a product over divisor factorizations is bounded by the full
product of the two finite sums. The proof reindexes the disjoint
divisor-antidiagonals and then enlarges their union to the rectangle. -/
theorem sum_divisorAntidiagonal_le_product {M : ℕ} (g : ℕ → ℝ)
    (hg : ∀ n ∈ Finset.Icc 1 M, 0 ≤ g n) :
    (∑ n ∈ Finset.Icc 1 M,
      ∑ z ∈ n.divisorsAntidiagonal, g z.1 * g z.2) ≤
        (∑ n ∈ Finset.Icc 1 M, g n) *
          (∑ n ∈ Finset.Icc 1 M, g n) := by
  classical
  let I := Finset.Icc 1 M
  let S := I.biUnion fun n => n.divisorsAntidiagonal
  have hdisj : (↑I : Set ℕ).PairwiseDisjoint fun n => n.divisorsAntidiagonal := by
    intro n hn m hm hnm
    simp only [Finset.mem_coe] at hn hm
    apply Finset.disjoint_left.mpr
    intro z hzn hzm
    have hprodn := (Nat.mem_divisorsAntidiagonal.mp hzn).1
    have hprodm := (Nat.mem_divisorsAntidiagonal.mp hzm).1
    exact hnm (by omega)
  have hsub : S ⊆ I ×ˢ I := by
    intro z hz
    rcases Finset.mem_biUnion.mp hz with ⟨n, hn, hzn⟩
    have hprod := (Nat.mem_divisorsAntidiagonal.mp hzn).1
    have hnI := Finset.mem_Icc.mp hn
    have hz1 : 0 < z.1 := by
      by_contra hnot
      have hz0 : z.1 = 0 := Nat.eq_zero_of_not_pos hnot
      simp [hz0] at hprod
      omega
    have hz2 : 0 < z.2 := by
      by_contra hnot
      have hz0 : z.2 = 0 := Nat.eq_zero_of_not_pos hnot
      simp [hz0] at hprod
      omega
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_Icc.mpr
      constructor
      · exact hz1
      · calc
          z.1 ≤ z.1 * z.2 := Nat.le_mul_of_pos_right _ hz2
          _ = n := hprod
          _ ≤ M := hnI.2
    · apply Finset.mem_Icc.mpr
      constructor
      · exact hz2
      · calc
          z.2 ≤ z.1 * z.2 := Nat.le_mul_of_pos_left _ hz1
          _ = n := hprod
          _ ≤ M := hnI.2
  have hnonneg : ∀ z ∈ I ×ˢ I, 0 ≤ g z.1 * g z.2 := by
    intro z hz
    have hz' := Finset.mem_product.mp hz
    exact mul_nonneg (hg z.1 hz'.1) (hg z.2 hz'.2)
  calc
    (∑ n ∈ Finset.Icc 1 M,
      ∑ z ∈ n.divisorsAntidiagonal, g z.1 * g z.2) =
        ∑ z ∈ S, g z.1 * g z.2 := by
          dsimp [S, I]
          symm
          exact Finset.sum_biUnion hdisj
    _ ≤ ∑ z ∈ I ×ˢ I, g z.1 * g z.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by
        intro z hz _
        exact hnonneg z hz)
    _ = (∑ n ∈ I, g n) * (∑ n ∈ I, g n) := by
      rw [Finset.sum_product]
      symm
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mul_sum]

/-- Exact product-triangle reindexing for divisor antidiagonals. The pairs
with product at most `M` are grouped by their first coordinate, leaving the
second coordinate in `1..M/a`. -/
theorem sum_divisorAntidiagonal_eq_triangle {M : ℕ} (F : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 M,
      ∑ z ∈ n.divisorsAntidiagonal, F z.1 * F z.2) =
        ∑ a ∈ Finset.Icc 1 M,
          F a * (∑ b ∈ Finset.Icc 1 (M / a), F b) := by
  classical
  let I := Finset.Icc 1 M
  let pairEmb (a : ℕ) : ℕ ↪ ℕ × ℕ :=
    ⟨fun b => (a, b), fun b c h => congrArg Prod.snd h⟩
  let S := I.biUnion fun n => n.divisorsAntidiagonal
  let T := I.biUnion fun a =>
    (Finset.Icc 1 (M / a)).map (pairEmb a)
  have hST : S = T := by
    ext z
    constructor
    · intro hz
      rcases Finset.mem_biUnion.mp hz with ⟨n, hn, hzn⟩
      have hprod := (Nat.mem_divisorsAntidiagonal.mp hzn).1
      have hnI := Finset.mem_Icc.mp hn
      have hz1 : 0 < z.1 := by
        by_contra hnot
        have hz0 : z.1 = 0 := Nat.eq_zero_of_not_pos hnot
        simp [hz0] at hprod
        omega
      have hz2 : 0 < z.2 := by
        by_contra hnot
        have hz0 : z.2 = 0 := Nat.eq_zero_of_not_pos hnot
        simp [hz0] at hprod
        omega
      have hprodLe : z.1 * z.2 ≤ M := by rw [hprod]; exact hnI.2
      have hz1Le : z.1 ≤ M := by
        calc
          z.1 ≤ z.1 * z.2 := Nat.le_mul_of_pos_right _ hz2
          _ ≤ M := hprodLe
      have hz2Le : z.2 ≤ M / z.1 :=
        (Nat.le_div_iff_mul_le hz1).2 (by simpa [Nat.mul_comm] using hprodLe)
      apply Finset.mem_biUnion.mpr
      refine ⟨z.1, Finset.mem_Icc.mpr ⟨hz1, hz1Le⟩, ?_⟩
      apply Finset.mem_map.mpr
      refine ⟨z.2, Finset.mem_Icc.mpr ⟨hz2, hz2Le⟩, ?_⟩
      rfl
    · intro hz
      rcases Finset.mem_biUnion.mp hz with ⟨a, ha, hza⟩
      rcases Finset.mem_map.mp hza with ⟨b, hb, habEq⟩
      have haI := Finset.mem_Icc.mp ha
      have hbI := Finset.mem_Icc.mp hb
      have hprodLe : a * b ≤ M := by
        have h := (Nat.le_div_iff_mul_le haI.1).1 hbI.2
        simpa [Nat.mul_comm] using h
      have hprodPos : 0 < a * b := Nat.mul_pos haI.1 hbI.1
      have hprodI : a * b ∈ I :=
        Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hprodPos.ne', hprodLe⟩
      rw [← habEq]
      apply Finset.mem_biUnion.mpr
      refine ⟨a * b, hprodI, ?_⟩
      exact Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, hprodPos.ne'⟩
  have hdisj :
      (↑I : Set ℕ).PairwiseDisjoint fun a =>
        (Finset.Icc 1 (M / a)).map (pairEmb a) := by
    intro a ha a' ha' haa
    simp only [Finset.mem_coe] at ha ha'
    apply Finset.disjoint_left.mpr
    intro z hza hza'
    rcases Finset.mem_map.mp hza with ⟨b, hb, rfl⟩
    rcases Finset.mem_map.mp hza' with ⟨b', hb', heq⟩
    exact haa (congrArg Prod.fst heq).symm
  calc
    (∑ n ∈ Finset.Icc 1 M,
      ∑ z ∈ n.divisorsAntidiagonal, F z.1 * F z.2) =
        ∑ z ∈ S, F z.1 * F z.2 := by
          dsimp [S, I]
          symm
          exact Finset.sum_biUnion (s := Finset.Icc 1 M)
            (t := fun n => n.divisorsAntidiagonal)
            (f := fun z => F z.1 * F z.2)
            (by
              intro n hn m hm hnm
              simp only [Finset.mem_coe] at hn hm
              apply Finset.disjoint_left.mpr
              intro z hzn hzm
              have hprod₁ := (Nat.mem_divisorsAntidiagonal.mp hzn).1
              have hprod₂ := (Nat.mem_divisorsAntidiagonal.mp hzm).1
              exact hnm (by omega))
    _ = ∑ z ∈ T, F z.1 * F z.2 := by rw [hST]
    _ = ∑ a ∈ I, ∑ b ∈ Finset.Icc 1 (M / a), F a * F b := by
          dsimp [T]
          rw [Finset.sum_biUnion hdisj]
          simp_rw [Finset.sum_map]
          rfl
    _ = ∑ a ∈ I, F a * (∑ b ∈ Finset.Icc 1 (M / a), F b) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [← Finset.mul_sum]

/-- Dividing the divisor convolution by `n` converts it into the product of
the two corresponding harmonic weights on the divisor antidiagonal. -/
theorem sum_divisorConvolution_div_eq_antidiagonal {n k : ℕ} (hn : n ≠ 0) :
    (∑ d ∈ n.divisors,
      (d.divisors.card : ℝ) ^ k * ((n / d).divisors.card : ℝ) ^ k) / n =
        ∑ z ∈ n.divisorsAntidiagonal,
          (((z.1.divisors.card : ℝ) ^ k / z.1) *
            ((z.2.divisors.card : ℝ) ^ k / z.2)) := by
  classical
  rw [Nat.sum_divisorsAntidiagonal (fun a b =>
    ((a.divisors.card : ℝ) ^ k / a) * ((b.divisors.card : ℝ) ^ k / b))]
  rw [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  have hdiv := Nat.mem_divisors.mp hd
  have hdne : d ≠ 0 := by
    intro heq
    subst d
    simp at hdiv
  have hmul : d * (n / d) = n := Nat.mul_div_cancel' hdiv.1
  have hqne : n / d ≠ 0 := by
    intro hq
    rw [hq, Nat.mul_zero] at hmul
    exact hn hmul.symm
  have hcast : (d : ℝ) * ((n / d : ℕ) : ℝ) = n := by exact_mod_cast hmul
  rw [← hcast]
  field_simp [Nat.cast_ne_zero.mpr hdne, Nat.cast_ne_zero.mpr hqne]

/-- The weighted divisor-moment recurrence underlying Hua's Lemma 2.4:
the `t`th harmonic moment is at most the square of the preceding one. -/
theorem divisorHarmonicMoment_le_square {M t : ℕ} (ht : 0 < t) :
    (∑ n ∈ Finset.Icc 1 M,
      (n.divisors.card : ℝ) ^ t / n) ≤
      (∑ n ∈ Finset.Icc 1 M,
        (n.divisors.card : ℝ) ^ (t - 1) / n) ^ 2 := by
  classical
  let I := Finset.Icc 1 M
  let g : ℕ → ℝ := fun n => (n.divisors.card : ℝ) ^ (t - 1) / n
  have hg : ∀ n ∈ I, 0 ≤ g n := by
    intro n hn
    dsimp [g]
    positivity
  have hpoint : ∀ n ∈ I,
      (n.divisors.card : ℝ) ^ t / n ≤
        ∑ z ∈ n.divisorsAntidiagonal, g z.1 * g z.2 := by
    intro n hn
    have hnI := Finset.mem_Icc.mp hn
    have hnpos : n ≠ 0 := by omega
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hnpos)
    have hnat := card_divisors_pow_le_divisorSum hnpos ht
    have hreal : (n.divisors.card ^ t : ℝ) ≤
        ∑ d ∈ n.divisors,
          (d.divisors.card : ℝ) ^ (t - 1) *
            ((n / d).divisors.card : ℝ) ^ (t - 1) := by
      exact_mod_cast hnat
    have hdiv := div_le_div_of_nonneg_right hreal hnreal.le
    rw [sum_divisorConvolution_div_eq_antidiagonal hnpos] at hdiv
    simpa [g] using hdiv
  have hsum :
      (∑ n ∈ I, (n.divisors.card : ℝ) ^ t / n) ≤
        ∑ n ∈ I, ∑ z ∈ n.divisorsAntidiagonal, g z.1 * g z.2 :=
    Finset.sum_le_sum fun n hn => hpoint n hn
  calc
    (∑ n ∈ Finset.Icc 1 M, (n.divisors.card : ℝ) ^ t / n) ≤
        ∑ n ∈ I, ∑ z ∈ n.divisorsAntidiagonal, g z.1 * g z.2 := by
          simpa [I] using hsum
    _ ≤ (∑ n ∈ I, g n) * (∑ n ∈ I, g n) :=
      sum_divisorAntidiagonal_le_product g hg
    _ = (∑ n ∈ Finset.Icc 1 M,
          (n.divisors.card : ℝ) ^ (t - 1) / n) ^ 2 := by
          simp [I, g, pow_two]

/-- The harmonic moment of the divisor function, with the zero-th moment
equal to the ordinary harmonic sum. -/
noncomputable def divisorHarmonicMoment (M t : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 M, (n.divisors.card : ℝ) ^ t / n

theorem divisorHarmonicMoment_zero (M : ℕ) :
    divisorHarmonicMoment M 0 = (harmonic M : ℝ) := by
  simp [divisorHarmonicMoment, harmonic_eq_sum_Icc, Rat.cast_sum,
    Rat.cast_inv, Rat.cast_natCast]

/-- Iterating the source's harmonic-moment recurrence gives the explicit
logarithmic envelope `(1 + log M)^(2^t)`. -/
theorem divisorHarmonicMoment_le_one_add_log_pow (M t : ℕ) :
    divisorHarmonicMoment M t ≤
      (1 + Real.log (M : ℝ)) ^ (2 ^ t) := by
  have hlog : 0 ≤ 1 + Real.log (M : ℝ) := by
    by_cases hM : M = 0
    · simp [hM]
    · have hMone : (1 : ℝ) ≤ M := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hM)
      have h := Real.log_nonneg hMone
      linarith
  induction t with
  | zero =>
      rw [divisorHarmonicMoment_zero]
      simpa using harmonic_le_one_add_log M
  | succ t ih =>
      have hrec : divisorHarmonicMoment M (t + 1) ≤
          (divisorHarmonicMoment M t) ^ 2 := by
        simpa [divisorHarmonicMoment] using
          divisorHarmonicMoment_le_square (M := M) (t := t + 1) (by omega)
      have hmoment_nonneg : 0 ≤ divisorHarmonicMoment M t := by
        unfold divisorHarmonicMoment
        apply Finset.sum_nonneg
        intro n hn
        positivity
      have hmajor_nonneg :
          0 ≤ (1 + Real.log (M : ℝ)) ^ (2 ^ t) := pow_nonneg hlog _
      calc
        divisorHarmonicMoment M (t + 1) ≤
            (divisorHarmonicMoment M t) ^ 2 := hrec
        _ ≤ ((1 + Real.log (M : ℝ)) ^ (2 ^ t)) ^ 2 :=
          (sq_le_sq₀ hmoment_nonneg hmajor_nonneg).2 ih
        _ = (1 + Real.log (M : ℝ)) ^ (2 ^ (t + 1)) := by
          rw [Nat.pow_succ, ← pow_mul]

/-- Hua's unweighted divisor moment, with the logarithmic envelope
`1+log M`. The induction uses the product-triangle reindexing and the
weighted harmonic moment proved above. -/
noncomputable def divisorUnweightedMoment (M t : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 M, (n.divisors.card : ℝ) ^ t

theorem divisorUnweightedMoment_le_envelope (M t : ℕ) :
    divisorUnweightedMoment M t ≤
      (M : ℝ) * (1 + Real.log (M : ℝ)) ^ (2 ^ t - 1) := by
  induction t generalizing M with
  | zero =>
      simp [divisorUnweightedMoment, Finset.sum_const, Nat.card_Icc]
  | succ t ih =>
      by_cases hMzero : M = 0
      · simp [divisorUnweightedMoment, hMzero]
      · have hMpos : 0 < M := Nat.pos_of_ne_zero hMzero
        let I := Finset.Icc 1 M
        let F : ℕ → ℝ := fun n => (n.divisors.card : ℝ) ^ t
        let H : ℝ := 1 + Real.log (M : ℝ)
        have hH : 0 ≤ H := by
          dsimp [H]
          have hMone : (1 : ℝ) ≤ M := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hMzero)
          linarith [Real.log_nonneg hMone]
        have hpoint : ∀ n ∈ I,
            (n.divisors.card : ℝ) ^ (t + 1) ≤
              ∑ z ∈ n.divisorsAntidiagonal, F z.1 * F z.2 := by
          intro n hn
          have hnI := Finset.mem_Icc.mp hn
          have hnpos : n ≠ 0 := by omega
          have hnat := card_divisors_pow_le_divisorSum hnpos (by omega : 0 < t + 1)
          have hreal : (n.divisors.card ^ (t + 1) : ℝ) ≤
              ∑ d ∈ n.divisors,
                (d.divisors.card : ℝ) ^ t *
                  ((n / d).divisors.card : ℝ) ^ t := by
            exact_mod_cast hnat
          have hanti :
              (∑ z ∈ n.divisorsAntidiagonal, F z.1 * F z.2) =
                ∑ d ∈ n.divisors,
                  (d.divisors.card : ℝ) ^ t *
                    ((n / d).divisors.card : ℝ) ^ t := by
            simpa [F] using
              (Nat.sum_divisorsAntidiagonal (fun a b =>
                (a.divisors.card : ℝ) ^ t * (b.divisors.card : ℝ) ^ t))
          exact hreal.trans_eq hanti.symm
        have hpointSum :
            divisorUnweightedMoment M (t + 1) ≤
              ∑ n ∈ I, ∑ z ∈ n.divisorsAntidiagonal, F z.1 * F z.2 := by
          unfold divisorUnweightedMoment
          simpa [I] using
            (Finset.sum_le_sum fun n hn => hpoint n hn)
        have htriangle :
            (∑ n ∈ I, ∑ z ∈ n.divisorsAntidiagonal, F z.1 * F z.2) =
              ∑ a ∈ I, F a * (∑ b ∈ Finset.Icc 1 (M / a), F b) := by
          simpa [I] using (sum_divisorAntidiagonal_eq_triangle (M := M) F)
        have hinner : ∀ a ∈ I,
            (∑ b ∈ Finset.Icc 1 (M / a), F b) ≤
              (M / a : ℝ) * H ^ (2 ^ t - 1) := by
          intro a ha
          have haI := Finset.mem_Icc.mp ha
          have haRealPos : 0 < (a : ℝ) := by exact_mod_cast haI.1
          have hquotOne : 1 ≤ M / a :=
            (Nat.le_div_iff_mul_le haI.1).2 (by simpa using haI.2)
          have hquotLe : M / a ≤ M := Nat.div_le_self _ _
          have hIH := ih (M / a)
          have hIH' :
              (∑ b ∈ Finset.Icc 1 (M / a), F b) ≤
                ((M / a : ℕ) : ℝ) *
                  (1 + Real.log ((M / a : ℕ) : ℝ)) ^ (2 ^ t - 1) := by
            simpa [divisorUnweightedMoment, F] using hIH
          have hquotCastPos : 0 < ((M / a : ℕ) : ℝ) := by
            exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hquotOne)
          have hquotCastLe : ((M / a : ℕ) : ℝ) ≤ (M : ℝ) := by
            exact_mod_cast hquotLe
          have hMRealPos : 0 < (M : ℝ) := by exact_mod_cast hMpos
          have hlogLe : Real.log ((M / a : ℕ) : ℝ) ≤ Real.log (M : ℝ) :=
            Real.strictMonoOn_log.monotoneOn
              (Set.mem_Ioi.mpr hquotCastPos)
              (Set.mem_Ioi.mpr hMRealPos)
              hquotCastLe
          have hlogEnvelopeLe :
              1 + Real.log ((M / a : ℕ) : ℝ) ≤ 1 + Real.log (M : ℝ) := by
            linarith
          have hHquot : 0 ≤ 1 + Real.log ((M / a : ℕ) : ℝ) := by
            have h := Real.log_nonneg
              (show (1 : ℝ) ≤ ((M / a : ℕ) : ℝ) by exact_mod_cast hquotOne)
            linarith
          have hpowCast :
              (1 + Real.log ((M / a : ℕ) : ℝ)) ^ (2 ^ t - 1) ≤
                H ^ (2 ^ t - 1) := by
            dsimp [H]
            exact pow_le_pow_left₀ hHquot hlogEnvelopeLe _
          have hdivNat : ((M / a : ℕ) : ℝ) ≤ (M : ℝ) / a := by
            apply (le_div_iff₀ haRealPos).2
            exact_mod_cast Nat.div_mul_le_self M a
          calc
            (∑ b ∈ Finset.Icc 1 (M / a), F b) ≤
                ((M / a : ℕ) : ℝ) *
                  (1 + Real.log ((M / a : ℕ) : ℝ)) ^ (2 ^ t - 1) := hIH'
            _ ≤ ((M / a : ℕ) : ℝ) * H ^ (2 ^ t - 1) :=
              mul_le_mul_of_nonneg_left hpowCast (by positivity)
            _ ≤ ((M : ℝ) / a) * H ^ (2 ^ t - 1) :=
              mul_le_mul_of_nonneg_right hdivNat (pow_nonneg hH _)
        have htriangleBound :
            (∑ a ∈ I, F a * (∑ b ∈ Finset.Icc 1 (M / a), F b)) ≤
              ∑ a ∈ I, F a * (((M : ℝ) / a) * H ^ (2 ^ t - 1)) := by
          apply Finset.sum_le_sum
          intro a ha
          exact mul_le_mul_of_nonneg_left (hinner a ha) (by positivity)
        have hfactor :
            (∑ a ∈ I, F a * (((M : ℝ) / a) * H ^ (2 ^ t - 1))) =
              ((M : ℝ) * H ^ (2 ^ t - 1)) * divisorHarmonicMoment M t := by
          calc
            _ = ∑ a ∈ I,
                ((M : ℝ) * H ^ (2 ^ t - 1)) * (F a / a) := by
                  apply Finset.sum_congr rfl
                  intro a ha
                  have haPos : a ≠ 0 := by
                    have := Finset.mem_Icc.mp ha
                    omega
                  field_simp [Nat.cast_ne_zero.mpr haPos]
            _ = ((M : ℝ) * H ^ (2 ^ t - 1)) *
                (∑ a ∈ I, F a / a) := by rw [Finset.mul_sum]
            _ = ((M : ℝ) * H ^ (2 ^ t - 1)) * divisorHarmonicMoment M t := by
                  simp [divisorHarmonicMoment, I, F]
        have hW := divisorHarmonicMoment_le_one_add_log_pow M t
        have hWnonneg : 0 ≤ divisorHarmonicMoment M t := by
          unfold divisorHarmonicMoment
          apply Finset.sum_nonneg
          intro n hn
          positivity
        have hfactorNonneg : 0 ≤ (M : ℝ) * H ^ (2 ^ t - 1) :=
          mul_nonneg (by positivity) (pow_nonneg hH _)
        have hexp : (2 ^ t - 1) + 2 ^ t = 2 ^ (t + 1) - 1 := by
          rw [Nat.pow_succ]
          omega
        calc
          divisorUnweightedMoment M (t + 1) ≤
              ∑ n ∈ I, ∑ z ∈ n.divisorsAntidiagonal, F z.1 * F z.2 := hpointSum
          _ = ∑ a ∈ I, F a * (∑ b ∈ Finset.Icc 1 (M / a), F b) := htriangle
          _ ≤ ∑ a ∈ I, F a * (((M : ℝ) / a) * H ^ (2 ^ t - 1)) := htriangleBound
          _ = ((M : ℝ) * H ^ (2 ^ t - 1)) * divisorHarmonicMoment M t := hfactor
          _ ≤ ((M : ℝ) * H ^ (2 ^ t - 1)) * H ^ (2 ^ t) :=
            mul_le_mul_of_nonneg_left hW hfactorNonneg
          _ = (M : ℝ) * (H ^ (2 ^ t - 1) * H ^ (2 ^ t)) := by ring
          _ = (M : ℝ) * H ^ ((2 ^ t - 1) + 2 ^ t) := by rw [← pow_add]
          _ = (M : ℝ) * H ^ (2 ^ (t + 1) - 1) := by rw [hexp]

/-- A thresholded nonnegative weight is controlled by its cubic moment.

This is the finite-sum mechanism behind Hua's Lemma 6.1: on the exceptional
set, `T ≤ C * f`, so `T^2 * f ≤ C^2 * f^3`. The cubic moment estimate needed
to apply this lemma to divisor counts is a separate arithmetic input. -/
theorem thresholded_sum_le_cubic_moment {α : Type*} [DecidableEq α]
    (s : Finset α) (P : α → Prop) [DecidablePred P]
    (f : α → ℝ) (T C : ℝ)
    (hT : 0 < T) (hC : 0 ≤ C)
    (hf : ∀ a ∈ s, 0 ≤ f a)
    (hthreshold : ∀ a ∈ s, P a → T ≤ C * f a) :
    T ^ 2 * (∑ a ∈ s.filter P, f a) ≤
      C ^ 2 * (∑ a ∈ s, f a ^ 3) := by
  have hpoint : ∀ a ∈ s.filter P,
      T ^ 2 * f a ≤ C ^ 2 * f a ^ 3 := by
    intro a ha
    have has := Finset.mem_filter.mp ha
    have hfa := hf a (Finset.mem_filter.mp ha |>.1)
    have hlarge := hthreshold a has.1 has.2
    have hCfa : 0 ≤ C * f a := mul_nonneg hC hfa
    have hsq : T ^ 2 ≤ (C * f a) ^ 2 :=
      (sq_le_sq₀ hT.le hCfa).2 hlarge
    calc
      T ^ 2 * f a ≤ (C * f a) ^ 2 * f a :=
        mul_le_mul_of_nonneg_right hsq hfa
      _ = C ^ 2 * f a ^ 3 := by ring
  calc
    T ^ 2 * (∑ a ∈ s.filter P, f a) =
        ∑ a ∈ s.filter P, T ^ 2 * f a := by rw [Finset.mul_sum]
    _ ≤ ∑ a ∈ s.filter P, C ^ 2 * f a ^ 3 :=
      Finset.sum_le_sum fun a ha => hpoint a ha
    _ = C ^ 2 * (∑ a ∈ s.filter P, f a ^ 3) := by rw [Finset.mul_sum]
    _ ≤ C ^ 2 * (∑ a ∈ s, f a ^ 3) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg C)
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro a ha hnot
      exact pow_nonneg (hf a ha) 3

/-- The divisor-count specialization of Hua's exceptional-set tail bound.
The threshold controls the exceptional weighted mass by the seventh-log
divisor moment supplied by the unweighted Hua Lemma 2.5 estimate. -/
theorem divisorThresholdedTail_le {M : ℕ} (P : ℕ → Prop) [DecidablePred P]
    (T C : ℝ) (hT : 0 < T) (hC : 0 ≤ C)
    (hthreshold : ∀ n ∈ Finset.Icc 1 M, P n →
      T ≤ C * (n.divisors.card : ℝ)) :
    T ^ 2 * (∑ n ∈ (Finset.Icc 1 M).filter P, (n.divisors.card : ℝ)) ≤
      C ^ 2 * (M : ℝ) * (1 + Real.log (M : ℝ)) ^ 7 := by
  have hmoment :
      (∑ n ∈ Finset.Icc 1 M, (n.divisors.card : ℝ) ^ 3) ≤
        (M : ℝ) * (1 + Real.log (M : ℝ)) ^ 7 := by
    simpa [divisorUnweightedMoment] using
      (divisorUnweightedMoment_le_envelope M 3)
  calc
    T ^ 2 * (∑ n ∈ (Finset.Icc 1 M).filter P, (n.divisors.card : ℝ)) ≤
        C ^ 2 * (∑ n ∈ Finset.Icc 1 M, (n.divisors.card : ℝ) ^ 3) :=
      thresholded_sum_le_cubic_moment
        (s := Finset.Icc 1 M) P (fun n => (n.divisors.card : ℝ)) T C
        hT hC (by
          intro n hn
          positivity) hthreshold
    _ ≤ C ^ 2 * ((M : ℝ) * (1 + Real.log (M : ℝ)) ^ 7) :=
      mul_le_mul_of_nonneg_left hmoment (sq_nonneg C)
    _ = C ^ 2 * (M : ℝ) * (1 + Real.log (M : ℝ)) ^ 7 := by ring

/-- Hua's smooth-large-divisor exceptional-set bound, with the source
conditions exposed explicitly. Any squarefree `n≤M` whose prime factors are
at most `B` and whose size satisfies `A≤log n` has divisor count at least
`2^(A/log B)`. The resulting weighted sum is charged to the existing cubic
divisor moment. -/
theorem smoothSquarefree_divisorTail_le {M B : ℕ} (hB : 1 < B) {A : ℝ} :
    (Real.rpow 2 (A / Real.log B)) ^ 2 *
      (∑ n ∈ (Finset.Icc 1 M).filter (fun n : ℕ => Squarefree n ∧ n ≠ 0 ∧
        (∀ p ∈ n.primeFactors, p ≤ B) ∧ A ≤ Real.log (n : ℝ)),
        (n.divisors.card : ℝ)) ≤
      (M : ℝ) * (1 + Real.log (M : ℝ)) ^ 7 := by
  classical
  let P : ℕ → Prop := fun n => Squarefree n ∧ n ≠ 0 ∧
    (∀ p ∈ n.primeFactors, p ≤ B) ∧ A ≤ Real.log (n : ℝ)
  have hT : 0 < Real.rpow 2 (A / Real.log B) :=
    Real.rpow_pos_of_pos (by norm_num) _
  simpa [P] using
    (divisorThresholdedTail_le (M := M) P
      (Real.rpow 2 (A / Real.log B)) 1 hT (by norm_num) (by
        intro n hn hnP
        rcases hnP with ⟨hsq, hn0, hFactors, hA⟩
        have hdiv := rpow_two_log_ratio_le_card_divisors_of_squarefree
          hsq hn0 hB hFactors hA
        simpa using hdiv))

/-- The divisor threshold produced by the smooth factor-count argument
eventually dominates every fixed logarithmic power. The exponent `L/log L`
grows faster than `log L`; this is the analytic absorption step needed to
turn the generic smooth-set tail into an arbitrarily strong log saving. -/
theorem eventually_log_pow_le_rpow_two_log_ratio {C K : ℝ}
    (hC : 0 < C) (hK : 0 ≤ K) :
    ∀ᶠ L : ℝ in Filter.atTop,
      1 < L ∧ L ^ K ≤
        (2 : ℝ) ^ (L / (C * Real.log L)) := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let D : ℝ := 16 * C * K / Real.log 2
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  have hroot : ∀ᶠ L : ℝ in Filter.atTop, D ≤ Real.rpow L (1 / 2 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually
      (Filter.eventually_atTop.2 ⟨D, fun _ h => h⟩)
  have hlarge : ∀ᶠ L : ℝ in Filter.atTop, (1 : ℝ) < L :=
    Filter.eventually_gt_atTop (1 : ℝ)
  filter_upwards [hlarge, hroot] with L hL hroot
  have hLpos : 0 < L := lt_trans zero_lt_one hL
  have hlogL : 0 < Real.log L := Real.log_pos hL
  have hlogLnonneg : 0 ≤ Real.log L := le_of_lt hlogL
  have hlogBound : Real.log L ≤ 4 * Real.rpow L (1 / 4 : ℝ) := by
    calc
      Real.log L ≤ Real.rpow L (1 / 4 : ℝ) / (1 / 4 : ℝ) :=
        Real.log_le_rpow_div hLpos.le (by norm_num)
      _ = 4 * Real.rpow L (1 / 4 : ℝ) := by ring
  have hpowSq : (Real.rpow L (1 / 4 : ℝ)) ^ 2 = Real.rpow L (1 / 2 : ℝ) := by
    calc
      (Real.rpow L (1 / 4 : ℝ)) ^ 2 =
          Real.rpow L (1 / 4 : ℝ) * Real.rpow L (1 / 4 : ℝ) := by rw [pow_two]
      _ = Real.rpow L ((1 / 4 : ℝ) + 1 / 4) :=
        (Real.rpow_add hLpos _ _).symm
      _ = Real.rpow L (1 / 2 : ℝ) := by congr 1; norm_num
  have hlogSq : (Real.log L) ^ 2 ≤ 16 * Real.rpow L (1 / 2 : ℝ) := by
    calc
      (Real.log L) ^ 2 ≤ (4 * Real.rpow L (1 / 4 : ℝ)) ^ 2 := by
        nlinarith [sq_nonneg (Real.log L), Real.rpow_nonneg hLpos.le (1 / 4 : ℝ)]
      _ = 16 * Real.rpow L (1 / 2 : ℝ) := by
        calc
          _ = 16 * (Real.rpow L (1 / 4 : ℝ)) ^ 2 := by ring
          _ = 16 * Real.rpow L (1 / 2 : ℝ) := by rw [hpowSq]
  have hDlog : D * Real.log 2 = 16 * C * K := by
    dsimp [D]
    field_simp [ne_of_gt hlog2]
  have hrootNonneg : 0 ≤ Real.rpow L (1 / 2 : ℝ) :=
    Real.rpow_nonneg hLpos.le _
  have hpowHalfSq : (Real.rpow L (1 / 2 : ℝ)) ^ 2 = L := by
    calc
      (Real.rpow L (1 / 2 : ℝ)) ^ 2 =
          Real.rpow L (1 / 2 : ℝ) * Real.rpow L (1 / 2 : ℝ) := by rw [pow_two]
      _ = Real.rpow L ((1 / 2 : ℝ) + 1 / 2) :=
        (Real.rpow_add hLpos _ _).symm
      _ = L := by norm_num [Real.rpow_one]
  have hscale := mul_le_mul_of_nonneg_right hroot
    (mul_nonneg hlog2.le hrootNonneg)
  have hsource : 16 * C * K * Real.rpow L (1 / 2 : ℝ) ≤
      Real.log 2 * L := by
    calc
      16 * C * K * Real.rpow L (1 / 2 : ℝ) =
          (D * Real.log 2) * Real.rpow L (1 / 2 : ℝ) := by rw [hDlog]
      _ = D * (Real.log 2 * Real.rpow L (1 / 2 : ℝ)) := by ring
      _ ≤ Real.rpow L (1 / 2 : ℝ) *
          (Real.log 2 * Real.rpow L (1 / 2 : ℝ)) := hscale
      _ = Real.log 2 * ((Real.rpow L (1 / 2 : ℝ)) ^ 2) := by ring
      _ = Real.log 2 * L := by rw [hpowHalfSq]
  have hkey : C * K * (Real.log L) ^ 2 ≤ Real.log 2 * L := by
    calc
      C * K * (Real.log L) ^ 2 ≤ C * K *
          (16 * Real.rpow L (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogSq (mul_nonneg hC.le hK)
      _ = 16 * C * K * Real.rpow L (1 / 2 : ℝ) := by ring
      _ ≤ Real.log 2 * L := hsource
  have hexponent' : K * Real.log L ≤ (L * Real.log 2) / (C * Real.log L) := by
    apply (le_div_iff₀ (mul_pos hC hlogL)).2
    nlinarith [hkey]
  have hexponent : K * Real.log L ≤ L / (C * Real.log L) * Real.log 2 := by
    calc
      K * Real.log L ≤ (L * Real.log 2) / (C * Real.log L) := hexponent'
      _ = L / (C * Real.log L) * Real.log 2 := by ring
  have hleftpos : 0 < L ^ K :=
    Real.rpow_pos_of_pos hLpos K
  have hrightpos : 0 < (2 : ℝ) ^ (L / (C * Real.log L)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨hL, ?_⟩
  rw [← Real.exp_log hleftpos, ← Real.exp_log hrightpos,
    Real.log_rpow hLpos, Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  exact Real.exp_le_exp.mpr hexponent

/-- The threshold still dominates every fixed logarithmic power after Hua's
large-factor cutoff removes `L^lambda₂` from the available size and the
remaining prime factors are bounded by `L^lambda₃`. The side condition records
the eventual estimate `lambda₂ * log L ≤ L/2`; in applications this makes
`L - lambda₂ * log L` a valid lower bound for the logarithm of a surviving
integer. -/
theorem eventually_log_pow_le_rpow_two_truncated_log_ratio
    {lambda₂ lambda₃ K : ℝ} (h₂ : 0 ≤ lambda₂) (h₃ : 0 < lambda₃)
    (hK : 0 ≤ K) :
    ∀ᶠ L : ℝ in Filter.atTop,
      1 < L ∧ lambda₂ * Real.log L ≤ L / 2 ∧
        L ^ K ≤
          (2 : ℝ) ^ ((L - lambda₂ * Real.log L) /
            (lambda₃ * Real.log L)) := by
  have hlarge : ∀ᶠ L : ℝ in Filter.atTop, 1 < L :=
    Filter.eventually_gt_atTop (1 : ℝ)
  have hroot : ∀ᶠ L : ℝ in Filter.atTop,
      4 * lambda₂ ≤ Real.rpow L (1 / 2 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually
      (Filter.eventually_atTop.2 ⟨4 * lambda₂, fun _ h => h⟩)
  have hmain :=
    eventually_log_pow_le_rpow_two_log_ratio
      (C := 2 * lambda₃) (K := K) (by positivity) hK
  filter_upwards [hlarge, hroot, hmain] with L hL hroot hmain
  have hLpos : 0 < L := lt_trans zero_lt_one hL
  have hlogL : 0 < Real.log L := Real.log_pos hL
  have hrootNonneg : 0 ≤ Real.rpow L (1 / 2 : ℝ) :=
    Real.rpow_nonneg hLpos.le _
  have hpowHalfSq : (Real.rpow L (1 / 2 : ℝ)) ^ 2 = L := by
    calc
      (Real.rpow L (1 / 2 : ℝ)) ^ 2 =
          Real.rpow L (1 / 2 : ℝ) * Real.rpow L (1 / 2 : ℝ) := by rw [pow_two]
      _ = Real.rpow L ((1 / 2 : ℝ) + 1 / 2) :=
        (Real.rpow_add hLpos _ _).symm
      _ = L := by norm_num [Real.rpow_one]
  have hlogBound : Real.log L ≤ 2 * Real.rpow L (1 / 2 : ℝ) := by
    calc
      Real.log L ≤ Real.rpow L (1 / 2 : ℝ) / (1 / 2 : ℝ) :=
        Real.log_le_rpow_div hLpos.le (by norm_num)
      _ = 2 * Real.rpow L (1 / 2 : ℝ) := by ring
  have hsmall : lambda₂ * Real.log L ≤ L / 2 := by
    have hlog := mul_le_mul_of_nonneg_left hlogBound h₂
    nlinarith [mul_nonneg (sub_nonneg.mpr hroot) hrootNonneg]
  have hmargin : L / (2 * (lambda₃ * Real.log L)) ≤
      (L - lambda₂ * Real.log L) / (lambda₃ * Real.log L) := by
    have hnum : L / 2 ≤ L - lambda₂ * Real.log L := by linarith
    calc
      L / (2 * (lambda₃ * Real.log L)) =
          (L / 2) / (lambda₃ * Real.log L) := by ring
      _ ≤ (L - lambda₂ * Real.log L) / (lambda₃ * Real.log L) :=
        div_le_div_of_nonneg_right hnum (le_of_lt (mul_pos h₃ hlogL))
  have hpow : (2 : ℝ) ^ (L / (2 * (lambda₃ * Real.log L))) ≤
      (2 : ℝ) ^ ((L - lambda₂ * Real.log L) /
        (lambda₃ * Real.log L)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hmargin
  refine ⟨hL, hsmall, ?_⟩
  have hmain' : L ^ K ≤ (2 : ℝ) ^ (L / (2 * (lambda₃ * Real.log L))) := by
    simpa [mul_assoc] using hmain.2
  exact le_trans hmain' hpow

/-- Hua's large/smooth cutoff feeds directly into the cubic divisor-moment
tail. For fixed cutoff exponents, any squarefree integer above
`exp(L - lambda₂ log L)` whose prime factors are at most `B`, with
`log B ≤ lambda₃ log L`, has at least `L^K` divisors eventually. Summing the
exceptional set costs at most the seventh-log divisor moment. -/
theorem eventually_truncatedLog_smoothSquarefree_divisorTail_le
    {lambda₂ lambda₃ K : ℝ} (h₂ : 0 ≤ lambda₂) (h₃ : 0 < lambda₃)
    (hK : 0 ≤ K) :
    ∀ᶠ L : ℝ in Filter.atTop,
      1 < L ∧ lambda₂ * Real.log L ≤ L / 2 ∧
        ∀ M B : ℕ, 1 < B → Real.log B ≤ lambda₃ * Real.log L →
          (L ^ K) ^ 2 *
            (∑ n ∈ (Finset.Icc 1 M).filter (fun n : ℕ =>
              Squarefree n ∧ n ≠ 0 ∧
                (∀ p ∈ n.primeFactors, p ≤ B) ∧
                L - lambda₂ * Real.log L ≤ Real.log (n : ℝ)),
              (n.divisors.card : ℝ)) ≤
            (M : ℝ) * (1 + Real.log (M : ℝ)) ^ 7 := by
  have hthreshold :=
    eventually_log_pow_le_rpow_two_truncated_log_ratio h₂ h₃ hK
  filter_upwards [hthreshold] with L hL
  refine ⟨hL.1, hL.2.1, ?_⟩
  intro M B hB hBlog
  let P : ℕ → Prop := fun n => Squarefree n ∧ n ≠ 0 ∧
    (∀ p ∈ n.primeFactors, p ≤ B) ∧
    L - lambda₂ * Real.log L ≤ Real.log (n : ℝ)
  have hT : 0 < L ^ K := Real.rpow_pos_of_pos (lt_trans zero_lt_one hL.1) K
  have htail := divisorThresholdedTail_le (M := M) P (L ^ K) 1 hT
      (by norm_num) (by
        intro n hn hnP
        rcases hnP with ⟨hsq, hn0, hFactors, hA⟩
        have hlogL : 0 < Real.log L := Real.log_pos hL.1
        have hdenL : 0 < lambda₃ * Real.log L := mul_pos h₃ hlogL
        have hdenB : 0 < Real.log (B : ℝ) := by
          exact Real.log_pos (by exact_mod_cast hB)
        have hAnonneg : 0 ≤ L - lambda₂ * Real.log L := by
          linarith [hL.2.1]
        have hratio : (L - lambda₂ * Real.log L) /
            (lambda₃ * Real.log L) ≤
              (L - lambda₂ * Real.log L) / Real.log B := by
          apply (div_le_div_iff₀ hdenL hdenB).2
          nlinarith [mul_nonneg hAnonneg (sub_nonneg.mpr hBlog)]
        have hbase : L ^ K ≤
            Real.rpow 2 ((L - lambda₂ * Real.log L) /
              (lambda₃ * Real.log L)) := hL.2.2
        have hpow := Real.rpow_le_rpow_of_exponent_le
          (by norm_num : (1 : ℝ) ≤ 2) hratio
        have hdiv := rpow_two_log_ratio_le_card_divisors_of_squarefree
          hsq hn0 hB hFactors hA
        simpa using le_trans hbase (le_trans hpow hdiv))
  simpa [P] using htail

/-- The truncated-log exceptional-set estimate with Hua's real prime-factor
cutoff made natural by flooring. For each fixed positive `lambda₃`, the floor
is eventually at least two and its logarithm is bounded above by
`lambda₃ * log L`; hence the generic smooth-squarefree tail applies directly
to factors `p ≤ L^lambda₃`. -/
theorem eventually_truncatedLog_natFloor_smoothSquarefree_divisorTail_le
    {lambda₂ lambda₃ K : ℝ} (h₂ : 0 ≤ lambda₂) (h₃ : 0 < lambda₃)
    (hK : 0 ≤ K) :
    ∀ᶠ L : ℝ in Filter.atTop,
      1 < L ∧ lambda₂ * Real.log L ≤ L / 2 ∧
        ∀ M : ℕ,
          (L ^ K) ^ 2 *
            (∑ n ∈ (Finset.Icc 1 M).filter (fun n : ℕ =>
              Squarefree n ∧ n ≠ 0 ∧
                (∀ p ∈ n.primeFactors,
                  p ≤ Nat.floor (Real.rpow L lambda₃)) ∧
                L - lambda₂ * Real.log L ≤ Real.log (n : ℝ)),
              (n.divisors.card : ℝ)) ≤
            (M : ℝ) * (1 + Real.log (M : ℝ)) ^ 7 := by
  have htail :=
    eventually_truncatedLog_smoothSquarefree_divisorTail_le h₂ h₃ hK
  have hlargePow : ∀ᶠ L : ℝ in Filter.atTop,
      2 ≤ Real.rpow L lambda₃ :=
    (tendsto_rpow_atTop h₃).eventually
      (Filter.eventually_atTop.2 ⟨2, fun _ h => h⟩)
  filter_upwards [htail, hlargePow] with L htail hlargePow
  rcases htail with ⟨hL, hsmall, hsum⟩
  refine ⟨hL, hsmall, ?_⟩
  intro M
  let B : ℕ := Nat.floor (Real.rpow L lambda₃)
  have hBtwo : 2 ≤ B := by
    dsimp [B]
    exact Nat.le_floor hlargePow
  have hB : 1 < B := by omega
  have hLpos : 0 < L := lt_trans zero_lt_one hL
  have hBpos : 0 < (B : ℝ) := by exact_mod_cast (by omega : 0 < B)
  have hBcast : (B : ℝ) ≤ Real.rpow L lambda₃ := by
    dsimp [B]
    exact Nat.floor_le (Real.rpow_nonneg hLpos.le lambda₃)
  have hBlog : Real.log B ≤ lambda₃ * Real.log L := by
    calc
      Real.log B ≤ Real.log (Real.rpow L lambda₃) :=
        Real.log_le_log hBpos hBcast
      _ = lambda₃ * Real.log L := Real.log_rpow hLpos lambda₃
  simpa [B] using hsum M B hB hBlog

/-- Hua's natural large-factor cutoff implies the logarithmic size condition
used by the smooth-divisor tail: if `n ≥ P/(log P)^lambda₂`, then
`log n ≥ log P - lambda₂ log log P`. -/
theorem log_nat_lower_of_truncatedLog_cutoff
    {P n : ℕ} {lambda₂ : ℝ} (hP : 1 < P)
    (hcut : (P : ℝ) / Real.rpow (Real.log P) lambda₂ ≤ (n : ℝ)) :
    Real.log P - lambda₂ * Real.log (Real.log P) ≤ Real.log n := by
  have hPpos : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
  have hLpos : 0 < Real.log P := Real.log_pos (by exact_mod_cast hP)
  have hdenpos : 0 < Real.rpow (Real.log P) lambda₂ :=
    Real.rpow_pos_of_pos hLpos lambda₂
  have hcutpos : 0 < (P : ℝ) / Real.rpow (Real.log P) lambda₂ :=
    div_pos hPpos hdenpos
  have hlogcut :
      Real.log ((P : ℝ) / Real.rpow (Real.log P) lambda₂) =
        Real.log P - lambda₂ * Real.log (Real.log P) := by
    calc
      Real.log ((P : ℝ) / Real.rpow (Real.log P) lambda₂) =
          Real.log P - Real.log (Real.rpow (Real.log P) lambda₂) :=
        Real.log_div (ne_of_gt hPpos) (ne_of_gt hdenpos)
      _ = Real.log P - lambda₂ * Real.log (Real.log P) :=
        congrArg (fun x : ℝ => Real.log P - x)
          (Real.log_rpow hLpos lambda₂)
  rw [← hlogcut]
  exact Real.log_le_log hcutpos hcut

/-- Hua's exceptional-set tail with the actual natural cutoffs. The lower
bound `n ≥ P/(log P)^lambda₂` supplies the logarithmic size hypothesis, and
the upper bound on prime factors is represented by the exact floor of
`(log P)^lambda₃`. -/
theorem eventually_hua_truncatedLog_smoothSquarefree_divisorTail_le
    {lambda₂ lambda₃ K : ℝ} (h₂ : 0 ≤ lambda₂) (h₃ : 0 < lambda₃)
    (hK : 0 ≤ K) :
    ∀ᶠ P : ℕ in Filter.atTop,
      1 < P ∧
        (Real.rpow (Real.log P) K) ^ 2 *
          (∑ n ∈ (Finset.Icc 1 P).filter (fun n : ℕ =>
            Squarefree n ∧ n ≠ 0 ∧
              (∀ p ∈ n.primeFactors,
                p ≤ Nat.floor (Real.rpow (Real.log P) lambda₃)) ∧
              (P : ℝ) / Real.rpow (Real.log P) lambda₂ ≤ (n : ℝ)),
            (n.divisors.card : ℝ)) ≤
          (P : ℝ) * (1 + Real.log P) ^ 7 := by
  have hlog : Filter.Tendsto (fun P : ℕ => Real.log (P : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htail := hlog.eventually
    (eventually_truncatedLog_natFloor_smoothSquarefree_divisorTail_le h₂ h₃ hK)
  have hPlarge : ∀ᶠ P : ℕ in Filter.atTop, 1 < P :=
    Filter.eventually_gt_atTop (1 : ℕ)
  filter_upwards [htail, hPlarge] with P htail hP
  rcases htail with ⟨hL, hsmall, hsum⟩
  let L : ℝ := Real.log (P : ℝ)
  let Source : ℕ → Prop := fun n => Squarefree n ∧ n ≠ 0 ∧
    (∀ p ∈ n.primeFactors, p ≤ Nat.floor (Real.rpow L lambda₃)) ∧
    (P : ℝ) / Real.rpow L lambda₂ ≤ (n : ℝ)
  let LogLarge : ℕ → Prop := fun n => Squarefree n ∧ n ≠ 0 ∧
    (∀ p ∈ n.primeFactors, p ≤ Nat.floor (Real.rpow L lambda₃)) ∧
    L - lambda₂ * Real.log L ≤ Real.log (n : ℝ)
  have hsubset :
      (Finset.Icc 1 P).filter Source ⊆ (Finset.Icc 1 P).filter LogLarge := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnI, hdata⟩
    rcases hdata with ⟨hsq, hn0, hFactors, hcut⟩
    refine Finset.mem_filter.mpr ⟨hnI, ⟨hsq, hn0, hFactors, ?_⟩⟩
    dsimp [L]
    exact log_nat_lower_of_truncatedLog_cutoff hP hcut
  have hsumSubset :
      (∑ n ∈ (Finset.Icc 1 P).filter Source, (n.divisors.card : ℝ)) ≤
        ∑ n ∈ (Finset.Icc 1 P).filter LogLarge,
          (n.divisors.card : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro n hn hnot
    positivity
  have hsumBound := hsum P
  have hfactorNonneg : 0 ≤ (L ^ K) ^ 2 := sq_nonneg (L ^ K)
  refine ⟨hP, ?_⟩
  calc
    (L ^ K) ^ 2 *
        (∑ n ∈ (Finset.Icc 1 P).filter Source, (n.divisors.card : ℝ)) ≤
      (L ^ K) ^ 2 *
        (∑ n ∈ (Finset.Icc 1 P).filter LogLarge,
          (n.divisors.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hsumSubset hfactorNonneg
    _ ≤ (P : ℝ) * (1 + L) ^ 7 := by
      simpa [L, LogLarge] using hsumBound

/-- Hua's smooth large-factor set has an arbitrary logarithmic saving in
cardinality. The proof charges each admissible squarefree integer to its
positive divisor count, then uses the seventh-log moment tail with a stronger
divisor threshold. This is the factor-count estimate used for the exceptional
set in the proof of Theorem 10. -/
theorem eventually_hua_truncatedLog_smoothSquarefree_count_le
    {lambda₂ lambda₃ sigma : ℝ} (h₂ : 0 ≤ lambda₂)
    (h₃ : 0 < lambda₃) (hσ : 0 ≤ sigma) :
    ∀ᶠ P : ℕ in Filter.atTop,
      1 < P ∧
        Real.rpow (Real.log P) sigma *
          (((Finset.Icc 1 P).filter (fun n : ℕ =>
            Squarefree n ∧ n ≠ 0 ∧
              (∀ p ∈ n.primeFactors,
                p ≤ Nat.floor (Real.rpow (Real.log P) lambda₃)) ∧
              (P : ℝ) / Real.rpow (Real.log P) lambda₂ ≤ (n : ℝ))).card : ℝ)
          ≤ (P : ℝ) := by
  let K : ℝ := sigma + 8
  have hK : 0 ≤ K := by dsimp [K]; linarith
  have htail := eventually_hua_truncatedLog_smoothSquarefree_divisorTail_le
    h₂ h₃ hK
  have hlog : Filter.Tendsto (fun P : ℕ => Real.log (P : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ P : ℕ in Filter.atTop,
      2 ≤ Real.log (P : ℝ) :=
    hlog.eventually (Filter.eventually_atTop.2 ⟨2, fun _ h => h⟩)
  filter_upwards [htail, hlarge] with P htail hlarge
  rcases htail with ⟨hP, hsum⟩
  let L : ℝ := Real.log (P : ℝ)
  let S : Finset ℕ := (Finset.Icc 1 P).filter fun n =>
    Squarefree n ∧ n ≠ 0 ∧
      (∀ p ∈ n.primeFactors,
        p ≤ Nat.floor (Real.rpow L lambda₃)) ∧
      (P : ℝ) / Real.rpow L lambda₂ ≤ (n : ℝ)
  have hLlarge : 2 ≤ L := by simpa [L] using hlarge
  have hLpos : 0 < L := by linarith
  have hlogFactor : 0 < (1 + L) ^ 7 := pow_pos (by positivity) 7
  have hSsum :
      ((S.card : ℕ) : ℝ) ≤
        ∑ n ∈ S, (n.divisors.card : ℝ) := by
    calc
      ((S.card : ℕ) : ℝ) = ∑ n ∈ S, (1 : ℝ) := by simp
      _ ≤ ∑ n ∈ S, (n.divisors.card : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        have hnIcc := (Finset.mem_filter.mp hn).1
        have hnpos : 0 < n := (Finset.mem_Icc.mp hnIcc).1
        have hone : 1 ∈ n.divisors :=
          Nat.mem_divisors.mpr ⟨one_dvd n, hnpos.ne'⟩
        have hcard : 0 < n.divisors.card := Finset.card_pos.mpr ⟨1, hone⟩
        exact_mod_cast (Nat.succ_le_of_lt hcard)
  have hsumS :
      (Real.rpow L K) ^ 2 *
        (∑ n ∈ S, (n.divisors.card : ℝ)) ≤
          (P : ℝ) * (1 + L) ^ 7 := by
    simpa [L, S, K] using hsum
  have hlogBase : (1 : ℝ) ≤ L := by linarith
  have hdenBound : (1 + L) ^ 7 ≤ L ^ 14 := by
    have hlinear : 1 + L ≤ L ^ 2 := by nlinarith
    calc
      (1 + L) ^ 7 ≤ (L ^ 2) ^ 7 := by gcongr
      _ = L ^ (2 * 7) := by rw [← pow_mul]
      _ = L ^ 14 := by norm_num
  have hScale :
      Real.rpow L sigma * (1 + L) ^ 7 ≤ (Real.rpow L K) ^ 2 := by
    have hExponent : sigma + 14 ≤ K + K := by
      dsimp [K]
      linarith
    calc
      Real.rpow L sigma * (1 + L) ^ 7 ≤ Real.rpow L sigma * L ^ 14 :=
        mul_le_mul_of_nonneg_left hdenBound
          (Real.rpow_nonneg hLpos.le sigma)
      _ = Real.rpow L (sigma + 14) := by
        calc
          Real.rpow L sigma * L ^ 14 =
              Real.rpow L sigma * Real.rpow L 14 := by
                exact congrArg (fun x : ℝ => Real.rpow L sigma * x)
                  (Real.rpow_natCast L 14).symm
          _ = Real.rpow L (sigma + 14) :=
            (Real.rpow_add hLpos sigma 14).symm
      _ ≤ Real.rpow L (K + K) :=
        Real.rpow_le_rpow_of_exponent_le hlogBase hExponent
      _ = (Real.rpow L K) ^ 2 := by
        calc
          Real.rpow L (K + K) = Real.rpow L K * Real.rpow L K :=
            Real.rpow_add hLpos K K
          _ = (Real.rpow L K) ^ 2 := by rw [pow_two]
  have htargetMul :
      (Real.rpow L sigma * (S.card : ℝ)) * (1 + L) ^ 7 ≤
        (P : ℝ) * (1 + L) ^ 7 := by
    calc
      (Real.rpow L sigma * (S.card : ℝ)) * (1 + L) ^ 7 =
          (Real.rpow L sigma * (1 + L) ^ 7) * (S.card : ℝ) := by ring
      _ ≤ (Real.rpow L K) ^ 2 * (S.card : ℝ) :=
        mul_le_mul_of_nonneg_right hScale (Nat.cast_nonneg _)
      _ ≤ (Real.rpow L K) ^ 2 *
          (∑ n ∈ S, (n.divisors.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hSsum (sq_nonneg (Real.rpow L K))
      _ ≤ (P : ℝ) * (1 + L) ^ 7 := hsumS
  have hresult := le_of_mul_le_mul_right htargetMul hlogFactor
  refine ⟨hP, ?_⟩
  simpa [L, S] using hresult

/-- Distinct prime factors of `n` at least the natural threshold `Y`. -/
def primeFactorsAtLeastCutoff (Y n : ℕ) : Finset ℕ :=
  n.primeFactors.filter (fun p => Y ≤ p)

/-- Multiplication by a new prime above the cutoff adds exactly one large
prime factor. The nondivisibility hypothesis is the no-repeated-prime case
in Hua's step-8 decomposition. -/
theorem card_primeFactorsAtLeastCutoff_mul_prime
    {Y p v : ℕ} (hp : Nat.Prime p) (hv : v ≠ 0)
    (hYp : Y ≤ p) (hnot : ¬p ∣ v) :
    (primeFactorsAtLeastCutoff Y (p * v)).card =
      (primeFactorsAtLeastCutoff Y v).card + 1 := by
  have hpnot : p ∉ v.primeFactors := by
    intro hpv
    exact hnot (Nat.dvd_of_mem_primeFactors hpv)
  have hpnotCutoff : p ∉ primeFactorsAtLeastCutoff Y v := by
    simp [primeFactorsAtLeastCutoff, hpnot]
  unfold primeFactorsAtLeastCutoff
  rw [Nat.primeFactors_mul hp.ne_zero hv, hp.primeFactors,
    Finset.filter_union, Finset.filter_singleton]
  simp only [if_pos hYp]
  exact Finset.card_insert_of_notMem hpnotCutoff

/-- Removing a chosen large prime from a squarefree integer reduces its
large-prime-factor count by exactly one. This is the quotient-side factor
count needed to reindex Hua's no-repeated-prime terms. -/
theorem card_primeFactorsAtLeastCutoff_div_prime
    {Y p n : ℕ} (hn : Squarefree n) (hp : Nat.Prime p)
    (hpdvd : p ∣ n) (hYp : Y ≤ p) :
    (primeFactorsAtLeastCutoff Y (n / p)).card + 1 =
      (primeFactorsAtLeastCutoff Y n).card := by
  have hn0 : n ≠ 0 := hn.ne_zero
  have hpquot : ¬p ∣ n / p := by
    intro hdiv
    have hsq : p * p ∣ n := Nat.mul_dvd_of_dvd_div hpdvd hdiv
    exact (Nat.squarefree_iff_prime_squarefree.mp hn) p hp hsq
  have hmul : p * (n / p) = n := by
    calc
      p * (n / p) = (n / p) * p := Nat.mul_comm _ _
      _ = n := Nat.div_mul_cancel hpdvd
  have hquot : n / p ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hmul
    exact hn0 hmul.symm
  rw [← hmul]
  have hcancel : p * (n / p) / p = n / p := by
    rw [mul_comm p (n / p), Nat.mul_div_left _ hp.pos]
  rw [hcancel]
  exact (card_primeFactorsAtLeastCutoff_mul_prime hp hquot hYp hpquot).symm

/-- A repeated large-prime pair has a unique squarefree quotient after
removing its repeated prime. If `v` has `s - 1` large factors and `p ∣ v`,
then writing `v = p * v₁` leaves exactly `s - 2` large factors in `v₁`.
This is the quotient classification used for Hua's exceptional terms. -/
theorem repeatedLargeFactor_quotient_existsUnique
    {Y p v s : ℕ} (hv : Squarefree v) (hp : Nat.Prime p)
    (hpv : p ∣ v) (hYp : Y ≤ p)
    (hcount : (primeFactorsAtLeastCutoff Y v).card + 1 = s) :
    ∃! v₁, v = p * v₁ ∧ ¬ p ∣ v₁ ∧ Squarefree v₁ ∧
      (primeFactorsAtLeastCutoff Y v₁).card + 2 = s := by
  have hquotSquarefree : Squarefree (v / p) :=
    hv.squarefree_of_dvd (Nat.div_dvd_of_dvd hpv)
  have hquotNot : ¬p ∣ v / p := by
    intro hdiv
    have hsq : p * p ∣ v := Nat.mul_dvd_of_dvd_div hpv hdiv
    exact (Nat.squarefree_iff_prime_squarefree.mp hv) p hp hsq
  have hquotCount := card_primeFactorsAtLeastCutoff_div_prime hv hp hpv hYp
  have hquotCount' : (primeFactorsAtLeastCutoff Y (v / p)).card + 2 = s := by
    omega
  refine ⟨v / p, ?_, ?_⟩
  · refine ⟨(Nat.mul_div_cancel' hpv).symm, hquotNot, hquotSquarefree,
      hquotCount'⟩
  · intro w hw
    apply Nat.mul_left_cancel hp.pos
    calc
      p * w = v := hw.1.symm
      _ = p * (v / p) := (Nat.mul_div_cancel' hpv).symm

/-- Recount a squarefree term once for each of its large prime factors.
For a term with exactly `s` such factors, the quotient-side indexing
`(p, d / p)` contains exactly `s` copies of the original summand. This is
the nonrepeated part of Hua's step-8 multiplicity identity; repeated-prime
products are deliberately handled separately. -/
theorem sum_primeFactorsAtLeastCutoff_div_recount
    {R : Type*} [AddCommMonoid R] {Y s : ℕ} {D : Finset ℕ}
    (hcount : ∀ d ∈ D, (primeFactorsAtLeastCutoff Y d).card = s)
    (f : ℕ → R) :
    (∑ d ∈ D, ∑ p ∈ primeFactorsAtLeastCutoff Y d,
      f (p * (d / p))) =
      ∑ d ∈ D, s • f d := by
  apply Finset.sum_congr rfl
  intro d hd
  have hterm : ∀ p ∈ primeFactorsAtLeastCutoff Y d,
      f (p * (d / p)) = f d := by
    intro p hp
    have hpdiv : p ∣ d :=
      Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp).1
    rw [Nat.mul_div_cancel' hpdiv]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, hcount d hd]

/-- The finite pair set obtained by selecting a large prime factor `p` of an
eligible divisor `d` and recording the quotient `v=d/p`. -/
def primeFactorQuotientPairs (Y : ℕ) (D : Finset ℕ) : Finset (ℕ × ℕ) :=
  D.biUnion fun d =>
    (primeFactorsAtLeastCutoff Y d).image fun p => (p, d / p)

/-- Membership in `primeFactorQuotientPairs` is exactly the divisor/quotient
indexing relation. -/
theorem mem_primeFactorQuotientPairs_iff
    {Y : ℕ} {D : Finset ℕ} {p v : ℕ} :
    (p, v) ∈ primeFactorQuotientPairs Y D ↔
      ∃ d ∈ D, p ∈ primeFactorsAtLeastCutoff Y d ∧ v = d / p := by
  constructor
  · intro h
    rcases Finset.mem_biUnion.mp h with ⟨d, hd, hpair⟩
    rcases Finset.mem_image.mp hpair with ⟨q, hq, heq⟩
    have hfst : q = p := congrArg Prod.fst heq
    have hsnd : d / q = v := congrArg Prod.snd heq
    subst q
    exact ⟨d, hd, hq, hsnd.symm⟩
  · rintro ⟨d, hd, hp, rfl⟩
    apply Finset.mem_biUnion.mpr ⟨d, hd, ?_⟩
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩

/-- If the eligible divisor family is squarefree, its quotient-pair
representation is equivalently the source-style condition `p` prime,
`p≥Y`, and `p*v∈D`. All restrictions on the product (including an upper
range or a progression congruence used to define `D`) are therefore
preserved exactly by this reindexing. -/
theorem mem_primeFactorQuotientPairs_iff_prime_product_mem
    {Y : ℕ} {D : Finset ℕ} {p v : ℕ}
    (hD : ∀ d ∈ D, Squarefree d) :
    (p, v) ∈ primeFactorQuotientPairs Y D ↔
      Nat.Prime p ∧ Y ≤ p ∧ p * v ∈ D := by
  constructor
  · intro h
    rcases mem_primeFactorQuotientPairs_iff.mp h with ⟨d, hd, hpf, hv⟩
    have hpf' := Finset.mem_filter.mp hpf
    have hp : Nat.Prime p := Nat.prime_of_mem_primeFactors hpf'.1
    have hpdiv : p ∣ d := Nat.dvd_of_mem_primeFactors hpf'.1
    have hprod : p * v = d := by
      rw [hv]
      exact Nat.mul_div_cancel' hpdiv
    exact ⟨hp, hpf'.2, hprod ▸ hd⟩
  · rintro ⟨hp, hYp, hprod⟩
    have hsq : Squarefree (p * v) := hD _ hprod
    have hne : p * v ≠ 0 := hsq.ne_zero
    have hpdiv : p ∣ p * v := ⟨v, rfl⟩
    have hpmem : p ∈ (p * v).primeFactors :=
      (Nat.mem_primeFactors_of_ne_zero hne).mpr ⟨hp, hpdiv⟩
    apply mem_primeFactorQuotientPairs_iff.mpr
    refine ⟨p * v, hprod, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨hpmem, hYp⟩
    · calc
        v = v * p / p := (Nat.mul_div_left v hp.pos).symm
        _ = p * v / p := by rw [Nat.mul_comm v p]

/-- Reindex the divisor-first factor/quotient sum as a sum over the
source-style good pairs `(p,v)`. Distinct eligible divisors give disjoint
pair fibers because the product `p*v` recovers the divisor. -/
theorem sum_primeFactorQuotientPairs_eq_recount
    {R : Type*} [AddCommMonoid R] {Y s : ℕ} {D : Finset ℕ}
    (hcount : ∀ d ∈ D, (primeFactorsAtLeastCutoff Y d).card = s)
    (f : ℕ → R) :
    (∑ z ∈ primeFactorQuotientPairs Y D, f (z.1 * z.2)) =
      ∑ d ∈ D, s • f d := by
  classical
  let factors (d : ℕ) := (primeFactorsAtLeastCutoff Y d).image
    (fun p => (p, d / p))
  have hdisj : Set.PairwiseDisjoint (↑D) factors := by
    intro d hd e he hde
    apply Finset.disjoint_left.mpr
    intro z hzd hze
    rcases Finset.mem_image.mp hzd with ⟨p, hp, hpz⟩
    rcases Finset.mem_image.mp hze with ⟨q, hq, hqz⟩
    have hpqpair : (p, d / p) = (q, e / q) := hpz.trans hqz.symm
    have hpq : p = q := congrArg Prod.fst hpqpair
    have hquot : d / p = e / q := congrArg Prod.snd hpqpair
    have hpdvd : p ∣ d :=
      Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp).1
    have hediv : q ∣ e :=
      Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hq).1
    subst q
    apply hde
    calc
      d = p * (d / p) := (Nat.mul_div_cancel' hpdvd).symm
      _ = p * (e / p) := by rw [hquot]
      _ = e := Nat.mul_div_cancel' hediv
  change (∑ z ∈ D.biUnion factors, f (z.1 * z.2)) = _
  rw [Finset.sum_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro d hd
  have hinj : Set.InjOn (fun p => (p, d / p))
      (primeFactorsAtLeastCutoff Y d) := by
    intro p hp q hq heq
    exact congrArg Prod.fst heq
  rw [Finset.sum_image hinj]
  have hterm : ∀ p ∈ primeFactorsAtLeastCutoff Y d,
      f (p * (d / p)) = f d := by
    intro p hp
    have hpdiv : p ∣ d :=
      Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp).1
    rw [Nat.mul_div_cancel' hpdiv]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, hcount d hd]

/-- For a fixed positive `p`, the positive integers `v` satisfying `p∣v`
and `p*v≤M` are at most `M/p²` in number. The injection is `v ↦ v/p`;
the product restriction becomes `p²*(v/p)≤M`. This is the per-prime
counting estimate for the repeated-pair branch of Hua step 8. -/
theorem card_positiveRepeatedMultiples_le_div_sq {p M : ℕ} (hp : 0 < p) :
    ((Finset.Icc 1 M).filter (fun v => p ∣ v ∧ p * v ≤ M)).card ≤
      M / (p * p) := by
  classical
  let S := (Finset.Icc 1 M).filter (fun v => p ∣ v ∧ p * v ≤ M)
  let T := Finset.Icc 1 (M / (p * p))
  have hmaps : Set.MapsTo (fun v => v / p) (↑S) (↑T) := by
    intro v hv
    rcases Finset.mem_filter.mp hv with ⟨hvI, hpv, hprod⟩
    rcases hpv with ⟨w, rfl⟩
    have hwpos : 0 < w := by
      by_contra hw
      have : w = 0 := Nat.eq_zero_of_not_pos hw
      simp [this] at hvI
    have hdiv : p * w / p = w := by
      rw [Nat.mul_comm p w, Nat.mul_div_left w hp]
    have hbound : (p * p) * w ≤ M := by
      simpa [Nat.mul_assoc] using hprod
    have hquotBound : w ≤ M / (p * p) :=
      (Nat.le_div_iff_mul_le (Nat.mul_pos hp hp)).2 (by
        simpa [Nat.mul_comm] using hbound)
    have hmapNe : p * w / p ≠ 0 := by rw [hdiv]; exact hwpos.ne'
    exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hmapNe, by
      simpa [hdiv] using hquotBound⟩
  have hinj : (↑S : Set ℕ).InjOn (fun v => v / p) := by
    intro a ha b hb hab
    have hap := (Finset.mem_filter.mp ha).2.1
    have hbp := (Finset.mem_filter.mp hb).2.1
    change a / p = b / p at hab
    calc
      a = p * (a / p) := (Nat.mul_div_cancel' hap).symm
      _ = p * (b / p) := by rw [hab]
      _ = b := Nat.mul_div_cancel' hbp
  change S.card ≤ M / (p * p)
  calc
    S.card ≤ T.card := Finset.card_le_card_of_injOn (fun v => v / p)
      hmaps hinj
    _ = M / (p * p) := by simp [T]

/-- The finite set of repeated-prime pairs with product at most `M` and
prime coordinate at least `Y`. -/
def repeatedPrimeProductPairs (Y M : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc Y M).filter Nat.Prime).biUnion fun p =>
    (((Finset.Icc 1 M).filter fun v => p ∣ v ∧ p * v ≤ M).image fun v => (p, v))

/-- Count repeated-prime pairs by fixing their prime coordinate. -/
theorem card_repeatedPrimeProductPairs_le_divisor_sum {Y M : ℕ} :
    (repeatedPrimeProductPairs Y M).card ≤
      ∑ p ∈ (Finset.Icc Y M).filter Nat.Prime, M / (p * p) := by
  classical
  let P := (Finset.Icc Y M).filter Nat.Prime
  let V (p : ℕ) := (Finset.Icc 1 M).filter fun v => p ∣ v ∧ p * v ≤ M
  calc
    (repeatedPrimeProductPairs Y M).card ≤
        ∑ p ∈ P, ((V p).image fun v => (p, v)).card := by
          simpa [repeatedPrimeProductPairs, P, V] using
            (Finset.card_biUnion_le (s := P)
              (t := fun p => (V p).image fun v => (p, v)))
    _ ≤ ∑ p ∈ P, M / (p * p) := by
      apply Finset.sum_le_sum
      intro p hp
      have hinj : Set.InjOn (fun v => (p, v)) (↑(V p) : Set ℕ) := by
        intro a ha b hb hab
        exact congrArg Prod.snd hab
      rw [Finset.card_image_of_injOn hinj]
      exact card_positiveRepeatedMultiples_le_div_sq
        (Nat.Prime.pos (Finset.mem_filter.mp hp).2)

/-- The reciprocal-square tail over primes, bounded by the corresponding
tail over all integers. This is the scalar estimate behind Hua's correction
for terms containing a repeated large prime factor. -/
theorem sum_prime_inverseSquare_Icc_le {Y M : ℕ} (hY : 0 < Y) :
    (∑ p ∈ (Finset.Icc Y M).filter Nat.Prime,
      ((p : ℝ) ^ 2)⁻¹) ≤ (2 : ℝ) / (Y : ℝ) := by
  let S := (Finset.Icc Y M).filter Nat.Prime
  have hsubset : S ⊆ Finset.Ioo (Y - 1) (M + 1) := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpIcc, _⟩
    rcases Finset.mem_Icc.mp hpIcc with ⟨hYp, hpM⟩
    simp only [Finset.mem_Ioo]
    omega
  calc
    (∑ p ∈ S, ((p : ℝ) ^ 2)⁻¹) ≤
        ∑ p ∈ Finset.Ioo (Y - 1) (M + 1), ((p : ℝ) ^ 2)⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro p hp hnot
      positivity
    _ ≤ (2 : ℝ) / (((Y - 1 : ℕ) : ℝ) + 1) := by
      exact sum_Ioo_inv_sq_le (α := ℝ) (Y - 1) (M + 1)
    _ = (2 : ℝ) / (Y : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ Y)]
      ring

/-- The repeated-prime square contribution is bounded by `2M/Y`: for a
fixed large prime `p`, at most the `M/p²` scale of multiples can occur, and
the sum of `1/p²` over primes is bounded by the integer reciprocal-square
tail. -/
theorem sum_prime_inverseSquare_weight_le {Y M : ℕ} (hY : 0 < Y) :
    (∑ p ∈ (Finset.Icc Y M).filter Nat.Prime,
      (M : ℝ) / ((p : ℝ) ^ 2)) ≤ (2 : ℝ) * M / Y := by
  let S := (Finset.Icc Y M).filter Nat.Prime
  calc
    (∑ p ∈ S, (M : ℝ) / ((p : ℝ) ^ 2)) =
        ∑ p ∈ S, (M : ℝ) * (((p : ℝ) ^ 2)⁻¹) := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [div_eq_mul_inv]
    _ = (M : ℝ) * (∑ p ∈ S, ((p : ℝ) ^ 2)⁻¹) := by
      rw [Finset.mul_sum]
    _ ≤ (M : ℝ) * ((2 : ℝ) / (Y : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (sum_prime_inverseSquare_Icc_le hY) (Nat.cast_nonneg M)
    _ = (2 : ℝ) * M / Y := by ring

/-- The repeated-pair count is bounded by the reciprocal-square prime tail.
This is Hua's `O(M / Y)` correction, now with the exact finite pair family. -/
theorem real_card_repeatedPrimeProductPairs_le {Y M : ℕ} (hY : 0 < Y) :
    ((repeatedPrimeProductPairs Y M).card : ℝ) ≤ (2 : ℝ) * M / Y := by
  let P := (Finset.Icc Y M).filter Nat.Prime
  calc
    ((repeatedPrimeProductPairs Y M).card : ℝ) ≤
        ∑ p ∈ P, ((M / (p * p) : ℕ) : ℝ) := by
          exact_mod_cast card_repeatedPrimeProductPairs_le_divisor_sum
    _ ≤ ∑ p ∈ P, (M : ℝ) / ((p : ℝ) ^ 2) := by
          apply Finset.sum_le_sum
          intro p hp
          calc
            ((M / (p * p) : ℕ) : ℝ) ≤ (M : ℝ) / ((p * p : ℕ) : ℝ) :=
              Nat.cast_div_le
            _ = (M : ℝ) / ((p : ℝ) ^ 2) := by simp [pow_two]
    _ ≤ (2 : ℝ) * M / Y := by
          simpa [P] using sum_prime_inverseSquare_weight_le hY

/-- Any unit-bounded summand over the repeated-prime pair family has total
norm at most the same `2M/Y` error bound. -/
theorem norm_sum_repeatedPrimeProductPairs_le
    {Y M : ℕ} (hY : 0 < Y) (f : ℕ × ℕ → ℂ)
    (hf : ∀ z ∈ repeatedPrimeProductPairs Y M, ‖f z‖ ≤ 1) :
    ‖∑ z ∈ repeatedPrimeProductPairs Y M, f z‖ ≤ (2 : ℝ) * M / Y := by
  calc
    ‖∑ z ∈ repeatedPrimeProductPairs Y M, f z‖ ≤
        ∑ z ∈ repeatedPrimeProductPairs Y M, ‖f z‖ := norm_sum_le _ _
    _ ≤ ∑ _z ∈ repeatedPrimeProductPairs Y M, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro z hz
      exact hf z hz
    _ = ((repeatedPrimeProductPairs Y M).card : ℝ) := by simp
    _ ≤ (2 : ℝ) * M / Y := real_card_repeatedPrimeProductPairs_le hY

/-- A unit-bounded complex sum over any finite set has norm at most the
cardinality of its index set. -/
theorem norm_sum_le_card_of_forall_norm_le_one
    {α : Type*} (S : Finset α) (f : α → ℂ)
    (hf : ∀ z ∈ S, ‖f z‖ ≤ 1) :
    ‖∑ z ∈ S, f z‖ ≤ (S.card : ℝ) := by
  calc
    ‖∑ z ∈ S, f z‖ ≤ ∑ z ∈ S, ‖f z‖ := norm_sum_le _ _
    _ ≤ ∑ _z ∈ S, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro z hz
      exact hf z hz
    _ = (S.card : ℝ) := by simp

/-- The same bound holds for any restricted subfamily of the repeated-prime
pairs, so additional congruence or divisor-family predicates may be retained. -/
theorem norm_sum_subset_repeatedPrimeProductPairs_le
    {Y M : ℕ} (hY : 0 < Y) {S : Finset (ℕ × ℕ)}
    (hS : S ⊆ repeatedPrimeProductPairs Y M) (f : ℕ × ℕ → ℂ)
    (hf : ∀ z ∈ S, ‖f z‖ ≤ 1) :
    ‖∑ z ∈ S, f z‖ ≤ (2 : ℝ) * M / Y := by
  calc
    ‖∑ z ∈ S, f z‖ ≤ (S.card : ℝ) :=
      norm_sum_le_card_of_forall_norm_le_one S f hf
    _ ≤ ((repeatedPrimeProductPairs Y M).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hS
    _ ≤ (2 : ℝ) * M / Y := real_card_repeatedPrimeProductPairs_le hY

/-- Membership in the repeated-pair family, exposing its source-style
conditions on the prime and quotient coordinates. -/
theorem mem_repeatedPrimeProductPairs_iff {Y M p v : ℕ} :
    (p, v) ∈ repeatedPrimeProductPairs Y M ↔
      Nat.Prime p ∧ Y ≤ p ∧ 0 < v ∧ p ∣ v ∧ p * v ≤ M := by
  classical
  constructor
  · intro h
    unfold repeatedPrimeProductPairs at h
    rcases Finset.mem_biUnion.mp h with ⟨q, hqP, hqv⟩
    rcases Finset.mem_filter.mp hqP with ⟨hqI, hqprime⟩
    rcases Finset.mem_Icc.mp hqI with ⟨hqY, hqM⟩
    rcases Finset.mem_image.mp hqv with ⟨w, hwfilter, hpair⟩
    rcases Finset.mem_filter.mp hwfilter with ⟨hwI, hwrel⟩
    rcases Finset.mem_Icc.mp hwI with ⟨hwpos, hwM⟩
    rcases hwrel with ⟨hqwdiv, hqprod⟩
    have hqp : q = p := congrArg Prod.fst hpair
    have hwv : w = v := congrArg Prod.snd hpair
    subst q
    subst w
    exact ⟨by simpa only [Nat.prime_iff] using hqprime, hqY, by omega,
      hqwdiv, hqprod⟩
  · rintro ⟨hp, hYp, hvpos, hpv, hprod⟩
    have hpM : p ≤ M := by
      have hple : p ≤ p * v := by
        calc
          p = p * 1 := by simp
          _ ≤ p * v := Nat.mul_le_mul_left p
            (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hvpos))
      exact le_trans hple hprod
    have hvM : v ≤ M := by
      have hpone : 1 ≤ p := Nat.succ_le_iff.mpr hp.pos
      have hvle : v ≤ p * v := by
        calc
          v = 1 * v := by simp
          _ ≤ p * v := Nat.mul_le_mul_right v hpone
      exact le_trans hvle hprod
    unfold repeatedPrimeProductPairs
    apply Finset.mem_biUnion.mpr ⟨p, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_Icc.mpr ⟨hYp, hpM⟩, by simpa only [Nat.prime_iff] using hp⟩
    · apply Finset.mem_image.mpr
      refine ⟨v, ?_, rfl⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_Icc.mpr ⟨by omega, hvM⟩, ⟨hpv, hprod⟩⟩

/-- The source-shaped exceptional family in Hua step 8: the quotient `v` is
squarefree and has exactly `s-1` prime factors above the cutoff, while the
selected prime `p` is repeated in `v`. The product bound models the upper
endpoint of the source progression. -/
def huaRepeatedStepEightPairs (Y M s : ℕ) : Finset (ℕ × ℕ) :=
  (repeatedPrimeProductPairs Y M).filter fun z =>
    Squarefree z.2 ∧
      (primeFactorsAtLeastCutoff Y z.2).card + 1 = s

/-- Every source-shaped repeated pair has a unique squarefree quotient
`v₁` with `v=p*v₁`; its large-prime count drops by one more, and the original
product bound becomes the source's `p²*v₁≤M` range. -/
theorem huaRepeatedStepEightPair_quotient_existsUnique
    {Y M s p v : ℕ} (hpair : (p, v) ∈ huaRepeatedStepEightPairs Y M s) :
    ∃! v₁, v = p * v₁ ∧ ¬p ∣ v₁ ∧ Squarefree v₁ ∧
      (primeFactorsAtLeastCutoff Y v₁).card + 2 = s ∧ p * p * v₁ ≤ M := by
  rcases Finset.mem_filter.mp hpair with ⟨hrep, ⟨hvsq, hvcount⟩⟩
  rcases mem_repeatedPrimeProductPairs_iff.mp hrep with
    ⟨hp, hYp, hvpos, hpv, hprod⟩
  have hcount : (primeFactorsAtLeastCutoff Y v).card + 1 = s := hvcount
  obtain ⟨v₁, ⟨hfactor, hnot, hsq, hcount₁⟩, hunique⟩ :=
    repeatedLargeFactor_quotient_existsUnique hvsq hp hpv hYp hcount
  refine ⟨v₁, ⟨hfactor, hnot, hsq, hcount₁, ?_⟩, ?_⟩
  · calc
      p * p * v₁ = p * (p * v₁) := by rw [Nat.mul_assoc]
      _ = p * v := by rw [← hfactor]
      _ ≤ M := hprod
  · intro w hw
    apply Nat.mul_left_cancel hp.pos
    calc
      p * w = v := hw.1.symm
      _ = p * v₁ := hfactor

/-- The exact repeated terms in Hua step 8 retain the same reciprocal-square
majorant as the ambient family. The factor-count and squarefree conditions
are preserved, not discarded, in the source decomposition. -/
theorem norm_sum_huaRepeatedStepEightPairs_le
    {Y M s : ℕ} (hY : 0 < Y) (f : ℕ × ℕ → ℂ)
    (hf : ∀ z ∈ huaRepeatedStepEightPairs Y M s, ‖f z‖ ≤ 1) :
    ‖∑ z ∈ huaRepeatedStepEightPairs Y M s, f z‖ ≤ (2 : ℝ) * M / Y := by
  apply norm_sum_subset_repeatedPrimeProductPairs_le hY
  · exact Finset.filter_subset _ _
  · exact hf

/-- Hua's logarithmic large-prime cutoff turns the repeated-square
contribution into `O(M / (log P)^lambda₃)`, uniformly in the progression
length `M`. The floor is handled explicitly, so the natural prime cutoff
does not introduce a rounding assumption. -/
theorem eventually_sum_prime_inverseSquare_logCutoff_le
    {lambda₃ : ℝ} (h₃ : 0 < lambda₃) :
    ∀ᶠ P : ℕ in Filter.atTop,
      1 < P ∧ ∀ M : ℕ,
        (∑ p ∈ (Finset.Icc
          (Nat.floor (Real.rpow (Real.log P) lambda₃)) M).filter Nat.Prime,
          (M : ℝ) / ((p : ℝ) ^ 2)) ≤
            (4 : ℝ) * M / Real.rpow (Real.log P) lambda₃ := by
  have hlog : Filter.Tendsto (fun P : ℕ => Real.log (P : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hcutoff : Filter.Tendsto
      (fun P : ℕ => Real.rpow (Real.log (P : ℝ)) lambda₃)
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop h₃).comp hlog
  have hlarge : ∀ᶠ P : ℕ in Filter.atTop,
      2 ≤ Real.rpow (Real.log (P : ℝ)) lambda₃ :=
    hcutoff.eventually (Filter.eventually_atTop.2 ⟨2, fun _ h => h⟩)
  have hPlarge : ∀ᶠ P : ℕ in Filter.atTop, 1 < P :=
    Filter.eventually_gt_atTop (1 : ℕ)
  filter_upwards [hlarge, hPlarge] with P hlarge hP
  let x : ℝ := Real.rpow (Real.log (P : ℝ)) lambda₃
  let Y : ℕ := Nat.floor x
  have hx : 2 ≤ x := by simpa [x] using hlarge
  have hYcast : (Y : ℝ) ≤ x := by
    dsimp [Y]
    exact Nat.floor_le (Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast hP.le)) _)
  have hfloor : x < (Y : ℝ) + 1 := by
    dsimp [Y]
    exact Nat.lt_floor_add_one x
  have hYlower : x / 2 ≤ (Y : ℝ) := by nlinarith
  have hYpos : 0 < Y := by
    have : (1 : ℝ) ≤ (Y : ℝ) := by nlinarith
    exact_mod_cast this
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hfrac : (2 : ℝ) / Y ≤ 4 / x := by
    apply (div_le_div_iff₀ (by exact_mod_cast hYpos) hxpos).2
    nlinarith [hYlower]
  refine ⟨hP, ?_⟩
  intro M
  have hbase := sum_prime_inverseSquare_weight_le (Y := Y) (M := M) hYpos
  calc
    (∑ p ∈ (Finset.Icc Y M).filter Nat.Prime,
        (M : ℝ) / ((p : ℝ) ^ 2)) ≤ (2 : ℝ) * M / Y := hbase
    _ = (M : ℝ) * ((2 : ℝ) / Y) := by ring
    _ ≤ (M : ℝ) * (4 / x) :=
      mul_le_mul_of_nonneg_left hfrac (Nat.cast_nonneg M)
    _ = (4 : ℝ) * M / x := by ring
    _ = (4 : ℝ) * M / Real.rpow (Real.log P) lambda₃ := by
      simp [x]

/-- The finite repeated-pair family inherits Hua's logarithmic saving from
the same prime-square tail, uniformly over every product bound `M`. -/
theorem eventually_real_card_repeatedPrimeProductPairs_logCutoff_le
    {lambda₃ : ℝ} (h₃ : 0 < lambda₃) :
    ∀ᶠ P : ℕ in Filter.atTop,
      1 < P ∧ ∀ M : ℕ,
        ((repeatedPrimeProductPairs
          (Nat.floor (Real.rpow (Real.log P) lambda₃)) M).card : ℝ) ≤
            (4 : ℝ) * M / Real.rpow (Real.log P) lambda₃ := by
  have hlog : Filter.Tendsto (fun P : ℕ => Real.log (P : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hcutoff : Filter.Tendsto
      (fun P : ℕ => Real.rpow (Real.log (P : ℝ)) lambda₃)
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop h₃).comp hlog
  have hlarge : ∀ᶠ P : ℕ in Filter.atTop,
      2 ≤ Real.rpow (Real.log (P : ℝ)) lambda₃ :=
    hcutoff.eventually (Filter.eventually_atTop.2 ⟨2, fun _ h => h⟩)
  have hPlarge : ∀ᶠ P : ℕ in Filter.atTop, 1 < P :=
    Filter.eventually_gt_atTop (1 : ℕ)
  filter_upwards [hlarge, hPlarge] with P hlarge hP
  let x : ℝ := Real.rpow (Real.log (P : ℝ)) lambda₃
  let Y : ℕ := Nat.floor x
  have hx : 2 ≤ x := by simpa [x] using hlarge
  have hYcast : (Y : ℝ) ≤ x := by
    dsimp [Y]
    exact Nat.floor_le (Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast hP.le)) _)
  have hfloor : x < (Y : ℝ) + 1 := by
    dsimp [Y]
    exact Nat.lt_floor_add_one x
  have hYlower : x / 2 ≤ (Y : ℝ) := by nlinarith
  have hYpos : 0 < Y := by
    have : (1 : ℝ) ≤ (Y : ℝ) := by nlinarith
    exact_mod_cast this
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hfrac : (2 : ℝ) / Y ≤ 4 / x := by
    apply (div_le_div_iff₀ (by exact_mod_cast hYpos) hxpos).2
    nlinarith [hYlower]
  refine ⟨hP, ?_⟩
  intro M
  calc
    ((repeatedPrimeProductPairs Y M).card : ℝ) ≤ (2 : ℝ) * M / Y :=
      real_card_repeatedPrimeProductPairs_le hYpos
    _ = (M : ℝ) * (2 / Y) := by ring
    _ ≤ (M : ℝ) * (4 / x) :=
      mul_le_mul_of_nonneg_left hfrac (Nat.cast_nonneg M)
    _ = (4 : ℝ) * M / x := by ring
    _ = (4 : ℝ) * M / Real.rpow (Real.log P) lambda₃ := by
      simp [x]

/-- Hua's logarithmic saving also bounds the norm of any unit-bounded sum
over the repeated-prime pair family, uniformly in its product limit. -/
theorem eventually_norm_sum_repeatedPrimeProductPairs_logCutoff_le
    {lambda₃ : ℝ} (h₃ : 0 < lambda₃) :
    ∀ᶠ P : ℕ in Filter.atTop,
      1 < P ∧ ∀ M : ℕ, ∀ f : ℕ × ℕ → ℂ,
        (∀ z ∈ repeatedPrimeProductPairs
          (Nat.floor (Real.rpow (Real.log P) lambda₃)) M, ‖f z‖ ≤ 1) →
        ‖∑ z ∈ repeatedPrimeProductPairs
          (Nat.floor (Real.rpow (Real.log P) lambda₃)) M, f z‖ ≤
            (4 : ℝ) * M / Real.rpow (Real.log P) lambda₃ := by
  filter_upwards
    [eventually_real_card_repeatedPrimeProductPairs_logCutoff_le h₃]
    with P hP
  rcases hP with ⟨hP, hcount⟩
  refine ⟨hP, ?_⟩
  intro M f hf
  calc
    ‖∑ z ∈ repeatedPrimeProductPairs
        (Nat.floor (Real.rpow (Real.log P) lambda₃)) M, f z‖ ≤
        ((repeatedPrimeProductPairs
          (Nat.floor (Real.rpow (Real.log P) lambda₃)) M).card : ℝ) :=
      norm_sum_le_card_of_forall_norm_le_one _ f hf
    _ ≤ (4 : ℝ) * M / Real.rpow (Real.log P) lambda₃ := hcount M

/-- Hua's logarithmic bound remains valid after imposing any extra finite
restrictions on the repeated-pair set. -/
theorem eventually_norm_sum_subset_repeatedPrimeProductPairs_logCutoff_le
    {lambda₃ : ℝ} (h₃ : 0 < lambda₃) :
    ∀ᶠ P : ℕ in Filter.atTop,
      1 < P ∧ ∀ M : ℕ, ∀ S : Finset (ℕ × ℕ),
        S ⊆ repeatedPrimeProductPairs
          (Nat.floor (Real.rpow (Real.log P) lambda₃)) M →
        ∀ f : ℕ × ℕ → ℂ,
          (∀ z ∈ S, ‖f z‖ ≤ 1) →
          ‖∑ z ∈ S, f z‖ ≤
            (4 : ℝ) * M / Real.rpow (Real.log P) lambda₃ := by
  filter_upwards
    [eventually_real_card_repeatedPrimeProductPairs_logCutoff_le h₃]
    with P hP
  rcases hP with ⟨hP, hcount⟩
  refine ⟨hP, ?_⟩
  intro M S hS f hf
  calc
    ‖∑ z ∈ S, f z‖ ≤ (S.card : ℝ) :=
      norm_sum_le_card_of_forall_norm_le_one S f hf
    _ ≤ ((repeatedPrimeProductPairs
          (Nat.floor (Real.rpow (Real.log P) lambda₃)) M).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hS
    _ ≤ (4 : ℝ) * M / Real.rpow (Real.log P) lambda₃ := hcount M

/-- The source-shaped exceptional family in Hua step 8 inherits the natural
logarithmic cutoff estimate, uniformly in the upper product bound, factor
count, and unit-bounded summand. -/
theorem eventually_norm_sum_huaRepeatedStepEightPairs_logCutoff_le
    {lambda₃ : ℝ} (h₃ : 0 < lambda₃) :
    ∀ᶠ P : ℕ in Filter.atTop,
      1 < P ∧ ∀ M s : ℕ, ∀ f : ℕ × ℕ → ℂ,
        (∀ z ∈ huaRepeatedStepEightPairs
          (Nat.floor (Real.rpow (Real.log P) lambda₃)) M s, ‖f z‖ ≤ 1) →
        ‖∑ z ∈ huaRepeatedStepEightPairs
          (Nat.floor (Real.rpow (Real.log P) lambda₃)) M s, f z‖ ≤
            (4 : ℝ) * M / Real.rpow (Real.log P) lambda₃ := by
  filter_upwards
    [eventually_norm_sum_subset_repeatedPrimeProductPairs_logCutoff_le h₃]
    with P hP
  rcases hP with ⟨hP, hbound⟩
  refine ⟨hP, ?_⟩
  intro M s f hf
  exact hbound M _ (Finset.filter_subset _ _) f hf

/-- Any fixed logarithmic loss is absorbed by the square-root saving in
Hua's initial-interval remainder. This scalar form can be multiplied by the
number of omitted terms without changing the main `P/(log P)^K` scale. -/
theorem eventually_sqrt_rpow_le_scale_div_log_pow (K : ℕ) :
    ∀ᶠ P : ℝ in Filter.atTop,
      1 < P ∧
        P ^ (1 / 2 : ℝ) ≤ P / (Real.log P) ^ K := by
  have hlittleO :
      (fun P : ℝ => Real.log P ^ K) =o[Filter.atTop]
        (fun P : ℝ => P ^ (1 / 2 : ℝ)) := by
    simpa only [Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (s := (1 / 2 : ℝ)) (K : ℝ)
        (by norm_num : (0 : ℝ) < 1 / 2))
  have hbound := hlittleO.bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hbound, Filter.eventually_gt_atTop (1 : ℝ)]
      with P hbound hP
  have hlogpos : 0 < Real.log P := Real.log_pos hP
  have hlognonneg : 0 ≤ Real.log P := hlogpos.le
  have hlogpow : 0 ≤ (Real.log P) ^ K := pow_nonneg hlognonneg K
  have hrootnonneg : 0 ≤ P ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one hP)) _
  have hpowerbound : (Real.log P) ^ K ≤ P ^ (1 / 2 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlogpow,
      Real.norm_eq_abs, abs_of_nonneg hrootnonneg, one_mul] using hbound
  have hhalfSq :
      P ^ (1 / 2 : ℝ) * P ^ (1 / 2 : ℝ) = P := by
    calc
      P ^ (1 / 2 : ℝ) * P ^ (1 / 2 : ℝ) =
          P ^ ((1 / 2 : ℝ) + 1 / 2) :=
        (Real.rpow_add (lt_trans zero_lt_one hP) _ _).symm
      _ = P ^ (1 : ℝ) := by
        rw [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num]
      _ = P := Real.rpow_one _
  have hprod :
      P ^ (1 / 2 : ℝ) * (Real.log P) ^ K ≤ P := by
    calc
      P ^ (1 / 2 : ℝ) * (Real.log P) ^ K ≤
          P ^ (1 / 2 : ℝ) * P ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hpowerbound hrootnonneg
      _ = P := hhalfSq
  refine ⟨hP, ?_⟩
  exact (le_div_iff₀ (pow_pos hlogpos K)).2 hprod

/-- The natural square-root endpoint used by Hua's finite initial interval is
also negligible at every fixed logarithmic saving. -/
theorem eventually_natSqrt_le_scale_div_log_pow (K : ℕ) :
    ∀ᶠ P : ℕ in Filter.atTop,
      1 < P ∧
        (Nat.sqrt P : ℝ) ≤
          (P : ℝ) / (Real.log (P : ℝ)) ^ K := by
  have hreal := (tendsto_natCast_atTop_atTop :
    Filter.Tendsto (fun P : ℕ => (P : ℝ)) Filter.atTop Filter.atTop).eventually
      (eventually_sqrt_rpow_le_scale_div_log_pow K)
  have hPlarge : ∀ᶠ P : ℕ in Filter.atTop, 1 < P :=
    Filter.eventually_gt_atTop (1 : ℕ)
  filter_upwards [hreal, hPlarge] with P hreal hP
  have hNatSquare : (Nat.sqrt P : ℝ) * (Nat.sqrt P : ℝ) ≤ (P : ℝ) := by
    exact_mod_cast (Nat.sqrt_le P)
  have hNatNonneg : 0 ≤ (Nat.sqrt P : ℝ) := by positivity
  have hRealRootNonneg : 0 ≤ (P : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  have hRealRootSq :
      (P : ℝ) ^ (1 / 2 : ℝ) * (P : ℝ) ^ (1 / 2 : ℝ) = (P : ℝ) := by
    calc
      (P : ℝ) ^ (1 / 2 : ℝ) * (P : ℝ) ^ (1 / 2 : ℝ) =
          (P : ℝ) ^ ((1 / 2 : ℝ) + 1 / 2) :=
        (Real.rpow_add (by positivity : (0 : ℝ) < P) _ _).symm
      _ = (P : ℝ) ^ (1 : ℝ) := by
        rw [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num]
      _ = P := Real.rpow_one _
  have hNatRoot : (Nat.sqrt P : ℝ) ≤ (P : ℝ) ^ (1 / 2 : ℝ) := by
    nlinarith [sq_nonneg ((Nat.sqrt P : ℝ) - (P : ℝ) ^ (1 / 2 : ℝ))]
  refine ⟨hP, ?_⟩
  calc
    (Nat.sqrt P : ℝ) ≤ (P : ℝ) ^ (1 / 2 : ℝ) := hNatRoot
    _ ≤ (P : ℝ) / (Real.log (P : ℝ)) ^ K := hreal.2

/-- Split the first divisor moment at a threshold: bounded divisor counts
contribute at most `T M`, while the divisor-rich tail is controlled by the
cubic moment. This is the coefficient-mass form used in Vaughan Type II. -/
theorem sum_divisorCount_le_threshold_split {M : ℕ} (T : ℝ) (hT : 0 < T) :
    (∑ n ∈ Finset.Icc 1 M, (n.divisors.card : ℝ)) ≤
      T * M + ((M : ℝ) * (1 + Real.log (M : ℝ)) ^ 7) / T ^ 2 := by
  classical
  let I := Finset.Icc 1 M
  let f : ℕ → ℝ := fun n => (n.divisors.card : ℝ)
  let B := I.filter fun n => T ≤ f n
  let G := I.filter fun n => ¬ T ≤ f n
  have hsplitPoint : ∀ n ∈ I,
      f n = (if T ≤ f n then f n else 0) + (if T ≤ f n then 0 else f n) := by
    intro n hn
    by_cases h : T ≤ f n <;> simp [h]
  have hsplit : (∑ n ∈ I, f n) = (∑ n ∈ B, f n) + (∑ n ∈ G, f n) := by
    calc
      (∑ n ∈ I, f n) =
          ∑ n ∈ I, ((if T ≤ f n then f n else 0) + (if T ≤ f n then 0 else f n)) := by
            apply Finset.sum_congr rfl
            intro n hn
            exact hsplitPoint n hn
      _ = (∑ n ∈ B, f n) + (∑ n ∈ G, f n) := by
            have hBsum : (∑ n ∈ B, f n) =
                ∑ n ∈ I, if T ≤ f n then f n else 0 := by
              simp [B, Finset.sum_filter]
            have hGsum : (∑ n ∈ G, f n) =
                ∑ n ∈ I, if T ≤ f n then 0 else f n := by
              calc
                (∑ n ∈ G, f n) =
                    ∑ n ∈ I, if ¬ T ≤ f n then f n else 0 := by
                      simp [G, Finset.sum_filter]
                _ = ∑ n ∈ I, if T ≤ f n then 0 else f n := by
                  apply Finset.sum_congr rfl
                  intro n hn
                  by_cases h : T ≤ f n <;> simp [h]
            rw [Finset.sum_add_distrib, ← hBsum, ← hGsum]
  have hcardG : (G.card : ℝ) ≤ M := by
    calc
      (G.card : ℝ) ≤ I.card := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      _ = M := by simp [I, Nat.card_Icc]
  have hG : (∑ n ∈ G, f n) ≤ T * M := by
    calc
      (∑ n ∈ G, f n) ≤ ∑ _n ∈ G, T := by
        apply Finset.sum_le_sum
        intro n hn
        have hmem := Finset.mem_filter.mp hn
        have hnot : ¬ T ≤ f n := hmem.2
        have hle : f n ≤ T := le_of_not_ge hnot
        simpa using hle
      _ = T * (G.card : ℝ) := by simp [mul_comm]
      _ ≤ T * M := mul_le_mul_of_nonneg_left hcardG hT.le
  have hBscaled : T ^ 2 * (∑ n ∈ B, f n) ≤
      (M : ℝ) * (1 + Real.log (M : ℝ)) ^ 7 := by
    simpa [B, I, f] using
      (divisorThresholdedTail_le (M := M) (P := fun n => T ≤
        (n.divisors.card : ℝ)) T 1 hT (by norm_num) (by
          intro n hn hnrich
          simpa using hnrich))
  have hB : (∑ n ∈ B, f n) ≤
      ((M : ℝ) * (1 + Real.log (M : ℝ)) ^ 7) / T ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hT)).2
    simpa [mul_comm] using hBscaled
  calc
    (∑ n ∈ Finset.Icc 1 M, (n.divisors.card : ℝ)) =
        (∑ n ∈ B, f n) + (∑ n ∈ G, f n) := by
          simpa [I, f] using hsplit
    _ ≤ ((M : ℝ) * (1 + Real.log (M : ℝ)) ^ 7) / T ^ 2 + T * M :=
      add_le_add hB hG
    _ = T * M + ((M : ℝ) * (1 + Real.log (M : ℝ)) ^ 7) / T ^ 2 := by ring

end CookMagyarCircle
end SystolicGrowth

#print axioms SystolicGrowth.CookMagyarCircle.card_divisors_eq_two_pow_card_primeFactors_of_squarefree
#print axioms SystolicGrowth.CookMagyarCircle.squarefree_le_primeFactorBound_pow
#print axioms SystolicGrowth.CookMagyarCircle.log_le_card_primeFactors_mul_log_of_squarefree
#print axioms SystolicGrowth.CookMagyarCircle.card_primeFactors_ge_log_ratio_of_squarefree
#print axioms SystolicGrowth.CookMagyarCircle.two_pow_le_card_divisors_of_squarefree
#print axioms SystolicGrowth.CookMagyarCircle.rpow_two_log_ratio_le_card_divisors_of_squarefree
#print axioms SystolicGrowth.CookMagyarCircle.smoothSquarefree_divisorTail_le
#print axioms SystolicGrowth.CookMagyarCircle.eventually_log_pow_le_rpow_two_truncated_log_ratio
#print axioms SystolicGrowth.CookMagyarCircle.eventually_truncatedLog_smoothSquarefree_divisorTail_le
#print axioms SystolicGrowth.CookMagyarCircle.eventually_truncatedLog_natFloor_smoothSquarefree_divisorTail_le
#print axioms SystolicGrowth.CookMagyarCircle.log_nat_lower_of_truncatedLog_cutoff
#print axioms SystolicGrowth.CookMagyarCircle.eventually_hua_truncatedLog_smoothSquarefree_divisorTail_le
#print axioms SystolicGrowth.CookMagyarCircle.eventually_hua_truncatedLog_smoothSquarefree_count_le
#print axioms SystolicGrowth.CookMagyarCircle.card_primeFactorsAtLeastCutoff_mul_prime
#print axioms SystolicGrowth.CookMagyarCircle.card_primeFactorsAtLeastCutoff_div_prime
#print axioms SystolicGrowth.CookMagyarCircle.repeatedLargeFactor_quotient_existsUnique
#print axioms SystolicGrowth.CookMagyarCircle.sum_primeFactorsAtLeastCutoff_div_recount
#print axioms SystolicGrowth.CookMagyarCircle.mem_primeFactorQuotientPairs_iff
#print axioms SystolicGrowth.CookMagyarCircle.mem_primeFactorQuotientPairs_iff_prime_product_mem
#print axioms SystolicGrowth.CookMagyarCircle.sum_primeFactorQuotientPairs_eq_recount
#print axioms SystolicGrowth.CookMagyarCircle.card_positiveRepeatedMultiples_le_div_sq
#print axioms SystolicGrowth.CookMagyarCircle.card_repeatedPrimeProductPairs_le_divisor_sum
#print axioms SystolicGrowth.CookMagyarCircle.real_card_repeatedPrimeProductPairs_le
#print axioms SystolicGrowth.CookMagyarCircle.norm_sum_repeatedPrimeProductPairs_le
#print axioms SystolicGrowth.CookMagyarCircle.norm_sum_le_card_of_forall_norm_le_one
#print axioms SystolicGrowth.CookMagyarCircle.norm_sum_subset_repeatedPrimeProductPairs_le
#print axioms SystolicGrowth.CookMagyarCircle.mem_repeatedPrimeProductPairs_iff
#print axioms SystolicGrowth.CookMagyarCircle.huaRepeatedStepEightPair_quotient_existsUnique
#print axioms SystolicGrowth.CookMagyarCircle.norm_sum_huaRepeatedStepEightPairs_le
#print axioms SystolicGrowth.CookMagyarCircle.sum_prime_inverseSquare_Icc_le
#print axioms SystolicGrowth.CookMagyarCircle.sum_prime_inverseSquare_weight_le
#print axioms SystolicGrowth.CookMagyarCircle.eventually_sum_prime_inverseSquare_logCutoff_le
#print axioms SystolicGrowth.CookMagyarCircle.eventually_real_card_repeatedPrimeProductPairs_logCutoff_le
#print axioms SystolicGrowth.CookMagyarCircle.eventually_norm_sum_repeatedPrimeProductPairs_logCutoff_le
#print axioms SystolicGrowth.CookMagyarCircle.eventually_norm_sum_subset_repeatedPrimeProductPairs_logCutoff_le
#print axioms SystolicGrowth.CookMagyarCircle.eventually_norm_sum_huaRepeatedStepEightPairs_logCutoff_le
#print axioms SystolicGrowth.CookMagyarCircle.eventually_sqrt_rpow_le_scale_div_log_pow
#print axioms SystolicGrowth.CookMagyarCircle.eventually_natSqrt_le_scale_div_log_pow
#print axioms SystolicGrowth.CookMagyarCircle.eventually_log_pow_le_rpow_two_log_ratio
