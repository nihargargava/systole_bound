module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.SingularSeriesEulerProductBridge
public import CookMagyar.LogCutoff
public import Mathlib.Topology.Algebra.InfiniteSum.Ring

@[expose] public section

open Filter
open scoped Topology

/-! Absolute convergence of the cubic singular series and its Euler product. -/

namespace SystolicGrowth.CookMagyarFiniteFourier

/-- The nonconstant prime-power tail for the maximum coefficient norm. -/
noncomputable def primePowerMaximumNormTail (p n : ℕ) : ℝ :=
  ∑' k : ℕ, singularSeriesTermNormMaximum n (p ^ (k + 1))

theorem singularSeriesTermNormMaximum_nonneg (n q : ℕ) :
    0 ≤ singularSeriesTermNormMaximum n q := by
  by_cases hq : q = 0
  · simp [singularSeriesTermNormMaximum, hq]
  · obtain ⟨t, ht⟩ := singularSeriesTermNormMaximum_attained n q (Nat.pos_of_ne_zero hq)
    rw [ht]
    exact norm_nonneg _

/-- Split the maximum prime-power tail into its first coefficient and all
higher powers. -/
theorem primePowerMaximumNormTail_eq_prime_add_higher
    {p n : ℕ} (hp : p.Prime) (hn : 33 ≤ n) :
    primePowerMaximumNormTail p n =
      singularSeriesTermNormMaximum n p +
        ∑' k : ℕ, singularSeriesTermNormMaximum n (p ^ (k + 2)) := by
  let f : ℕ → ℝ := fun k ↦ singularSeriesTermNormMaximum n (p ^ (k + 1))
  have hpow := summable_singularSeriesTermNormMaximum_prime_powers hp hn
  have hinj : Function.Injective (fun k : ℕ ↦ k + 1) := by
    intro a b h
    exact Nat.succ_injective h
  have hshift : Summable f := by
    simpa only [f, Function.comp_def] using hpow.comp_injective hinj
  have h := hshift.sum_add_tsum_nat_add 1
  change (∑' k : ℕ, f k) =
    singularSeriesTermNormMaximum n p +
      ∑' k : ℕ, singularSeriesTermNormMaximum n (p ^ (k + 2))
  calc
    (∑' k : ℕ, f k) = f 0 + ∑' k : ℕ, f (k + 1) := by
      simpa only [Finset.sum_range_one] using h.symm
    _ = _ := by simp [f, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- For large primes, the sum of maximum coefficient norms over all
nonconstant prime powers is bounded by a fixed-arity `p⁻²` majorant. -/
theorem primePowerMaximumNormTail_le_inv_sq
    {p n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 33 ≤ n) :
    primePowerMaximumNormTail p n ≤
      (((40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n) + 1) * (p : ℝ)⁻¹ ^ 2 := by
  have hsplit := primePowerMaximumNormTail_eq_prime_add_higher hp hn
  have hprime : singularSeriesTermNormMaximum n p ≤
      ((40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n) * (p : ℝ)⁻¹ ^ 2 := by
    have hprime' := singularSeriesTermNormMaximum_prime_le_inv_pow hp hp5 hn
    have hpone : (1 : ℝ) ≤ p := by
      have hponeNat : 1 ≤ p := by omega
      exact_mod_cast hponeNat
    have hinv : (p : ℝ)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ (by positivity : (0 : ℝ) < p)]
      exact hpone
    have hinvpow : (p : ℝ)⁻¹ ^ 7 ≤ (p : ℝ)⁻¹ ^ 2 :=
      pow_le_pow_of_le_one (by positivity) hinv (by norm_num)
    calc
      singularSeriesTermNormMaximum n p ≤
          (40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n / (p : ℝ) ^ 7 := hprime'
      _ = ((40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n) * (p : ℝ)⁻¹ ^ 7 := by
        rw [div_eq_mul_inv, inv_pow]
      _ ≤ ((40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n) * (p : ℝ)⁻¹ ^ 2 :=
        mul_le_mul_of_nonneg_left hinvpow (by positivity)
  have htail :
      (∑' k : ℕ, singularSeriesTermNormMaximum n (p ^ (k + 2))) ≤
        (p : ℝ)⁻¹ ^ 2 := by
    letI : NeZero p := ⟨hp.ne_zero⟩
    have hbase := CookMagyarPrimePower.tsum_singularSeriesTermNormMaximum_higherPrimePower_le
      hp hp5 hn
    have hr := inv_pow_le_half_of_prime_large hp5 hn
    let r : ℝ := ((p : ℝ)⁻¹) ^ (n - 2)
    let A : ℝ := ((2 : ℝ) ^ n * ((5 : ℝ) / 4) ^ (n - 1)) *
      (1 + (p : ℝ))
    have hden : 0 < 1 - r := by dsimp [r]; linarith
    have hr' : r ≤ 1 / 2 := by simpa [r] using hr
    have hAr : 0 ≤ A * r := by dsimp [A, r]; positivity
    have hhalf : A * r / (1 - r) ≤ 2 * (A * r) := by
      apply (div_le_iff₀ hden).2
      nlinarith [hr']
    have hnum := tail_numerator_le_inv_sq_of_prime_large hp5 hn
    calc
      _ ≤ A * r / (1 - r) := by simpa [A, r, mul_assoc, mul_div_assoc] using hbase
      _ ≤ 2 * (A * r) := hhalf
      _ ≤ (p : ℝ)⁻¹ ^ 2 := by simpa [A, r, mul_assoc] using hnum
  rw [hsplit]
  calc
    _ ≤ (((40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n) * (p : ℝ)⁻¹ ^ 2) +
        (p : ℝ)⁻¹ ^ 2 := add_le_add hprime htail
    _ = _ := by ring

/-- The maximum coefficient norm has summable prime-power tails over the
primes, including the finite exceptions at 2 and 3. -/
theorem summable_primePowerMaximumNormTail {n : ℕ} (hn : 33 ≤ n) :
    Summable (fun p : Nat.Primes ↦ primePowerMaximumNormTail (p : ℕ) n) := by
  let A : ℝ := (40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n + 1
  let C : ℝ := max A (max (4 * primePowerMaximumNormTail 2 n)
    (9 * primePowerMaximumNormTail 3 n))
  have hnat : Summable (fun q : ℕ => ((q : ℝ) ^ 2)⁻¹) :=
    Real.summable_nat_pow_inv.mpr (by norm_num)
  have hinj : Function.Injective (fun p : Nat.Primes ↦ (p : ℕ)) :=
    Subtype.val_injective
  have hprimes : Summable (fun p : Nat.Primes ↦ ((p : ℝ) ^ 2)⁻¹) := by
    simpa only [Function.comp_def] using hnat.comp_injective hinj
  have hmajor : Summable (fun p : Nat.Primes ↦ C * (p : ℝ)⁻¹ ^ 2) := by
    simpa only [inv_pow] using hprimes.mul_left C
  apply hmajor.of_nonneg_of_le
  · intro p
    exact tsum_nonneg (fun k ↦ singularSeriesTermNormMaximum_nonneg n
      ((p : ℕ) ^ (k + 1)))
  · intro p
    by_cases hp5 : 5 ≤ (p : ℕ)
    · have hbase := primePowerMaximumNormTail_le_inv_sq p.property hp5 hn
      exact hbase.trans (mul_le_mul_of_nonneg_right (le_max_left A _) (by positivity))
    · have hp2 : 2 ≤ (p : ℕ) := p.property.two_le
      have hp4 : (p : ℕ) ≤ 4 := by omega
      have hpne4 : (p : ℕ) ≠ 4 := by
        intro hfour
        have hprime := p.property
        norm_num [hfour] at hprime
      have hp23 : (p : ℕ) = 2 ∨ (p : ℕ) = 3 := by omega
      rcases hp23 with htwo | hthree
      · have hC : 4 * primePowerMaximumNormTail 2 n ≤ C :=
          (le_max_left _ _).trans (le_max_right _ _)
        have hbound : primePowerMaximumNormTail 2 n ≤ C * (2 : ℝ)⁻¹ ^ 2 := by
          norm_num at *
          nlinarith
        simpa [htwo] using hbound
      · have hC : 9 * primePowerMaximumNormTail 3 n ≤ C :=
          (le_max_right _ _).trans (le_max_right _ _)
        have hbound : primePowerMaximumNormTail 3 n ≤ C * (3 : ℝ)⁻¹ ^ 2 := by
          norm_num at *
          nlinarith
        simpa [hthree] using hbound

/-- Global absolute summability of the coefficient maxima. CRT
multiplicativity and the summable prime-power maximum tails combine through
the multiplicative-majorant argument. -/
theorem summable_singularSeriesTermNormMaximum {n : ℕ} (hn : 33 ≤ n) :
    Summable (fun q : ℕ ↦ singularSeriesTermNormMaximum n q) := by
  apply summable_of_multiplicative_of_primePowerTails_summable
  · simp [singularSeriesTermNormMaximum]
  · exact singularSeriesTermNormMaximum_one n
  · intro m r hcop
    by_cases hm : m = 0
    · subst m
      have hr : r = 1 := by simpa [Nat.Coprime] using hcop
      subst r
      simp [singularSeriesTermNormMaximum_one]
    · by_cases hr : r = 0
      · subst r
        have hm' : m = 1 := by
          simpa [Nat.Coprime, Nat.coprime_comm] using hcop
        subst m
        simp [singularSeriesTermNormMaximum_one]
      · exact singularSeriesTermNormMaximum_mul_of_coprime n m r
          (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hr) hcop
  · exact singularSeriesTermNormMaximum_nonneg n
  · intro p hp
    have hpow := summable_singularSeriesTermNormMaximum_prime_powers hp hn
    apply hpow.congr
    intro k
    rw [Real.norm_eq_abs, abs_of_nonneg
      (singularSeriesTermNormMaximum_nonneg n ((p : ℕ) ^ k))]
  · exact summable_primePowerMaximumNormTail hn

/-- For large primes, the contributions of powers at least two have a
target-independent `p⁻²` majorant. -/
theorem higherPrimePowerNormTail_le_inv_sq
    {p n T : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 33 ≤ n) :
    (∑' k : ℕ, ‖singularSeriesTerm n T (p ^ (k + 2))‖) ≤
      (p : ℝ)⁻¹ ^ 2 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hbase := CookMagyarPrimePower.tsum_norm_singularSeriesTerm_higherPrimePower_le
    (T := T) hp hp5 hn
  have hr := inv_pow_le_half_of_prime_large hp5 hn
  let r : ℝ := ((p : ℝ)⁻¹) ^ (n - 2)
  let A : ℝ := ((2 : ℝ) ^ n * ((5 : ℝ) / 4) ^ (n - 1)) *
    (1 + (p : ℝ))
  have hden : 0 < 1 - r := by dsimp [r]; linarith
  have hAr : 0 ≤ A * r := by dsimp [A, r]; positivity
  have hhalf : A * r / (1 - r) ≤ 2 * (A * r) := by
    apply (div_le_iff₀ hden).2
    nlinarith
  have hnum := tail_numerator_le_inv_sq_of_prime_large hp5 hn
  calc
    (∑' k : ℕ, ‖singularSeriesTerm n T (p ^ (k + 2))‖) ≤
        A * r / (1 - r) := by
          simpa [A, r, mul_assoc, mul_div_assoc] using hbase
    _ ≤ 2 * (A * r) := hhalf
    _ ≤ (p : ℝ)⁻¹ ^ 2 := by simpa [A, r, mul_assoc] using hnum

/-- Separate the prime term from the absolutely summable higher-power tail. -/
theorem primePowerNormTail_eq_prime_add_higher
    {p n T : ℕ} (hp : p.Prime) (hn : 33 ≤ n) :
    primePowerNormTail p n T =
      ‖singularSeriesTerm n T p‖ +
        ∑' k : ℕ, ‖singularSeriesTerm n T (p ^ (k + 2))‖ := by
  let f : ℕ → ℝ := fun k => ‖singularSeriesTerm n T (p ^ (k + 1))‖
  have hpow := summable_norm_singularSeriesTerm_prime_powers (T := T) hp hn
  have hinj : Function.Injective (fun k : ℕ => k + 1) := by
    intro a b h
    exact Nat.succ_injective h
  have hshift : Summable f := by
    simpa only [f, Function.comp_def] using hpow.comp_injective hinj
  have h := hshift.sum_add_tsum_nat_add 1
  change (∑' k : ℕ, f k) =
    ‖singularSeriesTerm n T p‖ +
      ∑' k : ℕ, ‖singularSeriesTerm n T (p ^ (k + 2))‖
  calc
    (∑' k : ℕ, f k) = f 0 + ∑' k : ℕ, f (k + 1) := by
      simpa only [Finset.sum_range_one] using h.symm
    _ = _ := by
      have hfirst : f 0 = ‖singularSeriesTerm n T p‖ := by simp [f]
      rw [hfirst]

/-- The prime-modulus coefficient has a fixed-arity `p⁻²` majorant. -/
theorem norm_singularSeriesTerm_prime_le_inv_sq
    {p n T : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 33 ≤ n) :
    ‖singularSeriesTerm n T p‖ ≤
      ((40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n) * (p : ℝ)⁻¹ ^ 2 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  let A : ℝ := (40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n
  have hprime := norm_singularSeriesTerm_prime_le_inv_pow hp hp5
    (by omega : 32 ≤ n) T
  have hpone : (1 : ℝ) ≤ p := by
    have hponeNat : 1 ≤ p := by omega
    exact_mod_cast hponeNat
  have hinv : (p : ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity : (0 : ℝ) < p)]
    exact hpone
  have hinvpow : (p : ℝ)⁻¹ ^ 7 ≤ (p : ℝ)⁻¹ ^ 2 :=
    pow_le_pow_of_le_one (by positivity) hinv (by norm_num)
  calc
    ‖singularSeriesTerm n T p‖ ≤ A / (p : ℝ) ^ 7 := by simpa [A] using hprime
    _ = A * (p : ℝ)⁻¹ ^ 7 := by rw [div_eq_mul_inv, inv_pow]
    _ ≤ A * (p : ℝ)⁻¹ ^ 2 :=
      mul_le_mul_of_nonneg_left hinvpow (by dsimp [A]; positivity)
    _ = _ := by rfl

/-- The complete nontrivial local norm tail has a fixed-arity `p⁻²` bound. -/
theorem primePowerNormTail_le_inv_sq
    {p n T : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 33 ≤ n) :
    primePowerNormTail p n T ≤
      (((40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n) + 1) * (p : ℝ)⁻¹ ^ 2 := by
  have hsplit := primePowerNormTail_eq_prime_add_higher (T := T) hp hn
  have hprime' := norm_singularSeriesTerm_prime_le_inv_sq (T := T) hp hp5 hn
  have htail := higherPrimePowerNormTail_le_inv_sq hp hp5 hn (T := T)
  rw [hsplit]
  calc
    _ ≤ (((40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n) * (p : ℝ)⁻¹ ^ 2) +
        (p : ℝ)⁻¹ ^ 2 := add_le_add hprime' htail
    _ = _ := by ring

/-- Every local norm tail is nonnegative. -/
theorem primePowerNormTail_nonneg (p n T : ℕ) :
    0 ≤ primePowerNormTail p n T := by
  unfold primePowerNormTail
  exact tsum_nonneg (fun _ => norm_nonneg _)

/-- A crude target-independent bound for an individual singular-series
coefficient: the trivial bound for the inner complete sum leaves at most one
factor of the totient. -/
private theorem norm_singularSeriesTerm_le_totient
    {q n T : ℕ} (hq : 0 < q) (_hn : 1 ≤ n) :
    ‖singularSeriesTerm n T q‖ ≤ (Nat.totient q : ℝ) := by
  rw [singularSeriesTerm_of_pos n T hq]
  letI : NeZero q := ⟨hq.ne'⟩
  unfold singularSeriesCoefficient
  let φ : ℝ := Nat.totient q
  have hφ : 0 < φ := by
    dsimp [φ]
    exact_mod_cast (Nat.totient_pos.mpr hq)
  have hsum :
      ‖∑ a : (ZMod q)ˣ,
          unitCubicExponentialSum (a : ZMod q) ^ n *
            standardAdditiveCharacter (-((a : ZMod q) * (T : ZMod q)))‖ ≤
        φ * φ ^ n := by
    calc
      _ ≤ ∑ a : (ZMod q)ˣ,
          ‖unitCubicExponentialSum (a : ZMod q) ^ n *
            standardAdditiveCharacter (-((a : ZMod q) * (T : ZMod q)))‖ := norm_sum_le _ _
      _ ≤ ∑ _a : (ZMod q)ˣ, φ ^ n := by
        apply Finset.sum_le_sum
        intro a _
        rw [norm_mul, AddChar.norm_apply, norm_pow]
        have hunit : ‖unitCubicExponentialSum (a : ZMod q)‖ ≤ φ := by
          unfold unitCubicExponentialSum
          calc
            _ ≤ ∑ u : (ZMod q)ˣ,
                ‖standardAdditiveCharacter
                  ((a : ZMod q) * cubicResidue (u : ZMod q))‖ := norm_sum_le _ _
            _ = φ := by simp [φ, AddChar.norm_apply, ZMod.card_units_eq_totient]
        calc
          ‖unitCubicExponentialSum (a : ZMod q)‖ ^ n * 1 ≤ φ ^ n * 1 :=
            mul_le_mul_of_nonneg_right
              (pow_le_pow_left₀ (norm_nonneg _) hunit _) (by norm_num)
          _ = φ ^ n := by ring
      _ = φ * φ ^ n := by
        simp [Finset.sum_const, φ, ZMod.card_units_eq_totient, nsmul_eq_mul]
  have hnorminv : ‖((Nat.totient q : ℂ)⁻¹)‖ = φ⁻¹ := by
    simp [φ]
  have hpow : ‖((Nat.totient q : ℂ)⁻¹) ^ n‖ = φ⁻¹ ^ n := by
    rw [norm_pow, hnorminv]
  calc
    ‖((Nat.totient q : ℂ)⁻¹) ^ n *
        ∑ a : (ZMod q)ˣ,
          unitCubicExponentialSum (a : ZMod q) ^ n *
            standardAdditiveCharacter (-((a : ZMod q) * (T : ZMod q)))‖
        ≤ (φ⁻¹ ^ n) * (φ * φ ^ n) := by
          rw [norm_mul, hpow]
          exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = φ := by
      rw [inv_pow]
      calc
        (φ ^ n)⁻¹ * (φ * φ ^ n) = ((φ ^ n)⁻¹ * φ ^ n) * φ := by ring
        _ = 1 * φ := by rw [inv_mul_cancel₀ (pow_ne_zero _ hφ.ne')]
        _ = φ := by ring
    _ = (Nat.totient q : ℝ) := by rfl

/-- The exceptional `2`-adic local norm tail is uniformly bounded by the
three surviving conductors `2`, `4`, and `8`. -/
theorem primePowerNormTail_two_le_seven
    {n T : ℕ} (hn : 33 ≤ n) :
    primePowerNormTail 2 n T ≤ 7 := by
  have hzero (k : ℕ) :
      singularSeriesTerm n T (2 ^ (k + 4)) = 0 :=
    CookMagyarPrimePower.singularSeriesTerm_two_power_exponent_eq_zero
      (m := k + 2) (T := T) (by omega) (by omega : 0 < n)
  change (∑' k : ℕ, ‖singularSeriesTerm n T (2 ^ (k + 1))‖) ≤ 7
  rw [tsum_eq_sum (s := Finset.range 3) (fun k hk => ?_)]
  · norm_num [Finset.sum_range_succ]
    have h2 := norm_singularSeriesTerm_le_totient (q := 2) (n := n) (T := T)
      (by norm_num) (by omega)
    have h4 := norm_singularSeriesTerm_le_totient (q := 4) (n := n) (T := T)
      (by norm_num) (by omega)
    have h8 := norm_singularSeriesTerm_le_totient (q := 8) (n := n) (T := T)
      (by norm_num) (by omega)
    norm_num at h2
    have hφ4 : Nat.totient 4 = 2 := by
      simpa [show 4 = 2 ^ 2 by norm_num] using
        (Nat.totient_prime_pow Nat.prime_two (by norm_num : 0 < 2))
    have hφ8 : Nat.totient 8 = 4 := by
      simpa [show 8 = 2 ^ 3 by norm_num] using
        (Nat.totient_prime_pow Nat.prime_two (by norm_num : 0 < 3))
    rw [hφ4] at h4
    rw [hφ8] at h8
    norm_num at h2 h4 h8
    linarith
  ·
    have hk : 3 ≤ k := by
      have : ¬ k < 3 := by
        intro hlt
        exact hk (Finset.mem_range.mpr hlt)
      omega
    have heq : k + 1 = (k - 3) + 4 := by omega
    rw [heq]
    simpa using hzero (k - 3)

/-- The exceptional `3`-adic local norm tail is uniformly bounded by its
single surviving prime-level conductor. -/
theorem primePowerNormTail_three_le_two
    {n T : ℕ} (hn : 33 ≤ n) :
    primePowerNormTail 3 n T ≤ 2 := by
  change (∑' k : ℕ, ‖singularSeriesTerm n T (3 ^ (k + 1))‖) ≤ 2
  rw [tsum_eq_sum (s := Finset.range 1) (fun k hk => ?_)]
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    have h3 := norm_singularSeriesTerm_le_totient (q := 3) (n := n) (T := T)
      (by norm_num) (by omega)
    have hφ3 : Nat.totient 3 = 2 := Nat.totient_prime (by norm_num)
    rw [hφ3] at h3
    simpa using h3
  ·
    have hk : 1 ≤ k := by
      have : ¬ k < 1 := by
        intro hlt
        exact hk (Finset.mem_range.mpr hlt)
      omega
    have hterm : singularSeriesTerm n T (3 ^ (k + 1)) = 0 := by
      exact CookMagyarPrimePower.singularSeriesTerm_three_power_eq_zero
        (T := T) (by omega) (by omega : 0 < n)
    simp [hterm]

/-- The local norm tails are summable over all primes, including `2` and `3`. -/
theorem summable_primePowerNormTail
    {n T : ℕ} (hn : 33 ≤ n) :
    Summable (fun p : Nat.Primes => primePowerNormTail (p : ℕ) n T) := by
  let A : ℝ := (40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n + 1
  let C : ℝ := max A (max (4 * primePowerNormTail 2 n T)
    (9 * primePowerNormTail 3 n T))
  have hnat : Summable (fun q : ℕ => ((q : ℝ) ^ 2)⁻¹) :=
    Real.summable_nat_pow_inv.mpr (by norm_num)
  have hinj : Function.Injective (fun p : Nat.Primes => (p : ℕ)) :=
    Subtype.val_injective
  have hprimes : Summable (fun p : Nat.Primes => ((p : ℝ) ^ 2)⁻¹) := by
    simpa only [Function.comp_def] using hnat.comp_injective hinj
  have hmajor : Summable (fun p : Nat.Primes => C * (p : ℝ)⁻¹ ^ 2) := by
    simpa only [inv_pow] using hprimes.mul_left C
  apply hmajor.of_nonneg_of_le
  · intro p
    exact primePowerNormTail_nonneg _ _ _
  · intro p
    by_cases hp5 : 5 ≤ (p : ℕ)
    · have hbase := primePowerNormTail_le_inv_sq p.property hp5 hn (T := T)
      have hC : A ≤ C := le_max_left _ _
      exact hbase.trans (mul_le_mul_of_nonneg_right hC (by positivity))
    · have hp2 : 2 ≤ (p : ℕ) := p.property.two_le
      have hp4 : (p : ℕ) ≤ 4 := by omega
      have hpne4 : (p : ℕ) ≠ 4 := by
        intro hfour
        have hprime := p.property
        norm_num [hfour] at hprime
      have hp23 : (p : ℕ) = 2 ∨ (p : ℕ) = 3 := by omega
      rcases hp23 with htwo | hthree
      · have hC : 4 * primePowerNormTail 2 n T ≤ C :=
          (le_max_left _ _).trans (le_max_right _ _)
        have hbound : primePowerNormTail 2 n T ≤ C * (2 : ℝ)⁻¹ ^ 2 := by
          norm_num at *
          nlinarith
        simpa [htwo] using hbound
      · have hC : 9 * primePowerNormTail 3 n T ≤ C :=
          (le_max_right _ _).trans (le_max_right _ _)
        have hbound : primePowerNormTail 3 n T ≤ C * (3 : ℝ)⁻¹ ^ 2 := by
          norm_num at *
          nlinarith
        simpa [hthree] using hbound

/-- A target-independent majorant for every local prime-power norm tail.
The constant absorbs the two exceptional primes as well as the large-prime
estimate. -/
noncomputable def primePowerNormTailUniformMajorant (n : ℕ) (p : Nat.Primes) : ℝ :=
  max ((40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n + 1) 28 * (p : ℝ)⁻¹ ^ 2

/-- Every local norm tail is dominated by the same summable majorant,
independently of the target `T`. -/
theorem primePowerNormTail_le_uniformMajorant
    {n T : ℕ} (hn : 33 ≤ n) (p : Nat.Primes) :
    primePowerNormTail (p : ℕ) n T ≤ primePowerNormTailUniformMajorant n p := by
  let A : ℝ := (40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n + 1
  by_cases hp5 : 5 ≤ (p : ℕ)
  · have hbase := primePowerNormTail_le_inv_sq p.property hp5 hn (T := T)
    dsimp [primePowerNormTailUniformMajorant]
    exact hbase.trans (mul_le_mul_of_nonneg_right (le_max_left A 28) (by positivity))
  · have hp2 : 2 ≤ (p : ℕ) := p.property.two_le
    have hp4 : (p : ℕ) ≤ 4 := by omega
    have hpne4 : (p : ℕ) ≠ 4 := by
      intro hfour
      have hprime := p.property
      norm_num [hfour] at hprime
    have hp23 : (p : ℕ) = 2 ∨ (p : ℕ) = 3 := by omega
    rcases hp23 with htwo | hthree
    · have htail := primePowerNormTail_two_le_seven (n := n) (T := T) hn
      have hbound : primePowerNormTail 2 n T ≤
          max A 28 * (2 : ℝ)⁻¹ ^ 2 := by
        have h28 : 28 ≤ max A 28 := le_max_right _ _
        norm_num at htail ⊢
        nlinarith
      simpa [primePowerNormTailUniformMajorant, htwo, A] using hbound
    · have htail := primePowerNormTail_three_le_two (n := n) (T := T) hn
      have hbound : primePowerNormTail 3 n T ≤
          max A 28 * (3 : ℝ)⁻¹ ^ 2 := by
        have h28 : 28 ≤ max A 28 := le_max_right _ _
        norm_num at htail ⊢
        nlinarith
      simpa [primePowerNormTailUniformMajorant, hthree, A] using hbound

/-- The explicit target-independent local-tail majorant is summable over
primes. -/
theorem summable_primePowerNormTailUniformMajorant (n : ℕ) :
    Summable (fun p : Nat.Primes => primePowerNormTailUniformMajorant n p) := by
  let C : ℝ := max ((40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n + 1) 28
  have hnat : Summable (fun q : ℕ => ((q : ℝ) ^ 2)⁻¹) :=
    Real.summable_nat_pow_inv.mpr (by norm_num)
  have hinj : Function.Injective (fun p : Nat.Primes => (p : ℕ)) :=
    Subtype.val_injective
  have hprimes : Summable (fun p : Nat.Primes => ((p : ℝ) ^ 2)⁻¹) := by
    simpa only [Function.comp_def] using hnat.comp_injective hinj
  have hsum : Summable (fun p : Nat.Primes => C * (p : ℝ)⁻¹ ^ 2) := by
    simpa only [inv_pow] using hprimes.mul_left C
  simpa [primePowerNormTailUniformMajorant, C] using hsum

/-- The cubic singular series converges absolutely at every target when
`n ≥ 33`. -/
theorem summable_norm_singularSeriesTerm
    {n T : ℕ} (hn : 33 ≤ n) :
    Summable (fun q : ℕ => ‖singularSeriesTerm n T q‖) := by
  let f : ℕ → ℝ := fun q => ‖singularSeriesTerm n T q‖
  have hf0 : f 0 = 0 := by simp [f]
  have hf1 : f 1 = 1 := by simp [f]
  have hmul : ∀ {m q : ℕ}, m.Coprime q → f (m * q) = f m * f q := by
    intro m q hcop
    simp only [f, singularSeriesTerm_mul_of_coprime n T hcop, norm_mul]
  have hnonneg : ∀ q, 0 ≤ f q := fun _ => norm_nonneg _
  have hlocal : ∀ {p : ℕ}, p.Prime →
      Summable (fun k : ℕ => ‖f (p ^ k)‖) := by
    intro p hp
    simpa only [f, Real.norm_eq_abs, abs_norm] using
      (summable_norm_singularSeriesTerm_prime_powers (T := T) hp hn)
  have htails : Summable (fun p : Nat.Primes =>
      ∑' k : ℕ, f ((p : ℕ) ^ (k + 1))) := by
    simpa only [f, primePowerNormTail] using
      (summable_primePowerNormTail (T := T) hn)
  exact summable_of_multiplicative_of_primePowerTails_summable
    hf0 hf1 hmul hnonneg hlocal htails

/-- The singular-series truncation error is dominated uniformly in the target
by the tail of the globally summable maximum coefficient envelope. -/
theorem norm_singularSeries_sub_truncated_le_maximum_tail
    {n T : ℕ} (hn : 33 ≤ n) (Q : ℕ) :
    ‖singularSeries n T - truncatedSingularSeries n T Q‖ ≤
      ∑' k : ℕ, singularSeriesTermNormMaximum n (k + (Q + 1)) := by
  have htrunc (Q : ℕ) :
      truncatedSingularSeries n T Q =
        ∑ q ∈ Finset.range (Q + 1), singularSeriesTerm n T q := by
    have hterm0 : singularSeriesTerm n T 0 = 0 := singularSeriesTerm_zero n T
    induction Q with
    | zero => simp [truncatedSingularSeries, hterm0]
    | succ Q ih =>
      change (∑ q ∈ Finset.Icc 1 (Q + 1), singularSeriesTerm n T q) =
        ∑ q ∈ Finset.range ((Q + 1) + 1), singularSeriesTerm n T q
      rw [Finset.sum_Icc_succ_top (a := 1) (b := Q) (by omega),
        Finset.sum_range_succ]
      have ih' :
          (∑ q ∈ Finset.Icc 1 Q, singularSeriesTerm n T q) =
            ∑ q ∈ Finset.range (Q + 1), singularSeriesTerm n T q := by
        simpa only [truncatedSingularSeries] using ih
      rw [ih']
  have hsum : Summable (fun q : ℕ ↦ singularSeriesTerm n T q) :=
    Summable.of_norm (summable_norm_singularSeriesTerm hn)
  have hdecomp : singularSeries n T =
      truncatedSingularSeries n T Q +
        ∑' k : ℕ, singularSeriesTerm n T (k + (Q + 1)) := by
    unfold singularSeries
    rw [htrunc Q]
    exact (hsum.sum_add_tsum_nat_add (Q + 1)).symm
  have hdiff : singularSeries n T - truncatedSingularSeries n T Q =
      ∑' k : ℕ, singularSeriesTerm n T (k + (Q + 1)) := by
    rw [hdecomp]
    ring
  have hnorm := summable_norm_singularSeriesTerm (T := T) hn
  have hinj : Function.Injective (fun k : ℕ ↦ k + (Q + 1)) := by
    intro a b h
    change a + (Q + 1) = b + (Q + 1) at h
    omega
  have hnormTail : Summable
      (fun k : ℕ ↦ ‖singularSeriesTerm n T (k + (Q + 1))‖) :=
    hnorm.comp_injective hinj
  have hmax := summable_singularSeriesTermNormMaximum hn
  have hmaxTail : Summable
      (fun k : ℕ ↦ singularSeriesTermNormMaximum n (k + (Q + 1))) :=
    hmax.comp_injective hinj
  have htaille := Summable.tsum_le_tsum
    (fun k ↦ norm_singularSeriesTerm_le_maximum n (k + (Q + 1)) T (by omega))
    hnormTail hmaxTail
  calc
    ‖singularSeries n T - truncatedSingularSeries n T Q‖ =
        ‖∑' k : ℕ, singularSeriesTerm n T (k + (Q + 1))‖ := by rw [hdiff]
    _ ≤ ∑' k : ℕ, ‖singularSeriesTerm n T (k + (Q + 1))‖ :=
      norm_tsum_le_tsum_norm hnormTail
    _ ≤ ∑' k : ℕ, singularSeriesTermNormMaximum n (k + (Q + 1)) := htaille

/-- The target-independent maximum-coefficient tails tend to zero as the
denominator cutoff tends to infinity. -/
theorem tendsto_singularSeriesTermNormMaximum_tail
    {n : ℕ} (hn : 33 ≤ n) :
    Tendsto
      (fun Q : ℕ =>
        ∑' k : ℕ, singularSeriesTermNormMaximum n (k + (Q + 1)))
      atTop (𝓝 0) := by
  let f : ℕ → ℝ := singularSeriesTermNormMaximum n
  have hf : Summable f := by
    simpa only [f] using summable_singularSeriesTermNormMaximum hn
  have hpartial : Tendsto
      (fun Q : ℕ => ∑ k ∈ Finset.range (Q + 1), f k)
      atTop (𝓝 (∑' k : ℕ, f k)) := by
    exact hf.hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
  have hcomplement : Tendsto
      (fun Q : ℕ => (∑' k : ℕ, f k) -
        ∑ k ∈ Finset.range (Q + 1), f k)
      atTop (𝓝 0) := by
    convert tendsto_const_nhds.sub hpartial using 1 <;> simp
  have htail_eq (Q : ℕ) :
      (∑' k : ℕ, f k) - ∑ k ∈ Finset.range (Q + 1), f k =
        ∑' k : ℕ, f (k + (Q + 1)) := by
    have hsplit := hf.sum_add_tsum_nat_add (Q + 1)
    have hsplit' :
        (∑ k ∈ Finset.range (Q + 1), f k) +
          ∑' k : ℕ, f (k + (Q + 1)) = ∑' k : ℕ, f k := by
      simpa only [f] using hsplit
    linarith
  convert hcomplement using 1
  funext Q
  exact (htail_eq Q).symm

/-- Uniform in the integer target, the singular series is approximated by
its denominator truncation once the cutoff is sufficiently large. -/
theorem eventually_norm_singularSeries_sub_truncated_lt
    {n : ℕ} (hn : 33 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Q : ℕ in atTop, ∀ T : ℕ,
      ‖singularSeries n T - truncatedSingularSeries n T Q‖ < ε := by
  have htail := tendsto_singularSeriesTermNormMaximum_tail hn
  have hevent : ∀ᶠ Q : ℕ in atTop,
      (∑' k : ℕ, singularSeriesTermNormMaximum n (k + (Q + 1))) < ε :=
    htail.eventually (Iio_mem_nhds hε)
  filter_upwards [hevent] with Q hQ T
  exact (norm_singularSeries_sub_truncated_le_maximum_tail
    (T := T) hn Q).trans_lt hQ

/-- Any cutoff tending to infinity gives singular-series truncation
convergence uniformly over a target that may itself vary with the scale. -/
theorem eventually_norm_singularSeries_sub_truncated_lt_of_cutoff
    {n : ℕ} (hn : 33 ≤ n) (cutoff : ℕ → ℕ)
    (hcutoff : Tendsto cutoff atTop atTop) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ T : ℕ,
      ‖singularSeries n T -
        truncatedSingularSeries n T (cutoff N)‖ < ε := by
  have hQ := eventually_norm_singularSeries_sub_truncated_lt hn hε
  filter_upwards [hcutoff.eventually hQ] with N hN T
  exact hN T

/-- The denominator truncation at the project's logarithmic cutoff converges
uniformly over targets, including targets varying with the scale. -/
theorem eventually_norm_singularSeries_sub_logarithmicTruncation_lt
    {n : ℕ} (hn : 33 ≤ n) (A : ℕ) (hA : 0 < A)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ T : ℕ,
      ‖singularSeries n T -
        truncatedSingularSeries n T (CookMagyarCircle.logarithmicDenominatorCutoff A N)‖ < ε :=
  eventually_norm_singularSeries_sub_truncated_lt_of_cutoff hn
    (CookMagyarCircle.logarithmicDenominatorCutoff A)
    (CookMagyarCircle.tendsto_logarithmicDenominatorCutoff A hA) hε

/-- The denominator truncations converge to the full singular series at every
target once absolute convergence has been established. -/
theorem tendsto_truncatedSingularSeries
    {n T : ℕ} (hn : 33 ≤ n) :
    Tendsto (fun Q : ℕ => truncatedSingularSeries n T Q)
      atTop (𝓝 (singularSeries n T)) := by
  have hterm0 : singularSeriesTerm n T 0 = 0 := singularSeriesTerm_zero n T
  have htrunc (Q : ℕ) :
      truncatedSingularSeries n T Q =
        ∑ q ∈ Finset.range (Q + 1), singularSeriesTerm n T q := by
    induction Q with
    | zero => simp [truncatedSingularSeries, hterm0]
    | succ Q ih =>
      change (∑ q ∈ Finset.Icc 1 (Q + 1), singularSeriesTerm n T q) =
        ∑ q ∈ Finset.range ((Q + 1) + 1), singularSeriesTerm n T q
      rw [Finset.sum_Icc_succ_top (a := 1) (b := Q) (by omega),
        Finset.sum_range_succ]
      have ih' :
          (∑ q ∈ Finset.Icc 1 Q, singularSeriesTerm n T q) =
            ∑ q ∈ Finset.range (Q + 1), singularSeriesTerm n T q := by
        simpa only [truncatedSingularSeries] using ih
      rw [ih']
  have hsum : Summable (fun q : ℕ => singularSeriesTerm n T q) :=
    Summable.of_norm (summable_norm_singularSeriesTerm hn)
  have hpartial : Tendsto
      (fun N : ℕ => ∑ q ∈ Finset.range N, singularSeriesTerm n T q)
      atTop (𝓝 (singularSeries n T)) := by
    simpa only [singularSeries] using hsum.hasSum.tendsto_sum_nat
  have hadd : Tendsto (fun Q : ℕ => Q + 1) atTop atTop :=
    Filter.tendsto_add_atTop_nat 1
  have hcomp := hpartial.comp hadd
  have hfunEq :
      (fun Q : ℕ => truncatedSingularSeries n T Q) =
        (fun Q => ∑ q ∈ Finset.range (Q + 1), singularSeriesTerm n T q) :=
    funext htrunc
  rw [hfunEq]
  exact hcomp

/-- The singular series is unconditionally the Euler product of its local
factors when `n ≥ 33`. -/
theorem singularSeries_eq_tprod_primeLocalFactor
    {n T : ℕ} (hn : 33 ≤ n) :
    singularSeries n T = ∏' p : Nat.Primes, primeLocalFactor p n T :=
  singularSeries_eq_tprod_primeLocalFactor_of_summable n T
    (summable_norm_singularSeriesTerm (T := T) hn)

end SystolicGrowth.CookMagyarFiniteFourier

#print axioms SystolicGrowth.CookMagyarFiniteFourier.summable_primePowerMaximumNormTail
#print axioms SystolicGrowth.CookMagyarFiniteFourier.summable_singularSeriesTermNormMaximum
#print axioms SystolicGrowth.CookMagyarFiniteFourier.norm_singularSeries_sub_truncated_le_maximum_tail
#print axioms SystolicGrowth.CookMagyarFiniteFourier.tendsto_singularSeriesTermNormMaximum_tail
#print axioms SystolicGrowth.CookMagyarFiniteFourier.eventually_norm_singularSeries_sub_truncated_lt_of_cutoff
#print axioms SystolicGrowth.CookMagyarFiniteFourier.eventually_norm_singularSeries_sub_logarithmicTruncation_lt
