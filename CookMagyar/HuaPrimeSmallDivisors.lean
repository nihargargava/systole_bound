module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.GeneralCubicWeyl
public import CookMagyar.HuaPrimeSieveIdentity

@[expose] public section

/-!
# Hua's actual small-divisor prime-sieve branch

Endpoint-uniform Type-I progression bounds are applied to both prefixes of
the exact quotient interval `(sqrt(P)/d,P/d]`. The original quadratic,
linear and constant coefficients are arbitrary throughout. Möbius weights
are bounded by one, not removed from a signed identity.
-/

open scoped BigOperators
open Filter

namespace SystolicGrowth.CookMagyarCircle

open CookMagyarArcs

private theorem sum_Ioc_eq_prefix_sub (A B : ℕ) (hAB : A ≤ B) (f : ℕ → ℂ) :
    (∑ m ∈ Finset.Ioc A B, f m) =
      (∑ m ∈ Finset.Icc 1 B, f m) - ∑ m ∈ Finset.Icc 1 A, f m := by
  classical
  have hd : Disjoint (Finset.Icc 1 A) (Finset.Ioc A B) := by
    apply Finset.disjoint_left.mpr
    intro m hm hm'
    exact (not_lt_of_ge (Finset.mem_Icc.mp hm).2) (Finset.mem_Ioc.mp hm').1
  have hu : Finset.Icc 1 A ∪ Finset.Ioc A B = Finset.Icc 1 B := by
    ext m
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hs := Finset.sum_union hd (f := f)
  rw [hu] at hs
  exact (eq_sub_iff_add_eq).mpr (by simpa only [add_comm] using hs.symm)

/-- Every actual small-divisor prefix has a coefficient-uniform Type-I
bound. Prefix zero is handled separately, so no lower length is assumed. -/
theorem eventually_hua_smallDivisor_generalCubic_prefix_norm_le
    (sigma sigma0 lambda1 saving : ℕ)
    (hbudget : 8 * (sigma0 + lambda1) + 8 ≤ sigma)
    (hsaving : 1 ≤ saving)
    (hcutoff : 3 * (lambda1 + 2) + 20 * saving ≤ sigma0) :
    ∀ᶠ P : ℕ in atTop,
      ∀ a q : ℕ, Nat.Coprime a q →
        Real.log ((P : ℝ) + 2) ^ sigma < (q : ℝ) →
        (q : ℝ) ≤ (P : ℝ) ^ 3 / Real.log ((P : ℝ) + 2) ^ sigma →
        ∀ b c e : ℝ, ∀ d K : ℕ, 0 < d →
          (d : ℝ) ≤ Real.log ((P : ℝ) + 2) ^ lambda1 → K ≤ P / d →
          ‖∑ m ∈ Finset.Icc 1 K,
            generalCubicPhase ((a : ℝ) / q) b c e (d * m)‖ ≤
              3806466 * (P : ℝ) /
                ((d : ℝ) * (Nat.floor (Real.log ((P : ℝ) + 2)) : ℝ) ^ saving) := by
  have hweyl :=
    eventually_hua_cubic_progression_partial_weyl_norm_bound_uniform_coefficients_uniform_a
      1 (by norm_num) sigma sigma0 lambda1 0 saving (by simpa using hbudget)
      hsaving (by simpa using hcutoff)
  filter_upwards [hweyl] with P hP
  intro a q hac hqLower hqUpper b c e d K hd hdlog hKP
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  by_cases hK : K = 0
  · simp only [hK, Finset.Icc_eq_empty_of_lt (by norm_num : (0 : ℕ) < 1),
      Finset.sum_empty, norm_zero]
    positivity
  have hKpos : 0 < K := Nat.pos_of_ne_zero hK
  have hdP : d ≤ P := by
    have hone : 1 ≤ P / d := (show 1 ≤ K from hKpos).trans hKP
    simpa only [one_mul] using (Nat.le_div_iff_mul_le hd).mp hone
  have hqpos : 0 < q := by
    have hlogpos : 0 < Real.log ((P : ℝ) + 2) :=
      Real.log_pos (by exact_mod_cast (show 1 < P + 2 by omega))
    have hqR : (0 : ℝ) < q := (pow_pos hlogpos sigma).trans hqLower
    exact_mod_cast hqR
  have hα : ((a : ℝ) / q) * (d : ℝ) ^ 3 =
      rationalCenter ((a * d ^ 3) / Nat.gcd q (a * d ^ 3))
        (q / Nat.gcd q (a * d ^ 3)) := by
    simpa only [rationalCenter, zero_mul, add_zero] using
      generalCubicLeadingCoeff_affineApprox_reduced
        (rationalCenter a q) 0 a q d hqpos (by simp)
  have hquot : (d * K - d) / d = K - 1 := by
    rw [show d * K - d = d * (K - 1) by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]]
    exact Nat.mul_div_cancel_left (K - 1) hd
  have hphase := sum_multiples_generalCubicPhase_eq_progression
    ((a : ℝ) / q) b c e d (d * K) hd
    (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left d hKpos)
  rw [Nat.mul_div_cancel_left K hd, hquot,
    show K - 1 + 1 = K by omega] at hphase
  have hN : K - 1 ≤ (P - d) / d := by
    apply (Nat.le_div_iff_mul_le hd).mpr
    rw [Nat.sub_mul, Nat.one_mul]
    exact Nat.sub_le_sub_right ((Nat.le_div_iff_mul_le hd).mp hKP) d
  have hbound := hP a
    (3 * (((a : ℝ) / q)) * d * (d : ℝ) ^ 2 + b * (d : ℝ) ^ 2)
    (3 * (((a : ℝ) / q)) * (d : ℝ) ^ 2 * d + 2 * b * d * d + c * d)
    ((((a : ℝ) / q)) * (d : ℝ) ^ 3 + b * (d : ℝ) ^ 2 + c * d + e)
    d 1 q 1 (by norm_num) hd (by norm_num) (by simp) (by simpa using hdP)
    hac hdlog (by simp) hqLower hqUpper (K - 1) (by simpa using hN)
  have hprefix :
      ‖∑ m ∈ Finset.Icc 1 K,
        generalCubicPhase ((a : ℝ) / q) b c e (d * m)‖ ≤
      1268822 * (((P - d) / d + 2 : ℕ) : ℝ) /
        (Nat.floor (Real.log ((P : ℝ) + 2)) : ℝ) ^ saving := by
    rw [hphase]
    nth_rw 1 [hα]
    simpa only [Nat.gcd_one_left, Nat.div_one, Nat.mul_one, generalCubicExpSum,
      show K - 1 + 1 = K by omega, Nat.cast_add, Nat.cast_ofNat] using hbound
  have hlength : (((P - d) / d + 2 : ℕ) : ℝ) ≤ 3 * ((P : ℝ) / d) := by
    have hdiv : (((P - d) / d : ℕ) : ℝ) ≤ (P : ℝ) / d :=
      (Nat.cast_div_le).trans (div_le_div_of_nonneg_right
        (by exact_mod_cast Nat.sub_le P d) hdR.le)
    have hone : (1 : ℝ) ≤ (P : ℝ) / d :=
      (le_div_iff₀ hdR).mpr
        (by simpa only [one_mul] using (show (d : ℝ) ≤ P by exact_mod_cast hdP))
    push_cast
    linarith only [hdiv, hone]
  calc
    _ ≤ 1268822 * (((P - d) / d + 2 : ℕ) : ℝ) /
        (Nat.floor (Real.log ((P : ℝ) + 2)) : ℝ) ^ saving := hprefix
    _ ≤ 1268822 * (3 * ((P : ℝ) / d)) /
        (Nat.floor (Real.log ((P : ℝ) + 2)) : ℝ) ^ saving :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlength (by norm_num)) (by positivity)
    _ = _ := by ring

/-- The exact large quotient interval for each small sieve divisor is
bounded by two actual Type-I prefixes, retaining every lower coefficient. -/
theorem eventually_hua_smallDivisor_generalCubic_interval_norm_le
    (sigma sigma0 lambda1 saving : ℕ)
    (hbudget : 8 * (sigma0 + lambda1) + 8 ≤ sigma)
    (hsaving : 1 ≤ saving)
    (hcutoff : 3 * (lambda1 + 2) + 20 * saving ≤ sigma0) :
    ∀ᶠ P : ℕ in atTop,
      ∀ a q : ℕ, Nat.Coprime a q →
        Real.log ((P : ℝ) + 2) ^ sigma < (q : ℝ) →
        (q : ℝ) ≤ (P : ℝ) ^ 3 / Real.log ((P : ℝ) + 2) ^ sigma →
        ∀ b c e : ℝ, ∀ d : ℕ, 0 < d →
          (d : ℝ) ≤ Real.log ((P : ℝ) + 2) ^ lambda1 →
          ‖∑ m ∈ Finset.Ioc (Nat.sqrt P / d) (P / d),
            generalCubicPhase ((a : ℝ) / q) b c e (d * m)‖ ≤
              7612932 * (P : ℝ) /
                ((d : ℝ) * (Nat.floor (Real.log ((P : ℝ) + 2)) : ℝ) ^ saving) := by
  filter_upwards [eventually_hua_smallDivisor_generalCubic_prefix_norm_le
    sigma sigma0 lambda1 saving hbudget hsaving hcutoff] with P hP
  intro a q hac hqLower hqUpper b c e d hd hdlog
  have hroot : Nat.sqrt P / d ≤ P / d := Nat.div_le_div_right (Nat.sqrt_le_self P)
  rw [sum_Ioc_eq_prefix_sub _ _ hroot]
  have hupper := hP a q hac hqLower hqUpper b c e d (P / d) hd hdlog le_rfl
  have hlower := hP a q hac hqLower hqUpper b c e d (Nat.sqrt P / d) hd hdlog hroot
  calc
    _ ≤ ‖∑ m ∈ Finset.Icc 1 (P / d),
          generalCubicPhase ((a : ℝ) / q) b c e (d * m)‖ +
        ‖∑ m ∈ Finset.Icc 1 (Nat.sqrt P / d),
          generalCubicPhase ((a : ℝ) / q) b c e (d * m)‖ := norm_sub_le _ _
    _ ≤ 3806466 * (P : ℝ) /
          ((d : ℝ) * (Nat.floor (Real.log ((P : ℝ) + 2)) : ℝ) ^ saving) +
        3806466 * (P : ℝ) /
          ((d : ℝ) * (Nat.floor (Real.log ((P : ℝ) + 2)) : ℝ) ^ saving) :=
      add_le_add hupper hlower
    _ = _ := by ring

/-- The actual Möbius-weighted small-divisor sieve branch has the prescribed
logarithmic saving, with the exact square-root quotient endpoint retained.
The exponent budget is deliberately coarse and uniform in all coefficients. -/
theorem eventually_hua_prime_smallDivisors_generalCubic_logSaving_le
    (sigma sigma0 lambda1 saving decay : ℕ)
    (hbudget : 8 * (sigma0 + lambda1) + 8 ≤ sigma)
    (hsaving : 1 ≤ saving)
    (hcutoff : 3 * (lambda1 + 2) + 20 * saving ≤ sigma0)
    (hdecay : decay + lambda1 ≤ saving) :
    ∀ᶠ P : ℕ in atTop,
      ∀ a q : ℕ, Nat.Coprime a q →
        Real.log ((P : ℝ) + 2) ^ sigma < (q : ℝ) →
        (q : ℝ) ≤ (P : ℝ) ^ 3 / Real.log ((P : ℝ) + 2) ^ sigma →
        ∀ b c e : ℝ,
          ‖∑ d ∈ (huaStepEightSieveProduct P).divisors.filter
              (fun d : ℕ => (d : ℝ) ≤ Real.rpow (Real.log P) (lambda1 : ℝ)),
            (ArithmeticFunction.moebius d : ℂ) *
              ∑ m ∈ Finset.Ioc (Nat.sqrt P / d) (P / d),
                generalCubicPhase ((a : ℝ) / q) b c e (d * m)‖ ≤
            (7612932 * (2 : ℝ) ^ saving) * P / Real.log (P : ℝ) ^ decay := by
  classical
  have hlog : Tendsto (fun P : ℕ => Real.log (P : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_hua_smallDivisor_generalCubic_interval_norm_le
    sigma sigma0 lambda1 saving hbudget hsaving hcutoff,
    hlog.eventually_ge_atTop (2 : ℝ)] with P hP hLtwo
  intro a q hac hqLower hqUpper b c e
  simp only [Real.rpow_eq_pow, Real.rpow_natCast]
  let L := Real.log (P : ℝ)
  let Lplus := Real.log ((P : ℝ) + 2)
  let B := Nat.floor Lplus
  let I := (huaStepEightSieveProduct P).divisors.filter
    (fun d : ℕ => (d : ℝ) ≤ L ^ lambda1)
  have hLone : 1 ≤ L := by dsimp [L]; linarith
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hLone
  have hPpos : 0 < P := by
    by_contra h
    have hzero : P = 0 := Nat.eq_zero_of_not_pos h
    norm_num [hzero] at hLtwo
  have hLLplus : L ≤ Lplus :=
    Real.log_le_log (by exact_mod_cast hPpos) (by linarith)
  have hBhalf : L / 2 ≤ (B : ℝ) := by
    have hfloor := Nat.lt_floor_add_one Lplus
    change Lplus < (B : ℝ) + 1 at hfloor
    have htwo : 2 ≤ L := hLtwo
    linarith only [hLLplus, hfloor, htwo]
  have hBpos : (0 : ℝ) < B :=
    (div_pos hLpos (by norm_num : (0 : ℝ) < 2)).trans_le hBhalf
  have hcard : (I.card : ℝ) ≤ L ^ lambda1 := by
    have hsub : I ⊆ Finset.Icc 1 (Nat.floor (L ^ lambda1)) := by
      intro d hd
      rcases Finset.mem_filter.mp hd with ⟨hdH, hdL⟩
      exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hdH, Nat.le_floor hdL⟩
    calc
      _ ≤ ((Finset.Icc 1 (Nat.floor (L ^ lambda1))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      _ = (Nat.floor (L ^ lambda1) : ℝ) := by simp [Nat.card_Icc]
      _ ≤ _ := Nat.floor_le (pow_nonneg hLpos.le _)
  have hterm (d : ℕ) (hd : d ∈ I) :
      ‖(ArithmeticFunction.moebius d : ℂ) *
        ∑ m ∈ Finset.Ioc (Nat.sqrt P / d) (P / d),
          generalCubicPhase ((a : ℝ) / q) b c e (d * m)‖ ≤
        7612932 * (P : ℝ) / (B : ℝ) ^ saving := by
    rcases Finset.mem_filter.mp hd with ⟨hdH, hdL⟩
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hdH
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hdpos
    have hdlog : (d : ℝ) ≤ Lplus ^ lambda1 :=
      hdL.trans (pow_le_pow_left₀ hLpos.le hLLplus _)
    have hdsq := (squarefree_huaStepEightSieveProduct P).squarefree_of_dvd
      (Nat.mem_divisors.mp hdH).1
    have hsign : (ArithmeticFunction.moebius d : ℂ) =
        (-1 : ℂ) ^ d.primeFactors.card := by
      exact_mod_cast hua_moebius_eq_primeFactor_sign_of_squarefree d hdsq
    have hmu : ‖(ArithmeticFunction.moebius d : ℂ)‖ = 1 := by
      rw [hsign, norm_pow]
      norm_num
    rw [norm_mul, hmu, one_mul]
    calc
      _ ≤ 7612932 * (P : ℝ) / ((d : ℝ) * (B : ℝ) ^ saving) :=
        hP a q hac hqLower hqUpper b c e d hdpos hdlog
      _ ≤ _ := by
        apply div_le_div_of_nonneg_left (by positivity) (pow_pos hBpos _)
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hdR
          (pow_nonneg hBpos.le saving)
  have hsum :
      ‖∑ d ∈ I, (ArithmeticFunction.moebius d : ℂ) *
        ∑ m ∈ Finset.Ioc (Nat.sqrt P / d) (P / d),
          generalCubicPhase ((a : ℝ) / q) b c e (d * m)‖ ≤
        7612932 * (P : ℝ) * (L ^ lambda1 / (B : ℝ) ^ saving) := by
    calc
      _ ≤ ∑ d ∈ I, ‖(ArithmeticFunction.moebius d : ℂ) *
          ∑ m ∈ Finset.Ioc (Nat.sqrt P / d) (P / d),
            generalCubicPhase ((a : ℝ) / q) b c e (d * m)‖ := norm_sum_le _ _
      _ ≤ ∑ _d ∈ I, 7612932 * (P : ℝ) / (B : ℝ) ^ saving :=
        Finset.sum_le_sum hterm
      _ = (I.card : ℝ) * (7612932 * (P : ℝ) / (B : ℝ) ^ saving) := by simp
      _ ≤ L ^ lambda1 * (7612932 * (P : ℝ) / (B : ℝ) ^ saving) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by ring
  have hBpower : L ^ saving ≤ (2 : ℝ) ^ saving * (B : ℝ) ^ saving := by
    calc
      _ ≤ (2 * (B : ℝ)) ^ saving :=
        pow_le_pow_left₀ hLpos.le (by linarith only [hBhalf]) saving
      _ = _ := mul_pow _ _ _
  have hratio : L ^ lambda1 / (B : ℝ) ^ saving ≤ (2 : ℝ) ^ saving / L ^ decay := by
    apply (div_le_div_iff₀ (pow_pos hBpos saving) (pow_pos hLpos decay)).mpr
    calc
      _ = L ^ (lambda1 + decay) := (pow_add _ _ _).symm
      _ ≤ L ^ saving := pow_le_pow_right₀ hLone (by omega)
      _ ≤ _ := hBpower
  change ‖∑ d ∈ I, (ArithmeticFunction.moebius d : ℂ) *
    ∑ m ∈ Finset.Ioc (Nat.sqrt P / d) (P / d),
      generalCubicPhase ((a : ℝ) / q) b c e (d * m)‖ ≤
    (7612932 * (2 : ℝ) ^ saving) * P / L ^ decay
  calc
    _ ≤ 7612932 * (P : ℝ) * (L ^ lambda1 / (B : ℝ) ^ saving) := hsum
    _ ≤ 7612932 * (P : ℝ) * ((2 : ℝ) ^ saving / L ^ decay) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = (7612932 * (2 : ℝ) ^ saving) * P / L ^ decay := by ring

#print axioms eventually_hua_smallDivisor_generalCubic_prefix_norm_le
#print axioms eventually_hua_smallDivisor_generalCubic_interval_norm_le
#print axioms eventually_hua_prime_smallDivisors_generalCubic_logSaving_le

end SystolicGrowth.CookMagyarCircle
