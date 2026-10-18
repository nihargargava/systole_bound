module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.SingularSeriesAbsoluteConvergence
public import CookMagyar.EulerProductFiniteExceptions
public import CookMagyar.RealEulerProductBridge
public import CookMagyar.LocalPrimeBaseFactorBridge

@[expose] public section

namespace SystolicGrowth.CookMagyarFiniteFourier

open CookMagyarEulerProduct

/-! A target-uniform positive lower bound for the admissible cubic singular series. -/

/-- One three-adic unit solution gives a uniform lower bound for the
three-adic factor. -/
theorem primeLocalFactor_three_re_ge_lower
    {n T : ℕ} (hn : 1 ≤ n) (hT : 24 ∣ T) :
    (3 : ℝ) / (2 : ℝ) ^ n ≤ (primeLocalFactor 3 n T).re := by
  rw [CookMagyarPrimePower.primeLocalFactor_three_eq_normalizedUnitCubicCount
    (by omega), Complex.ofReal_re]
  have hcount : (1 : ℝ) ≤ unitCubicSolutionCount n (T : ZMod 3) := by
    exact_mod_cast unitCubicSolutionCount_pos_three_power
      (n := n) (k := 1) hn hT
  unfold normalizedUnitCubicCount
  norm_num [Nat.totient_prime Nat.prime_three]
  exact (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2 ^ n)).2
    (by nlinarith)

/-- An explicit positive bound at every prime: exact at `2`, and derived
from one nonsingular solution at all other primes. -/
noncomputable def primeLocalUniformLower (n : ℕ) (p : Nat.Primes) : ℝ :=
  if (p : ℕ) = 2 then 8 else
    if (p : ℕ) = 3 then (3 : ℝ) / (2 : ℝ) ^ n else
      (p : ℝ) / (((p : ℕ) - 1 : ℕ) : ℝ) ^ n

/-- Every explicit local lower bound is positive. -/
theorem primeLocalUniformLower_pos (n : ℕ) (p : Nat.Primes) :
    0 < primeLocalUniformLower n p := by
  by_cases hp2 : (p : ℕ) = 2
  · simp [primeLocalUniformLower, hp2]
  by_cases hp3 : (p : ℕ) = 3
  · simp [primeLocalUniformLower, hp3]
  have hp2le : 2 ≤ (p : ℕ) := p.property.two_le
  have hpminus : 0 < (p : ℕ) - 1 := by omega
  simp only [primeLocalUniformLower, hp2, hp3, ↓reduceIte]
  exact div_pos (by exact_mod_cast p.property.pos)
    (pow_pos (by exact_mod_cast hpminus) n)

/-- Each local factor dominates its target-independent prime lower bound. -/
theorem primeLocalFactor_re_ge_uniformLower
    {n T : ℕ} (hn : 33 ≤ n) (hT : 24 ∣ T) (p : Nat.Primes) :
    primeLocalUniformLower n p ≤ (primeLocalFactor p n T).re := by
  by_cases hp2 : (p : ℕ) = 2
  · have h8 : 8 ∣ T := dvd_trans (by norm_num : 8 ∣ 24) hT
    have htwo := CookMagyarPrimePower.primeLocalFactor_two_eq_eight_of_dvd_eight
      (by omega : 0 < n) h8
    simp [primeLocalUniformLower, hp2, htwo]
  by_cases hp3 : (p : ℕ) = 3
  · have hthree := primeLocalFactor_three_re_ge_lower
      (by omega : 1 ≤ n) hT
    simpa [primeLocalUniformLower, hp2, hp3] using hthree
  have hp5 : 5 ≤ (p : ℕ) := by
    have hp2le := p.property.two_le
    have hpne4 : (p : ℕ) ≠ 4 := by
      intro hfour
      have hprime := p.property
      norm_num [hfour] at hprime
    omega
  have hlarge := primeLocalFactor_re_ge_lift_bound_of_prime_ge_five
    p.property hp5 hn (T := T)
  simpa [primeLocalUniformLower, hp2, hp3] using hlarge

/-- All admissible real local-factor products have one positive lower bound
depending only on the arity. -/
theorem exists_uniform_realPrimeLocalFactor_tprod_lower
    {n : ℕ} (hn : 33 ≤ n) :
    ∃ c : ℝ, 0 < c ∧
      ∀ T : ℕ, 24 ∣ T →
        c ≤ ∏' p : Nat.Primes, (primeLocalFactor p n T).re := by
  let C : ℝ := (40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨N₀, hN₀⟩ := exists_square_threshold_cutoff (C := 2 * C)
    (by positivity)
  let N : ℕ := max N₀ 5
  have hSfinite : {p : Nat.Primes | (p : ℕ) < N}.Finite := by
    apply (Set.finite_Iio N).preimage
    intro p _ q _ hpq
    exact Subtype.val_injective hpq
  let S : Finset Nat.Primes := hSfinite.toFinset
  have hS (p : Nat.Primes) : p ∈ S ↔ (p : ℕ) < N := by
    simp [S]
  let a : Nat.Primes → ℝ := fun p => C * (p : ℝ)⁻¹ ^ 2
  let b : Nat.Primes → ℝ := primeLocalUniformLower n
  have hsumNat : Summable (fun q : ℕ => ((q : ℝ) ^ 2)⁻¹) :=
    Real.summable_nat_pow_inv.mpr (by norm_num)
  have hsumPrime : Summable (fun p : Nat.Primes => C * (p : ℝ)⁻¹ ^ 2) := by
    have hinj : Function.Injective (fun p : Nat.Primes => (p : ℕ)) :=
      Subtype.val_injective
    have hpow : Summable (fun p : Nat.Primes => ((p : ℝ) ^ 2)⁻¹) := by
      simpa only [Function.comp_def] using hsumNat.comp_injective hinj
    simpa only [inv_pow] using hpow.mul_left C
  have ha : Summable
      (fun p : {p : Nat.Primes // p ∈ (S : Set Nat.Primes)ᶜ} => a p) := by
    exact hsumPrime.subtype _
  have hhalf : ∀ p : Nat.Primes, p ∉ S → a p ≤ 1 / 2 := by
    intro p hpS
    have hpN : N ≤ (p : ℕ) := Nat.le_of_not_lt ((hS p).not.mp hpS)
    have hpN₀ : N₀ ≤ (p : ℕ) := (Nat.le_max_left _ _).trans hpN
    have hthreshold := hN₀ p hpN₀
    have hppos : 0 < (p : ℝ) ^ 2 := by
      have hp_pos : 0 < (p : ℝ) := by exact_mod_cast p.property.pos
      positivity
    change C * (p : ℝ)⁻¹ ^ 2 ≤ 1 / 2
    rw [inv_pow, ← one_div, mul_one_div]
    apply (div_le_iff₀ hppos).2
    nlinarith
  have hdev : ∀ T : ℕ, ∀ p : Nat.Primes, p ∉ S →
      |(primeLocalFactor p n T).re - 1| ≤ a p := by
    intro T p hpS
    have hpN : N ≤ (p : ℕ) := Nat.le_of_not_lt ((hS p).not.mp hpS)
    have hp5 : 5 ≤ (p : ℕ) := (Nat.le_max_right _ _).trans hpN
    letI : NeZero (p : ℕ) := ⟨p.property.ne_zero⟩
    have hnorm := norm_primeLocalFactor_sub_one_le_rpow_two
      p.property hp5 hn (T := T)
    have hre := Complex.abs_re_le_norm (primeLocalFactor p n T - 1)
    simpa only [a, Complex.sub_re, Complex.one_re] using hre.trans hnorm
  let c : ℝ := (∏ p ∈ S, b p) *
    Real.exp (-2 * ∑' p : {p : Nat.Primes // p ∈ (S : Set Nat.Primes)ᶜ}, a p)
  refine ⟨c, ?_, ?_⟩
  · dsimp [c]
    apply mul_pos
    · apply Finset.prod_pos
      intro p hp
      exact primeLocalUniformLower_pos n p
    · exact Real.exp_pos _
  · intro T hT
    exact tprod_lower_of_finite_exceptions S ha hhalf (hdev T)
      (fun p hp => ⟨primeLocalUniformLower_pos n p,
        primeLocalFactor_re_ge_uniformLower hn hT p⟩)

/-- A real local-factor deviation is bounded by the corresponding absolute
prime-power coefficient tail. -/
theorem abs_realPrimeLocalFactor_sub_one_le_primePowerNormTail
    {n T : ℕ} (hn : 33 ≤ n) (p : Nat.Primes) :
    |(primeLocalFactor p n T).re - 1| ≤
      primePowerNormTail p n T := by
  have hpow := summable_norm_singularSeriesTerm_prime_powers
    (T := T) p.property hn
  have hinj : Function.Injective (fun k : ℕ => k + 1) := by
    intro a b h
    exact Nat.succ_injective h
  have hshift : Summable (fun k : ℕ =>
      ‖singularSeriesTerm n T ((p : ℕ) ^ (k + 1))‖) := by
    simpa only [Function.comp_def] using hpow.comp_injective hinj
  have hnorm := norm_tsum_le_tsum_norm hshift
  have hre := Complex.abs_re_le_norm (primeLocalFactor p n T - 1)
  calc
    |(primeLocalFactor p n T).re - 1| ≤
        ‖primeLocalFactor p n T - 1‖ := by simpa using hre
    _ = ‖∑' k : ℕ, singularSeriesTerm n T ((p : ℕ) ^ (k + 1))‖ := by
      simp [primeLocalFactor]
    _ ≤ ∑' k : ℕ, ‖singularSeriesTerm n T ((p : ℕ) ^ (k + 1))‖ := hnorm
    _ = primePowerNormTail p n T := rfl

/-- The real local-factor deviations from one are summable over all primes. -/
theorem summable_abs_realPrimeLocalFactor_sub_one
    {n T : ℕ} (hn : 33 ≤ n) :
    Summable (fun p : Nat.Primes =>
      |(primeLocalFactor p n T).re - 1|) := by
  apply (summable_primePowerNormTail (T := T) hn).of_nonneg_of_le
  · intro p
    exact abs_nonneg _
  · intro p
    exact abs_realPrimeLocalFactor_sub_one_le_primePowerNormTail hn p

/-- Every admissible local factor is real, including the exceptional primes. -/
theorem primeLocalFactor_eq_ofReal_re_of_admissible
    {n T : ℕ} (hn : 33 ≤ n) (hT : 24 ∣ T) (p : Nat.Primes) :
    primeLocalFactor p n T = ((primeLocalFactor p n T).re : ℂ) := by
  by_cases hp2 : (p : ℕ) = 2
  · have h8 : 8 ∣ T := dvd_trans (by norm_num : 8 ∣ 24) hT
    have htwo := CookMagyarPrimePower.primeLocalFactor_two_eq_eight_of_dvd_eight
      (by omega : 0 < n) h8
    simp [hp2, htwo]
  by_cases hp3 : (p : ℕ) = 3
  · have hthree := CookMagyarPrimePower.primeLocalFactor_three_eq_normalizedUnitCubicCount
      (by omega : 0 < n) (T := T)
    simp [hp3, hthree]
  have hp5 : 5 ≤ (p : ℕ) := by
    have hp2le := p.property.two_le
    have hpne4 : (p : ℕ) ≠ 4 := by
      intro hfour
      have hprime := p.property
      norm_num [hfour] at hprime
    omega
  exact primeLocalFactor_eq_realPart_of_large_arity p.property hp5 hn

/-- On admissible targets, the complex singular series is the real Euler
product embedded in `ℂ`. -/
theorem singularSeries_eq_ofReal_tprod_realPrimeLocalFactor
    {n T : ℕ} (hn : 33 ≤ n) (hT : 24 ∣ T) :
    singularSeries n T =
      ((∏' p : Nat.Primes, (primeLocalFactor p n T).re : ℝ) : ℂ) := by
  let f : Nat.Primes → ℝ := fun p => (primeLocalFactor p n T).re
  have hsum : Summable (fun p : Nat.Primes => f p - 1) := by
    apply Summable.of_norm
    simpa only [f, Real.norm_eq_abs] using
      (summable_abs_realPrimeLocalFactor_sub_one (T := T) hn)
  have hmult : Multipliable f := by
    have h := Real.multipliable_one_add_of_summable hsum
    have heq : (fun p : Nat.Primes => (1 : ℝ) + (f p - 1)) = f := by
      funext p
      ring
    simpa only [heq] using h
  have hmap := hmult.map_tprod Complex.ofRealHom Complex.continuous_ofReal
  have hcomplex : (∏' p : Nat.Primes, (f p : ℂ)) =
      ∏' p : Nat.Primes, primeLocalFactor p n T := by
    apply tprod_congr
    intro p
    exact (primeLocalFactor_eq_ofReal_re_of_admissible hn hT p).symm
  have hseries := singularSeries_eq_tprod_primeLocalFactor (T := T) hn
  have heq : ((∏' p : Nat.Primes, f p : ℝ) : ℂ) = singularSeries n T := by
    exact hmap.trans (hcomplex.trans hseries.symm)
  exact heq.symm

/-- On admissible targets, the real part of the singular series is the
positive real Euler product. -/
theorem singularSeries_re_eq_tprod_realPrimeLocalFactor
    {n T : ℕ} (hn : 33 ≤ n) (hT : 24 ∣ T) :
    (singularSeries n T).re =
      ∏' p : Nat.Primes, (primeLocalFactor p n T).re := by
  rw [singularSeries_eq_ofReal_tprod_realPrimeLocalFactor hn hT]
  exact Complex.ofReal_re _

/-- The singular series is real on all admissible targets. -/
theorem singularSeries_im_eq_zero_of_admissible
    {n T : ℕ} (hn : 33 ≤ n) (hT : 24 ∣ T) :
    (singularSeries n T).im = 0 := by
  rw [singularSeries_eq_ofReal_tprod_realPrimeLocalFactor hn hT]
  exact Complex.ofReal_im _

/-- The singular series has an arity-dependent strictly positive lower bound
uniform over all targets divisible by `24`. -/
theorem exists_uniform_singularSeries_re_lower
    {n : ℕ} (hn : 33 ≤ n) :
    ∃ c : ℝ, 0 < c ∧
      ∀ T : ℕ, 24 ∣ T → c ≤ (singularSeries n T).re := by
  obtain ⟨c, hc, hbound⟩ :=
    exists_uniform_realPrimeLocalFactor_tprod_lower hn
  refine ⟨c, hc, ?_⟩
  intro T hT
  rw [singularSeries_re_eq_tprod_realPrimeLocalFactor hn hT]
  exact hbound T hT

end SystolicGrowth.CookMagyarFiniteFourier
