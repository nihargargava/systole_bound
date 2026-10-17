module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.APNonunit
public import CookMagyar.LogCutoff
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.NumberTheory.LSeries.PrimesInAP

@[expose] public section

open Finset
open Filter
open scoped BigOperators ArithmeticFunction
open scoped Topology
open scoped Classical

namespace SystolicGrowth
namespace CookMagyarMajorArc

/-- The principal character modulo `q` keeps exactly the von Mangoldt
coefficients supported on units. -/
theorem principal_twisted_vonMangoldt_eq_sum_units
    (q m : ℕ) [NeZero q] :
    (∑ k ∈ Icc 0 m,
      (1 : DirichletCharacter ℂ q) k *
        (ArithmeticFunction.vonMangoldt k : ℂ)) =
      ∑ k ∈ (Icc 0 m).filter (fun k : ℕ => IsUnit (k : ZMod q)),
        (ArithmeticFunction.vonMangoldt k : ℂ) := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hu : IsUnit (k : ZMod q)
  · rw [ite_eq_left hu]
    simp [MulChar.one_apply hu]
  · rw [ite_eq_right hu]
    simp [MulChar.apply_eq_zero_iff, hu]

private theorem omitted_vonMangoldt_mass_eq_prime_power_sum
    (q m : ℕ) [NeZero q] :
    (∑ k ∈ Icc 0 m,
      if ¬ IsUnit (k : ZMod q) then ArithmeticFunction.vonMangoldt k else 0) =
      ∑ j ∈ Icc 1 ⌊Real.log (m : ℝ) / Real.log 2⌋₊,
        ∑ p ∈ Ioc 0 ⌊(m : ℝ) ^ ((1 : ℝ) / j)⌋₊ with p.Prime,
          if ¬ IsUnit ((p ^ j : ℕ) : ZMod q) then Real.log p else 0 := by
  classical
  let f : ℕ → ℝ := fun k =>
    if ¬ IsUnit (k : ZMod q) then ArithmeticFunction.vonMangoldt k else 0
  have htotal : (∑ k ∈ Icc 0 m, f k) = ∑ k ∈ Ioc 0 m, f k := by
    rw [← add_sum_Ioc_eq_sum_Icc (by omega : (0 : ℕ) ≤ m)]
    simp [f, ArithmeticFunction.vonMangoldt_apply, not_isPrimePow_zero]
  have hcomp :
      (∑ k ∈ Ioc 0 m with ¬ IsPrimePow k, f k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp [f, ArithmeticFunction.vonMangoldt_apply, (Finset.mem_filter.mp hk).2]
  have hfilter : (∑ k ∈ Ioc 0 m, f k) =
      ∑ k ∈ Ioc 0 m with IsPrimePow k, f k := by
    rw [← Finset.sum_filter_add_sum_filter_not (Ioc 0 m)
      (fun k : ℕ => IsPrimePow k)]
    rw [hcomp, add_zero]
  have hdecomp := Chebyshev.sum_PrimePow_eq_sum_sum (f := f)
    (x := (m : ℝ)) (by exact_mod_cast Nat.zero_le m)
  calc
    (∑ k ∈ Icc 0 m, f k) = ∑ k ∈ Ioc 0 m, f k := htotal
    _ = ∑ k ∈ Ioc 0 m with IsPrimePow k, f k := hfilter
    _ = ∑ j ∈ Icc 1 ⌊Real.log (m : ℝ) / Real.log 2⌋₊,
          ∑ p ∈ Ioc 0 ⌊(m : ℝ) ^ ((1 : ℝ) / j)⌋₊ with p.Prime, f (p ^ j) := by
        simpa [Nat.floor_natCast] using hdecomp
    _ = ∑ j ∈ Icc 1 ⌊Real.log (m : ℝ) / Real.log 2⌋₊,
          ∑ p ∈ Ioc 0 ⌊(m : ℝ) ^ ((1 : ℝ) / j)⌋₊ with p.Prime,
            if ¬ IsUnit ((p ^ j : ℕ) : ZMod q) then Real.log p else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro p hp
        simp only [f]
        have hj0 : j ≠ 0 := Nat.ne_of_gt
          (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hj).1)
        rw [ArithmeticFunction.vonMangoldt_apply_pow hj0]
        rw [ArithmeticFunction.vonMangoldt_apply_prime
          (Finset.mem_filter.mp hp).2]

private theorem prime_dvd_modulus_of_power_not_unit
    {q p j : ℕ} [NeZero q] (hp : p.Prime) (hj : 0 < j)
    (hunit : ¬ IsUnit ((p ^ j : ℕ) : ZMod q)) : p ∣ q := by
  have hnotcop : ¬ Nat.Coprime (p ^ j) q := by
    intro hcop
    apply hunit
    exact (ZMod.isUnit_iff_coprime (p ^ j) q).2 hcop
  have hnotcop' : ¬ Nat.Coprime p q := by
    intro hcop
    apply hnotcop
    exact (Nat.coprime_pow_left_iff hj p q).2 hcop
  by_contra hnotdvd
  exact hnotcop' ((hp.coprime_iff_not_dvd).2 hnotdvd)

/-- For a unit residue class, the finite von Mangoldt mass is the character
orthogonality average of the twisted von Mangoldt sums. The pointwise
orthogonality formula and Dirichlet-character API are from mathlib; this
lemma adapts them to the repository's `Icc 0 m` convention. -/
theorem cubicResiduePartialSum_eq_character_average
    (q m : ℕ) [NeZero q] (r : ZMod q) (hr : IsUnit r) :
    cubicResiduePartialSum q r m =
      (Nat.totient q : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q, χ r⁻¹ *
          ∑ k ∈ Icc 0 m,
            χ k * (ArithmeticFunction.vonMangoldt k : ℂ) := by
  classical
  let A : ℂ := (Nat.totient q : ℂ)⁻¹
  have hcoeff (k : ℕ) :
      cubicResidueCoefficient q r k =
        A * ∑ χ : DirichletCharacter ℂ q,
          χ r⁻¹ * χ k * (ArithmeticFunction.vonMangoldt k : ℂ) := by
    dsimp [A]
    have hpoint := ArithmeticFunction.vonMangoldt.residueClass_apply
      (q := q) (a := r) hr k
    by_cases hkr : (k : ZMod q) = r
    · simpa [hkr, cubicResidueCoefficient,
        ArithmeticFunction.vonMangoldt.residueClass] using hpoint
    · simpa [hkr, cubicResidueCoefficient,
        ArithmeticFunction.vonMangoldt.residueClass] using hpoint
  calc
    cubicResiduePartialSum q r m =
        ∑ k ∈ Icc 0 m,
          A * ∑ χ : DirichletCharacter ℂ q,
            χ r⁻¹ * χ k * (ArithmeticFunction.vonMangoldt k : ℂ) := by
      rw [cubicResiduePartialSum]
      apply Finset.sum_congr rfl
      intro k hk
      exact hcoeff k
    _ = A * ∑ χ : DirichletCharacter ℂ q,
          χ r⁻¹ * ∑ k ∈ Icc 0 m,
            χ k * (ArithmeticFunction.vonMangoldt k : ℂ) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro χ hχ
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
    _ = (Nat.totient q : ℂ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q,
            χ r⁻¹ * ∑ k ∈ Icc 0 m,
              χ k * (ArithmeticFunction.vonMangoldt k : ℂ) := by
      rfl

/-- Separate the principal character from the finite orthogonality formula.
This is the exact finite decomposition needed before estimating the principal
prime sum and the nonprincipal logarithmic derivatives analytically. -/
theorem cubicResiduePartialSum_eq_principal_and_nontrivial_characters
    (q m : ℕ) [NeZero q] (r : ZMod q) (hr : IsUnit r) :
    cubicResiduePartialSum q r m =
      (Nat.totient q : ℂ)⁻¹ *
        (∑ k ∈ Icc 0 m,
            (1 : DirichletCharacter ℂ q) k *
              (ArithmeticFunction.vonMangoldt k : ℂ) +
          ∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ q)),
            χ r⁻¹ * ∑ k ∈ Icc 0 m,
              χ k * (ArithmeticFunction.vonMangoldt k : ℂ)) := by
  classical
  rw [cubicResiduePartialSum_eq_character_average q m r hr]
  have hrInv : IsUnit (r⁻¹) := isUnit_of_dvd_one
    ⟨r, (ZMod.inv_mul_of_unit r hr).symm⟩
  rw [Fintype.sum_eq_add_sum_compl 1, MulChar.one_apply hrInv, one_mul,
    add_comm]

/-- Away from the pole, the regularized principal-character logarithmic
derivative is the zeta logarithmic derivative together with the explicit
simple-pole term. This is the analytic normalization used when estimating
the principal-character contribution to Siegel--Walfisz. -/
theorem neg_logDeriv_LFunctionTrivChar₁_eq_pole_sub_logDeriv
    (q : ℕ) [NeZero q] {s : ℂ} (hs : s ≠ 1)
    (hL : DirichletCharacter.LFunctionTrivChar q s ≠ 0) :
    -deriv (DirichletCharacter.LFunctionTrivChar₁ q) s /
        DirichletCharacter.LFunctionTrivChar₁ q s =
      -1 / (s - 1) -
        deriv (DirichletCharacter.LFunctionTrivChar q) s /
          DirichletCharacter.LFunctionTrivChar q s := by
  rw [DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one q hs,
    DirichletCharacter.LFunctionTrivChar₁,
    Function.update_of_ne hs]
  have hs' : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  field_simp; ring

/-- Changing a nontrivial Dirichlet character's modulus changes its
logarithmic derivative by exactly the logarithmic derivative of the finite
Euler-factor correction. This is the algebraic bridge needed to transfer
primitive-character estimates to characters at the AP modulus. -/
theorem logDeriv_LFunction_changeLevel_eq_add_correction
    {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    (χ : DirichletCharacter ℂ M) (hχ : χ ≠ 1) {s : ℂ}
    (hbase : DirichletCharacter.LFunction χ s ≠ 0)
    (hcorr : (∏ p ∈ N.primeFactors,
      (1 - χ p * (p : ℂ) ^ (-s))) ≠ 0) :
    deriv (DirichletCharacter.LFunction
        (DirichletCharacter.changeLevel hMN χ)) s /
        DirichletCharacter.LFunction (DirichletCharacter.changeLevel hMN χ) s =
      deriv (DirichletCharacter.LFunction χ) s /
          DirichletCharacter.LFunction χ s +
        deriv (fun z : ℂ => ∏ p ∈ N.primeFactors,
          (1 - χ p * (p : ℂ) ^ (-z))) s /
            (∏ p ∈ N.primeFactors, (1 - χ p * (p : ℂ) ^ (-s))) := by
  classical
  let E : ℂ → ℂ := fun z =>
    ∏ p ∈ N.primeFactors, (1 - χ p * (p : ℂ) ^ (-z))
  have hE : DifferentiableAt ℂ E s := by
    dsimp [E]
    refine .fun_finsetProd fun p hp ↦ ?_
    have : NeZero p := ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩
    fun_prop
  have hF : DifferentiableAt ℂ (DirichletCharacter.LFunction χ) s :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableAt
  have hEq : DirichletCharacter.LFunction (DirichletCharacter.changeLevel hMN χ) =
      fun z : ℂ => DirichletCharacter.LFunction χ z * E z := by
    funext z
    simpa [E] using
      (DirichletCharacter.LFunction_changeLevel hMN χ (Or.inl hχ) (s := z))
  have hderiv := congrArg (fun f : ℂ → ℂ => deriv f s) hEq
  rw [deriv_fun_mul hF hE] at hderiv
  rw [hderiv, congrFun hEq s]
  dsimp [E] at hderiv ⊢
  field_simp [hbase, hcorr]

/-- On `Re(s) > 1`, Mathlib's nonvanishing theorem discharges every
denominator condition in the imprimitive logarithmic-derivative identity.
Thus a nontrivial character's level change is an unconditional exact formula
throughout the half-plane of absolute convergence. -/
theorem logDeriv_LFunction_changeLevel_eq_add_correction_of_one_lt
    {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    (χ : DirichletCharacter ℂ M) (hχ : χ ≠ 1) {s : ℂ}
    (hs : 1 < s.re) :
    deriv (DirichletCharacter.LFunction
        (DirichletCharacter.changeLevel hMN χ)) s /
        DirichletCharacter.LFunction (DirichletCharacter.changeLevel hMN χ) s =
      deriv (DirichletCharacter.LFunction χ) s /
          DirichletCharacter.LFunction χ s +
        deriv (fun z : ℂ => ∏ p ∈ N.primeFactors,
          (1 - χ p * (p : ℂ) ^ (-z))) s /
            (∏ p ∈ N.primeFactors, (1 - χ p * (p : ℂ) ^ (-s))) := by
  have hbase : DirichletCharacter.LFunction χ s ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := χ)
      (Or.inl hχ) hs.le
  have hchanged : DirichletCharacter.changeLevel hMN χ ≠ 1 := by
    intro h
    exact hχ ((DirichletCharacter.changeLevel_eq_one_iff hMN).mp h)
  have hnew : DirichletCharacter.LFunction
      (DirichletCharacter.changeLevel hMN χ) s ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re
      (χ := DirichletCharacter.changeLevel hMN χ) (Or.inl hchanged) hs.le
  have hlevel := DirichletCharacter.LFunction_changeLevel hMN χ (Or.inl hχ)
    (s := s)
  have hcorr : (∏ p ∈ N.primeFactors,
      (1 - χ p * (p : ℂ) ^ (-s))) ≠ 0 := by
    intro hzero
    apply hnew
    rw [hlevel, hzero]
    simp
  exact logDeriv_LFunction_changeLevel_eq_add_correction
    hMN χ hχ hbase hcorr

/-- The derivative of one imprimitive Euler factor has the usual explicit
prime-local form. -/
theorem deriv_localImprimitiveEulerFactor
    {M p : ℕ} [NeZero p] (χ : DirichletCharacter ℂ M) (s : ℂ) :
    deriv (fun z : ℂ => 1 - χ (p : ZMod M) * (p : ℂ) ^ (-z)) s =
      χ (p : ZMod M) * Complex.log (p : ℂ) * (p : ℂ) ^ (-s) := by
  let g : ℂ → ℂ := fun z => χ (p : ZMod M) * (p : ℂ) ^ (-z)
  have hg : DifferentiableAt ℂ g s := by
    dsimp [g]
    have : NeZero p := ‹NeZero p›
    fun_prop
  rw [show (fun z : ℂ => 1 - χ (p : ZMod M) * (p : ℂ) ^ (-z)) =
      fun z => 1 - g z by rfl, deriv_const_sub,
    show deriv g s =
      χ (p : ZMod M) *
        deriv (fun z : ℂ => (p : ℂ) ^ (-z)) s by
          exact deriv_const_mul_field (χ (p : ZMod M))]
  rw [Complex.deriv_const_cpow (by fun_prop)]
  simp
  ring

/-- Derivative of the prime Euler factor removed from the principal
Dirichlet-character `L`-function. -/
theorem deriv_principalLocalEulerFactor
    {p : ℕ} [NeZero p] (s : ℂ) :
    deriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s =
      Complex.log (p : ℂ) * (p : ℂ) ^ (-s) := by
  have hpow : DifferentiableAt ℂ (fun z : ℂ => (p : ℂ) ^ (-z)) s := by
    fun_prop
  rw [deriv_const_sub]
  rw [Complex.deriv_const_cpow (by fun_prop)]
  simp

/-- The principal-character logarithmic derivative is the zeta logarithmic
derivative plus the finite local-factor correction. This identity isolates
the elementary modulus dependence from the analytic prime-number theorem. -/
theorem logDeriv_LFunctionTrivChar_eq_zeta_add_local_corrections_of_pos
    {q : ℕ} [NeZero q] {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    (hζ : riemannZeta s ≠ 0) :
    deriv (DirichletCharacter.LFunctionTrivChar q) s /
        DirichletCharacter.LFunctionTrivChar q s =
      deriv riemannZeta s / riemannZeta s +
        ∑ p ∈ q.primeFactors,
          Complex.log (p : ℂ) * (p : ℂ) ^ (-s) /
            (1 - (p : ℂ) ^ (-s)) := by
  classical
  let E : ℂ → ℂ := fun z =>
    ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))
  have hfactor : ∀ p ∈ q.primeFactors,
      (1 - (p : ℂ) ^ (-s)) ≠ 0 := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hpow : ‖(p : ℂ) ^ (-s)‖ < 1 := by
      rw [Complex.norm_natCast_cpow_of_re_ne_zero p (by
        change (-s.re) ≠ 0
        exact neg_ne_zero.mpr (ne_of_gt hs))]
      have hneg : (-s).re < 0 := by change -s.re < 0; linarith
      exact Real.rpow_lt_one_of_one_lt_of_neg
        (by exact_mod_cast hprime.one_lt) hneg
    intro hzero
    have heq : (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp hzero).symm
    rw [heq, norm_one] at hpow
    exact (lt_irrefl 1) hpow
  have hE : DifferentiableAt ℂ E s := by
    dsimp [E]
    refine .fun_finsetProd fun p hp => ?_
    have : NeZero p := ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩
    fun_prop
  have hζdiff : DifferentiableAt ℂ riemannZeta s :=
    differentiableAt_riemannZeta hs1
  have hvalue : DirichletCharacter.LFunctionTrivChar q s =
      E s * riemannZeta s := by
    simpa [E] using
      (DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := q) hs1)
  have hfun : (fun z : ℂ => DirichletCharacter.LFunctionTrivChar q z) =ᶠ[𝓝 s]
      fun z => E z * riemannZeta z := by
    filter_upwards [isOpen_ne.mem_nhds hs1] with z hz
    simpa [E] using
      (DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := q) hz)
  have hderiv : deriv (DirichletCharacter.LFunctionTrivChar q) s =
      deriv (fun z : ℂ => E z * riemannZeta z) s := hfun.deriv_eq
  have hEne : E s ≠ 0 := Finset.prod_ne_zero_iff.mpr hfactor
  have hdiff : ∀ p ∈ q.primeFactors,
      DifferentiableAt ℂ (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s := by
    intro p hp
    have : NeZero p := ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩
    fun_prop
  have hlogE := logDeriv_fun_prod hfactor hdiff
  have hsum :
      (∑ p ∈ q.primeFactors,
        deriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s /
          (1 - (p : ℂ) ^ (-s))) =
      ∑ p ∈ q.primeFactors,
        Complex.log (p : ℂ) * (p : ℂ) ^ (-s) /
          (1 - (p : ℂ) ^ (-s)) := by
    apply Finset.sum_congr rfl
    intro p hp
    have : NeZero p := ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩
    rw [deriv_principalLocalEulerFactor]
  simp only [logDeriv_apply] at hlogE
  rw [hsum] at hlogE
  calc
    deriv (DirichletCharacter.LFunctionTrivChar q) s /
        DirichletCharacter.LFunctionTrivChar q s =
      deriv (fun z : ℂ => E z * riemannZeta z) s /
        (E s * riemannZeta s) := by rw [hderiv, hvalue]
    _ = deriv E s / E s + deriv riemannZeta s / riemannZeta s := by
      rw [deriv_fun_mul hE hζdiff]
      field_simp [hEne, hζ]
    _ = deriv riemannZeta s / riemannZeta s +
        ∑ p ∈ q.primeFactors,
          Complex.log (p : ℂ) * (p : ℂ) ^ (-s) /
            (1 - (p : ℂ) ^ (-s)) := by
      rw [hlogE]
      ring

/-- Expand the imprimitive correction into one local logarithmic derivative
per prime dividing the larger modulus. The nonvanishing of every local factor
follows from the nonvanishing of the two `L`-functions in `Re(s)>1`. -/
theorem logDeriv_LFunction_changeLevel_eq_sum_local_corrections_of_one_lt
    {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    (χ : DirichletCharacter ℂ M) (hχ : χ ≠ 1) {s : ℂ}
    (hs : 1 < s.re) :
    deriv (DirichletCharacter.LFunction
        (DirichletCharacter.changeLevel hMN χ)) s /
        DirichletCharacter.LFunction (DirichletCharacter.changeLevel hMN χ) s =
      deriv (DirichletCharacter.LFunction χ) s /
          DirichletCharacter.LFunction χ s +
        ∑ p ∈ N.primeFactors,
          deriv (fun z : ℂ => 1 - χ p * (p : ℂ) ^ (-z)) s /
            (1 - χ p * (p : ℂ) ^ (-s)) := by
  classical
  have hbase : DirichletCharacter.LFunction χ s ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := χ)
      (Or.inl hχ) hs.le
  have hchanged : DirichletCharacter.changeLevel hMN χ ≠ 1 := by
    intro h
    exact hχ ((DirichletCharacter.changeLevel_eq_one_iff hMN).mp h)
  have hnew : DirichletCharacter.LFunction
      (DirichletCharacter.changeLevel hMN χ) s ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re
      (χ := DirichletCharacter.changeLevel hMN χ) (Or.inl hchanged) hs.le
  have hlevel := DirichletCharacter.LFunction_changeLevel hMN χ (Or.inl hχ)
    (s := s)
  have hcorr : (∏ p ∈ N.primeFactors,
      (1 - χ p * (p : ℂ) ^ (-s))) ≠ 0 := by
    intro hzero
    apply hnew
    rw [hlevel, hzero]
    simp
  have hfactor : ∀ p ∈ N.primeFactors,
      (1 - χ p * (p : ℂ) ^ (-s)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp hcorr
  have hdiff : ∀ p ∈ N.primeFactors,
      DifferentiableAt ℂ (fun z : ℂ => 1 - χ p * (p : ℂ) ^ (-z)) s := by
    intro p hp
    have : NeZero p := ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩
    fun_prop
  have hlog := logDeriv_LFunction_changeLevel_eq_add_correction_of_one_lt
    hMN χ hχ hs
  change logDeriv (DirichletCharacter.LFunction
      (DirichletCharacter.changeLevel hMN χ)) s =
    logDeriv (DirichletCharacter.LFunction χ) s +
      logDeriv (fun z : ℂ => ∏ p ∈ N.primeFactors,
        (1 - χ p * (p : ℂ) ^ (-z))) s at hlog
  rw [logDeriv_fun_prod hfactor hdiff] at hlog
  simpa only [logDeriv_apply] using hlog

/-- Expanding each local logarithmic derivative gives an explicit finite sum
of Euler-factor corrections at primes dividing the larger modulus. -/
theorem logDeriv_LFunction_changeLevel_eq_explicit_local_corrections_of_one_lt
    {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    (χ : DirichletCharacter ℂ M) (hχ : χ ≠ 1) {s : ℂ}
    (hs : 1 < s.re) :
    deriv (DirichletCharacter.LFunction
        (DirichletCharacter.changeLevel hMN χ)) s /
        DirichletCharacter.LFunction (DirichletCharacter.changeLevel hMN χ) s =
      deriv (DirichletCharacter.LFunction χ) s /
          DirichletCharacter.LFunction χ s +
        ∑ p ∈ N.primeFactors,
          χ (p : ZMod M) * Complex.log (p : ℂ) * (p : ℂ) ^ (-s) /
            (1 - χ (p : ZMod M) * (p : ℂ) ^ (-s)) := by
  have h := logDeriv_LFunction_changeLevel_eq_sum_local_corrections_of_one_lt
    hMN χ hχ hs
  have hsum :
      (∑ p ∈ N.primeFactors,
        deriv (fun z : ℂ => 1 - χ (p : ZMod M) * (p : ℂ) ^ (-z)) s /
          (1 - χ (p : ZMod M) * (p : ℂ) ^ (-s))) =
        ∑ p ∈ N.primeFactors,
          χ (p : ZMod M) * Complex.log (p : ℂ) * (p : ℂ) ^ (-s) /
            (1 - χ (p : ZMod M) * (p : ℂ) ^ (-s)) := by
    apply Finset.sum_congr rfl
    intro p hp
    have : NeZero p := ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩
    rw [deriv_localImprimitiveEulerFactor]
  rw [hsum] at h
  exact h

/-- Each explicit imprimitive Euler correction is bounded uniformly in the
half-plane `Re(s) ≥ 1/2`, including the shifted contours used in a
Siegel--Walfisz argument. -/
theorem norm_explicit_imprimitive_local_correction_le_of_re_ge_half
    {M p : ℕ} (hp : p.Prime) (χ : DirichletCharacter ℂ M)
    {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖χ (p : ZMod M) * Complex.log (p : ℂ) * (p : ℂ) ^ (-s) /
        (1 - χ (p : ZMod M) * (p : ℂ) ^ (-s))‖ ≤
      (((2 : ℝ) ^ (-1 / 2 : ℝ)) /
        (1 - (2 : ℝ) ^ (-1 / 2 : ℝ))) * Real.log p := by
  let c : ℝ := (2 : ℝ) ^ (-1 / 2 : ℝ)
  have hcpos : 0 < c := by
    dsimp [c]
    positivity
  have hc_lt_one : c < 1 := by
    dsimp [c]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hpow : ‖(p : ℂ) ^ (-s)‖ ≤ c := by
    rw [Complex.norm_natCast_cpow_of_re_ne_zero p (by
      have hspos : 0 < s.re := by linarith
      have hsne : s.re ≠ 0 := ne_of_gt hspos
      change (-s.re) ≠ 0
      exact neg_ne_zero.mpr hsne)]
    dsimp [c]
    calc
      (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (- (1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_le)
          (by linarith)
      _ ≤ (2 : ℝ) ^ (- (1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num)
          (by exact_mod_cast hp.two_le) (by norm_num)
      _ = c := by
        dsimp [c]
        congr 1
        norm_num
  have hchar := DirichletCharacter.norm_le_one χ (p : ZMod M)
  have hp0 : 0 ≤ (p : ℝ) := by positivity
  have hlog : ‖Complex.log (p : ℂ)‖ = Real.log p := by
    rw [show Complex.log (p : ℂ) = (Real.log p : ℂ) from
      (Complex.natCast_log (n := p)).symm,
      Complex.norm_real, Real.norm_of_nonneg
        (Real.log_nonneg (by exact_mod_cast hp.one_le))]
  have hlogNonneg : 0 ≤ Real.log p :=
    Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hz : ‖χ (p : ZMod M) * (p : ℂ) ^ (-s)‖ ≤ c := by
    rw [norm_mul]
    calc
      ‖χ (p : ZMod M)‖ * ‖(p : ℂ) ^ (-s)‖ ≤ 1 * c :=
        mul_le_mul hchar hpow (norm_nonneg _) (by positivity)
      _ = c := by ring
  have hden : 1 - c ≤
      ‖(1 : ℂ) - χ (p : ZMod M) * (p : ℂ) ^ (-s)‖ := by
    have htri := norm_sub_norm_le (1 : ℂ)
      (χ (p : ZMod M) * (p : ℂ) ^ (-s))
    rw [norm_one] at htri
    linarith
  have hdenPos : 0 <
      ‖(1 : ℂ) - χ (p : ZMod M) * (p : ℂ) ^ (-s)‖ := by
    have : 0 < 1 - c := by linarith
    linarith
  have hnum :
      ‖χ (p : ZMod M) * Complex.log (p : ℂ) * (p : ℂ) ^ (-s)‖ ≤
        Real.log p * c := by
    rw [norm_mul, norm_mul, hlog]
    calc
      ‖χ (p : ZMod M)‖ * Real.log p * ‖(p : ℂ) ^ (-s)‖ ≤
          1 * Real.log p * c := by
        gcongr
      _ = Real.log p * c := by ring
  rw [norm_div]
  have hcoef_nonneg : 0 ≤ c / (1 - c) * Real.log p := by
    positivity
  change ‖χ (p : ZMod M) * Complex.log (p : ℂ) * (p : ℂ) ^ (-s)‖ /
      ‖(1 : ℂ) - χ (p : ZMod M) * (p : ℂ) ^ (-s)‖ ≤
        (c / (1 - c)) * Real.log p
  apply (div_le_iff₀ hdenPos).2
  calc
    ‖χ (p : ZMod M) * Complex.log (p : ℂ) * (p : ℂ) ^ (-s)‖ ≤
        Real.log p * c := hnum
    _ = (c / (1 - c) * Real.log p) * (1 - c) := by
      field_simp [ne_of_gt (by linarith : 0 < 1 - c)]
    _ ≤ (c / (1 - c) * Real.log p) *
        ‖(1 : ℂ) - χ (p : ZMod M) * (p : ℂ) ^ (-s)‖ :=
      mul_le_mul_of_nonneg_left hden hcoef_nonneg

/-- The distinct prime divisors of a positive modulus contribute at most
the logarithm of that modulus. -/
theorem sum_log_primeFactors_le_log {N : ℕ} (hN : 1 ≤ N) :
    (∑ p ∈ N.primeFactors, Real.log (p : ℝ)) ≤ Real.log N := by
  have hprod_dvd : (∏ p ∈ N.primeFactors, p) ∣ N := Nat.prod_primeFactors_dvd N
  have hprod_le : (∏ p ∈ N.primeFactors, p) ≤ N :=
    Nat.le_of_dvd (by omega) hprod_dvd
  have hprod_pos : 0 < ∏ p ∈ N.primeFactors, p :=
    Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
  have hcast_prod :
      (∏ p ∈ N.primeFactors, (p : ℝ)) =
        ((∏ p ∈ N.primeFactors, p : ℕ) : ℝ) :=
    (Finset.prod_natCast N.primeFactors fun p => p).symm
  calc
    (∑ p ∈ N.primeFactors, Real.log (p : ℝ)) =
        Real.log (∏ p ∈ N.primeFactors, (p : ℝ)) := by
          rw [← Real.log_prod]
          · exact fun p hp => by
              exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    _ = Real.log ((∏ p ∈ N.primeFactors, p : ℕ) : ℝ) := by rw [hcast_prod]
    _ ≤ Real.log N := by
      apply Real.log_le_log (by exact_mod_cast hprod_pos)
      exact_mod_cast hprod_le

/-- The principal-character finite sum differs from the full Chebyshev sum
only by prime powers whose base prime divides the modulus. The omitted mass
is at most one `log q` per possible exponent. -/
theorem principal_omitted_vonMangoldt_mass_le
    (q m : ℕ) [NeZero q] :
    (∑ k ∈ Icc 0 m,
      if ¬ IsUnit (k : ZMod q) then ArithmeticFunction.vonMangoldt k else 0) ≤
      (⌊Real.log (m : ℝ) / Real.log 2⌋₊ : ℝ) * Real.log q := by
  classical
  rw [omitted_vonMangoldt_mass_eq_prime_power_sum]
  let B := ⌊Real.log (m : ℝ) / Real.log 2⌋₊
  have hinner (j : ℕ) (hj : j ∈ Icc 1 B) :
      (∑ p ∈ Ioc 0 ⌊(m : ℝ) ^ ((1 : ℝ) / j)⌋₊ with p.Prime,
        if ¬ IsUnit ((p ^ j : ℕ) : ZMod q) then Real.log p else 0) ≤ Real.log q := by
    let ps := Ioc 0 ⌊(m : ℝ) ^ ((1 : ℝ) / j)⌋₊
    let s := ps.filter
      (fun p : ℕ => p.Prime ∧ ¬ IsUnit ((p ^ j : ℕ) : ZMod q))
    have hsum :
        (∑ p ∈ ps with p.Prime,
          if ¬ IsUnit ((p ^ j : ℕ) : ZMod q) then Real.log p else 0) =
        ∑ p ∈ s, Real.log p := by
      change (∑ p ∈ ps.filter (fun p => p.Prime),
          if ¬ IsUnit ((p ^ j : ℕ) : ZMod q) then Real.log p else 0) =
        ∑ p ∈ ps.filter (fun p => p.Prime ∧ ¬ IsUnit ((p ^ j : ℕ) : ZMod q)),
          Real.log p
      rw [Finset.sum_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hprime : p.Prime <;> simp [hprime]
    rw [hsum]
    have hsub : s ⊆ q.primeFactors := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨_, hprime, hnonunit⟩
      have hjpos : 0 < j := (Finset.mem_Icc.mp hj).1
      have hdvd := prime_dvd_modulus_of_power_not_unit hprime hjpos hnonunit
      rw [Nat.mem_primeFactors]
      exact ⟨hprime, hdvd, NeZero.ne q⟩
    calc
      (∑ p ∈ s, Real.log p) ≤ ∑ p ∈ q.primeFactors, Real.log p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro p hp hnot
        exact Real.log_nonneg (by
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le)
      _ ≤ Real.log q := sum_log_primeFactors_le_log
        (Nat.succ_le_of_lt (NeZero.pos q))
  have hsum := Finset.sum_le_sum fun j hj => hinner j hj
  calc
    _ ≤ ∑ j ∈ Icc 1 B, Real.log q := hsum
    _ = (⌊Real.log (m : ℝ) / Real.log 2⌋₊ : ℝ) * Real.log q := by
      rw [Finset.sum_const]
      simp [B]

/-- Arbitrary-modulus principal twisted `ψ` differs from conductor one by
the omitted prime powers supported at primes dividing the modulus. This is
the finite-sum correction used to transfer the strong PNT to principal
characters uniformly in the modulus. -/
theorem norm_principal_twistedPsi_sub_chebyshevPsi_le
    (q m : ℕ) [NeZero q] :
    ‖(∑ k ∈ Icc 0 m,
        (1 : DirichletCharacter ℂ q) k *
          (ArithmeticFunction.vonMangoldt k : ℂ)) -
      (Chebyshev.psi m : ℂ)‖ ≤
      (⌊Real.log (m : ℝ) / Real.log 2⌋₊ : ℝ) * Real.log q := by
  classical
  rw [principal_twisted_vonMangoldt_eq_sum_units]
  have hψ : (Chebyshev.psi m : ℂ) =
      ∑ k ∈ Icc 0 m, (ArithmeticFunction.vonMangoldt k : ℂ) := by
    rw [Chebyshev.psi_eq_sum_Icc]
    simp only [Nat.floor_natCast]
    rw [Complex.ofReal_sum]
  have hsplit := Finset.sum_filter_add_sum_filter_not (Icc 0 m)
    (fun k : ℕ => IsUnit (k : ZMod q))
    (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
  have hnonunit :
      (∑ k ∈ Icc 0 m,
        if ¬ IsUnit (k : ZMod q) then
          (ArithmeticFunction.vonMangoldt k : ℂ) else 0) =
        ∑ k ∈ (Icc 0 m).filter (fun k : ℕ => ¬ IsUnit (k : ZMod q)),
          (ArithmeticFunction.vonMangoldt k : ℂ) := by
    rw [Finset.sum_filter]
  have hdiff :
      (∑ k ∈ (Icc 0 m).filter (fun k : ℕ => IsUnit (k : ZMod q)),
          (ArithmeticFunction.vonMangoldt k : ℂ)) - (Chebyshev.psi m : ℂ) =
        -∑ k ∈ Icc 0 m,
          if ¬ IsUnit (k : ZMod q) then
            (ArithmeticFunction.vonMangoldt k : ℂ) else 0 := by
    rw [hψ, hnonunit]
    rw [← hsplit]
    ring
  rw [hdiff, norm_neg]
  have hreal :
      (∑ k ∈ Icc 0 m,
        if ¬ IsUnit (k : ZMod q) then
          (ArithmeticFunction.vonMangoldt k : ℂ) else 0) =
        ((∑ k ∈ Icc 0 m,
          if ¬ IsUnit (k : ZMod q) then
            ArithmeticFunction.vonMangoldt k else 0 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro k hk
    split_ifs <;> simp
  have hmassnonneg : 0 ≤
      ∑ k ∈ Icc 0 m,
        if ¬ IsUnit (k : ZMod q) then
          ArithmeticFunction.vonMangoldt k else 0 :=
    Finset.sum_nonneg fun k hk => by
      by_cases hu : IsUnit (k : ZMod q)
      · simp [hu]
      · simpa only [ite_eq_left hu] using ArithmeticFunction.vonMangoldt_nonneg
  rw [hreal, Complex.norm_real, Real.norm_of_nonneg hmassnonneg]
  exact principal_omitted_vonMangoldt_mass_le q m

/-- Changing level discards only the von Mangoldt mass at nonunits of the
larger modulus. Its norm costs at most one `log q` per prime-power exponent,
uniformly in the original character. This is the finite-sum conductor-to-
modulus transfer; no pointwise contour correction is integrated. -/
theorem norm_changeLevel_twistedPsi_sub_le
    {d q : ℕ} [NeZero q] (hd : d ∣ q)
    (χ : DirichletCharacter ℂ d) (m : ℕ) :
    ‖(∑ k ∈ Icc 0 m,
        DirichletCharacter.changeLevel hd χ k *
          (ArithmeticFunction.vonMangoldt k : ℂ)) -
      ∑ k ∈ Icc 0 m, χ k * (ArithmeticFunction.vonMangoldt k : ℂ)‖ ≤
      (⌊Real.log (m : ℝ) / Real.log 2⌋₊ : ℝ) * Real.log q := by
  have hterm (k : ℕ) :
      ‖DirichletCharacter.changeLevel hd χ k *
          (ArithmeticFunction.vonMangoldt k : ℂ) -
        χ k * (ArithmeticFunction.vonMangoldt k : ℂ)‖ ≤
      if ¬ IsUnit (k : ZMod q) then ArithmeticFunction.vonMangoldt k else 0 := by
    by_cases hu : IsUnit (k : ZMod q)
    · have heq : DirichletCharacter.changeLevel hd χ k = χ k := by
        calc
          DirichletCharacter.changeLevel hd χ k =
              DirichletCharacter.changeLevel hd χ hu.unit := by rw [hu.unit_spec]
          _ = χ (ZMod.cast (hu.unit : ZMod q)) :=
            DirichletCharacter.changeLevel_eq_cast_of_dvd χ hd hu.unit
          _ = χ k := by rw [hu.unit_spec, ZMod.cast_natCast hd]
      simp [heq, hu]
    · have hzero : DirichletCharacter.changeLevel hd χ k = 0 :=
        MulChar.apply_eq_zero_iff.mpr hu
      rw [ite_eq_left hu, hzero, zero_mul, zero_sub, norm_neg, norm_mul]
      have hΛ : ‖(ArithmeticFunction.vonMangoldt k : ℂ)‖ =
          ArithmeticFunction.vonMangoldt k := by
        rw [Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      rw [hΛ]
      exact (mul_le_mul_of_nonneg_right (χ.norm_le_one _)
        ArithmeticFunction.vonMangoldt_nonneg).trans_eq (one_mul _)
  calc
    _ = ‖∑ k ∈ Icc 0 m,
          (DirichletCharacter.changeLevel hd χ k *
            (ArithmeticFunction.vonMangoldt k : ℂ) -
          χ k * (ArithmeticFunction.vonMangoldt k : ℂ))‖ := by rw [Finset.sum_sub_distrib]
    _ ≤ ∑ k ∈ Icc 0 m,
          ‖DirichletCharacter.changeLevel hd χ k *
            (ArithmeticFunction.vonMangoldt k : ℂ) -
          χ k * (ArithmeticFunction.vonMangoldt k : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Icc 0 m,
          if ¬ IsUnit (k : ZMod q) then ArithmeticFunction.vonMangoldt k else 0 :=
      Finset.sum_le_sum fun k _ => hterm k
    _ ≤ _ := principal_omitted_vonMangoldt_mass_le q m

/-- Bound one local factor in the principal-character correction on the
half-plane used by the shifted contour. -/
theorem norm_principal_local_correction_le_of_re_ge_half
    {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖Complex.log (p : ℂ) * (p : ℂ) ^ (-s) /
        (1 - (p : ℂ) ^ (-s))‖ ≤
      (((2 : ℝ) ^ (-1 / 2 : ℝ)) /
        (1 - (2 : ℝ) ^ (-1 / 2 : ℝ))) * Real.log p := by
  let c : ℝ := (2 : ℝ) ^ (-1 / 2 : ℝ)
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hc_lt_one : c < 1 := by
    dsimp [c]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hpow : ‖(p : ℂ) ^ (-s)‖ ≤ c := by
    rw [Complex.norm_natCast_cpow_of_re_ne_zero p (by
      have hspos : 0 < s.re := by linarith
      have hsne : s.re ≠ 0 := ne_of_gt hspos
      change (-s.re) ≠ 0
      exact neg_ne_zero.mpr hsne)]
    dsimp [c]
    calc
      (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (- (1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_le)
          (by linarith)
      _ ≤ (2 : ℝ) ^ (- (1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num)
          (by exact_mod_cast hp.two_le) (by norm_num)
      _ = c := by
        dsimp [c]
        congr 1
        norm_num
  have hlog : ‖Complex.log (p : ℂ)‖ = Real.log p := by
    rw [show Complex.log (p : ℂ) = (Real.log p : ℂ) from
      (Complex.natCast_log (n := p)).symm,
      Complex.norm_real, Real.norm_of_nonneg
        (Real.log_nonneg (by exact_mod_cast hp.one_le))]
  have hlogNonneg : 0 ≤ Real.log p :=
    Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hden : 1 - c ≤ ‖(1 : ℂ) - (p : ℂ) ^ (-s)‖ := by
    have htri := norm_sub_norm_le (1 : ℂ) ((p : ℂ) ^ (-s))
    rw [norm_one] at htri
    linarith
  have hdenPos : 0 < ‖(1 : ℂ) - (p : ℂ) ^ (-s)‖ := by
    have : 0 < 1 - c := by linarith
    linarith
  have hnum :
      ‖Complex.log (p : ℂ) * (p : ℂ) ^ (-s)‖ ≤ Real.log p * c := by
    rw [norm_mul, hlog]
    exact mul_le_mul_of_nonneg_left hpow hlogNonneg
  rw [norm_div]
  change ‖Complex.log (p : ℂ) * (p : ℂ) ^ (-s)‖ /
      ‖(1 : ℂ) - (p : ℂ) ^ (-s)‖ ≤ (c / (1 - c)) * Real.log p
  apply (div_le_iff₀ hdenPos).2
  have hcoef_nonneg : 0 ≤ c / (1 - c) * Real.log p := by positivity
  calc
    ‖Complex.log (p : ℂ) * (p : ℂ) ^ (-s)‖ ≤ Real.log p * c := hnum
    _ = (c / (1 - c) * Real.log p) * (1 - c) := by
      field_simp [ne_of_gt (by linarith : 0 < 1 - c)]
    _ ≤ (c / (1 - c) * Real.log p) *
        ‖(1 : ℂ) - (p : ℂ) ^ (-s)‖ :=
      mul_le_mul_of_nonneg_left hden hcoef_nonneg

/-- The principal-character Euler-factor correction over `q` is uniformly
bounded by an explicit constant times `log q` on `Re(s)≥1/2`. -/
theorem norm_sum_principal_local_corrections_le
    {q : ℕ} (hq : 1 ≤ q) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖∑ p ∈ q.primeFactors,
        Complex.log (p : ℂ) * (p : ℂ) ^ (-s) /
          (1 - (p : ℂ) ^ (-s))‖ ≤
      (((2 : ℝ) ^ (-1 / 2 : ℝ)) /
        (1 - (2 : ℝ) ^ (-1 / 2 : ℝ))) * Real.log q := by
  let c : ℝ := (2 : ℝ) ^ (-1 / 2 : ℝ)
  have hlogs := sum_log_primeFactors_le_log hq
  have hterm :
      (∑ p ∈ q.primeFactors,
        ‖Complex.log (p : ℂ) * (p : ℂ) ^ (-s) /
          (1 - (p : ℂ) ^ (-s))‖) ≤
        ∑ p ∈ q.primeFactors, (c / (1 - c)) * Real.log p := by
    apply Finset.sum_le_sum
    intro p hp
    simpa [c] using
      norm_principal_local_correction_le_of_re_ge_half
        (Nat.prime_of_mem_primeFactors hp) hs
  have hc : 0 ≤ c / (1 - c) := by
    have hcpos : 0 < c := by dsimp [c]; positivity
    have hclt : c < 1 := by
      dsimp [c]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    positivity
  calc
    ‖∑ p ∈ q.primeFactors,
        Complex.log (p : ℂ) * (p : ℂ) ^ (-s) /
          (1 - (p : ℂ) ^ (-s))‖ ≤
        ∑ p ∈ q.primeFactors,
          ‖Complex.log (p : ℂ) * (p : ℂ) ^ (-s) /
            (1 - (p : ℂ) ^ (-s))‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ q.primeFactors, (c / (1 - c)) * Real.log p := hterm
    _ = (c / (1 - c)) * ∑ p ∈ q.primeFactors, Real.log p := by
      rw [Finset.mul_sum]
    _ ≤ (c / (1 - c)) * Real.log q :=
      mul_le_mul_of_nonneg_left hlogs hc

/-- Transfer a zeta logarithmic-derivative estimate to the principal
character modulo `q`, with the explicit finite-modulus loss. -/
theorem norm_sub_logDeriv_LFunctionTrivChar_le
    {q : ℕ} [NeZero q] (hq : 1 ≤ q) {s : ℂ}
    (hs : 0 < s.re) (hsHalf : 1 / 2 ≤ s.re) (hs1 : s ≠ 1)
    (hζ : riemannZeta s ≠ 0) :
    ‖deriv (DirichletCharacter.LFunctionTrivChar q) s /
        DirichletCharacter.LFunctionTrivChar q s -
      deriv riemannZeta s / riemannZeta s‖ ≤
      (((2 : ℝ) ^ (-1 / 2 : ℝ)) /
        (1 - (2 : ℝ) ^ (-1 / 2 : ℝ))) * Real.log q := by
  rw [logDeriv_LFunctionTrivChar_eq_zeta_add_local_corrections_of_pos
    hs hs1 hζ, add_sub_cancel_left]
  exact norm_sum_principal_local_corrections_le hq hsHalf

/-- Summing the imprimitive Euler corrections over all prime divisors of the
larger modulus costs only a fixed constant times its logarithm, uniformly on
`Re(s) ≥ 1/2`. -/
theorem norm_sum_explicit_imprimitive_local_corrections_le
    {M N : ℕ} (hN : 1 ≤ N) (χ : DirichletCharacter ℂ M) {s : ℂ}
    (hs : 1 / 2 ≤ s.re) :
    ‖∑ p ∈ N.primeFactors,
        χ (p : ZMod M) * Complex.log (p : ℂ) * (p : ℂ) ^ (-s) /
          (1 - χ (p : ZMod M) * (p : ℂ) ^ (-s))‖ ≤
      (((2 : ℝ) ^ (-1 / 2 : ℝ)) /
        (1 - (2 : ℝ) ^ (-1 / 2 : ℝ))) * Real.log N := by
  let c : ℝ := (2 : ℝ) ^ (-1 / 2 : ℝ)
  have hlogs := sum_log_primeFactors_le_log hN
  have hterm :
      (∑ p ∈ N.primeFactors,
        ‖χ (p : ZMod M) * Complex.log (p : ℂ) * (p : ℂ) ^ (-s) /
          (1 - χ (p : ZMod M) * (p : ℂ) ^ (-s))‖) ≤
        ∑ p ∈ N.primeFactors, (c / (1 - c)) * Real.log p := by
    apply Finset.sum_le_sum
    intro p hp
    simpa [c] using
      norm_explicit_imprimitive_local_correction_le_of_re_ge_half
        (Nat.prime_of_mem_primeFactors hp) χ hs
  have hc : 0 ≤ c / (1 - c) := by
    have hcpos : 0 < c := by dsimp [c]; positivity
    have hclt : c < 1 := by
      dsimp [c]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    positivity
  calc
    ‖∑ p ∈ N.primeFactors,
        χ (p : ZMod M) * Complex.log (p : ℂ) * (p : ℂ) ^ (-s) /
          (1 - χ (p : ZMod M) * (p : ℂ) ^ (-s))‖ ≤
        ∑ p ∈ N.primeFactors,
          ‖χ (p : ZMod M) * Complex.log (p : ℂ) * (p : ℂ) ^ (-s) /
            (1 - χ (p : ZMod M) * (p : ℂ) ^ (-s))‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ N.primeFactors, (c / (1 - c)) * Real.log p := hterm
    _ = (c / (1 - c)) * ∑ p ∈ N.primeFactors, Real.log p := by rw [Finset.mul_sum]
    _ ≤ (c / (1 - c)) * Real.log N :=
      mul_le_mul_of_nonneg_left hlogs hc

/-- Extend the exact imprimitive logarithmic-derivative formula to the
right half-plane. The only analytic input left as a premise is nonvanishing
of the original character's `L`-function at `s`; the finite Euler factors
are automatically nonzero when `Re(s)>0`. -/
theorem logDeriv_LFunction_changeLevel_eq_explicit_local_corrections_of_pos
    {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    (χ : DirichletCharacter ℂ M) (hχ : χ ≠ 1) {s : ℂ}
    (hs : 0 < s.re)
    (hbase : DirichletCharacter.LFunction χ s ≠ 0) :
    deriv (DirichletCharacter.LFunction
        (DirichletCharacter.changeLevel hMN χ)) s /
        DirichletCharacter.LFunction (DirichletCharacter.changeLevel hMN χ) s =
      deriv (DirichletCharacter.LFunction χ) s /
          DirichletCharacter.LFunction χ s +
        ∑ p ∈ N.primeFactors,
          χ (p : ZMod M) * Complex.log (p : ℂ) * (p : ℂ) ^ (-s) /
            (1 - χ (p : ZMod M) * (p : ℂ) ^ (-s)) := by
  classical
  have hfactor : ∀ p ∈ N.primeFactors,
      (1 - χ (p : ZMod M) * (p : ℂ) ^ (-s)) ≠ 0 := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hpow : ‖(p : ℂ) ^ (-s)‖ < 1 := by
      rw [Complex.norm_natCast_cpow_of_re_ne_zero p (by
        change (-s.re) ≠ 0
        exact neg_ne_zero.mpr (ne_of_gt hs))]
      have hneg : (-s).re < 0 := by change -s.re < 0; linarith
      exact Real.rpow_lt_one_of_one_lt_of_neg
        (by exact_mod_cast hprime.one_lt) hneg
    have hchar := DirichletCharacter.norm_le_one χ (p : ZMod M)
    have hmul :
        ‖χ (p : ZMod M) * (p : ℂ) ^ (-s)‖ < 1 := by
      rw [norm_mul]
      calc
        ‖χ (p : ZMod M)‖ * ‖(p : ℂ) ^ (-s)‖ ≤
            1 * ‖(p : ℂ) ^ (-s)‖ :=
          mul_le_mul_of_nonneg_right hchar (norm_nonneg _)
        _ < 1 := by simpa using hpow
    intro hzero
    have heq : χ (p : ZMod M) * (p : ℂ) ^ (-s) = 1 :=
      (sub_eq_zero.mp hzero).symm
    rw [heq, norm_one] at hmul
    exact (lt_irrefl 1) hmul
  have hcorr : (∏ p ∈ N.primeFactors,
      (1 - χ p * (p : ℂ) ^ (-s))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hfactor
  have hderiv := logDeriv_LFunction_changeLevel_eq_add_correction
    hMN χ hχ hbase hcorr
  have hdiff : ∀ p ∈ N.primeFactors,
      DifferentiableAt ℂ (fun z : ℂ => 1 - χ p * (p : ℂ) ^ (-z)) s := by
    intro p hp
    have : NeZero p := ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩
    fun_prop
  change logDeriv (DirichletCharacter.LFunction
      (DirichletCharacter.changeLevel hMN χ)) s =
    logDeriv (DirichletCharacter.LFunction χ) s +
      logDeriv (fun z : ℂ => ∏ p ∈ N.primeFactors,
        (1 - χ p * (p : ℂ) ^ (-z))) s at hderiv
  rw [logDeriv_fun_prod hfactor hdiff] at hderiv
  have hsum :
      (∑ p ∈ N.primeFactors,
        deriv (fun z : ℂ => 1 - χ (p : ZMod M) * (p : ℂ) ^ (-z)) s /
          (1 - χ (p : ZMod M) * (p : ℂ) ^ (-s))) =
      ∑ p ∈ N.primeFactors,
        χ (p : ZMod M) * Complex.log (p : ℂ) * (p : ℂ) ^ (-s) /
          (1 - χ (p : ZMod M) * (p : ℂ) ^ (-s)) := by
    apply Finset.sum_congr rfl
    intro p hp
    have : NeZero p := ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩
    rw [deriv_localImprimitiveEulerFactor]
  simp only [logDeriv_apply] at hderiv
  rw [hsum] at hderiv
  simpa only [logDeriv_apply] using hderiv

/-- A primitive-character logarithmic-derivative estimate transfers to its
imprimitive lift with an explicit additive loss bounded by a constant times
the logarithm of the larger modulus. -/
theorem norm_sub_logDeriv_LFunction_changeLevel_le
    {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    (hN : 1 ≤ N) (χ : DirichletCharacter ℂ M) (hχ : χ ≠ 1) {s : ℂ}
    (hs : 0 < s.re) (hsHalf : 1 / 2 ≤ s.re)
    (hbase : DirichletCharacter.LFunction χ s ≠ 0) :
    ‖deriv (DirichletCharacter.LFunction
        (DirichletCharacter.changeLevel hMN χ)) s /
        DirichletCharacter.LFunction (DirichletCharacter.changeLevel hMN χ) s -
      deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s‖ ≤
      (((2 : ℝ) ^ (-1 / 2 : ℝ)) /
        (1 - (2 : ℝ) ^ (-1 / 2 : ℝ))) * Real.log N := by
  rw [logDeriv_LFunction_changeLevel_eq_explicit_local_corrections_of_pos
    hMN χ hχ hs hbase]
  rw [add_sub_cancel_left]
  exact norm_sum_explicit_imprimitive_local_corrections_le hN χ hsHalf

/-- The ineffective Siegel lower bound at exponent `1/(3A)` turns a
polylogarithmic conductor bound into a square-root-log exponential saving.
This is the scalar absorption needed for the possible exceptional real zero
in the Siegel--Walfisz contour argument. The analytic Siegel bound itself is
not assumed or proved here. -/
theorem eventually_exceptional_zero_term_le_of_siegel_bound
    {A C c : ℝ} (hA : 0 < A) (hC : 0 < C) (_hc : 0 < c)
    (q : ℕ → ℕ) (β : ℕ → ℝ)
    (hmod : ∀ᶠ N : ℕ in atTop,
      1 ≤ q N ∧ (q N : ℝ) ≤ Real.log ((N : ℝ) + 2) ^ A)
    (hSiegel : ∀ᶠ N : ℕ in atTop,
      1 - β N ≥ C * (q N : ℝ) ^ (-(1 / (3 * A)))) :
    ∀ᶠ N : ℕ in atTop,
      ((N : ℝ) + 2) ^ β N ≤
        ((N : ℝ) + 2) *
          Real.exp (-c * Real.sqrt (Real.log ((N : ℝ) + 2))) := by
  have hlog : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 2)) atTop atTop := by
    have harg : Tendsto (fun N : ℕ => (N : ℝ) + 2) atTop atTop := by
      convert tendsto_atTop_add_const_right _ (2 : ℝ)
        tendsto_natCast_atTop_atTop using 1
    exact Real.tendsto_log_atTop.comp harg
  have hlogPow : Tendsto
      (fun N : ℕ => Real.log ((N : ℝ) + 2) ^ (1 / 6 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp hlog
  have hlargeLog := hlog.eventually_ge_atTop (1 : ℝ)
  have hlargePow := hlogPow.eventually_ge_atTop (c / C)
  filter_upwards [hmod, hSiegel, hlargeLog, hlargePow] with N hmodN hSiegelN hlogN hpowN
  let x : ℝ := (N : ℝ) + 2
  let y : ℝ := Real.log x
  have hx : 0 < x := by dsimp [x]; positivity
  have hy : 1 ≤ y := by simpa [x, y] using hlogN
  have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hyle : 0 ≤ y := le_of_lt hypos
  have hqpos : 0 < (q N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hmodN.1)
  have hqupper : (q N : ℝ) ≤ y ^ A := by simpa [x, y] using hmodN.2
  have hqpow : y ^ (-1 / 3 : ℝ) ≤ (q N : ℝ) ^ (-(1 / (3 * A))) := by
    have hneg : -(1 / (3 * A)) ≤ 0 := by
      have hden : 0 < 3 * A := mul_pos (by norm_num) hA
      exact neg_nonpos.mpr (div_nonneg (by norm_num) hden.le)
    have hmono := Real.rpow_le_rpow_of_nonpos hqpos hqupper
      hneg
    have hpowid : y ^ (-1 / 3 : ℝ) = (y ^ A) ^ (-(1 / (3 * A))) := by
      have hexp : (-1 / 3 : ℝ) = A * (-(1 / (3 * A))) := by
        field_simp
      rw [hexp, Real.rpow_mul hyle]
    rw [hpowid]
    exact hmono
  have hSiegelLog : C * y ^ (-1 / 3 : ℝ) ≤ 1 - β N := by
    calc
      C * y ^ (-1 / 3 : ℝ) ≤ C * (q N : ℝ) ^ (-(1 / (3 * A))) :=
        mul_le_mul_of_nonneg_left hqpow hC.le
      _ ≤ 1 - β N := by simpa [y, x] using hSiegelN
  have hprod : y ^ (-1 / 3 : ℝ) * y = y ^ (2 / 3 : ℝ) := by
    calc
      y ^ (-1 / 3 : ℝ) * y = y ^ (-1 / 3 : ℝ) * y ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = y ^ ((-1 / 3 : ℝ) + 1) := by rw [← Real.rpow_add hypos]
      _ = y ^ (2 / 3 : ℝ) := by congr 1; ring
  have hbetaGap : C * y ^ (2 / 3 : ℝ) ≤ (1 - β N) * y := by
    calc
      C * y ^ (2 / 3 : ℝ) = C * (y ^ (-1 / 3 : ℝ) * y) := by rw [hprod]
      _ = (C * y ^ (-1 / 3 : ℝ)) * y := by ring
      _ ≤ (1 - β N) * y := mul_le_mul_of_nonneg_right hSiegelLog hyle
  have hrootPow : y ^ (2 / 3 : ℝ) = Real.sqrt y * y ^ (1 / 6 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    calc
      y ^ (2 / 3 : ℝ) = y ^ ((1 / 2 : ℝ) + 1 / 6) := by congr 1; ring
      _ = y ^ (1 / 2 : ℝ) * y ^ (1 / 6 : ℝ) := by rw [Real.rpow_add hypos]
  have hcPow : c ≤ C * y ^ (1 / 6 : ℝ) := by
    have hpowN' : c / C ≤ y ^ (1 / 6 : ℝ) := by simpa [y, x] using hpowN
    simpa [mul_comm] using (div_le_iff₀ hC).mp hpowN'
  have hcRoot : c * Real.sqrt y ≤ C * y ^ (2 / 3 : ℝ) := by
    rw [hrootPow]
    calc
      c * Real.sqrt y ≤ (C * y ^ (1 / 6 : ℝ)) * Real.sqrt y :=
        mul_le_mul_of_nonneg_right hcPow (Real.sqrt_nonneg y)
      _ = C * (Real.sqrt y * y ^ (1 / 6 : ℝ)) := by ring
  have hdecay : Real.exp (-C * y ^ (2 / 3 : ℝ)) ≤
      Real.exp (-c * Real.sqrt y) :=
    Real.exp_le_exp.mpr (by nlinarith [hcRoot])
  have hexpArg : β N * y ≤ y - C * y ^ (2 / 3 : ℝ) := by nlinarith [hbetaGap]
  calc
    x ^ β N = Real.exp (β N * y) := by
      rw [Real.rpow_def_of_pos hx]
      simp [y, x, mul_comm]
    _ ≤ Real.exp (y - C * y ^ (2 / 3 : ℝ)) := Real.exp_le_exp.mpr hexpArg
    _ = x * Real.exp (-C * y ^ (2 / 3 : ℝ)) := by
      rw [show y - C * y ^ (2 / 3 : ℝ) = y + (-C * y ^ (2 / 3 : ℝ)) by ring,
        Real.exp_add, Real.exp_log hx]
    _ ≤ x * Real.exp (-c * Real.sqrt y) :=
      mul_le_mul_of_nonneg_left hdecay hx.le
    _ = ((N : ℝ) + 2) *
          Real.exp (-c * Real.sqrt (Real.log ((N : ℝ) + 2))) := by
      simp [x, y]

/-- Version of exceptional-zero absorption for the repository's actual
integer logarithmic cutoff `floor(log(N+2))^A`. -/
theorem eventually_exceptional_zero_term_le_of_cutoff_bound
    {A : ℕ} {C c : ℝ} (hA : 0 < A) (hC : 0 < C) (hc : 0 < c)
    (q : ℕ → ℕ) (β : ℕ → ℝ)
    (hmod : ∀ᶠ N : ℕ in atTop,
      1 ≤ q N ∧ q N ≤ CookMagyarCircle.logarithmicDenominatorCutoff A N)
    (hSiegel : ∀ᶠ N : ℕ in atTop,
      1 - β N ≥ C * (q N : ℝ) ^ (-(1 / (3 * (A : ℝ))))) :
    ∀ᶠ N : ℕ in atTop,
      ((N : ℝ) + 2) ^ β N ≤
        ((N : ℝ) + 2) *
          Real.exp (-c * Real.sqrt (Real.log ((N : ℝ) + 2))) := by
  have hmodReal : ∀ᶠ N : ℕ in atTop,
      1 ≤ q N ∧ (q N : ℝ) ≤ Real.log ((N : ℝ) + 2) ^ (A : ℝ) := by
    filter_upwards [hmod] with N hN
    refine ⟨hN.1, ?_⟩
    calc
      (q N : ℝ) ≤
          (CookMagyarCircle.logarithmicDenominatorCutoff A N : ℝ) :=
        Nat.cast_le.mpr hN.2
      _ ≤ Real.log ((N : ℝ) + 2) ^ A :=
        CookMagyarCircle.logarithmicDenominatorCutoff_le_log_pow A N
      _ = Real.log ((N : ℝ) + 2) ^ (A : ℝ) := by norm_cast
  exact eventually_exceptional_zero_term_le_of_siegel_bound
    (A := (A : ℝ)) (C := C) (c := c) (by exact_mod_cast hA) hC hc q β
    hmodReal hSiegel

/-! ## Current proof frontier

The finite character split and principal-pole normalization are proved. The
principal `L`-function has an exact zeta-plus-finite-factor log-derivative
decomposition for `Re(s)>0`, and the local factors have a uniform `O(log q)`
bound for `Re(s)≥1/2`. The exact imprimitive change-of-level correction is
proved for `Re(s)>1`; a
conditional extension to `Re(s)>0` is also proved, with only nonvanishing of
the original-level `L`-function assumed. The finite correction sum has a
uniform `O(log N)` norm bound throughout `Re(s)≥1/2`. The zero-free theorem
must supply the extension's nonvanishing premise uniformly along the contour.
The theorem `norm_sub_logDeriv_LFunction_changeLevel_le` packages this as a
direct primitive-to-imprimitive transfer estimate.
The finite twisted-`ψ` sum changes by at most
`floor(log m / log 2) * log q` under every change of level; this comes from
the omitted prime-power mass and the bound on the logarithms of prime divisors
of `q`. The principal strong-PNT transfer is proved in
`MajorArcExerciseGaps`, while the primitive nonprincipal terms still need
uniform quantitative logarithmic-derivative bounds (including the exceptional
real character). Those estimates are not supplied by this module.
-/

end CookMagyarMajorArc
end SystolicGrowth

#print axioms SystolicGrowth.CookMagyarMajorArc.cubicResiduePartialSum_eq_character_average
#print axioms SystolicGrowth.CookMagyarMajorArc.cubicResiduePartialSum_eq_principal_and_nontrivial_characters
#print axioms SystolicGrowth.CookMagyarMajorArc.neg_logDeriv_LFunctionTrivChar₁_eq_pole_sub_logDeriv
#print axioms SystolicGrowth.CookMagyarMajorArc.logDeriv_LFunction_changeLevel_eq_add_correction
#print axioms SystolicGrowth.CookMagyarMajorArc.logDeriv_LFunction_changeLevel_eq_add_correction_of_one_lt
#print axioms SystolicGrowth.CookMagyarMajorArc.logDeriv_LFunction_changeLevel_eq_sum_local_corrections_of_one_lt
#print axioms SystolicGrowth.CookMagyarMajorArc.deriv_localImprimitiveEulerFactor
#print axioms SystolicGrowth.CookMagyarMajorArc.deriv_principalLocalEulerFactor
#print axioms SystolicGrowth.CookMagyarMajorArc.logDeriv_LFunctionTrivChar_eq_zeta_add_local_corrections_of_pos
#print axioms SystolicGrowth.CookMagyarMajorArc.norm_principal_local_correction_le_of_re_ge_half
#print axioms SystolicGrowth.CookMagyarMajorArc.norm_sum_principal_local_corrections_le
#print axioms SystolicGrowth.CookMagyarMajorArc.norm_sub_logDeriv_LFunctionTrivChar_le
#print axioms SystolicGrowth.CookMagyarMajorArc.logDeriv_LFunction_changeLevel_eq_explicit_local_corrections_of_one_lt
#print axioms SystolicGrowth.CookMagyarMajorArc.norm_explicit_imprimitive_local_correction_le_of_re_ge_half
#print axioms SystolicGrowth.CookMagyarMajorArc.sum_log_primeFactors_le_log
#print axioms SystolicGrowth.CookMagyarMajorArc.norm_sum_explicit_imprimitive_local_corrections_le
#print axioms SystolicGrowth.CookMagyarMajorArc.logDeriv_LFunction_changeLevel_eq_explicit_local_corrections_of_pos
#print axioms SystolicGrowth.CookMagyarMajorArc.norm_sub_logDeriv_LFunction_changeLevel_le
#print axioms SystolicGrowth.CookMagyarMajorArc.eventually_exceptional_zero_term_le_of_siegel_bound
#print axioms SystolicGrowth.CookMagyarMajorArc.eventually_exceptional_zero_term_le_of_cutoff_bound
#print axioms SystolicGrowth.CookMagyarMajorArc.principal_twisted_vonMangoldt_eq_sum_units
#print axioms SystolicGrowth.CookMagyarMajorArc.omitted_vonMangoldt_mass_eq_prime_power_sum
#print axioms SystolicGrowth.CookMagyarMajorArc.principal_omitted_vonMangoldt_mass_le
#print axioms SystolicGrowth.CookMagyarMajorArc.norm_principal_twistedPsi_sub_chebyshevPsi_le
#print axioms SystolicGrowth.CookMagyarMajorArc.norm_changeLevel_twistedPsi_sub_le
