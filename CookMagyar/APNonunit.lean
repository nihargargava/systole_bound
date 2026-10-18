module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.CubicResidueAbel
public import Mathlib.NumberTheory.Chebyshev

@[expose] public section

open Finset
open scoped ArithmeticFunction

namespace SystolicGrowth
namespace CookMagyarMajorArc

open CookMagyarCircle CookMagyarArcs CookMagyarFiniteFourier

/-! # Von Mangoldt mass in a nonunit residue class

If a prime lies in a nonunit class modulo `q`, it divides `q` and is at most
`q`. The remaining von Mangoldt mass comes from proper prime powers, whose
total mass is `O(√N)` by the elementary Chebyshev estimate in mathlib.
-/

private theorem prime_le_modulus_of_nonunit
    (q : ℕ) [NeZero q] {r : ZMod q} (hr : ¬IsUnit r)
    {p : ℕ} (hp : p.Prime) (hpr : (p : ZMod q) = r) : p ≤ q := by
  have hpnot : ¬IsUnit (p : ZMod q) := by simpa [hpr] using hr
  have hpdvd : p ∣ q := by
    by_contra h
    exact hpnot (ZMod.isUnit_prime_of_not_dvd hp h)
  exact Nat.le_of_dvd (NeZero.pos q) hpdvd

private theorem sum_nonprime_vonMangoldt_eq_psi_sub_theta (m : ℕ) :
    (∑ k ∈ Icc 0 m,
      if ¬k.Prime then ArithmeticFunction.vonMangoldt k else 0) =
      Chebyshev.psi m - Chebyshev.theta m := by
  rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc]
  simp only [Nat.floor_natCast, Finset.sum_filter]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  by_cases hp : k.Prime
  · simp [hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
  · simp [hp]

private theorem sum_small_vonMangoldt_le_psi (q m : ℕ) :
    (∑ k ∈ Icc 0 m,
      if k ≤ q then ArithmeticFunction.vonMangoldt k else 0) ≤
      Chebyshev.psi q := by
  calc
    _ = ∑ k ∈ (Icc 0 m).filter (fun k ↦ k ≤ q),
        ArithmeticFunction.vonMangoldt k := by rw [Finset.sum_filter]
    _ ≤ ∑ k ∈ Icc 0 q, ArithmeticFunction.vonMangoldt k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, (Finset.mem_filter.mp hk).2⟩
      · intro k _hk _hnot
        exact ArithmeticFunction.vonMangoldt_nonneg
    _ = Chebyshev.psi q := by
      rw [Chebyshev.psi_eq_sum_Icc]
      simp

/-- A nonunit class has no large prime contribution: its partial sum is
bounded by the proper-prime-power mass plus the total mass up to `q`. -/
theorem norm_cubicResiduePartialSum_nonunit_le
    (q : ℕ) [NeZero q] (r : ZMod q) (hr : ¬IsUnit r) (m : ℕ) :
    ‖cubicResiduePartialSum q r m‖ ≤
      Chebyshev.psi m - Chebyshev.theta m + Chebyshev.psi q := by
  classical
  have hnorm : ‖cubicResiduePartialSum q r m‖ ≤
      ∑ k ∈ Icc 0 m,
        if (k : ZMod q) = r then ArithmeticFunction.vonMangoldt k else 0 := by
    unfold cubicResiduePartialSum
    calc
      _ ≤ ∑ k ∈ Icc 0 m, ‖cubicResidueCoefficient q r k‖ := norm_sum_le _ _
      _ = ∑ k ∈ Icc 0 m,
          if (k : ZMod q) = r then ArithmeticFunction.vonMangoldt k else 0 := by
        apply Finset.sum_congr rfl
        intro k _hk
        unfold cubicResidueCoefficient
        split_ifs <;> simp [Complex.norm_real,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  have hpoint (k : ℕ) :
      (if (k : ZMod q) = r then ArithmeticFunction.vonMangoldt k else 0) ≤
        (if ¬k.Prime then ArithmeticFunction.vonMangoldt k else 0) +
          (if k ≤ q then ArithmeticFunction.vonMangoldt k else 0) := by
    by_cases hkr : (k : ZMod q) = r
    · by_cases hp : k.Prime
      · have hkq := prime_le_modulus_of_nonunit q hr hp hkr
        simp [hkr, hp, hkq]
      · simp [hkr, hp]
        split_ifs <;> positivity
    · simp [hkr]
      split_ifs <;> positivity
  calc
    ‖cubicResiduePartialSum q r m‖ ≤
        ∑ k ∈ Icc 0 m,
          if (k : ZMod q) = r then ArithmeticFunction.vonMangoldt k else 0 := hnorm
    _ ≤ ∑ k ∈ Icc 0 m,
          ((if ¬k.Prime then ArithmeticFunction.vonMangoldt k else 0) +
            (if k ≤ q then ArithmeticFunction.vonMangoldt k else 0)) := by
      apply Finset.sum_le_sum
      intro k _hk
      exact hpoint k
    _ = (∑ k ∈ Icc 0 m,
          if ¬k.Prime then ArithmeticFunction.vonMangoldt k else 0) +
        (∑ k ∈ Icc 0 m,
          if k ≤ q then ArithmeticFunction.vonMangoldt k else 0) :=
      Finset.sum_add_distrib
    _ ≤ Chebyshev.psi m - Chebyshev.theta m + Chebyshev.psi q := by
      rw [sum_nonprime_vonMangoldt_eq_psi_sub_theta]
      exact add_le_add (le_refl _) (sum_small_vonMangoldt_le_psi q m)

private theorem norm_cubicResiduePartialSum_le_total_mass
    (q : ℕ) [NeZero q] (r : ZMod q) (m : ℕ) :
    ‖cubicResiduePartialSum q r m‖ ≤ Chebyshev.psi m := by
  unfold cubicResiduePartialSum
  calc
    ‖∑ k ∈ Icc 0 m, cubicResidueCoefficient q r k‖ ≤
        ∑ k ∈ Icc 0 m, ‖cubicResidueCoefficient q r k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Icc 0 m, (ArithmeticFunction.vonMangoldt k : ℝ) := by
      apply Finset.sum_le_sum
      intro k _hk
      unfold cubicResidueCoefficient
      split_ifs <;> simp [Complex.norm_real,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    _ = Chebyshev.psi m := by
      rw [Chebyshev.psi_eq_sum_Icc]
      simp

/-- Below `sqrt N`, a unit residue-class discrepancy is bounded by the
entire Chebyshev mass plus the expected main term. This is the elementary
small-endpoint half of the unit-class AP estimate. -/
theorem norm_cubicResiduePartialSum_unit_le_small
    (q : ℕ) [NeZero q] (r : ZMod q) (hr : IsUnit r)
    (N m : ℕ) (_hmN : m ≤ N)
    (hsmall : (m : ℝ) ≤ Real.sqrt (N : ℝ)) :
    ‖cubicResiduePartialSum q r m -
        (m + 1 : ℕ) *
          (if IsUnit r then (Nat.totient q : ℂ)⁻¹ else 0)‖ ≤
      (Real.log 4 + 6) * (Real.sqrt (N : ℝ) + 1) := by
  rw [if_pos hr]
  have hmass := norm_cubicResiduePartialSum_le_total_mass q r m
  have htotientPos : 0 < Nat.totient q := Nat.totient_pos.mpr (NeZero.pos q)
  have htotientOne : (1 : ℝ) ≤ (Nat.totient q : ℝ) := by
    exact_mod_cast (show 1 ≤ Nat.totient q by omega)
  have hmain_eq :
      ‖(m + 1 : ℕ) * (Nat.totient q : ℂ)⁻¹‖ =
        (m + 1 : ℝ) / (Nat.totient q : ℝ) := by
    simp only [norm_mul, norm_inv, Complex.norm_natCast]
    rw [div_eq_mul_inv]
    push_cast
    rfl
  have hmain : ‖(m + 1 : ℕ) * (Nat.totient q : ℂ)⁻¹‖ ≤ (m + 1 : ℝ) := by
    rw [hmain_eq]
    exact div_le_self (by positivity) htotientOne
  have hpsi : Chebyshev.psi m ≤ (Real.log 4 + 4) * (m : ℝ) :=
    Chebyshev.psi_le_const_mul_self (by positivity)
  have hmplus : (m + 1 : ℝ) = (m : ℝ) + 1 := by norm_num
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hsqrt : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  calc
    ‖cubicResiduePartialSum q r m -
        (m + 1 : ℕ) * (Nat.totient q : ℂ)⁻¹‖ ≤
        ‖cubicResiduePartialSum q r m‖ +
          ‖(m + 1 : ℕ) * (Nat.totient q : ℂ)⁻¹‖ := norm_sub_le _ _
    _ ≤ Chebyshev.psi m + (m + 1 : ℝ) := add_le_add hmass hmain
    _ ≤ (Real.log 4 + 4) * (m : ℝ) + ((m : ℝ) + 1) := by rw [hmplus]; exact add_le_add hpsi le_rfl
    _ ≤ (Real.log 4 + 4) * Real.sqrt (N : ℝ) + (Real.sqrt (N : ℝ) + 1) := by
      gcongr
    _ ≤ (Real.log 4 + 6) * (Real.sqrt (N : ℝ) + 1) := by
      nlinarith

/-- Uniform nonunit-class AP control in exactly the error shape used by
`norm_cubicResidueClassSum_sub_stepModel_le_of_AP`. The constant is the one
provided by mathlib's Chebyshev proper-prime-power estimate. -/
theorem exists_uniform_nonunit_residue_AP_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (q : ℕ) [NeZero q] (r : ZMod q), ¬IsUnit r →
        ∀ (A : ℂ) (N m : ℕ), m ≤ N →
          ‖cubicResiduePartialSum q r m -
              (m + 1 : ℕ) * (if IsUnit r then A else 0)‖ ≤
            C * Real.sqrt N + (Real.log 4 + 4) * q := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨|C|, abs_nonneg _, ?_⟩
  intro q _inst r hr A N m hmN
  simp only [if_neg hr, mul_zero, sub_zero]
  have hmass := norm_cubicResiduePartialSum_nonunit_le q r hr m
  have hproper := hC (m : ℝ)
  have hq : Chebyshev.psi (q : ℝ) ≤ (Real.log 4 + 4) * q :=
    Chebyshev.psi_le_const_mul_self (by positivity)
  have hsqrt : Real.sqrt (m : ℝ) ≤ Real.sqrt (N : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hmN)
  have hCabs : C ≤ |C| := le_abs_self C
  have hnonneg : 0 ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
  calc
    ‖cubicResiduePartialSum q r m‖ ≤
        Chebyshev.psi m - Chebyshev.theta m + Chebyshev.psi q := hmass
    _ ≤ C * Real.sqrt m + Chebyshev.psi q := by gcongr
    _ ≤ |C| * Real.sqrt N + (Real.log 4 + 4) * q := by
      have hfirst : C * Real.sqrt (m : ℝ) ≤ |C| * Real.sqrt (N : ℝ) :=
        (mul_le_mul_of_nonneg_right hCabs hnonneg).trans
          (mul_le_mul_of_nonneg_left hsqrt (abs_nonneg C))
      exact add_le_add hfirst hq

/-- A fixed constant for the uniform nonunit AP estimate. -/
noncomputable def nonunitResidueAPConstant : ℝ :=
  Classical.choose exists_uniform_nonunit_residue_AP_bound

theorem nonunitResidueAPConstant_nonneg : 0 ≤ nonunitResidueAPConstant :=
  (Classical.choose_spec exists_uniform_nonunit_residue_AP_bound).1

/-- The nonunit half of the arithmetic-progression hypothesis consumed by
the cubic Abel-summation bridge. This version requires no existential
elimination at its call site. -/
theorem norm_cubicResiduePartialSum_nonunit_le_uniform
    (q : ℕ) [NeZero q] (r : ZMod q) (hr : ¬IsUnit r)
    (A : ℂ) (N m : ℕ) (hmN : m ≤ N) :
    ‖cubicResiduePartialSum q r m -
        (m + 1 : ℕ) * (if IsUnit r then A else 0)‖ ≤
      nonunitResidueAPConstant * Real.sqrt N + (Real.log 4 + 4) * q :=
  (Classical.choose_spec exists_uniform_nonunit_residue_AP_bound).2 q r hr A N m hmN

/-- The complete small-endpoint AP estimate, uniform over unit and nonunit
residue classes. The Siegel--Walfisz input is only needed above `sqrt N`. -/
theorem norm_cubicResiduePartialSum_sub_density_le_small
    (q : ℕ) [NeZero q] (r : ZMod q) (N m : ℕ)
    (hmN : m ≤ N) (hsmall : (m : ℝ) ≤ Real.sqrt (N : ℝ)) :
    ‖cubicResiduePartialSum q r m -
        (m + 1 : ℕ) *
          (if IsUnit r then (Nat.totient q : ℂ)⁻¹ else 0)‖ ≤
      (nonunitResidueAPConstant + (Real.log 4 + 6)) *
          (Real.sqrt (N : ℝ) + 1) + (Real.log 4 + 4) * q := by
  by_cases hr : IsUnit r
  · have hunit := norm_cubicResiduePartialSum_unit_le_small q r hr N m hmN hsmall
    have hC : 0 ≤ nonunitResidueAPConstant := nonunitResidueAPConstant_nonneg
    have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hsqrt : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
    simpa only [if_pos hr] using le_trans hunit (by
      have hq : 0 ≤ (Real.log 4 + 4) * (q : ℝ) := by positivity
      nlinarith)
  · have hnonunit := norm_cubicResiduePartialSum_nonunit_le_uniform
      q r hr 0 N m hmN
    have hC : 0 ≤ nonunitResidueAPConstant := nonunitResidueAPConstant_nonneg
    have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hsqrt : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
    simpa only [if_neg hr, mul_zero, sub_zero] using le_trans hnonunit (by
      nlinarith)

/-- The large-endpoint unit-class estimate, together with the already-proved
small-endpoint and nonunit estimates, gives one uniform all-residue AP
envelope. This is an adapter only: the Siegel--Walfisz proof must supply
`hunitLarge` rather than treating it as a project assumption. -/
theorem norm_cubicResiduePartialSum_sub_density_le_of_unit_large
    (q Q N m : ℕ) [NeZero q] (r : ZMod q) (U : ℝ)
    (hq : q ≤ Q) (hmN : m ≤ N) (hU : 0 ≤ U)
    (hunitLarge : IsUnit r → Real.sqrt (N : ℝ) < (m : ℝ) →
      ‖cubicResiduePartialSum q r m -
          (m + 1 : ℕ) * (Nat.totient q : ℂ)⁻¹‖ ≤ U) :
    ‖cubicResiduePartialSum q r m -
        (m + 1 : ℕ) *
          (if IsUnit r then (Nat.totient q : ℂ)⁻¹ else 0)‖ ≤
      U + (nonunitResidueAPConstant + (Real.log 4 + 6)) *
            (Real.sqrt (N : ℝ) + 1) + (Real.log 4 + 4) * Q := by
  have hK : 0 ≤ nonunitResidueAPConstant :=
    nonunitResidueAPConstant_nonneg
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hsqrt : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hsmallConstant : 0 ≤
      nonunitResidueAPConstant + (Real.log 4 + 6) := by positivity
  have hqReal : (q : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hq
  have hqTerm : (Real.log 4 + 4) * (q : ℝ) ≤
      (Real.log 4 + 4) * (Q : ℝ) :=
    mul_le_mul_of_nonneg_left hqReal (by positivity)
  by_cases hr : IsUnit r
  · by_cases hsmall : (m : ℝ) ≤ Real.sqrt (N : ℝ)
    · have hbound := norm_cubicResiduePartialSum_sub_density_le_small
        q r N m hmN hsmall
      simpa only [if_pos hr] using le_trans hbound (by
        have hsmallTerm : 0 ≤
            (nonunitResidueAPConstant + (Real.log 4 + 6)) *
              (Real.sqrt (N : ℝ) + 1) := by positivity
        nlinarith [hqTerm])
    · have hlarge : Real.sqrt (N : ℝ) < (m : ℝ) := lt_of_not_ge hsmall
      simpa only [if_pos hr] using le_trans (hunitLarge hr hlarge) (by
        have hlargeTerm : 0 ≤
            (nonunitResidueAPConstant + (Real.log 4 + 6)) *
              (Real.sqrt (N : ℝ) + 1) := by positivity
        have hQTerm : 0 ≤ (Real.log 4 + 4) * (Q : ℝ) := by positivity
        linarith)
  · have hnonunit := norm_cubicResiduePartialSum_nonunit_le_uniform
      q r hr 0 N m hmN
    simpa only [if_neg hr, mul_zero, sub_zero] using le_trans hnonunit (by
      have hKsqrt : nonunitResidueAPConstant * Real.sqrt (N : ℝ) ≤
          (nonunitResidueAPConstant + (Real.log 4 + 6)) *
            (Real.sqrt (N : ℝ) + 1) := by nlinarith
      have hqTerm' : (Real.log 4 + 4) * (q : ℝ) ≤
          (Real.log 4 + 4) * (Q : ℝ) := hqTerm
      nlinarith)

/-- Converting the source convention `m/φ(q)` to the inclusive endpoint
convention `(m+1)/φ(q)` costs at most one, since `φ(q)≥1` for `q>0`. -/
theorem norm_cubicResiduePartialSum_sub_endpointDensity_le
    (q m : ℕ) [NeZero q] (r : ZMod q) (W : ℝ)
    (hsource :
      ‖cubicResiduePartialSum q r m -
        (m : ℕ) * (Nat.totient q : ℂ)⁻¹‖ ≤ W) :
    ‖cubicResiduePartialSum q r m -
        (m + 1 : ℕ) * (Nat.totient q : ℂ)⁻¹‖ ≤ W + 1 := by
  have htotientPosNat : 0 < Nat.totient q :=
    Nat.totient_pos.mpr (NeZero.pos q)
  have htotientOne : (1 : ℝ) ≤ (Nat.totient q : ℝ) := by
    exact_mod_cast htotientPosNat
  have htotientPos : (0 : ℝ) < (Nat.totient q : ℝ) := by linarith
  have hinv : ‖(Nat.totient q : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_natCast]
    exact (inv_le_one₀ htotientPos).2 htotientOne
  have hstep :
      (m + 1 : ℕ) * (Nat.totient q : ℂ)⁻¹ -
        (m : ℕ) * (Nat.totient q : ℂ)⁻¹ =
          (Nat.totient q : ℂ)⁻¹ := by
    push_cast
    ring
  calc
    ‖cubicResiduePartialSum q r m -
        (m + 1 : ℕ) * (Nat.totient q : ℂ)⁻¹‖ =
        ‖(cubicResiduePartialSum q r m -
            (m : ℕ) * (Nat.totient q : ℂ)⁻¹) -
          ((m + 1 : ℕ) * (Nat.totient q : ℂ)⁻¹ -
            (m : ℕ) * (Nat.totient q : ℂ)⁻¹)‖ := by
      congr 1
      push_cast
      ring
    _ ≤ ‖cubicResiduePartialSum q r m -
          (m : ℕ) * (Nat.totient q : ℂ)⁻¹‖ +
        ‖(m + 1 : ℕ) * (Nat.totient q : ℂ)⁻¹ -
          (m : ℕ) * (Nat.totient q : ℂ)⁻¹‖ := norm_sub_le _ _
    _ = ‖cubicResiduePartialSum q r m -
          (m : ℕ) * (Nat.totient q : ℂ)⁻¹‖ +
        ‖(Nat.totient q : ℂ)⁻¹‖ := by rw [hstep]
    _ ≤ W + 1 := add_le_add hsource hinv

/-- A large-endpoint unit-class AP estimate feeds through the proved
nonunit/small-endpoint bounds, Abel summation, and residue recombination to
the weighted exponential sum on a major arc. The hypothesis is precisely
the remaining unit-class analytic input; this adapter does not assert or
assume it globally. -/
theorem norm_cubicVonMangoldtExpSum_sub_stepModel_le_of_unit_large
    (q Q a : ℕ) [NeZero q] (beta : ℝ) (N X : ℕ)
    (hN : 0 < N) (hNX : N ≤ X) (hq : q ≤ Q)
    (U : ℝ) (hU : 0 ≤ U)
    (hunitLarge : ∀ r : ZMod q, IsUnit r → ∀ m ≤ X,
      Real.sqrt (X : ℝ) < (m : ℝ) →
        ‖cubicResiduePartialSum q r m -
            (m : ℕ) * (Nat.totient q : ℂ)⁻¹‖ ≤ U) :
    ‖cubicVonMangoldtExpSum (rationalCenter a q + beta) N -
        unitCubicExponentialSum (a : ZMod q) *
          ((Nat.totient q : ℂ)⁻¹ *
            ∑ k ∈ Icc 0 N, addChar beta (primeCubic k))‖ ≤
      (q : ℝ) *
        ((U + 1 + (nonunitResidueAPConstant + (Real.log 4 + 6)) *
              (Real.sqrt (X : ℝ) + 1) + (Real.log 4 + 4) * Q) *
          (1 + (N : ℝ) *
            (2 * Real.pi * |beta| * (3 * (N : ℝ) ^ 2 + 1)))) := by
  let Delta : ℝ :=
    U + 1 + (nonunitResidueAPConstant + (Real.log 4 + 6)) *
      (Real.sqrt (X : ℝ) + 1) + (Real.log 4 + 4) * Q
  have hDelta : 0 ≤ Delta := by
    dsimp [Delta]
    have hK := nonunitResidueAPConstant_nonneg
    have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  apply norm_cubicVonMangoldtExpSum_sub_stepModel_le_of_AP
    q a (Nat.totient q : ℂ)⁻¹ beta N hN hDelta
  intro r m hm
  have hmX : m ≤ X := hm.trans hNX
  have hlargeUnit := hunitLarge r
  have hlargeAtEndpoint : IsUnit r → Real.sqrt (X : ℝ) < (m : ℝ) →
      ‖cubicResiduePartialSum q r m -
          (m + 1 : ℕ) * (Nat.totient q : ℂ)⁻¹‖ ≤ U + 1 := by
    intro hr hlarge
    exact norm_cubicResiduePartialSum_sub_endpointDensity_le
      q m r U (hlargeUnit hr m hmX hlarge)
  exact norm_cubicResiduePartialSum_sub_density_le_of_unit_large
    q Q X m r (U + 1) hq hmX (by linarith) hlargeAtEndpoint

/-- Abel summation on an initial interval controlled by the elementary
small-endpoint AP estimate. `X` is the global scale used in the square-root
split, while `N` is the actual endpoint of this weighted sum. -/
theorem norm_cubicResidueClassSum_sub_stepModel_le_small
    (q : ℕ) [NeZero q] (r : ZMod q) (beta : ℝ) (N X : ℕ)
    (hN : 0 < N) (hNX : N ≤ X)
    (hsmall : (N : ℝ) ≤ Real.sqrt (X : ℝ)) :
    ‖cubicResidueClassSum q r beta N -
        residueClassMain r
          ((Nat.totient q : ℂ)⁻¹ *
            ∑ k ∈ Icc 0 N, addChar beta (primeCubic k))‖ ≤
      ((nonunitResidueAPConstant + (Real.log 4 + 6)) *
          (Real.sqrt (X : ℝ) + 1) + (Real.log 4 + 4) * q) *
        (1 + (N : ℝ) *
          (2 * Real.pi * |beta| * (3 * (N : ℝ) ^ 2 + 1))) := by
  have hDelta : 0 ≤
      (nonunitResidueAPConstant + (Real.log 4 + 6)) *
        (Real.sqrt (X : ℝ) + 1) + (Real.log 4 + 4) * q := by
    have hC := nonunitResidueAPConstant_nonneg
    have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  apply norm_cubicResidueClassSum_sub_stepModel_le_of_AP
    q r (Nat.totient q : ℂ)⁻¹ beta N hN hDelta
  intro m hm
  exact norm_cubicResiduePartialSum_sub_density_le_small
    q r X m (hm.trans hNX) (by
      exact le_trans (by exact_mod_cast hm) hsmall)

/-- Abel summation turns the nonunit AP bound into a bound for the weighted
residue-class sum; its expected major-arc main term is zero. -/
theorem norm_cubicResidueClassSum_nonunit_le
    (q : ℕ) [NeZero q] (r : ZMod q) (hr : ¬IsUnit r)
    (beta : ℝ) (N : ℕ) (hN : 0 < N) :
    ‖cubicResidueClassSum q r beta N‖ ≤
      (nonunitResidueAPConstant * Real.sqrt N + (Real.log 4 + 4) * q) *
        (1 + (N : ℝ) *
          (2 * Real.pi * |beta| * (3 * (N : ℝ) ^ 2 + 1))) := by
  let Delta : ℝ :=
    nonunitResidueAPConstant * Real.sqrt N + (Real.log 4 + 4) * q
  have hDelta : 0 ≤ Delta := by
    dsimp [Delta]
    have := nonunitResidueAPConstant_nonneg
    positivity
  have hAP : ∀ m ≤ N,
      ‖cubicResiduePartialSum q r m -
        (m + 1 : ℕ) * (if IsUnit r then (0 : ℂ) else 0)‖ ≤ Delta := by
    intro m hm
    exact norm_cubicResiduePartialSum_nonunit_le_uniform q r hr 0 N m hm
  have h := norm_cubicResidueClassSum_sub_stepModel_le_of_AP
    q r (0 : ℂ) beta N hN hDelta hAP
  simpa [residueClassMain, hr, Delta] using h

end CookMagyarMajorArc
end SystolicGrowth

#print axioms SystolicGrowth.CookMagyarMajorArc.norm_cubicResiduePartialSum_unit_le_small
#print axioms SystolicGrowth.CookMagyarMajorArc.norm_cubicResiduePartialSum_sub_density_le_small
#print axioms SystolicGrowth.CookMagyarMajorArc.norm_cubicResiduePartialSum_sub_density_le_of_unit_large
#print axioms SystolicGrowth.CookMagyarMajorArc.norm_cubicResiduePartialSum_sub_endpointDensity_le
#print axioms SystolicGrowth.CookMagyarMajorArc.norm_cubicVonMangoldtExpSum_sub_stepModel_le_of_unit_large
#print axioms SystolicGrowth.CookMagyarMajorArc.norm_cubicResidueClassSum_sub_stepModel_le_small
