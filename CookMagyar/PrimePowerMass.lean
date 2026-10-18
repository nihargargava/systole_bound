module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.PrimePowerAnalytic
public import Mathlib.NumberTheory.Chebyshev

@[expose] public section

open scoped ArithmeticFunction
open Filter Asymptotics

namespace SystolicGrowth
namespace CookMagyarCircle

/-! # The mass of the discarded prime powers

Mathlib's Chebyshev function already contains the sharp elementary fact that
the total von--Mangoldt mass of proper prime powers up to `N` is
`O(√N)`.  The only additional term discarded here is the even prime `2`.
This file identifies our coefficient mass exactly with `ψ(N)-θ(N)+log 2`
and records an explicit bound.
-/

open Finset

/-- The total coefficient mass is exactly Chebyshev's `ψ` function. -/
theorem cubicVonMangoldtMass_eq_psi (N : ℕ) :
    cubicVonMangoldtMass N = Chebyshev.psi N := by
  unfold cubicVonMangoldtMass
  rw [Fin.sum_univ_eq_sum_range
    (fun x : ℕ ↦ ArithmeticFunction.vonMangoldt x) (N + 1)]
  rw [Nat.range_succ_eq_Icc_zero, Chebyshev.psi_eq_sum_Icc]
  norm_num

/-- Chebyshev's explicit linear upper bound for the full coefficient mass. -/
theorem cubicVonMangoldtMass_le_const_mul (N : ℕ) :
    cubicVonMangoldtMass N ≤ (Real.log 4 + 4) * N := by
  rw [cubicVonMangoldtMass_eq_psi]
  exact Chebyshev.psi_le_const_mul_self (by positivity)

/-- In asymptotic notation, the full coefficient mass is `O(N)`. -/
theorem isBigO_cubicVonMangoldtMass_id :
    (fun N : ℕ ↦ cubicVonMangoldtMass N) =O[atTop]
      (fun N : ℕ ↦ (N : ℝ)) := by
  rw [isBigO_iff]
  refine ⟨Real.log 4 + 4, Filter.Eventually.of_forall fun N ↦ ?_⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (cubicVonMangoldtMass_nonneg N),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ N)]
  exact cubicVonMangoldtMass_le_const_mul N

private theorem not_oddPrime_filter_eq_not_prime_union_two
    [DecidablePred (fun x : ℕ ↦ ¬IsOddPrime x)]
    {N : ℕ} (hN : 2 ≤ N) :
    (Finset.Icc 0 N).filter (fun x ↦ ¬IsOddPrime x) =
      (Finset.Icc 0 N).filter (fun x ↦ ¬x.Prime) ∪ {2} := by
  classical
  ext x
  simp only [mem_filter, mem_Icc, zero_le, true_and, mem_union, mem_singleton]
  constructor
  · rintro ⟨hxN, hbad⟩
    by_cases hp : x.Prime
    · right
      by_contra hx2
      exact hbad ⟨hp, hx2⟩
    · exact Or.inl ⟨hxN, hp⟩
  · rintro (⟨hxN, hp⟩ | rfl)
    · exact ⟨hxN, fun h ↦ hp h.1⟩
    · exact ⟨hN, fun h ↦ h.2 rfl⟩

/-- The bad coefficient mass consists of proper prime powers together with
the contribution of the prime `2`. -/
theorem cubicBadPrimePowerMass_eq_psi_sub_theta_add_log_two
    {N : ℕ} (hN : 2 ≤ N) :
    cubicBadPrimePowerMass N =
      Chebyshev.psi N - Chebyshev.theta N + Real.log 2 := by
  classical
  unfold cubicBadPrimePowerMass
  rw [Fin.sum_univ_eq_sum_range
    (fun x : ℕ ↦ if ¬IsOddPrime x then
      ArithmeticFunction.vonMangoldt x else 0) (N + 1)]
  rw [Nat.range_succ_eq_Icc_zero]
  rw [← Finset.sum_filter]
  rw [not_oddPrime_filter_eq_not_prime_union_two hN]
  have hdisjoint :
      Disjoint ((Finset.Icc 0 N).filter (fun x ↦ ¬x.Prime)) ({2} : Finset ℕ) := by
    rw [Finset.disjoint_singleton_right]
    simp only [Finset.mem_filter, Finset.mem_Icc, zero_le, true_and, not_and,
      not_not]
    exact fun _ ↦ Nat.prime_two
  rw [Finset.sum_union hdisjoint]
  simp only [Finset.sum_singleton]
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
  norm_num
  rw [Finset.sum_filter, Finset.sum_filter]
  rw [← Finset.add_sum_Ioc_eq_sum_Icc]
  simp
  positivity

/-- An explicit elementary estimate for the bad mass. -/
theorem cubicBadPrimePowerMass_le_sqrt_mul_log_add
    {N : ℕ} (hN : 2 ≤ N) :
    cubicBadPrimePowerMass N ≤
      2 * Real.sqrt N * Real.log N + Real.log 2 := by
  rw [cubicBadPrimePowerMass_eq_psi_sub_theta_add_log_two hN]
  gcongr
  exact Chebyshev.psi_sub_theta_le (by exact_mod_cast (hN.trans' (by norm_num)))

/-- In asymptotic notation, the discarded one-dimensional coefficient mass
is `O(√N)`. -/
theorem isBigO_cubicBadPrimePowerMass_sqrt :
    (fun N : ℕ ↦ cubicBadPrimePowerMass N) =O[atTop]
      (fun N : ℕ ↦ Real.sqrt N) := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  rw [isBigO_iff]
  refine ⟨|C| + Real.log 2, eventually_atTop.2 ⟨2, ?_⟩⟩
  intro N hN
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  rw [abs_of_nonneg (cubicBadPrimePowerMass_nonneg N),
    abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [cubicBadPrimePowerMass_eq_psi_sub_theta_add_log_two hN]
  have hsqrt : 1 ≤ Real.sqrt (N : ℝ) := by
    rw [Real.one_le_sqrt]
    exact_mod_cast (show 1 ≤ N by omega)
  have hdiff := hC (N : ℝ)
  have hCle : C ≤ |C| := le_abs_self C
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogmul : Real.log 2 ≤ Real.log 2 * Real.sqrt (N : ℝ) := by
    calc
      Real.log 2 = Real.log 2 * 1 := by ring
      _ ≤ Real.log 2 * Real.sqrt (N : ℝ) :=
        mul_le_mul_of_nonneg_left hsqrt hlog
  calc
    Chebyshev.psi N - Chebyshev.theta N + Real.log 2 ≤
        C * Real.sqrt N + Real.log 2 := by gcongr
    _ ≤ |C| * Real.sqrt N + Real.log 2 := by gcongr
    _ ≤ |C| * Real.sqrt N + Real.log 2 * Real.sqrt N := by
      exact add_le_add (le_refl _) hlogmul
    _ = (|C| + Real.log 2) * Real.sqrt N := by ring

end CookMagyarCircle
end SystolicGrowth
