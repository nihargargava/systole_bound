module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.NumberTheory.AbelSummation

@[expose] public section

open Finset MeasureTheory

namespace SystolicGrowth
namespace CookMagyarMajorArc

/-! # Uniform partial-summation error bound

This is the analytic bookkeeping that turns a uniform bound for partial
sums in an arithmetic progression into a bound for the same coefficients
against a smooth oscillatory weight.  The number-theoretic estimate and the
phase derivative are deliberately separate inputs.
-/

/-- Abel summation with a uniform partial-sum error.  At a positive endpoint,
if the weight has norm at most one there and all coefficient partial sums
have norm at most `Delta`, then the weighted error is controlled by the total
variation of the weight. -/
theorem norm_sum_mul_le_partialSumBound_mul_one_add_integral_norm_deriv
    (c : ℕ → ℂ) {f : ℝ → ℂ} (N : ℕ) {Delta : ℝ}
    (hN : 0 < N)
    (_hDelta : 0 ≤ Delta)
    (hfdiff : ∀ t ∈ Set.Icc (0 : ℝ) N, DifferentiableAt ℝ f t)
    (hfint : IntegrableOn (deriv f) (Set.Icc (0 : ℝ) N))
    (hfN : ‖f N‖ ≤ 1)
    (hpartial : ∀ t ∈ Set.Ioc (0 : ℝ) N,
      ‖∑ k ∈ Icc 0 ⌊t⌋₊, c k‖ ≤ Delta) :
    ‖∑ k ∈ Icc 0 N, f k * c k‖ ≤
      Delta * (1 + ∫ t in Set.Ioc (0 : ℝ) N, ‖deriv f t‖) := by
  have hAbel := sum_mul_eq_sub_integral_mul' c N hfdiff hfint
  rw [hAbel]
  have hpartialN : ‖∑ k ∈ Icc 0 N, c k‖ ≤ Delta := by
    simpa using hpartial (N : ℝ) ⟨by exact_mod_cast hN, le_rfl⟩
  have hhead : ‖f N * ∑ k ∈ Icc 0 N, c k‖ ≤ Delta := by
    rw [norm_mul]
    calc
      ‖f N‖ * ‖∑ k ∈ Icc 0 N, c k‖ ≤ 1 * Delta := by
        exact mul_le_mul hfN hpartialN (norm_nonneg _) (by norm_num)
      _ = Delta := one_mul _
  let F : ℝ → ℝ := fun t =>
    ‖deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k‖
  let G : ℝ → ℝ := fun t => Delta * ‖deriv f t‖
  have hcomplex : IntegrableOn
      (fun t => deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k)
      (Set.Ioc (0 : ℝ) N) := by
    exact (integrableOn_mul_sum_Icc c (a := (0 : ℝ)) (b := (N : ℝ))
      (by norm_num) hfint).mono_set Set.Ioc_subset_Icc_self
  have hF : IntegrableOn F (Set.Ioc (0 : ℝ) N) := hcomplex.norm
  have hG : IntegrableOn G (Set.Ioc (0 : ℝ) N) := by
    have hnorm : IntegrableOn (fun t ↦ ‖deriv f t‖)
        (Set.Icc (0 : ℝ) N) := hfint.norm
    have hnormIoc : IntegrableOn (fun t ↦ ‖deriv f t‖)
        (Set.Ioc (0 : ℝ) N) :=
      IntegrableOn.mono_set hnorm Set.Ioc_subset_Icc_self
    exact Integrable.const_mul hnormIoc Delta
  have hpoint : ∀ t ∈ Set.Ioc (0 : ℝ) N, F t ≤ G t := by
    intro t ht
    dsimp only [F, G]
    rw [norm_mul]
    calc
      ‖deriv f t‖ * ‖∑ k ∈ Icc 0 ⌊t⌋₊, c k‖ ≤
          ‖deriv f t‖ * Delta :=
        mul_le_mul_of_nonneg_left (hpartial t ht) (norm_nonneg _)
      _ = Delta * ‖deriv f t‖ := mul_comm _ _
  have hintegral :
      ‖∫ t in Set.Ioc (0 : ℝ) N,
          deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k‖ ≤
        Delta * ∫ t in Set.Ioc (0 : ℝ) N, ‖deriv f t‖ := by
    calc
      ‖∫ t in Set.Ioc (0 : ℝ) N,
          deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k‖ ≤
          ∫ t in Set.Ioc (0 : ℝ) N, F t := by
        exact norm_integral_le_integral_norm _
      _ ≤ ∫ t in Set.Ioc (0 : ℝ) N, G t :=
        setIntegral_mono_on hF hG measurableSet_Ioc hpoint
      _ = Delta * ∫ t in Set.Ioc (0 : ℝ) N, ‖deriv f t‖ := by
        dsimp only [G]
        rw [integral_const_mul]
  calc
    ‖f N * ∑ k ∈ Icc 0 N, c k -
        ∫ t in Set.Ioc (0 : ℝ) N,
          deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k‖ ≤
      ‖f N * ∑ k ∈ Icc 0 N, c k‖ +
        ‖∫ t in Set.Ioc (0 : ℝ) N,
          deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k‖ := norm_sub_le _ _
    _ ≤ Delta + Delta *
        ∫ t in Set.Ioc (0 : ℝ) N, ‖deriv f t‖ :=
      add_le_add hhead hintegral
    _ = Delta * (1 +
        ∫ t in Set.Ioc (0 : ℝ) N, ‖deriv f t‖) := by ring

/-- A uniform derivative bound turns the variation term in Abel summation
into an explicit interval-length factor. -/
theorem norm_sum_mul_le_partialSumBound_mul_one_add_length_deriv
    (c : ℕ → ℂ) {f : ℝ → ℂ} (N : ℕ) {Delta B : ℝ}
    (hN : 0 < N) (hDelta : 0 ≤ Delta)
    (hfdiff : ∀ t ∈ Set.Icc (0 : ℝ) N, DifferentiableAt ℝ f t)
    (hfint : IntegrableOn (deriv f) (Set.Icc (0 : ℝ) N))
    (hfN : ‖f N‖ ≤ 1)
    (hpartial : ∀ t ∈ Set.Ioc (0 : ℝ) N,
      ‖∑ k ∈ Icc 0 ⌊t⌋₊, c k‖ ≤ Delta)
    (hderiv : ∀ t ∈ Set.Ioc (0 : ℝ) N, ‖deriv f t‖ ≤ B) :
    ‖∑ k ∈ Icc 0 N, f k * c k‖ ≤
      Delta * (1 + (N : ℝ) * B) := by
  have hbase := norm_sum_mul_le_partialSumBound_mul_one_add_integral_norm_deriv
    c N hN hDelta hfdiff hfint hfN hpartial
  have hvariation :
      (∫ t in Set.Ioc (0 : ℝ) N, ‖deriv f t‖) ≤ (N : ℝ) * B := by
    calc
      (∫ t in Set.Ioc (0 : ℝ) N, ‖deriv f t‖) ≤
          ∫ _t in Set.Ioc (0 : ℝ) N, B := by
        apply setIntegral_mono_on
        · exact IntegrableOn.mono_set hfint.norm Set.Ioc_subset_Icc_self
        · exact integrableOn_const (by simp)
        · exact measurableSet_Ioc
        · exact hderiv
      _ = (N : ℝ) * B := by
        simp [Nat.cast_nonneg]
  exact hbase.trans (mul_le_mul_of_nonneg_left
    (by linarith : 1 + (∫ t in Set.Ioc (0 : ℝ) N, ‖deriv f t‖) ≤
      1 + (N : ℝ) * B) hDelta)

end CookMagyarMajorArc
end SystolicGrowth
