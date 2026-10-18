module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.CubicHighMoment
public import CookMagyar.MinorArcReduction

@[expose] public section

open MeasureTheory Filter

namespace SystolicGrowth
namespace CookMagyarCircle

open CookMagyarArcs

/-! # The 32nd-moment minor-arc reduction

The actual minor-arc integral is controlled by the pointwise prime-sum
bound to the power `n - 32` and the global weighted 32nd moment. This is
the deterministic bridge for the logarithmic-cutoff route at `n ≥ 33`.
-/

private theorem continuous_norm_cubicVonMangoldtExpSum_pow_thirtyTwo (N : ℕ) :
    Continuous (fun α : ℝ => ‖cubicVonMangoldtExpSum α N‖ ^ 32) := by
  unfold cubicVonMangoldtExpSum addChar
  fun_prop

/-- Exact pointwise factorization, uniform in the target character. -/
theorem norm_cubicIntegrand_eq_pow_sub_thirtyTwo_mul
    {n N T : ℕ} (hn : 32 ≤ n) (alpha : ℝ) :
    ‖cubicIntegrand n N T alpha‖ =
      ‖cubicVonMangoldtExpSum alpha N‖ ^ (n - 32) *
        ‖cubicVonMangoldtExpSum alpha N‖ ^ 32 := by
  unfold cubicIntegrand
  rw [norm_mul, norm_pow, norm_negAddChar, mul_one, ← pow_add]
  congr 1
  omega

/-- The 32nd-moment route bounds the actual target-dependent minor
integral, without any pointwise weighted/unweighted comparison. -/
theorem norm_cubicMinorArcIntegral_le_sup_pow_mul_thirtySecondMoment
    {n N T Q : ℕ} (hn : 32 ≤ n) {A : ℝ} (hA : 0 ≤ A)
    (hsup : ∀ alpha ∈ minorArcs N Q,
      ‖cubicVonMangoldtExpSum alpha N‖ ≤ A) :
    ‖cubicMinorArcIntegral n N T Q‖ ≤
      A ^ (n - 32) *
        (∫ alpha in Set.Icc (0 : ℝ) 1,
          ‖cubicVonMangoldtExpSum alpha N‖ ^ 32) := by
  let f : ℝ → ℝ := fun alpha => ‖cubicIntegrand n N T alpha‖
  let g : ℝ → ℝ := fun alpha =>
    A ^ (n - 32) * ‖cubicVonMangoldtExpSum alpha N‖ ^ 32
  have hf : IntegrableOn f (minorArcs N Q) :=
    (cubicIntegrand_integrableOn_minorArcs n N T Q).norm
  have hgIcc : IntegrableOn g (Set.Icc (0 : ℝ) 1) := by
    apply Continuous.integrableOn_Icc
    dsimp only [g]
    exact continuous_const.mul
      (continuous_norm_cubicVonMangoldtExpSum_pow_thirtyTwo N)
  have hg : IntegrableOn g (minorArcs N Q) :=
    hgIcc.mono_set (minorArcs_subset_Icc N Q)
  have hpoint : ∀ alpha ∈ minorArcs N Q, f alpha ≤ g alpha := by
    intro alpha halpha
    dsimp only [f, g]
    rw [norm_cubicIntegrand_eq_pow_sub_thirtyTwo_mul hn]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (hsup alpha halpha) (n - 32))
      (pow_nonneg (norm_nonneg _) 32)
  calc
    ‖cubicMinorArcIntegral n N T Q‖ ≤
        ∫ alpha in minorArcs N Q, f alpha := by
      unfold cubicMinorArcIntegral
      exact norm_integral_le_integral_norm _
    _ ≤ ∫ alpha in minorArcs N Q, g alpha :=
      setIntegral_mono_on hf hg (minorArcs_measurableSet N Q) hpoint
    _ ≤ ∫ alpha in Set.Icc (0 : ℝ) 1, g alpha := by
      exact setIntegral_mono_set hgIcc
        (Eventually.of_forall fun alpha => by
          dsimp only [g]
          positivity)
        (Eventually.of_forall (minorArcs_subset_Icc N Q))
    _ = A ^ (n - 32) *
          (∫ alpha in Set.Icc (0 : ℝ) 1,
            ‖cubicVonMangoldtExpSum alpha N‖ ^ 32) := by
      dsimp only [g]
      rw [integral_const_mul]

/-- The exact unweighted count is the only global moment needed by the
logarithmic-cutoff minor-arc argument. -/
theorem norm_cubicMinorArcIntegral_le_sup_pow_mul_unweightedCount
    {n N T Q : ℕ} (hn : 32 ≤ n) {A : ℝ} (hA : 0 ≤ A)
    (hsup : ∀ alpha ∈ minorArcs N Q,
      ‖cubicVonMangoldtExpSum alpha N‖ ≤ A) :
    ‖cubicMinorArcIntegral n N T Q‖ ≤
      A ^ (n - 32) * Real.log (N + 1 : ℝ) ^ 32 *
        cubicThirtySecondSolutionCount N := by
  calc
    ‖cubicMinorArcIntegral n N T Q‖ ≤
        A ^ (n - 32) *
          (∫ alpha in Set.Icc (0 : ℝ) 1,
            ‖cubicVonMangoldtExpSum alpha N‖ ^ 32) :=
      norm_cubicMinorArcIntegral_le_sup_pow_mul_thirtySecondMoment hn hA hsup
    _ ≤ A ^ (n - 32) *
          (Real.log (N + 1 : ℝ) ^ 32 * cubicThirtySecondSolutionCount N) := by
      rw [integral_norm_cubicVonMangoldtExpSum_pow_thirtyTwo]
      exact mul_le_mul_of_nonneg_left
        (cubicVonMangoldtThirtySecondEnergy_le_count N)
        (pow_nonneg hA _)
    _ = A ^ (n - 32) * Real.log (N + 1 : ℝ) ^ 32 *
          cubicThirtySecondSolutionCount N := by ring

end CookMagyarCircle
end SystolicGrowth
