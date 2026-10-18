module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.Arcs
public import CookMagyar.PrimePowerAnalytic
public import CookMagyar.HuaEstimate

@[expose] public section

open MeasureTheory Filter

namespace SystolicGrowth
namespace CookMagyarCircle

open CookMagyarArcs

/-! # The `L∞`--`L⁸` minor-arc reduction

For at least eight variables, all target dependence is carried by a unit
complex character.  The minor-arc integral is therefore bounded by a
pointwise bound for the cubic von--Mangoldt sum to the power `n - 8`, times
its target-free eighth moment.  This is the exact interface between the
Vaughan/Weyl estimate and Hua's lemma.
-/

private theorem continuous_norm_cubicVonMangoldtExpSum_pow_eight (N : ℕ) :
    Continuous (fun α : ℝ => ‖cubicVonMangoldtExpSum α N‖ ^ 8) := by
  unfold cubicVonMangoldtExpSum addChar
  fun_prop

/-- The exact pointwise factorization used on the minor arcs. -/
theorem norm_cubicIntegrand_eq_pow_sub_eight_mul
    {n N T : ℕ} (hn : 8 ≤ n) (alpha : ℝ) :
    ‖cubicIntegrand n N T alpha‖ =
      ‖cubicVonMangoldtExpSum alpha N‖ ^ (n - 8) *
        ‖cubicVonMangoldtExpSum alpha N‖ ^ 8 := by
  unfold cubicIntegrand
  rw [norm_mul, norm_pow, norm_negAddChar, mul_one, ← pow_add]
  congr 1
  omega

/-- A pointwise minor-arc bound and the eighth moment control the entire
minor-arc contribution.  The conclusion is uniform in the target `T`. -/
theorem norm_cubicMinorArcIntegral_le_sup_pow_mul_eighthMoment
    {n N T Q : ℕ} (hn : 8 ≤ n) {A : ℝ} (hA : 0 ≤ A)
    (hsup : ∀ alpha ∈ minorArcs N Q,
      ‖cubicVonMangoldtExpSum alpha N‖ ≤ A) :
    ‖cubicMinorArcIntegral n N T Q‖ ≤
      A ^ (n - 8) * cubicVonMangoldtEighthMoment N := by
  let f : ℝ → ℝ := fun alpha =>
    ‖cubicIntegrand n N T alpha‖
  let g : ℝ → ℝ := fun alpha =>
    A ^ (n - 8) * ‖cubicVonMangoldtExpSum alpha N‖ ^ 8
  have hf : IntegrableOn f (minorArcs N Q) := by
    exact (cubicIntegrand_integrableOn_minorArcs n N T Q).norm
  have hgIcc : IntegrableOn g (Set.Icc (0 : ℝ) 1) := by
    apply Continuous.integrableOn_Icc
    dsimp only [g]
    exact continuous_const.mul
      (continuous_norm_cubicVonMangoldtExpSum_pow_eight N)
  have hg : IntegrableOn g (minorArcs N Q) :=
    hgIcc.mono_set (minorArcs_subset_Icc N Q)
  have hpoint : ∀ alpha ∈ minorArcs N Q, f alpha ≤ g alpha := by
    intro alpha halpha
    dsimp only [f, g]
    rw [norm_cubicIntegrand_eq_pow_sub_eight_mul hn]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _)
        (hsup alpha halpha) (n - 8))
      (pow_nonneg (norm_nonneg _) 8)
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
    _ = A ^ (n - 8) * cubicVonMangoldtEighthMoment N := by
      dsimp only [g, cubicVonMangoldtEighthMoment]
      rw [integral_const_mul]

/-- A cubic Weyl saving of `N^(3/4)` on the minor arcs, combined with the
fully proved elementary eighth-moment estimate, gives an explicit
target-uniform minor-arc bound. For `n ≥ 33`, its polynomial exponent is
strictly below the main scale even before absorbing the logarithm. -/
theorem norm_cubicMinorArcIntegral_le_threeQuarterWeyl_mul_elementaryMoment
    {n N T Q : ℕ} (hn : 8 ≤ n) {C : ℝ} (hC : 0 ≤ C)
    (hsup : ∀ alpha ∈ minorArcs N Q,
      ‖cubicVonMangoldtExpSum alpha N‖ ≤ C * (N : ℝ) ^ (3 / 4 : ℝ)) :
    ‖cubicMinorArcIntegral n N T Q‖ ≤
      (C * (N : ℝ) ^ (3 / 4 : ℝ)) ^ (n - 8) *
        (2 * Real.log (N + 1 : ℝ) ^ 8 * (N + 1 : ℝ) ^ 7) := by
  have hA : 0 ≤ C * (N : ℝ) ^ (3 / 4 : ℝ) :=
    mul_nonneg hC (Real.rpow_nonneg (by positivity) _)
  calc
    ‖cubicMinorArcIntegral n N T Q‖ ≤
        (C * (N : ℝ) ^ (3 / 4 : ℝ)) ^ (n - 8) *
          cubicVonMangoldtEighthMoment N :=
      norm_cubicMinorArcIntegral_le_sup_pow_mul_eighthMoment hn hA hsup
    _ ≤ (C * (N : ℝ) ^ (3 / 4 : ℝ)) ^ (n - 8) *
          (2 * Real.log (N + 1 : ℝ) ^ 8 * (N + 1 : ℝ) ^ 7) := by
      exact mul_le_mul_of_nonneg_left (cubicVonMangoldtEighthMoment_le N)
        (pow_nonneg hA _)

end CookMagyarCircle
end SystolicGrowth
