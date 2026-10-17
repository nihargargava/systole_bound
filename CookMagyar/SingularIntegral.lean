module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.RealBridge
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

open MeasureTheory
open Filter
open scoped Topology

namespace SystolicGrowth
namespace CookMagyarReal

/-! # The diagonal cubic singular integral

For the highest-degree form `x₁³ + ⋯ + xₙ³`, the oscillatory integral
factors as the `n`th power of a one-dimensional integral.  This file defines
that factor, the truncated singular integral, and the full (improper)
integral, and proves all elementary continuity, integrability-on-compacts,
and norm bounds.  Decay at infinity and identification with the geometric
density are deliberately separate analytic theorems.
-/

/-- The real-frequency additive character `exp(2πiτy)`. -/
noncomputable def realAddChar (tau y : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (tau : ℂ) * (y : ℂ))

@[simp] theorem norm_realAddChar (tau y : ℝ) :
    ‖realAddChar tau y‖ = 1 := by
  unfold realAddChar
  have h :
      2 * Real.pi * Complex.I * (tau : ℂ) * (y : ℂ) =
        ((2 * Real.pi * tau * y : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- One coordinate of the cubic oscillatory integral over the unit interval. -/
noncomputable def oneDimensionalCubicIntegral (tau : ℝ) : ℂ :=
  ∫ x in Set.Icc (0 : ℝ) 1, realAddChar tau (x ^ 3)

theorem oneDimensionalCubicIntegrand_integrable (tau : ℝ) :
    IntegrableOn (fun x : ℝ ↦ realAddChar tau (x ^ 3))
      (Set.Icc (0 : ℝ) 1) := by
  apply Continuous.integrableOn_Icc
  unfold realAddChar
  fun_prop

/-- The one-dimensional oscillatory integral depends continuously on its
frequency. -/
theorem oneDimensionalCubicIntegral_continuous :
    Continuous oneDimensionalCubicIntegral := by
  unfold oneDimensionalCubicIntegral
  apply continuous_parametric_integral_of_continuous
  · unfold realAddChar
    fun_prop
  · exact isCompact_Icc

/-- The trivial unit-interval bound. -/
theorem norm_oneDimensionalCubicIntegral_le_one (tau : ℝ) :
    ‖oneDimensionalCubicIntegral tau‖ ≤ 1 := by
  unfold oneDimensionalCubicIntegral
  calc
    ‖∫ x in Set.Icc (0 : ℝ) 1, realAddChar tau (x ^ 3)‖ ≤
        1 * volume.real (Set.Icc (0 : ℝ) 1) := by
      apply norm_setIntegral_le_of_norm_le_const measure_Icc_lt_top
      intro x _hx
      simp
    _ = 1 := by simp

/-- The Fourier integrand defining the real density for `n` cubic
variables and normalized target `mu`. -/
noncomputable def singularIntegrand (n : ℕ) (mu tau : ℝ) : ℂ :=
  oneDimensionalCubicIntegral tau ^ n * realAddChar (-tau) mu

theorem singularIntegrand_continuous (n : ℕ) (mu : ℝ) :
    Continuous (singularIntegrand n mu) := by
  unfold singularIntegrand
  apply oneDimensionalCubicIntegral_continuous.pow n |>.mul
  unfold realAddChar
  fun_prop

theorem norm_singularIntegrand_le_one (n : ℕ) (mu tau : ℝ) :
    ‖singularIntegrand n mu tau‖ ≤ 1 := by
  unfold singularIntegrand
  rw [norm_mul, norm_pow, norm_realAddChar, mul_one]
  exact pow_le_one₀ (norm_nonneg _) (norm_oneDimensionalCubicIntegral_le_one tau)

/-- The singular integral truncated to `[-Phi, Phi]`. -/
noncomputable def truncatedSingularIntegral (n : ℕ) (mu Phi : ℝ) : ℂ :=
  ∫ tau in Set.Icc (-Phi) Phi, singularIntegrand n mu tau

theorem singularIntegrand_integrableOn_truncation
    (n : ℕ) (mu Phi : ℝ) :
    IntegrableOn (singularIntegrand n mu) (Set.Icc (-Phi) Phi) := by
  apply Continuous.integrableOn_Icc
  exact singularIntegrand_continuous n mu

/-- The full real singular integral.  For the large arities used by
Cook--Magyar, subsequent decay estimates prove that this integral is
integrable and equals the limit of `truncatedSingularIntegral`. -/
noncomputable def singularIntegral (n : ℕ) (mu : ℝ) : ℂ :=
  ∫ tau : ℝ, singularIntegrand n mu tau

/-- Absolute integrability makes the symmetric truncations converge to the
full singular integral.  This records the precise improper-integral
interpretation used by the circle method. -/
theorem truncatedSingularIntegral_tendsto_nat (n : ℕ) (mu : ℝ)
    (hint : Integrable (singularIntegrand n mu)) :
    Tendsto (fun k : ℕ ↦ truncatedSingularIntegral n mu (k : ℝ)) atTop
      (𝓝 (singularIntegral n mu)) := by
  let s : ℕ → Set ℝ := fun k ↦ Set.Icc (-(k : ℝ)) (k : ℝ)
  have hs_meas : ∀ k, MeasurableSet (s k) := fun _ ↦ measurableSet_Icc
  have hs_mono : Monotone s := by
    intro i j hij x hx
    have hijR : (i : ℝ) ≤ j := by exact_mod_cast hij
    exact ⟨(neg_le_neg hijR).trans hx.1, hx.2.trans hijR⟩
  have hs_union : ⋃ k, s k = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨k, hk⟩ := exists_nat_ge |x|
    apply Set.mem_iUnion.mpr
    exact ⟨k, neg_le_of_abs_le hk, le_of_abs_le hk⟩
  have ht := tendsto_setIntegral_of_monotone hs_meas hs_mono hint.integrableOn
  rw [hs_union] at ht
  simpa only [s, truncatedSingularIntegral, singularIntegral,
    Measure.restrict_univ] using ht

end CookMagyarReal
end SystolicGrowth
