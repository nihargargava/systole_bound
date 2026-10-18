module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.SingularIntegral
public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

@[expose] public section

open MeasureTheory Filter
open scoped Interval FourierTransform RealInnerProductSpace Topology

namespace SystolicGrowth
namespace CookMagyarReal

/-! # The cubic oscillatory integral as a Fourier transform

The substitution `y = x³` sends Lebesgue measure on `[0,1]` to the
density `(1/3)y⁻²ᐟ³`.  This file proves that change of variables exactly,
packages the density as an `L¹` function on the real line, and identifies
`oneDimensionalCubicIntegral` with its Fourier transform.  Mathlib's
Riemann--Lebesgue lemma then gives qualitative decay at infinity.
-/

/-- The density of the pushforward of unit-interval Lebesgue measure under
the cube map, before restricting its support to `(0,1]`. -/
noncomputable def cubicPushforwardDensity (y : ℝ) : ℝ :=
  (1 / 3 : ℝ) * y ^ (-(2 : ℝ) / 3)

/-- The cubic Jacobian cancels the pushforward density away from zero. -/
theorem cubicDerivative_mul_pushforwardDensity {x : ℝ} (hx : 0 < x) :
    (3 * x ^ 2 : ℝ) * cubicPushforwardDensity (x ^ 3) = 1 := by
  unfold cubicPushforwardDensity
  have hcube : x ^ (3 : ℕ) = Real.rpow x (3 : ℝ) :=
    (Real.rpow_natCast x 3).symm
  rw [hcube]
  change 3 * x ^ 2 * (1 / 3 * ((x ^ (3 : ℝ)) ^ (-(2 : ℝ) / 3))) = 1
  rw [← Real.rpow_mul hx.le]
  norm_num
  field_simp

/-- The density is integrable over the unit interval. -/
theorem cubicPushforwardDensity_intervalIntegrable :
    IntervalIntegrable cubicPushforwardDensity volume 0 1 := by
  unfold cubicPushforwardDensity
  exact (intervalIntegral.intervalIntegrable_rpow'
    (by norm_num : (-1 : ℝ) < -(2 : ℝ) / 3)).const_mul (1 / 3)

/-- The density multiplied by the positive-frequency additive character. -/
noncomputable def cubicDensityFourierIntegrand (tau y : ℝ) : ℂ :=
  cubicPushforwardDensity y • realAddChar tau y

/-- The complex-valued, compactly supported `L¹` density used by mathlib's
Fourier transform. -/
noncomputable def unitCubicDensity (y : ℝ) : ℂ :=
  Set.indicator (Set.Ioc (0 : ℝ) 1)
    (fun y ↦ (cubicPushforwardDensity y : ℂ)) y

theorem unitCubicDensity_integrable : Integrable unitCubicDensity := by
  have hIcc : IntegrableOn cubicPushforwardDensity (Set.Icc (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp
      cubicPushforwardDensity_intervalIntegrable
  have hIoc : IntegrableOn cubicPushforwardDensity (Set.Ioc (0 : ℝ) 1) :=
    hIcc.mono_set Set.Ioc_subset_Icc_self
  have hcomplex : IntegrableOn (fun y ↦ (cubicPushforwardDensity y : ℂ))
      (Set.Ioc (0 : ℝ) 1) := hIoc.ofReal
  unfold unitCubicDensity
  rw [integrable_indicator_iff measurableSet_Ioc]
  exact hcomplex

/-- Exact change of variables `y = x³` for the oscillatory integral. -/
theorem cubicDensity_changeVariables_interval (tau : ℝ) :
    (∫ x in (0 : ℝ)..1, realAddChar tau (x ^ 3)) =
      ∫ y in (0 : ℝ)..1, cubicDensityFourierIntegrand tau y := by
  have hsub := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (a := (0 : ℝ)) (b := 1)
    (f := fun x : ℝ ↦ x ^ 3) (f' := fun x : ℝ ↦ 3 * x ^ 2)
    (g := cubicDensityFourierIntegrand tau)
    (by fun_prop)
    (by
      intro x _hx
      simpa only [Nat.cast_ofNat] using (hasDerivAt_pow 3 x))
    (by intro x _hx; positivity)
  norm_num only [zero_pow, one_pow] at hsub
  rw [← hsub]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [] with x hx
  have hxpos : 0 < x := by norm_num at hx ⊢; exact hx.1
  change realAddChar tau (x ^ 3) =
    (3 * x ^ 2) • (cubicPushforwardDensity (x ^ 3) • realAddChar tau (x ^ 3))
  rw [← mul_smul, cubicDerivative_mul_pushforwardDensity hxpos]
  simp

theorem oneDimensionalCubicIntegral_eq_densityIntegral (tau : ℝ) :
    oneDimensionalCubicIntegral tau =
      ∫ y in Set.Icc (0 : ℝ) 1, cubicDensityFourierIntegrand tau y := by
  unfold oneDimensionalCubicIntegral
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    cubicDensity_changeVariables_interval,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc]

/-- The one-dimensional cubic factor is the standard Fourier transform of
`unitCubicDensity`, evaluated at the negative frequency because
`realAddChar` uses the positive exponential convention. -/
theorem oneDimensionalCubicIntegral_eq_fourier (tau : ℝ) :
    oneDimensionalCubicIntegral tau = 𝓕 unitCubicDensity (-tau) := by
  rw [oneDimensionalCubicIntegral_eq_densityIntegral, Real.fourier_eq']
  rw [integral_Icc_eq_integral_Ioc, ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : y ∈ Set.Ioc (0 : ℝ) 1
  · simp only [Set.indicator_of_mem hy, unitCubicDensity]
    unfold cubicDensityFourierIntegrand realAddChar
    simp only [Real.inner_apply, neg_mul]
    simp only [Complex.real_smul, smul_eq_mul]
    have hexp :
        2 * (Real.pi : ℂ) * Complex.I * (tau : ℂ) * (y : ℂ) =
          ((-(2 * Real.pi * (y * -tau)) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hexp, mul_comm]
  · simp [unitCubicDensity, hy]

/-- Qualitative decay of the cubic oscillatory integral, obtained from the
Riemann--Lebesgue lemma for the explicit `L¹` density. -/
theorem oneDimensionalCubicIntegral_tendsto_zero_cocompact :
    Tendsto oneDimensionalCubicIntegral (cocompact ℝ) (𝓝 0) := by
  have h := (Real.tendsto_integral_exp_smul_cocompact unitCubicDensity).comp
    (Homeomorph.neg ℝ).toCocompactMap.cocompact_tendsto'
  have hfourier :
      Tendsto (fun tau : ℝ ↦ 𝓕 unitCubicDensity (-tau))
        (cocompact ℝ) (𝓝 0) := by
    simpa [Real.fourier_eq, Function.comp_def, Real.inner_apply,
      Homeomorph.toCocompactMap, mul_comm] using h
  exact hfourier.congr' <| Eventually.of_forall fun tau ↦
    (oneDimensionalCubicIntegral_eq_fourier tau).symm

/-- Every positive-arity singular integrand tends to zero at real infinity.
This is qualitative decay; absolute integrability still needs a quantitative
rate. -/
theorem singularIntegrand_tendsto_zero_cocompact {n : ℕ} (hn : 0 < n)
    (mu : ℝ) :
    Tendsto (singularIntegrand n mu) (cocompact ℝ) (𝓝 0) := by
  have hp : Tendsto (fun tau ↦ oneDimensionalCubicIntegral tau ^ n)
      (cocompact ℝ) (𝓝 0) := by
    simpa [zero_pow hn.ne'] using
      oneDimensionalCubicIntegral_tendsto_zero_cocompact.pow n
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [singularIntegrand, norm_mul, norm_realAddChar, mul_one,
    norm_zero] using hp.norm

end CookMagyarReal
end SystolicGrowth
