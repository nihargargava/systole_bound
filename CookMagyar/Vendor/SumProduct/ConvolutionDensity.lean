module

/-
Copyright (c) 2026 Formal Frontier Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.MeasureTheory.Measure.IntegralCharFun

@[expose] public section

/-!
# Vendored convolution densities and Fourier inversion

This file contains a small, project-local adaptation of the density machinery
from `SumProduct/CubeSectionCore.lean` in `mathlib-initiative/sum_product`,
commit `80e4127a67742659d521466204c6d2d7e0ca2b3f`:

https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionCore.lean

Only the general convolution-with-density identity and the general Fourier
inversion argument behind the upstream cube-law specialization are retained.
The declarations live in a vendored namespace so that their provenance and
future upstream replacement remain explicit.
-/

open MeasureTheory
open scoped ENNReal MeasureTheory FourierTransform

namespace SystolicGrowth
namespace Vendor
namespace SumProduct

noncomputable section

/-- Convolution on the right by a measure with density again has an explicit
density. This is adapted from `SumProduct.conv_withDensity_right_eq`. -/
theorem conv_withDensity_right_eq
    (μ : Measure ℝ) [SFinite μ] {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    μ ∗ volume.withDensity f =
      volume.withDensity (fun z : ℝ => ∫⁻ x : ℝ, f (z - x) ∂μ) := by
  refine Measure.ext_of_lintegral _ ?_
  intro φ hφ
  rw [Measure.lintegral_conv hφ]
  rw [lintegral_withDensity_eq_lintegral_mul]
  · have hinner : ∀ x : ℝ,
        (∫⁻ y : ℝ, φ (x + y) ∂volume.withDensity f) =
          ∫⁻ y : ℝ, f y * φ (x + y) := by
      intro x
      rw [lintegral_withDensity_eq_lintegral_mul]
      · rfl
      · exact hf
      · exact hφ.comp (by fun_prop)
    simp_rw [hinner]
    have htranslate : ∀ x : ℝ,
        (∫⁻ y : ℝ, f y * φ (x + y)) =
          ∫⁻ a : ℝ, f (a - x) * φ a := by
      intro x
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (MeasureTheory.lintegral_add_left_eq_self
          (μ := (volume : Measure ℝ)) (f := fun a : ℝ => f (a - x) * φ a) x)
    simp_rw [htranslate]
    rw [lintegral_lintegral_swap]
    · have hfactor : ∀ y : ℝ,
          (∫⁻ x : ℝ, f (y - x) * φ y ∂μ) =
            (∫⁻ x : ℝ, f (y - x) ∂μ) * φ y := by
        intro y
        rw [lintegral_mul_const'' (φ y)]
        exact (hf.comp (by fun_prop)).aemeasurable
      simp_rw [hfactor]
      rfl
    · fun_prop
  · fun_prop
  · exact hφ

/-- The Fourier transform of the real density of `volume.withDensity d` is
its characteristic function at the frequency `-2πw`. This is the generic
form of the Fourier-identification step used in the upstream cube-law proof. -/
theorem fourier_toReal_withDensity_eq_charFun_scaled
    {d : ℝ → ℝ≥0∞} [IsFiniteMeasure (volume.withDensity d)]
    (hd : Measurable d) (hd_top : ∀ᵐ x ∂volume, d x < ∞) (w : ℝ) :
    𝓕 (fun x : ℝ => ((d x).toReal : ℂ)) w =
      charFun (volume.withDensity d) ((-2 * Real.pi) * w) := by
  rw [Real.fourier_eq]
  rw [charFun_apply_real]
  rw [integral_withDensity_eq_integral_toReal_smul hd hd_top]
  simp [Real.fourierChar_apply, Circle.smul_def, smul_eq_mul, mul_comm,
    mul_left_comm, mul_assoc]

/-- Fourier inversion at zero for an explicit finite density whose
characteristic function is integrable. This abstracts the analytic core of
`cubeSumLawSuccDensity_zero_eq_inv_two_pi_integral_re_charFun`. -/
theorem withDensity_toReal_zero_eq_inv_two_pi_integral_re_charFun
    {d : ℝ → ℝ≥0∞} [IsFiniteMeasure (volume.withDensity d)]
    (hd : Measurable d) (hd_top : ∀ᵐ x ∂volume, d x < ∞)
    (hd_int : Integrable (fun x : ℝ => ((d x).toReal : ℂ)))
    (hchar_int : Integrable (fun t : ℝ => charFun (volume.withDensity d) t))
    (hd_cont : ContinuousAt (fun x : ℝ => ((d x).toReal : ℂ)) 0) :
    (d 0).toReal =
      (2 * Real.pi)⁻¹ *
        ∫ t : ℝ, (charFun (volume.withDensity d) t).re := by
  let f : ℝ → ℂ := fun x => ((d x).toReal : ℂ)
  have hscale_ne : (-2 * Real.pi) ≠ (0 : ℝ) := by
    nlinarith [Real.pi_pos]
  have hchar_scaled :
      Integrable (fun w : ℝ =>
        charFun (volume.withDensity d) ((-2 * Real.pi) * w)) :=
    hchar_int.comp_mul_left' hscale_ne
  have hFint : Integrable (𝓕 f) := by
    refine hchar_scaled.congr ?_
    filter_upwards with w
    exact (fourier_toReal_withDensity_eq_charFun_scaled hd hd_top w).symm
  have hinv : 𝓕⁻ (𝓕 f) 0 = f 0 :=
    hd_int.fourierInv_fourier_eq hFint hd_cont
  have hinvInt : ∫ w : ℝ, 𝓕 f w = f 0 := by
    simpa [Real.fourierInv_eq', f] using hinv
  have hinvRe : (d 0).toReal = ∫ w : ℝ, (𝓕 f w).re := by
    have h := congrArg Complex.re hinvInt
    have h_re : ∫ w : ℝ, (𝓕 f w).re = (∫ w : ℝ, 𝓕 f w).re := by
      simpa [RCLike.re_eq_complex_re] using
        (integral_re (μ := volume) (f := fun w : ℝ => 𝓕 f w) hFint)
    rw [← h_re] at h
    simpa [f] using h.symm
  have hfour_re :
      (∫ w : ℝ, (𝓕 f w).re) =
        ∫ w : ℝ,
          (charFun (volume.withDensity d) ((-2 * Real.pi) * w)).re := by
    apply integral_congr_ae
    filter_upwards with w
    rw [fourier_toReal_withDensity_eq_charFun_scaled hd hd_top]
  have hscale :
      (∫ w : ℝ,
          (charFun (volume.withDensity d) ((-2 * Real.pi) * w)).re) =
        (2 * Real.pi)⁻¹ *
          ∫ t : ℝ, (charFun (volume.withDensity d) t).re := by
    have h := Measure.integral_comp_mul_left
      (fun t : ℝ => (charFun (volume.withDensity d) t).re) (-2 * Real.pi)
    have habs : |((-2 * Real.pi)⁻¹ : ℝ)| = (2 * Real.pi)⁻¹ := by
      rw [abs_inv]
      have hneg : (-2 * Real.pi : ℝ) < 0 := by
        nlinarith [Real.pi_pos]
      rw [abs_of_neg hneg]
      ring
    simpa [habs, smul_eq_mul, abs_of_pos Real.pi_pos, mul_comm,
      mul_left_comm, mul_assoc] using h
  calc
    (d 0).toReal = ∫ w : ℝ, (𝓕 f w).re := hinvRe
    _ = ∫ w : ℝ,
        (charFun (volume.withDensity d) ((-2 * Real.pi) * w)).re := hfour_re
    _ = (2 * Real.pi)⁻¹ *
        ∫ t : ℝ, (charFun (volume.withDensity d) t).re := hscale

end

end SumProduct
end Vendor
end SystolicGrowth
