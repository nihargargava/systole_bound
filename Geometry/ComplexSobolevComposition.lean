module

public import Geometry.ComplexSobolevEllipticRegularity
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

@[expose] public section

/-!
# Sobolev representatives and nonlinear composition on the complex plane

The first step identifies the inverse Fourier transform of an `L¹` function
with a bounded continuous representative of the corresponding tempered
distribution.  In particular, `H²(ℂ)` distributions have continuous
representatives by the Fourier integrability estimate in mathlib.
-/

open FourierTransform TemperedDistribution MeasureTheory Real
open scoped SchwartzMap BoundedContinuousFunction

namespace SystolicGrowth

noncomputable section

private theorem complex_integral_fourierInv_mul_eq
    (v : Lp ℂ 1 (volume : Measure ℂ))
    (φ : 𝓢(ℂ, ℂ)) :
    ∫ x, (𝓕⁻ (v : ℂ → ℂ) x) * φ x =
      ∫ ξ, (v ξ) * (𝓕⁻ φ ξ) := by
  have hL : Continuous (fun p : ℂ × ℂ =>
      (-innerₗ ℂ) p.1 p.2) := by
    have h : Continuous (fun p : ℂ × ℂ =>
        -inner ℝ p.1 p.2) :=
      (continuous_inner : Continuous (fun p : ℂ × ℂ =>
        inner ℝ p.1 p.2)).neg
    simpa only [LinearMap.neg_apply, innerₗ_apply_apply] using h
  have hcomm (x y : ℂ) : inner ℝ x y = inner ℝ y x := by
    have hh := congrArg (fun L : ℂ →ₗ[ℝ] ℂ →ₗ[ℝ] ℝ => L y x)
      (flip_innerₗ ℂ)
    simpa only [LinearMap.flip_apply, innerₗ_apply_apply] using hh
  simpa [SchwartzMap.fourierInv_coe, Real.fourierInv_eq,
    VectorFourier.fourierIntegral, smul_eq_mul,
    hcomm] using
    (VectorFourier.integral_fourierIntegral_smul_eq_flip
      (L := -innerₗ ℂ) (μ := volume) (ν := volume)
      Real.continuous_fourierChar hL (L1.integrable_coeFn v) φ.integrable)

/-- The inverse Fourier transform of an `L¹` function represents the inverse
Fourier transform of its associated tempered distribution. This is a direct
Fubini calculation on Schwartz test functions. -/
theorem complex_fourierInv_L1_integral_representation
    (v : Lp ℂ 1 (volume : Measure ℂ))
    (φ : 𝓢(ℂ, ℂ)) :
    𝓕⁻ (v : 𝓢'(ℂ, ℂ)) φ =
      ∫ x, φ x * (𝓕⁻ (v : ℂ → ℂ) x) := by
  rw [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply]
  simpa only [smul_eq_mul, mul_comm] using
    (complex_integral_fourierInv_mul_eq v φ).symm

/-- Every `H²(ℂ)` tempered distribution has a bounded continuous
representative, identified by its action on every Schwartz test function. -/
theorem complex_memSobolev_two_boundedContinuous_representation
    (w : 𝓢'(ℂ, ℂ)) (hw : MemSobolev 2 2 w) :
    ∃ c : ℂ →ᵇ ℂ,
      ∀ φ : 𝓢(ℂ, ℂ),
        w φ = ∫ x, φ x * c x := by
  obtain ⟨v, hv⟩ := hw.fourier_memL1 (by
    rw [Complex.finrank_real_complex]
    norm_num)
  let c : ℂ →ᵇ ℂ :=
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun x : ℂ => (Lp.fourierTransform v) (-x))
      ((Lp.fourierTransform v).continuous.comp continuous_neg)
      ‖Lp.fourierTransform v‖
      (fun x => (Lp.fourierTransform v).norm_coe_le_norm (-x))
  refine ⟨c, ?_⟩
  intro φ
  have hwv : w = 𝓕⁻ (v : 𝓢'(ℂ, ℂ)) := by
    rw [← hv, FourierTransform.fourierInv_fourier_eq]
  rw [hwv, complex_fourierInv_L1_integral_representation]
  congr 1
  funext x
  simp [c, Lp.fourierTransform_apply, Real.fourierInv_eq_fourier_neg]

#print axioms complex_fourierInv_L1_integral_representation
#print axioms complex_memSobolev_two_boundedContinuous_representation

end

end SystolicGrowth

