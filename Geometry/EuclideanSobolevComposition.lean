module

public import Geometry.DistributionCutoffLaplacian

@[expose] public section

/-!
# Sobolev representatives and nonlinear composition on the Euclidean plane

The first step identifies the inverse Fourier transform of an `L¹` function
with a bounded continuous representative of the corresponding tempered
distribution.  In particular, `H²(ℝ²)` distributions have continuous
representatives by the Fourier integrability estimate in mathlib.
-/

open FourierTransform TemperedDistribution MeasureTheory Real
open scoped SchwartzMap BoundedContinuousFunction

namespace SystolicGrowth

noncomputable section

private theorem euclidean_integral_fourierInv_mul_eq
    (v : Lp ℂ 1 (volume : Measure EuclideanPlane))
    (φ : 𝓢(EuclideanPlane, ℂ)) :
    ∫ x, (𝓕⁻ (v : EuclideanPlane → ℂ) x) * φ x =
      ∫ ξ, (v ξ) * (𝓕⁻ φ ξ) := by
  have hL : Continuous (fun p : EuclideanPlane × EuclideanPlane =>
      (-innerₗ EuclideanPlane) p.1 p.2) := by
    have h : Continuous (fun p : EuclideanPlane × EuclideanPlane =>
        -inner ℝ p.1 p.2) :=
      (continuous_inner : Continuous (fun p : EuclideanPlane × EuclideanPlane =>
        inner ℝ p.1 p.2)).neg
    simpa only [LinearMap.neg_apply, innerₗ_apply_apply] using h
  have hcomm (x y : EuclideanPlane) : inner ℝ x y = inner ℝ y x := by
    have hh := congrArg (fun L : EuclideanPlane →ₗ[ℝ] EuclideanPlane →ₗ[ℝ] ℝ => L y x)
      (flip_innerₗ EuclideanPlane)
    simpa only [LinearMap.flip_apply, innerₗ_apply_apply] using hh
  simpa [SchwartzMap.fourierInv_coe, Real.fourierInv_eq,
    VectorFourier.fourierIntegral, smul_eq_mul,
    hcomm] using
    (VectorFourier.integral_fourierIntegral_smul_eq_flip
      (L := -innerₗ EuclideanPlane) (μ := volume) (ν := volume)
      Real.continuous_fourierChar hL (L1.integrable_coeFn v) φ.integrable)

/-- The inverse Fourier transform of an `L¹` function represents the inverse
Fourier transform of its associated tempered distribution. This is a direct
Fubini calculation on Schwartz test functions. -/
theorem euclidean_fourierInv_L1_integral_representation
    (v : Lp ℂ 1 (volume : Measure EuclideanPlane))
    (φ : 𝓢(EuclideanPlane, ℂ)) :
    𝓕⁻ (v : 𝓢'(EuclideanPlane, ℂ)) φ =
      ∫ x, φ x * (𝓕⁻ (v : EuclideanPlane → ℂ) x) := by
  rw [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply]
  simpa only [smul_eq_mul, mul_comm] using
    (euclidean_integral_fourierInv_mul_eq v φ).symm

/-- Every `H²(ℝ²)` tempered distribution has a bounded continuous
representative, identified by its action on every Schwartz test function. -/
theorem euclidean_memSobolev_two_boundedContinuous_representation
    (w : 𝓢'(EuclideanPlane, ℂ)) (hw : MemSobolev 2 2 w) :
    ∃ c : EuclideanPlane →ᵇ ℂ,
      ∀ φ : 𝓢(EuclideanPlane, ℂ),
        w φ = ∫ x, φ x * c x := by
  obtain ⟨v, hv⟩ := hw.fourier_memL1 (by norm_num)
  let c : EuclideanPlane →ᵇ ℂ :=
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun x : EuclideanPlane => (Lp.fourierTransform v) (-x))
      ((Lp.fourierTransform v).continuous.comp continuous_neg)
      ‖Lp.fourierTransform v‖
      (fun x => (Lp.fourierTransform v).norm_coe_le_norm (-x))
  refine ⟨c, ?_⟩
  intro φ
  have hwv : w = 𝓕⁻ (v : 𝓢'(EuclideanPlane, ℂ)) := by
    rw [← hv, FourierTransform.fourierInv_fourier_eq]
  rw [hwv, euclidean_fourierInv_L1_integral_representation]
  congr 1
  funext x
  simp [c, Lp.fourierTransform_apply, Real.fourierInv_eq_fourier_neg]

#print axioms euclidean_fourierInv_L1_integral_representation
#print axioms euclidean_memSobolev_two_boundedContinuous_representation

end

end SystolicGrowth
