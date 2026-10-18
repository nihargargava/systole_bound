module

public import Mathlib.Analysis.Distribution.Sobolev

@[expose] public section

/-!
# Constant-coefficient Sobolev gain on the Euclidean plane

The Fourier convention in mathlib sends the distributional Laplacian to the
multiplier `-(2 * π)^2 ‖ξ‖²`.  Consequently its order-two Bessel potential is
`1 - (2 * π)^(-2) Δ`, rather than `1 - Δ`.
-/

open TemperedDistribution
open MeasureTheory
open scoped Laplacian SchwartzMap Real

namespace SystolicGrowth

noncomputable section

abbrev EuclideanPlane := EuclideanSpace ℝ (Fin 2)

/-- The order-two Bessel potential is the distributional operator
`1 - (2π)⁻² Δ`, with mathlib's Fourier normalization. -/
theorem euclidean_besselPotential_two_eq
    (w : 𝓢'(EuclideanPlane, ℂ)) :
    besselPotential EuclideanPlane ℂ 2 w =
      w - ((1 / (2 * Real.pi) ^ 2 : ℂ) • (Δ w)) := by
  rw [besselPotential, laplacian_eq_fourierMultiplierCLM]
  simp only [show (2 / 2 : ℝ) = 1 by norm_num, Real.rpow_one]
  simp only [fourierMultiplierCLM_apply]
  have hsymbol :
      (fun x : EuclideanPlane => ((1 + ‖x‖ ^ 2 : ℝ) : ℂ)) =
        (fun _ : EuclideanPlane => (1 : ℂ)) +
          (fun x : EuclideanPlane => ((‖x‖ ^ 2 : ℝ) : ℂ)) := by
    funext x
    simp
  rw [hsymbol, smulLeftCLM_add (by fun_prop) (by fun_prop)]
  simp only [add_apply, smulLeftCLM_const, one_smul]
  rw [FourierTransform.fourierInv_add, FourierTransform.fourierInv_fourier_eq]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  simp only [sub_eq_add_neg, smul_smul]
  simp [Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_mul]

/-- If a tempered distribution and its distributional Laplacian both lie in
`Hˢ(ℝ²)`, then the distribution lies in `Hˢ⁺²(ℝ²)`. -/
theorem euclidean_memSobolev_add_two_of_laplacian
    (s : ℝ) (w : 𝓢'(EuclideanPlane, ℂ))
    (hw : MemSobolev s 2 w) (hΔ : MemSobolev s 2 (Δ w)) :
    MemSobolev (s + 2) 2 w := by
  have hb : MemSobolev s 2 (besselPotential EuclideanPlane ℂ 2 w) := by
    rw [euclidean_besselPotential_two_eq]
    exact hw.sub (hΔ.smul _)
  simpa only [add_comm] using (memSobolev_besselPotential_iff.mp hb)

/-- A distributional solution to `(1 - Δ)w = F`, with both `w` and `F` in
`Hˢ(ℝ²)`, gains two Sobolev orders. No classical derivatives are assumed. -/
theorem euclidean_memSobolev_add_two_of_resolvent
    (s : ℝ) (w : 𝓢'(EuclideanPlane, ℂ))
    (hw : MemSobolev s 2 w)
    (hres : MemSobolev s 2 (w - Δ w)) :
    MemSobolev (s + 2) 2 w := by
  have hΔ : MemSobolev s 2 (Δ w) := by
    convert hw.sub hres using 1
    abel
  exact euclidean_memSobolev_add_two_of_laplacian s w hw hΔ

/-- If `w` and its weak distributional Laplacian are represented by genuine
`L²` functions, then `w ∈ H²(ℝ²)`. -/
theorem euclidean_memSobolev_two_of_L2_laplacian_L2
    (w : 𝓢'(EuclideanPlane, ℂ))
    (hw : ∃ v : Lp ℂ 2 (volume : Measure EuclideanPlane), w = v)
    (hΔ : ∃ f : Lp ℂ 2 (volume : Measure EuclideanPlane), Δ w = f) :
    MemSobolev 2 2 w := by
  have hw₀ : MemSobolev 0 2 w := memSobolev_zero_iff.mpr hw
  have hΔ₀ : MemSobolev 0 2 (Δ w) := memSobolev_zero_iff.mpr hΔ
  simpa using euclidean_memSobolev_add_two_of_laplacian 0 w hw₀ hΔ₀

#print axioms euclidean_besselPotential_two_eq
#print axioms euclidean_memSobolev_add_two_of_laplacian
#print axioms euclidean_memSobolev_add_two_of_resolvent
#print axioms euclidean_memSobolev_two_of_L2_laplacian_L2

end

end SystolicGrowth
