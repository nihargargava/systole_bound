module

public import Mathlib.Analysis.Distribution.Sobolev

@[expose] public section

/-!
# Constant-coefficient Sobolev gain directly on complex chart coordinates

The complex plane is used as a two-dimensional real inner-product space.
This avoids an auxiliary conversion of the surface's actual complex charts
to `EuclideanSpace ℝ (Fin 2)`.
-/

open TemperedDistribution
open MeasureTheory
open scoped Laplacian SchwartzMap Real

namespace SystolicGrowth

noncomputable section

theorem complex_besselPotential_two_eq (w : 𝓢'(ℂ, ℂ)) :
    besselPotential ℂ ℂ 2 w =
      w - ((1 / (2 * Real.pi) ^ 2 : ℂ) • (Δ w)) := by
  rw [besselPotential, laplacian_eq_fourierMultiplierCLM]
  simp only [show (2 / 2 : ℝ) = 1 by norm_num, Real.rpow_one]
  simp only [fourierMultiplierCLM_apply]
  have hsymbol :
      (fun x : ℂ => ((1 + ‖x‖ ^ 2 : ℝ) : ℂ)) =
        (fun _ : ℂ => (1 : ℂ)) +
          (fun x : ℂ => ((‖x‖ ^ 2 : ℝ) : ℂ)) := by
    funext x
    simp
  rw [hsymbol, smulLeftCLM_add (by fun_prop) (by fun_prop)]
  simp only [add_apply, smulLeftCLM_const, one_smul]
  rw [FourierTransform.fourierInv_add, FourierTransform.fourierInv_fourier_eq]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  simp only [sub_eq_add_neg, smul_smul]
  simp [Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_mul]

theorem complex_memSobolev_add_two_of_laplacian
    (s : ℝ) (w : 𝓢'(ℂ, ℂ))
    (hw : MemSobolev s 2 w) (hΔ : MemSobolev s 2 (Δ w)) :
    MemSobolev (s + 2) 2 w := by
  have hb : MemSobolev s 2 (besselPotential ℂ ℂ 2 w) := by
    rw [complex_besselPotential_two_eq]
    exact hw.sub (hΔ.smul _)
  simpa only [add_comm] using (memSobolev_besselPotential_iff.mp hb)

theorem complex_memSobolev_two_of_L2_laplacian_L2
    (w : 𝓢'(ℂ, ℂ))
    (hw : ∃ v : Lp ℂ 2 (volume : Measure ℂ), w = v)
    (hΔ : ∃ f : Lp ℂ 2 (volume : Measure ℂ), Δ w = f) :
    MemSobolev 2 2 w := by
  have hw₀ : MemSobolev 0 2 w := memSobolev_zero_iff.mpr hw
  have hΔ₀ : MemSobolev 0 2 (Δ w) := memSobolev_zero_iff.mpr hΔ
  simpa using complex_memSobolev_add_two_of_laplacian 0 w hw₀ hΔ₀

#print axioms complex_besselPotential_two_eq
#print axioms complex_memSobolev_add_two_of_laplacian
#print axioms complex_memSobolev_two_of_L2_laplacian_L2

end

end SystolicGrowth
