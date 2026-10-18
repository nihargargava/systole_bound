module

public import Geometry.EuclideanSobolevContinuousRepresentative
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

@[expose] public section

/-!
# Dominated convergence in `L²` for weak chain rules

This is the analytic limit argument for products of bounded nonlinear
coefficients with a fixed weak derivative.
-/

open MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace SystolicGrowth

noncomputable section

/-- Pointwise-a.e. convergence to zero, dominated in norm by one `L²`
function, implies convergence to zero in `L²` seminorm. -/
theorem tendsto_eLpNorm_two_zero_of_ae_tendsto_dominated
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (F : ℕ → α → ℂ) (G : α → ℂ)
    (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    (hG : MemLp G 2 μ)
    (hdom : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ ‖G x‖)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (F n) 2 μ) atTop (𝓝 0) := by
  let B : α → ℝ≥0∞ := fun x => ‖G x‖ₑ ^ (2 : ℝ)
  let H : ℕ → α → ℝ≥0∞ := fun n x => ‖F n x‖ₑ ^ (2 : ℝ)
  have hmeas (n : ℕ) : AEMeasurable (H n) μ := by
    exact (hF n).aemeasurable.enorm.pow_const _
  have hbd (n : ℕ) : H n ≤ᵐ[μ] B := by
    filter_upwards [hdom n] with x hx
    exact ENNReal.rpow_le_rpow (enorm_le_iff_norm_le.mpr hx) (by norm_num)
  have hfin : ∫⁻ x, B x ∂μ ≠ ∞ := by
    change (∫⁻ x, ‖G x‖ₑ ^ (2 : ℝ) ∂μ) ≠ ∞
    have hp := eLpNorm_nnreal_pow_eq_lintegral
      (p := (2 : ℝ≥0)) (f := G) (μ := μ) (by norm_num) hG.aestronglyMeasurable
    have hp' : (∫⁻ x, ‖G x‖ₑ ^ (2 : ℝ) ∂μ) =
        eLpNorm G 2 μ ^ (2 : ℝ) := by
      simpa using hp.symm
    rw [hp']
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hG.eLpNorm_lt_top.ne
  have hpoint : ∀ᵐ x ∂μ, Tendsto (fun n => H n x) atTop (𝓝 0) := by
    filter_upwards [hlim] with x hx
    have h₁ : Tendsto (fun n => ‖F n x‖ₑ) atTop (𝓝 0) := by
      simpa using hx.enorm
    have hpow : Continuous (fun t : ℝ≥0∞ => t ^ (2 : ℝ)) :=
      ENNReal.continuous_rpow_const
    simpa [H, Function.comp_def, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
      using (hpow.tendsto 0).comp h₁
  have hInt : Tendsto (fun n => ∫⁻ x, H n x ∂μ) atTop (𝓝 0) := by
    simpa using tendsto_lintegral_of_dominated_convergence' B hmeas hbd hfin hpoint
  have hNorm (n : ℕ) : eLpNorm (F n) 2 μ = (∫⁻ x, H n x ∂μ) ^ (1 / 2 : ℝ) := by
    simpa [H] using eLpNorm_eq_lintegral_rpow_enorm_toReal
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) (hF n)
  have hpow : Continuous (fun t : ℝ≥0∞ => t ^ (1 / 2 : ℝ)) :=
    ENNReal.continuous_rpow_const
  simpa only [hNorm, Function.comp_def, ENNReal.zero_rpow_of_pos
    (by norm_num : (0 : ℝ) < 1 / 2)] using
    (hpow.tendsto 0).comp hInt

/-- A.e.-convergent, uniformly bounded coefficients converge strongly when
multiplied by any fixed `L²` function. This is the product-limit step in the
first weak chain rule. -/
theorem tendsto_eLpNorm_two_bounded_coeff_mul
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (a : ℕ → α → ℂ) (b g : α → ℂ) (C : ℝ)
    (ha : ∀ n, AEStronglyMeasurable (a n) μ)
    (hb : AEStronglyMeasurable b μ)
    (hg : MemLp g 2 μ)
    (hC0 : 0 ≤ C)
    (hC : ∀ n, ∀ᵐ x ∂μ, ‖a n x - b x‖ ≤ C)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => a n x) atTop (𝓝 (b x))) :
    Tendsto (fun n => eLpNorm (fun x => (a n x - b x) * g x) 2 μ)
      atTop (𝓝 0) := by
  have hG : MemLp (fun x => (C : ℂ) * g x) 2 μ := hg.const_mul _
  apply tendsto_eLpNorm_two_zero_of_ae_tendsto_dominated μ
    (fun n x => (a n x - b x) * g x) (fun x => (C : ℂ) * g x)
  · intro n
    exact ((ha n).sub hb).mul hg.aestronglyMeasurable
  · exact hG
  · intro n
    filter_upwards [hC n] with x hx
    simpa [norm_mul, Complex.norm_real, Real.norm_of_nonneg hC0] using
      mul_le_mul_of_nonneg_right hx (norm_nonneg (g x))
  · filter_upwards [hlim] with x hx
    have hsub : Tendsto (fun n => a n x - b x) atTop (𝓝 0) := by
      simpa using hx.sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => b x) atTop (𝓝 (b x)))
    simpa using hsub.mul_const (g x)

#print axioms tendsto_eLpNorm_two_zero_of_ae_tendsto_dominated
#print axioms tendsto_eLpNorm_two_bounded_coeff_mul

end

end SystolicGrowth
