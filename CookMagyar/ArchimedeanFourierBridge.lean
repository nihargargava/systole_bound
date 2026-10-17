module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.RealDensityConvolution
public import CookMagyar.DecayTemp
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-!
# The unconditional Fourier side of the Archimedean density

This module isolates the part of the real-place argument that follows
unconditionally from the explicit cubic decay estimate.  In arity at least
four, the Cook--Magyar singular integral is literally the Fourier transform
of an `L¹` cubic frequency factor.  It is therefore a continuous function of
the normalized target and vanishes at infinity.

The remaining bridge to the positive geometric density is pointwise Fourier
inversion for the concrete convolution density.  `RealDensityConvolution`
already supplies that identification at any continuity point of that density.
-/

open MeasureTheory Filter
open scoped FourierTransform Topology

namespace SystolicGrowth
namespace CookMagyarReal

noncomputable section

/-- The integrable frequency-side factor whose Fourier transform is the
Archimedean singular integral. -/
def cubicFrequencyFactor (n : ℕ) (tau : ℝ) : ℂ :=
  oneDimensionalCubicIntegral tau ^ n

/-- Conjugating the real additive character reverses its frequency. -/
theorem realAddChar_star (tau y : ℝ) :
    star (realAddChar tau y) = realAddChar (-tau) y := by
  unfold realAddChar
  change (starRingEnd ℂ) (Complex.exp _) = Complex.exp _
  rw [← Complex.exp_conj]
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

/-- The one-variable cubic oscillatory integral has the expected conjugate
symmetry. -/
theorem oneDimensionalCubicIntegral_star (tau : ℝ) :
    star (oneDimensionalCubicIntegral tau) = oneDimensionalCubicIntegral (-tau) := by
  unfold oneDimensionalCubicIntegral
  change (starRingEnd ℂ)
      (∫ x : ℝ, realAddChar tau (x ^ 3) ∂volume.restrict (Set.Icc 0 1)) =
    ∫ x : ℝ, realAddChar (-tau) (x ^ 3) ∂volume.restrict (Set.Icc 0 1)
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  unfold realAddChar
  rw [← Complex.exp_conj]
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

/-- The full cubic Fourier integrand is conjugate-symmetric in frequency. -/
theorem singularIntegrand_star (n : ℕ) (mu tau : ℝ) :
    star (singularIntegrand n mu tau) = singularIntegrand n mu (-tau) := by
  unfold singularIntegrand
  change (starRingEnd ℂ) (_ * _) = _
  rw [map_mul, map_pow]
  change star (oneDimensionalCubicIntegral tau) ^ n *
      star (realAddChar (-tau) mu) = _
  rw [oneDimensionalCubicIntegral_star, realAddChar_star]

/-- The Archimedean singular integral is real-valued.  This does not use
Fourier inversion or a positivity hypothesis. -/
theorem singularIntegral_star (n : ℕ) (mu : ℝ) :
    star (singularIntegral n mu) = singularIntegral n mu := by
  unfold singularIntegral
  change (starRingEnd ℂ) (∫ tau : ℝ, singularIntegrand n mu tau) = _
  rw [← integral_conj]
  calc
    ∫ tau : ℝ, (starRingEnd ℂ) (singularIntegrand n mu tau) =
        ∫ tau : ℝ, singularIntegrand n mu (-tau) := by
          apply integral_congr_ae
          filter_upwards with tau
          exact singularIntegrand_star n mu tau
    _ = ∫ tau : ℝ, singularIntegrand n mu tau :=
      integral_neg_eq_self _ volume

theorem singularIntegral_im_eq_zero (n : ℕ) (mu : ℝ) :
    (singularIntegral n mu).im = 0 :=
  Complex.conj_eq_iff_im.mp (singularIntegral_star n mu)

theorem singularIntegral_eq_ofReal_re (n : ℕ) (mu : ℝ) :
    singularIntegral n mu = ((singularIntegral n mu).re : ℂ) :=
  (Complex.conj_eq_iff_re.mp (singularIntegral_star n mu)).symm

theorem cubicFrequencyFactor_integrable {n : ℕ} (hn : 4 ≤ n) :
    Integrable (cubicFrequencyFactor n) := by
  change Integrable (fun tau : ℝ => oneDimensionalCubicIntegral tau ^ n)
  exact cubicIntegral_pow_integrable_of_singularIntegrand
    (singularIntegrand_integrable hn 0)

/-- Absolute convergence turns the singular integral into the ordinary real
Fourier transform of the cubic frequency factor. -/
theorem singularIntegral_eq_fourier_cubicFrequencyFactor {n : ℕ}
    (mu : ℝ) :
    singularIntegral n mu = 𝓕 (cubicFrequencyFactor n) mu := by
  unfold singularIntegral cubicFrequencyFactor
  rw [Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards with tau
  unfold singularIntegrand
  have hchar : realAddChar (-tau) mu =
      Complex.exp (((-2 * Real.pi * (tau * mu) : ℝ) : ℂ) * Complex.I) := by
    unfold realAddChar
    congr 1
    push_cast
    ring
  rw [hchar]
  simp only [Real.inner_apply]
  rw [mul_comm (oneDimensionalCubicIntegral tau ^ n)]
  rfl

/-- In every arity in which the decay estimate is integrable, the singular
integral varies continuously with the normalized target. -/
theorem singularIntegral_continuous {n : ℕ} (hn : 4 ≤ n) :
    Continuous (singularIntegral n) := by
  have hident : singularIntegral n = 𝓕 (cubicFrequencyFactor n) :=
    funext singularIntegral_eq_fourier_cubicFrequencyFactor
  rw [hident]
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ (cubicFrequencyFactor_integrable hn)

theorem singularIntegral_re_continuous {n : ℕ} (hn : 4 ≤ n) :
    Continuous (fun mu : ℝ => (singularIntegral n mu).re) :=
  Complex.continuous_re.comp (singularIntegral_continuous hn)

/-- If the normalized target tends to a limit while the truncation radius
tends to infinity, the truncated singular integrals converge to the full
integral at that limiting target. The dominating function is the absolute
value of the limiting-target integrand; the additive-character factor has
norm one for every target. -/
theorem truncatedSingularIntegral_tendsto_target {n : ℕ} (hn : 4 ≤ n)
    {mu : ℕ → ℝ} {muLim : ℝ} (hmu : Tendsto mu atTop (𝓝 muLim)) :
    Tendsto (fun Q : ℕ =>
      truncatedSingularIntegral n (mu Q) (Q : ℝ)) atTop
        (𝓝 (singularIntegral n muLim)) := by
  let F : ℕ → ℝ → ℂ := fun Q tau =>
    Set.indicator (Set.Icc (-(Q : ℝ)) (Q : ℝ))
      (fun tau => singularIntegrand n (mu Q) tau) tau
  let B : ℝ → ℝ := fun tau => ‖singularIntegrand n muLim tau‖
  have hB : Integrable B := by
    exact (singularIntegrand_integrable hn muLim).norm
  have hFmeas : ∀ Q, AEStronglyMeasurable (F Q) volume := by
    intro Q
    dsimp [F]
    exact (singularIntegrand_continuous n (mu Q)).aestronglyMeasurable.indicator
      measurableSet_Icc
  have hnorm (Q : ℕ) (tau : ℝ) :
      ‖singularIntegrand n (mu Q) tau‖ =
        ‖singularIntegrand n muLim tau‖ := by
    simp [singularIntegrand]
  have hbound : ∀ Q, ∀ᵐ tau ∂volume, ‖F Q tau‖ ≤ B tau := by
    intro Q
    filter_upwards [] with tau
    by_cases hτ : tau ∈ Set.Icc (-(Q : ℝ)) (Q : ℝ)
    · simp [F, B, hτ, hnorm]
    · simp [F, B, hτ]
  have hpoint (tau : ℝ) :
      Tendsto (fun Q : ℕ => F Q tau) atTop
        (𝓝 (singularIntegrand n muLim tau)) := by
    have hcont : Continuous (fun x : ℝ => singularIntegrand n x tau) := by
      unfold singularIntegrand realAddChar
      fun_prop
    have htarget : Tendsto (fun Q : ℕ => singularIntegrand n (mu Q) tau)
        atTop (𝓝 (singularIntegrand n muLim tau)) :=
      hcont.continuousAt.tendsto.comp hmu
    obtain ⟨q, hq⟩ := exists_nat_gt |tau|
    have hmem : ∀ᶠ Q : ℕ in atTop,
        tau ∈ Set.Icc (-(Q : ℝ)) (Q : ℝ) := by
      have hqR : |tau| < (q : ℝ) := by exact_mod_cast hq
      filter_upwards [eventually_ge_atTop q] with Q hQ
      have hQR : (q : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
      rw [Set.mem_Icc]
      have hτabs : |tau| ≤ (Q : ℝ) := le_trans hqR.le hQR
      exact abs_le.mp hτabs
    have heq : (fun Q : ℕ => F Q tau) =ᶠ[atTop]
        fun Q => singularIntegrand n (mu Q) tau := by
      filter_upwards [hmem] with Q hQ
      simp [F, hQ]
    exact htarget.congr' heq.symm
  have hDCT := MeasureTheory.tendsto_integral_of_dominated_convergence
    B hFmeas hB hbound
    (Filter.Eventually.of_forall hpoint)
  have hIntegralEq : (fun Q : ℕ => ∫ tau, F Q tau) =
      fun Q => truncatedSingularIntegral n (mu Q) (Q : ℝ) := by
    funext Q
    change (∫ tau, Set.indicator (Set.Icc (-(Q : ℝ)) (Q : ℝ))
        (fun tau => singularIntegrand n (mu Q) tau) tau) = _
    rw [integral_indicator measurableSet_Icc]
    rfl
  rw [hIntegralEq] at hDCT
  simpa [singularIntegral] using hDCT

/-- The error in truncating the Archimedean integral is bounded by the
absolute-integrand tail. The right-hand side is independent of the target,
since the additive-character factor has norm one. -/
theorem truncatedSingularIntegral_error_le {n : ℕ} (hn : 4 ≤ n)
    (mu Q : ℝ) :
    ‖truncatedSingularIntegral n mu Q - singularIntegral n mu‖ ≤
      ∫ tau in (Set.Icc (-Q) Q)ᶜ, ‖singularIntegrand n mu tau‖ := by
  let I := Set.Icc (-Q) Q
  have hI : MeasurableSet I := measurableSet_Icc
  have hint := singularIntegrand_integrable hn mu
  have hcompl : (∫ tau in Iᶜ, singularIntegrand n mu tau) =
      singularIntegral n mu - truncatedSingularIntegral n mu Q := by
    simpa [I, singularIntegral, truncatedSingularIntegral] using
      (setIntegral_compl hI hint)
  have hindicator :
      (∫ tau, Iᶜ.indicator (singularIntegrand n mu) tau) =
        ∫ tau in Iᶜ, singularIntegrand n mu tau :=
    integral_indicator hI.compl
  calc
    _ = ‖-(∫ tau in Iᶜ, singularIntegrand n mu tau)‖ := by
      congr 1
      rw [hcompl]
      simp
    _ = ‖∫ tau in Iᶜ, singularIntegrand n mu tau‖ := norm_neg _
    _ = ‖∫ tau, Iᶜ.indicator (singularIntegrand n mu) tau‖ := by
      rw [hindicator]
    _ ≤ ∫ tau, ‖Iᶜ.indicator (singularIntegrand n mu) tau‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ tau, Iᶜ.indicator (fun tau => ‖singularIntegrand n mu tau‖) tau := by
      congr 1
      ext tau
      by_cases htau : tau ∈ Iᶜ <;> simp [htau]
    _ = ∫ tau in Iᶜ, ‖singularIntegrand n mu tau‖ := integral_indicator hI.compl

/-- Symmetric truncation converges uniformly in the normalized target. This
stronger form is suited to Cook--Magyar's target window, where the target may
vary with the circle-method scale instead of converging to a point. -/
theorem truncatedSingularIntegral_tendsto_uniform {n : ℕ} (hn : 4 ≤ n)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Q : ℕ in atTop, ∀ mu : ℝ,
      ‖truncatedSingularIntegral n mu (Q : ℝ) - singularIntegral n mu‖ < ε := by
  let B : ℝ → ℝ := fun tau => ‖singularIntegrand n 0 tau‖
  have hB : Integrable B := by
    exact (singularIntegrand_integrable hn 0).norm
  have hBcont : Continuous B := by
    exact (singularIntegrand_continuous n 0).norm
  let F : ℕ → ℝ → ℝ := fun Q tau =>
    Set.indicator (Set.Icc (-(Q : ℝ)) (Q : ℝ))ᶜ B tau
  have hFmeas : ∀ Q, AEStronglyMeasurable (F Q) volume := by
    intro Q
    dsimp [F]
    exact hBcont.aestronglyMeasurable.indicator measurableSet_Icc.compl
  have hbound : ∀ Q, ∀ᵐ tau ∂volume, ‖F Q tau‖ ≤ B tau := by
    intro Q
    filter_upwards [] with tau
    by_cases htau : tau ∈ (Set.Icc (-(Q : ℝ)) (Q : ℝ))ᶜ
    · simp [F, B, htau]
    · simp [F, B, htau]
  have hpoint (tau : ℝ) : Tendsto (fun Q : ℕ => F Q tau) atTop (𝓝 0) := by
    obtain ⟨q, hq⟩ := exists_nat_gt |tau|
    have hqR : |tau| < (q : ℝ) := by exact_mod_cast hq
    have heq : (fun Q : ℕ => F Q tau) =ᶠ[atTop] fun _ => (0 : ℝ) := by
      filter_upwards [eventually_ge_atTop q] with Q hQ
      have hQR : (q : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
      have hmem : tau ∈ Set.Icc (-(Q : ℝ)) (Q : ℝ) := by
        rw [Set.mem_Icc]
        exact abs_le.mp (le_trans hqR.le hQR)
      simp [F, hmem]
    exact tendsto_const_nhds.congr' heq.symm
  have hDCT := MeasureTheory.tendsto_integral_of_dominated_convergence
    B hFmeas hB hbound (Filter.Eventually.of_forall hpoint)
  have htail : Tendsto (fun Q : ℕ =>
      ∫ tau in (Set.Icc (-(Q : ℝ)) (Q : ℝ))ᶜ, B tau) atTop (𝓝 0) := by
    have heq : (fun Q : ℕ => ∫ tau, F Q tau) = fun Q : ℕ =>
        ∫ tau in (Set.Icc (-(Q : ℝ)) (Q : ℝ))ᶜ, B tau := by
      funext Q
      exact integral_indicator (measurableSet_Icc.compl)
    rw [heq] at hDCT
    simpa using hDCT
  filter_upwards [Metric.tendsto_nhds.1 htail ε hε] with Q hQ mu
  have hnorm : ∀ tau, ‖singularIntegrand n mu tau‖ = B tau := by
    intro tau
    simp [B, singularIntegrand]
  have herr := truncatedSingularIntegral_error_le hn mu (Q : ℝ)
  rw [show (fun tau => ‖singularIntegrand n mu tau‖) = B from funext hnorm] at herr
  have htail_nonneg : 0 ≤ ∫ tau in (Set.Icc (-(Q : ℝ)) (Q : ℝ))ᶜ, B tau :=
    integral_nonneg (fun _ => norm_nonneg _)
  have hQ' : (∫ tau in (Set.Icc (-(Q : ℝ)) (Q : ℝ))ᶜ, B tau) < ε := by
    simpa [Real.dist_eq, abs_of_nonneg htail_nonneg] using hQ
  exact lt_of_le_of_lt herr hQ'

/-- Zero is the limiting target when the integer target remains fixed as the
circle-method scale grows. -/
theorem truncatedSingularIntegral_tendsto_target_zero {n : ℕ} (hn : 4 ≤ n)
    {mu : ℕ → ℝ} (hmu : Tendsto mu atTop (𝓝 0)) :
    Tendsto (fun Q : ℕ =>
      truncatedSingularIntegral n (mu Q) (Q : ℝ)) atTop
        (𝓝 (singularIntegral n 0)) :=
  truncatedSingularIntegral_tendsto_target hn hmu

/-- The real singular integral is uniformly continuous on the compact
normalized Cook--Magyar target window.  In particular, a later positivity
proof may be checked on a finite cover once it supplies a quantitative
modulus or pointwise lower estimates. -/
theorem singularIntegral_re_uniformContinuousOn_normalizedTargetWindow
    {n : ℕ} (hn : 4 ≤ n) :
    UniformContinuousOn (fun mu : ℝ => (singularIntegral n mu).re)
      {mu | NormalizedTargetWindow n mu} := by
  change UniformContinuousOn (fun mu : ℝ => (singularIntegral n mu).re)
    (Set.Icc ((n : ℝ) - 1 / 3) ((n : ℝ) - 1 / 5))
  exact isCompact_Icc.uniformContinuousOn_of_continuous
    (singularIntegral_re_continuous hn).continuousOn

/-- The Fourier-side formula also gives the Riemann--Lebesgue decay of the
singular integral as the normalized target escapes every compact interval. -/
theorem singularIntegral_tendsto_zero_cocompact (n : ℕ) :
    Tendsto (singularIntegral n) (cocompact ℝ) (𝓝 0) := by
  have hident : singularIntegral n = 𝓕 (cubicFrequencyFactor n) :=
    funext singularIntegral_eq_fourier_cubicFrequencyFactor
  rw [hident]
  exact Real.zero_at_infty_fourier (cubicFrequencyFactor n)

/-- In the arities relevant to Cook--Magyar, decay already discharges the
integrability clause in `HasCubicRealFourierInversion`.  Thus the remaining
real-place task is exactly the pointwise identification of the Fourier
integral with the explicit positive geometric density. -/
theorem hasCubicRealFourierInversion_iff_density_identification {n : ℕ}
    (hn : 4 ≤ n) :
    HasCubicRealFourierInversion n ↔
      ∀ mu, NormalizedTargetWindow n mu →
        singularIntegral n mu = (geometricCubicDensityReal n mu : ℂ) := by
  constructor
  · intro h mu hmu
    exact (h mu hmu).2
  · intro h mu hmu
    exact ⟨singularIntegrand_integrable hn mu, h mu hmu⟩

end

end CookMagyarReal
end SystolicGrowth
