module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.RealDensity
public import CookMagyar.RealFourier
public import CookMagyar.Vendor.SumProduct.ConvolutionDensity
public import CookMagyar.DecayTemp

@[expose] public section

/-!
# Convolution model for the cubic real density

This file applies the vendored convolution-density identity to the explicit
one-dimensional cubic pushforward density from `CookMagyar.RealFourier`.
It constructs the finite measure for one cube, its iterated convolution law,
and an explicit density for every positive arity.  The resulting Fourier
transform is exactly the power of `oneDimensionalCubicIntegral` occurring in
the Cook--Magyar singular integrand.
-/

open MeasureTheory
open scoped ENNReal FourierTransform

namespace SystolicGrowth
namespace CookMagyarReal

noncomputable section

/-- The real-valued version of `unitCubicDensity`. -/
def unitCubicDensityReal (y : ℝ) : ℝ :=
  Set.indicator (Set.Ioc (0 : ℝ) 1) cubicPushforwardDensity y

theorem unitCubicDensityReal_measurable : Measurable unitCubicDensityReal := by
  unfold unitCubicDensityReal cubicPushforwardDensity
  exact (by fun_prop : Measurable (fun y : ℝ => (1 / 3 : ℝ) * y ^ (-(2 : ℝ) / 3))).indicator
    measurableSet_Ioc

theorem unitCubicDensityReal_nonneg (y : ℝ) : 0 ≤ unitCubicDensityReal y := by
  by_cases hy : y ∈ Set.Ioc (0 : ℝ) 1
  · rw [unitCubicDensityReal, Set.indicator_of_mem hy]
    unfold cubicPushforwardDensity
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg hy.1.le _)
  · simp [unitCubicDensityReal, hy]

@[simp] theorem unitCubicDensityReal_ofReal (y : ℝ) :
    (unitCubicDensityReal y : ℂ) = unitCubicDensity y := by
  by_cases hy : y ∈ Set.Ioc (0 : ℝ) 1 <;>
    simp [unitCubicDensityReal, unitCubicDensity, hy]

theorem unitCubicDensityReal_integrable : Integrable unitCubicDensityReal := by
  have h := unitCubicDensity_integrable.re
  refine h.congr (ae_of_all volume fun y => ?_)
  change (unitCubicDensity y).re = unitCubicDensityReal y
  simpa only [Complex.ofReal_re] using
    congrArg Complex.re (unitCubicDensityReal_ofReal y).symm

/-- The extended nonnegative density used by `Measure.withDensity`. -/
def unitCubicDensityENNReal (y : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (unitCubicDensityReal y)

theorem unitCubicDensityENNReal_measurable : Measurable unitCubicDensityENNReal :=
  ENNReal.measurable_ofReal.comp unitCubicDensityReal_measurable

theorem unitCubicDensityENNReal_lt_top (y : ℝ) :
    unitCubicDensityENNReal y < ∞ := by
  simp [unitCubicDensityENNReal]

@[simp] theorem unitCubicDensityENNReal_toReal (y : ℝ) :
    (unitCubicDensityENNReal y).toReal = unitCubicDensityReal y := by
  rw [unitCubicDensityENNReal, ENNReal.toReal_ofReal (unitCubicDensityReal_nonneg y)]

@[simp] theorem unitCubicDensityENNReal_toReal_ofReal (y : ℝ) :
    ((unitCubicDensityENNReal y).toReal : ℂ) = unitCubicDensity y := by
  rw [unitCubicDensityENNReal_toReal, unitCubicDensityReal_ofReal]

/-- The distribution of one variable `x³` for `x` uniformly distributed on
the unit interval, represented by its explicit density. -/
def unitCubicMeasure : Measure ℝ :=
  volume.withDensity unitCubicDensityENNReal

noncomputable instance instIsFiniteMeasureUnitCubicMeasure :
    IsFiniteMeasure unitCubicMeasure := by
  unfold unitCubicMeasure unitCubicDensityENNReal
  exact isFiniteMeasure_withDensity_ofReal
    unitCubicDensityReal_integrable.hasFiniteIntegral

/-- The characteristic function of the one-cube law, in the repository's
`2π` frequency convention. -/
theorem charFun_unitCubicMeasure_two_pi_mul (tau : ℝ) :
    charFun unitCubicMeasure (2 * Real.pi * tau) =
      oneDimensionalCubicIntegral tau := by
  letI : IsFiniteMeasure (volume.withDensity unitCubicDensityENNReal) := by
    change IsFiniteMeasure unitCubicMeasure
    infer_instance
  have h :=
    Vendor.SumProduct.fourier_toReal_withDensity_eq_charFun_scaled
      unitCubicDensityENNReal_measurable
      (ae_of_all volume unitCubicDensityENNReal_lt_top) (-tau)
  change
    𝓕 (fun x : ℝ => ((unitCubicDensityENNReal x).toReal : ℂ)) (-tau) =
      charFun unitCubicMeasure ((-2 * Real.pi) * -tau) at h
  rw [show (fun x : ℝ => ((unitCubicDensityENNReal x).toReal : ℂ)) =
      unitCubicDensity from funext unitCubicDensityENNReal_toReal_ofReal] at h
  rw [← oneDimensionalCubicIntegral_eq_fourier tau] at h
  rw [show (-2 * Real.pi) * (-tau) = 2 * Real.pi * tau by ring] at h
  exact h.symm

/-- The law of a sum of `n` independent one-cube variables, constructed by
iterated convolution. -/
def cubicSumMeasure : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | n + 1 => cubicSumMeasure n ∗ unitCubicMeasure

noncomputable instance instIsFiniteMeasureCubicSumMeasure (n : ℕ) :
    IsFiniteMeasure (cubicSumMeasure n) := by
  induction n with
  | zero =>
      simp only [cubicSumMeasure]
      infer_instance
  | succ n ih =>
      simp only [cubicSumMeasure]
      letI : IsFiniteMeasure (cubicSumMeasure n) := ih
      infer_instance

theorem charFun_cubicSumMeasure_two_pi_mul (n : ℕ) (tau : ℝ) :
    charFun (cubicSumMeasure n) (2 * Real.pi * tau) =
      oneDimensionalCubicIntegral tau ^ n := by
  induction n with
  | zero => simp [cubicSumMeasure]
  | succ n ih =>
      rw [cubicSumMeasure, charFun_conv, ih,
        charFun_unitCubicMeasure_two_pi_mul, pow_succ]

/-- The explicit density obtained by adjoining one more cubic variable to
the `n`-variable convolution law. Thus this is the density for `n + 1`
variables. -/
def cubicSumDensity (n : ℕ) (z : ℝ) : ℝ≥0∞ :=
  ∫⁻ x : ℝ, unitCubicDensityENNReal (z - x) ∂cubicSumMeasure n

theorem cubicSumDensity_measurable (n : ℕ) :
    Measurable (cubicSumDensity n) := by
  let F : ℝ → ℝ → ℝ≥0∞ := fun z x => unitCubicDensityENNReal (z - x)
  have hF : Measurable (Function.uncurry F) :=
    unitCubicDensityENNReal_measurable.comp (measurable_fst.sub measurable_snd)
  exact hF.lintegral_prod_right

/-- Every positive-arity cubic sum law has the explicit convolution density
`cubicSumDensity`. -/
theorem cubicSumMeasure_succ_eq_withDensity (n : ℕ) :
    cubicSumMeasure (n + 1) = volume.withDensity (cubicSumDensity n) := by
  rw [cubicSumMeasure]
  exact Vendor.SumProduct.conv_withDensity_right_eq
    (cubicSumMeasure n) unitCubicDensityENNReal_measurable

theorem cubicSumDensity_lintegral_ne_top (n : ℕ) :
    (∫⁻ x : ℝ, cubicSumDensity n x) ≠ ∞ := by
  have hfin :
      (volume.withDensity (cubicSumDensity n)) Set.univ ≠ ∞ := by
    rw [← cubicSumMeasure_succ_eq_withDensity n]
    exact measure_ne_top _ _
  rw [withDensity_apply _ MeasurableSet.univ] at hfin
  simpa using hfin

theorem cubicSumDensity_ae_lt_top (n : ℕ) :
    ∀ᵐ x : ℝ ∂volume, cubicSumDensity n x < ∞ :=
  ae_lt_top (cubicSumDensity_measurable n)
    (cubicSumDensity_lintegral_ne_top n)

theorem cubicSumDensity_toReal_integrable (n : ℕ) :
    Integrable (fun x : ℝ => (cubicSumDensity n x).toReal) :=
  integrable_toReal_of_lintegral_ne_top
    (cubicSumDensity_measurable n).aemeasurable
    (cubicSumDensity_lintegral_ne_top n)

theorem cubicSumDensity_toReal_complex_integrable (n : ℕ) :
    Integrable (fun x : ℝ => ((cubicSumDensity n x).toReal : ℂ)) :=
  (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).integrable_comp
    (cubicSumDensity_toReal_integrable n)

/-- The Fourier transform of the explicit `(n+1)`-cube density is the
corresponding power of the one-dimensional cubic integral. -/
theorem fourier_cubicSumDensity_eq_cubicIntegral_pow (n : ℕ) (w : ℝ) :
    𝓕 (fun x : ℝ => ((cubicSumDensity n x).toReal : ℂ)) w =
      oneDimensionalCubicIntegral (-w) ^ (n + 1) := by
  letI : IsFiniteMeasure (volume.withDensity (cubicSumDensity n)) := by
    rw [← cubicSumMeasure_succ_eq_withDensity n]
    infer_instance
  have h :=
    Vendor.SumProduct.fourier_toReal_withDensity_eq_charFun_scaled
      (cubicSumDensity_measurable n) (cubicSumDensity_ae_lt_top n) w
  rw [← cubicSumMeasure_succ_eq_withDensity n] at h
  rw [show (-2 * Real.pi) * w = 2 * Real.pi * (-w) by ring,
    charFun_cubicSumMeasure_two_pi_mul] at h
  exact h

/-- The unit-modulus target character can be removed from an integrability
question. This connects the exact Cook--Magyar integrand hypothesis to the
Fourier transform of `cubicSumDensity`. -/
theorem cubicIntegral_pow_integrable_of_singularIntegrand
    {k : ℕ} {mu : ℝ} (h : Integrable (singularIntegrand k mu)) :
    Integrable (fun tau : ℝ => oneDimensionalCubicIntegral tau ^ k) := by
  let g : ℝ → ℂ := fun tau => oneDimensionalCubicIntegral tau ^ k
  have hg_meas : AEStronglyMeasurable g :=
    oneDimensionalCubicIntegral_continuous.pow k |>.aestronglyMeasurable
  apply (integrable_norm_iff hg_meas).mp
  refine h.norm.congr (ae_of_all volume fun tau => ?_)
  simp only [g, singularIntegrand, norm_mul, norm_pow, norm_realAddChar, mul_one]

/-- Pointwise Fourier inversion identifies the explicit convolution density
with the Cook--Magyar singular integral. The two hypotheses are precisely the
remaining analytic regularity obligations: absolute convergence of the
singular integrand and continuity of the convolution density at the target.
No identification with `geometricCubicDensityReal` is assumed here. -/
theorem cubicSumDensity_eq_singularIntegral
    (n : ℕ) (mu : ℝ)
    (hint : Integrable (singularIntegrand (n + 1) mu))
    (hcont : ContinuousAt
      (fun x : ℝ => ((cubicSumDensity n x).toReal : ℂ)) mu) :
    ((cubicSumDensity n mu).toReal : ℂ) = singularIntegral (n + 1) mu := by
  let f : ℝ → ℂ := fun x => ((cubicSumDensity n x).toReal : ℂ)
  let g : ℝ → ℂ := fun tau => oneDimensionalCubicIntegral tau ^ (n + 1)
  have hg : Integrable g := by
    simpa [g] using
      cubicIntegral_pow_integrable_of_singularIntegrand hint
  have hgneg : Integrable (fun w : ℝ => g (-w)) := by
    have hcomp :=
      (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_of_integrable hg
    simpa [Function.comp_def] using hcomp
  have hFint : Integrable (𝓕 f) := by
    refine hgneg.congr (ae_of_all volume fun w => ?_)
    exact (fourier_cubicSumDensity_eq_cubicIntegral_pow n w).symm
  have hinv : 𝓕⁻ (𝓕 f) mu = f mu :=
    (cubicSumDensity_toReal_complex_integrable n).fourierInv_fourier_eq
      hFint hcont
  rw [Real.fourierInv_eq'] at hinv
  let F : ℝ → ℂ := fun w =>
    Complex.exp (((2 * Real.pi * (w * mu) : ℝ) : ℂ) * Complex.I) * g (-w)
  have hinvF : ∫ w : ℝ, F w = f mu := by
    rw [← hinv]
    apply integral_congr_ae
    filter_upwards with w
    rw [fourier_cubicSumDensity_eq_cubicIntegral_pow]
    simp only [g, F, Real.inner_apply, smul_eq_mul]
  have hneg := Measure.integral_comp_mul_left F (-1 : ℝ)
  have hF_neg : (∫ w : ℝ, F w) = ∫ tau : ℝ, F (-tau) := by
    have habs : |((-1 : ℝ)⁻¹)| = 1 := by norm_num
    simpa [habs, smul_eq_mul] using hneg.symm
  have hpoint : ∀ tau : ℝ,
      F (-tau) = singularIntegrand (n + 1) mu tau := by
    intro tau
    unfold F g singularIntegrand realAddChar
    simp only [neg_neg, neg_mul]
    rw [mul_comm]
    congr 1
    push_cast
    ring_nf
  unfold singularIntegral
  change f mu = ∫ tau : ℝ, singularIntegrand (n + 1) mu tau
  rw [← hinvF, hF_neg]
  apply integral_congr_ae
  exact ae_of_all volume hpoint

/-- For four or more cubic variables, the elementary oscillatory decay makes
the Fourier integrand absolutely integrable. Thus continuity of the explicit
convolution density is the only remaining hypothesis in its pointwise
identification with the singular integral. -/
theorem cubicSumDensity_eq_singularIntegral_of_continuous
    (n : ℕ) (mu : ℝ) (hn : 3 ≤ n)
    (hcont : ContinuousAt
      (fun x : ℝ => ((cubicSumDensity n x).toReal : ℂ)) mu) :
    ((cubicSumDensity n mu).toReal : ℂ) = singularIntegral (n + 1) mu := by
  apply cubicSumDensity_eq_singularIntegral n mu
  · exact singularIntegrand_integrable (by omega) mu
  · exact hcont

end

end CookMagyarReal
end SystolicGrowth
