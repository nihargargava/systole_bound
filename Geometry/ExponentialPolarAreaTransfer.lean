module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.ExponentialGlobalGauss
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Exponential.CInftyGlobal
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

@[expose] public section

/-!
# Actual exponential polar determinant-area transfer

The change-of-variables Jacobian is identified with the determinant of
the genuine pulled-back metric. This transports native chart determinant
area to actual exponential polar sectors, without a supplied area formula.
-/

open Set Bundle Manifold Riemannian MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SystolicGrowth

variable {M : Type*} [MetricSpace M] [ChartedSpace ℂ M]
  [IsManifold (modelWithCornersSelf ℝ ℂ) ∞ M]
  [SigmaCompactSpace M] [CompleteSpace M]

local instance exponentialPolarAreaComplexFinrankNonzero : NeZero (Module.finrank ℝ ℂ) :=
  ⟨by rw [Complex.finrank_real_complex]; norm_num⟩

/-- **Math.** The actual coordinate Gram matrix in the real `1,I` frame. -/
def nativeComplexChartMetricGram
    (g : RiemannianMetric (modelWithCornersSelf ℝ ℂ) M) (ζ : M) (y : ℂ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => chartMetricInner g ζ y
    (if i = 0 then 1 else Complex.I) (if j = 0 then 1 else Complex.I)

/-- **Math.** Native chart area computed from the actual metric determinant. -/
def nativeComplexChartMetricArea
    (g : RiemannianMetric (modelWithCornersSelf ℝ ℂ) M) (ζ : M) : Measure ℂ :=
  volume.withDensity (fun y => ENNReal.ofReal
    (Real.sqrt (nativeComplexChartMetricGram g ζ y).det))

/-- **Math.** Literal global exponential polar chart with complex coordinates
whose real and imaginary parts are radius and angle. -/
def globalExponentialComplexPolarChart
    (g : RiemannianMetric (modelWithCornersSelf ℝ ℂ) M) (hg : g.IsRiemannianDist)
    (p ζ : M) (e : Fin 2 → ℂ) (z : ℂ) : ℂ :=
  globalExponentialPolarChart g hg p ζ e (z.re, z.im)

omit [SigmaCompactSpace M] [CompleteSpace M] in
private theorem chartMetricInner_complex_coordinates
    (g : RiemannianMetric (modelWithCornersSelf ℝ ℂ) M) (ζ : M)
    (y v w : ℂ) :
    chartMetricInner g ζ y v w =
      v.re * w.re * chartMetricInner g ζ y 1 1 +
      v.re * w.im * chartMetricInner g ζ y 1 Complex.I +
      v.im * w.re * chartMetricInner g ζ y Complex.I 1 +
      v.im * w.im * chartMetricInner g ζ y Complex.I Complex.I := by
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im v).symm
  have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by
    simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im w).symm
  conv_lhs => rw [hv, hw]
  simp only [chartMetricInner_add_left, chartMetricInner_add_right,
    chartMetricInner_smul_left, chartMetricInner_smul_right]
  ring

private theorem complex_real_det (D : ℂ →L[ℝ] ℂ) :
    LinearMap.det D.toLinearMap =
      (D 1).re * (D Complex.I).im - (D Complex.I).re * (D 1).im := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply]

omit [SigmaCompactSpace M] [CompleteSpace M] in
/-- **Math.** The determinant of the actual pulled-back coordinate metric
equals the squared true Jacobian times the original metric determinant. -/
theorem nativeComplexChartMetricGram_pullback_det
    (g : RiemannianMetric (modelWithCornersSelf ℝ ℂ) M) (ζ : M)
    (y : ℂ) (D : ℂ →L[ℝ] ℂ) :
    Matrix.det (fun i j : Fin 2 => chartMetricInner g ζ y
      (D (if i = 0 then 1 else Complex.I))
      (D (if j = 0 then 1 else Complex.I))) =
      (LinearMap.det D.toLinearMap) ^ 2 * (nativeComplexChartMetricGram g ζ y).det := by
  simp only [Matrix.det_fin_two, nativeComplexChartMetricGram]
  change chartMetricInner g ζ y (D 1) (D 1) *
      chartMetricInner g ζ y (D Complex.I) (D Complex.I) -
      chartMetricInner g ζ y (D 1) (D Complex.I) *
      chartMetricInner g ζ y (D Complex.I) (D 1) =
    (LinearMap.det D.toLinearMap) ^ 2 *
      (chartMetricInner g ζ y 1 1 * chartMetricInner g ζ y Complex.I Complex.I -
        chartMetricInner g ζ y 1 Complex.I * chartMetricInner g ζ y Complex.I 1)
  rw [complex_real_det]
  rw [chartMetricInner_complex_coordinates g ζ y (D 1) (D 1),
    chartMetricInner_complex_coordinates g ζ y (D Complex.I) (D Complex.I),
    chartMetricInner_complex_coordinates g ζ y (D 1) (D Complex.I),
    chartMetricInner_complex_coordinates g ζ y (D Complex.I) (D 1)]
  ring

omit [SigmaCompactSpace M] [CompleteSpace M] in
/-- **Math.** The metric area density transforms by the absolute true
Jacobian; this follows from the metric pullback, not from an area premise. -/
theorem nativeComplexChartMetricGram_pullback_areaDensity
    (g : RiemannianMetric (modelWithCornersSelf ℝ ℂ) M) (ζ : M)
    (y : ℂ) (D : ℂ →L[ℝ] ℂ) :
    Real.sqrt (Matrix.det (fun i j : Fin 2 => chartMetricInner g ζ y
      (D (if i = 0 then 1 else Complex.I))
      (D (if j = 0 then 1 else Complex.I)))) =
      |LinearMap.det D.toLinearMap| * Real.sqrt (nativeComplexChartMetricGram g ζ y).det := by
  rw [nativeComplexChartMetricGram_pullback_det, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq_eq_abs]

/-- **Math.** At any point whose exponential image lies in the terminal
chart, the actual complex polar differential has the actual radial and
angular exponential differential images as its `1,I` columns. -/
theorem globalExponentialComplexPolarChart_fderiv_columns
    (g : RiemannianMetric (modelWithCornersSelf ℝ ℂ) M) (hg : g.IsRiemannianDist)
    (p ζ : M) (e : Fin 2 → ℂ) (z : ℂ)
    (hsrc : Exponential.expMapGlobal g hg p (z.re • exponentialPolarUnit e z.im) ∈
      (chartAt ℂ ζ).source) :
    DifferentiableAt ℝ (globalExponentialComplexPolarChart g hg p ζ e) z ∧
      fderiv ℝ (globalExponentialComplexPolarChart g hg p ζ e) z 1 =
        globalExponentialPolarFrame g hg p ζ e z.re z.im 0 ∧
      fderiv ℝ (globalExponentialComplexPolarChart g hg p ζ e) z Complex.I =
        globalExponentialPolarFrame g hg p ζ e z.re z.im 1 := by
  let f := globalExponentialChartMap g hg p ζ
  let U := exponentialPolarUnit e z.im
  let N := exponentialPolarNormal e z.im
  have hf : DifferentiableAt ℝ f (z.re • U) :=
    ((contMDiffAt_extChartAt' hsrc).comp (z.re • U)
      (Exponential.contMDiff_expMapGlobal g hg p (z.re • U))).contDiffAt.differentiableAt
        (by norm_num)
  have hN := (exponentialPolarUnit_hasDerivAt e z.im).hasFDerivAt.comp z
    Complex.imCLM.hasFDerivAt
  have hS := (Complex.reCLM.hasFDerivAt (x := z)).smul hN
  have hF := hf.hasFDerivAt.comp z hS
  change HasFDerivAt (globalExponentialComplexPolarChart g hg p ζ e) _ z at hF
  refine ⟨hF.differentiableAt, ?_, ?_⟩
  · rw [hF.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, Complex.reCLM_apply, Complex.imCLM_apply,
      Complex.one_re, Complex.one_im, zero_smul, smul_zero, one_smul, zero_add,
      Function.comp_apply]
    rfl
  · rw [hF.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, Complex.reCLM_apply, Complex.imCLM_apply,
      Complex.I_re, Complex.I_im, zero_smul, one_smul, add_zero,
      Function.comp_apply]
    rfl

/-- **Math.** Native determinant area of any genuine injective exponential
polar sector is the integral of its actual pulled-back metric determinant.
The source and injectivity premises concern only the selected chart sector. -/
theorem nativeComplexChartMetricArea_image_globalExponentialPolar
    (g : RiemannianMetric (modelWithCornersSelf ℝ ℂ) M) (hg : g.IsRiemannianDist)
    (p ζ : M) (e : Fin 2 → ℂ) {s : Set ℂ} (hs : MeasurableSet s)
    (hsrc : ∀ z ∈ s,
      Exponential.expMapGlobal g hg p (z.re • exponentialPolarUnit e z.im) ∈
        (chartAt ℂ ζ).source)
    (hinj : InjOn (globalExponentialComplexPolarChart g hg p ζ e) s) :
    nativeComplexChartMetricArea g ζ
        (globalExponentialComplexPolarChart g hg p ζ e '' s) =
      ∫⁻ z in s, ENNReal.ofReal
        (Real.sqrt (globalExponentialPolarGram g hg p ζ e z.re z.im).det) := by
  let F := globalExponentialComplexPolarChart g hg p ζ e
  have hcols (z : ℂ) (hz : z ∈ s) :=
    globalExponentialComplexPolarChart_fderiv_columns g hg p ζ e z (hsrc z hz)
  have hFD : ∀ z ∈ s, HasFDerivWithinAt F (fderiv ℝ F z) s z :=
    fun z hz => (hcols z hz).1.hasFDerivAt.hasFDerivWithinAt
  rw [nativeComplexChartMetricArea,
    withDensity_apply _ (measurable_image_of_fderivWithin hs hFD hinj),
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs hFD hinj]
  apply setLIntegral_congr_fun hs
  intro z hz
  change ENNReal.ofReal |LinearMap.det (fderiv ℝ F z).toLinearMap| *
      ENNReal.ofReal (Real.sqrt (nativeComplexChartMetricGram g ζ (F z)).det) =
    ENNReal.ofReal (Real.sqrt (globalExponentialPolarGram g hg p ζ e z.re z.im).det)
  have hcol0 : fderiv ℝ F z 1 = globalExponentialPolarFrame g hg p ζ e z.re z.im 0 :=
    (hcols z hz).2.1
  have hcol1 : fderiv ℝ F z Complex.I =
      globalExponentialPolarFrame g hg p ζ e z.re z.im 1 := (hcols z hz).2.2
  have hcol (i : Fin 2) : fderiv ℝ F z (if i = 0 then 1 else Complex.I) =
      globalExponentialPolarFrame g hg p ζ e z.re z.im i := by
    fin_cases i
    · exact hcol0
    · exact hcol1
  have hGram : globalExponentialPolarGram g hg p ζ e z.re z.im =
      (fun i j : Fin 2 => chartMetricInner g ζ (F z)
        (fderiv ℝ F z (if i = 0 then 1 else Complex.I))
        (fderiv ℝ F z (if j = 0 then 1 else Complex.I))) := by
    ext i j
    change chartMetricInner g ζ (F z)
      (globalExponentialPolarFrame g hg p ζ e z.re z.im i)
      (globalExponentialPolarFrame g hg p ζ e z.re z.im j) = _
    rw [hcol i, hcol j]
  rw [hGram, nativeComplexChartMetricGram_pullback_areaDensity,
    ENNReal.ofReal_mul (abs_nonneg _)]

#print axioms nativeComplexChartMetricGram_pullback_areaDensity
#print axioms globalExponentialComplexPolarChart_fderiv_columns
#print axioms nativeComplexChartMetricArea_image_globalExponentialPolar

end SystolicGrowth

end
