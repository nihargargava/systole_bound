module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingPolarOrientation
public import Geometry.HyperbolicBallExactVolume
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section

/-!
# Actual area density in native polar and signed collar coordinates

The original polar differential and Poincaré tangent form determine its
Jacobian. Change of variables then gives the actual native area density,
without a supplied metric-area identification.
-/

open Set MeasureTheory UpperHalfPlane
open scoped UpperHalfPlane ComplexConjugate ENNReal NNReal MatrixGroups Pointwise

namespace SystolicGrowth

private theorem complex_area_det (D : ℂ →L[ℝ] ℂ) :
    LinearMap.det D.toLinearMap =
      (D 1).re * (D Complex.I).im - (D Complex.I).re * (D 1).im := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply]

private theorem complex_area_frame_det (D : ℂ →L[ℝ] ℂ) (A : ℂ) (s u v : ℝ)
    (hD : ∀ z : ℂ, D z = A * ((u * z.re : ℝ) + Complex.I * (s * v * z.im : ℝ))) :
    LinearMap.det D.toLinearMap = u * v * ‖A‖ ^ 2 * s := by
  rw [complex_area_det, hD, hD, Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
  ring

/-- The actual polar differential has its genuine radial vector as the
coefficient of the orthogonal hyperbolic radial/angular frame. -/
theorem gluingPolarLiftFDeriv_radial_frame (o : ℍ) (p v : ℝ × ℝ) :
    gluingPolarLiftFDeriv o p v = gluingPolarLiftFDeriv o p (1, 0) *
      ((v.1 : ℂ) + Complex.I * (Real.sinh p.1 : ℂ) * (v.2 : ℂ)) := by
  have hC (w : ℂ) :
      gluingCenteredCayleyFDeriv o (gluingPolarDiskLift p) w =
        gluingCenteredCayleyDeriv o (gluingPolarDiskLift p) * w := by
    simp [gluingCenteredCayleyFDeriv, smul_eq_mul, mul_comm]
  simp only [gluingPolarLiftFDeriv, ContinuousLinearMap.comp_apply, hC,
    gluingPolarDiskLiftFDeriv_frame,
    Complex.ofReal_one, Complex.ofReal_zero, mul_zero, add_zero, mul_one]
  ring

/-- The genuine radial differential has Euclidean norm equal to the
imaginary coordinate, as forced by its unit hyperbolic tangent norm. -/
theorem gluingPolarLiftFDeriv_radial_norm_sq (o : ℍ) (p : ℝ × ℝ) :
    ‖gluingPolarLiftFDeriv o p (1, 0)‖ ^ 2 = (gluingPolarLift o p).im ^ 2 := by
  have him : 0 < (gluingPolarLift o p).im :=
    (gluingPolarPoint o (Circle.exp p.2) p.1).im_pos
  have h := gluingPolarLift_tangentForm_pullback o p (1, 0) (1, 0)
  simp only [gluingHalfPlaneTangentForm, one_mul, mul_zero, add_zero] at h
  rw [Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re] at h
  exact (div_eq_iff (pow_ne_zero 2 him.ne')).mp h |>.trans (one_mul _)

/-- Actual polar Jacobian, obtained from its already-proved metric
pullback rather than assumed from a polar-area formula. -/
theorem gluingPolarLiftFDeriv_det_eq (o : ℍ) (p : ℝ × ℝ) :
    LinearMap.det ((gluingPolarLiftFDeriv o p).comp
      (Complex.equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ)).toLinearMap =
      Real.sinh p.1 * (gluingPolarLift o p).im ^ 2 := by
  let A := gluingPolarLiftFDeriv o p (1, 0)
  have him : 0 < (gluingPolarLift o p).im :=
    (gluingPolarPoint o (Circle.exp p.2) p.1).im_pos
  have hnorm : ‖A‖ ^ 2 = (gluingPolarLift o p).im ^ 2 := by
    have h := gluingPolarLift_tangentForm_pullback o p (1, 0) (1, 0)
    simp only [gluingHalfPlaneTangentForm, one_mul,
      mul_zero, add_zero] at h
    change (A * conj A).re / (gluingPolarLift o p).im ^ 2 = 1 at h
    rw [Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re] at h
    exact (div_eq_iff (pow_ne_zero 2 him.ne')).mp h |>.trans (one_mul _)
  rw [complex_area_det]
  have hangle : gluingPolarLiftFDeriv o p (0, 1) =
      A * (Complex.I * (Real.sinh p.1 : ℂ)) := by
    rw [gluingPolarLiftFDeriv_radial_frame]
    simp only [Complex.ofReal_zero, Complex.ofReal_one, mul_one, zero_add]
    rfl
  change A.re * (gluingPolarLiftFDeriv o p (0, 1)).im -
    (gluingPolarLiftFDeriv o p (0, 1)).re * A.im = _
  rw [hangle, ← hnorm, Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

#print axioms gluingPolarLiftFDeriv_radial_frame
#print axioms gluingPolarLiftFDeriv_det_eq

/-- Exact signed outgoing Jacobian of the original reflected polar lift. -/
theorem gluingOutgoingPolarLift_fderiv_det_eq (o : ℍ) (r : ℝ) (z : ℂ) :
    LinearMap.det (fderiv ℝ (gluingOutgoingPolarLift o r) z).toLinearMap =
      -Real.sinh (r - z.re) * (gluingOutgoingPolarLift o r z).im ^ 2 := by
  let p := gluingOutgoingPolarCoordinates r z
  have hD := (gluingPolarLift_hasFDerivAt o p).comp z
    (gluingOutgoingPolarCoordinates_hasFDerivAt r z)
  change HasFDerivAt (gluingOutgoingPolarLift o r) _ z at hD
  rw [hD.fderiv]
  rw [complex_area_frame_det _ (gluingPolarLiftFDeriv o p (1, 0))
    (Real.sinh p.1) (-1) 1 (by
      intro w
      rw [ContinuousLinearMap.comp_apply, gluingPolarLiftFDeriv_radial_frame]
      simp [gluingOutgoingPolarCoordinateDeriv, ContinuousLinearEquiv.smulLeft,
        Complex.ofReal_mul, mul_assoc])]
  rw [gluingPolarLiftFDeriv_radial_norm_sq]
  change -1 * 1 * (gluingOutgoingPolarLift o r z).im ^ 2 *
    Real.sinh (r - z.re) = _
  ring

/-- Exact signed incoming Jacobian, including the actual angular reflection. -/
theorem gluingIncomingPolarLift_fderiv_det_eq (o : ℍ) (r : ℝ) (z : ℂ) :
    LinearMap.det (fderiv ℝ (gluingIncomingPolarLift o r) z).toLinearMap =
      -Real.sinh (r + z.re) * (gluingIncomingPolarLift o r z).im ^ 2 := by
  let p := gluingIncomingPolarCoordinates r z
  have hD := (gluingPolarLift_hasFDerivAt o p).comp z
    (gluingIncomingPolarCoordinates_hasFDerivAt r z)
  change HasFDerivAt (gluingIncomingPolarLift o r) _ z at hD
  rw [hD.fderiv]
  rw [complex_area_frame_det _ (gluingPolarLiftFDeriv o p (1, 0))
    (Real.sinh p.1) 1 (-1) (by
      intro w
      rw [ContinuousLinearMap.comp_apply, gluingPolarLiftFDeriv_radial_frame]
      simp [gluingIncomingPolarCoordinateDeriv, ContinuousLinearEquiv.smulLeft,
        Complex.ofReal_mul, mul_assoc])]
  rw [gluingPolarLiftFDeriv_radial_norm_sq]
  change 1 * -1 * (gluingIncomingPolarLift o r z).im ^ 2 *
    Real.sinh (r + z.re) = _
  ring

#print axioms gluingOutgoingPolarLift_fderiv_det_eq
#print axioms gluingIncomingPolarLift_fderiv_det_eq

private theorem polar_area_density_cancel {s y : ℝ} (hs : 0 ≤ s) (hy : 0 < y) :
    ENNReal.ofReal |(-s * y ^ 2)| *
      (↑((1 / ‖y‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal s := by
  rw [abs_mul, abs_neg, abs_of_nonneg hs, abs_of_nonneg (sq_nonneg y),
    ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_mul (mul_nonneg hs (sq_nonneg y))]
  congr 1
  simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one,
    coe_nnnorm, Real.norm_eq_abs, abs_of_pos hy]
  field_simp [hy.ne']

/-- Actual outgoing polar sectors have the literal native hyperbolic
area density. Injectivity is only local, on the chosen genuine sheet. -/
theorem volume_image_gluingOutgoingPolarPoint (o : ℍ) (r : ℝ) {s : Set ℂ}
    (hs : MeasurableSet s) (hpos : ∀ z ∈ s, 0 < r - z.re)
    (hinj : InjOn (gluingOutgoingPolarLift o r) s) :
    volume ((fun z : ℂ => gluingPolarPoint o (Circle.exp z.im) (r - z.re)) '' s) =
      ∫⁻ z : ℂ in s, ENNReal.ofReal (Real.sinh (r - z.re)) := by
  rw [UpperHalfPlane.volume_eq_lintegral, image_image]
  change (∫⁻ w : ℂ in gluingOutgoingPolarLift o r '' s,
    (↑((1 / ‖w.im‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞)) = _
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (fun z _ => ((gluingOutgoingPolarLift_contDiff o r).differentiable
      (by simp)).differentiableAt.hasFDerivAt.hasFDerivWithinAt) hinj]
  apply setLIntegral_congr_fun hs
  intro z hz
  change ENNReal.ofReal |LinearMap.det
    (fderiv ℝ (gluingOutgoingPolarLift o r) z).toLinearMap| *
      (↑((1 / ‖(gluingOutgoingPolarLift o r z).im‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) = _
  rw [gluingOutgoingPolarLift_fderiv_det_eq]
  exact polar_area_density_cancel (Real.sinh_pos_iff.mpr (hpos z hz)).le
    (gluingPolarPoint o (Circle.exp z.im) (r - z.re)).im_pos

/-- The reflected incoming polar sectors have the same positive area
density; the orientation-reversing sign is removed by the true Jacobian. -/
theorem volume_image_gluingIncomingPolarPoint (o : ℍ) (r : ℝ) {s : Set ℂ}
    (hs : MeasurableSet s) (hpos : ∀ z ∈ s, 0 < r + z.re)
    (hinj : InjOn (gluingIncomingPolarLift o r) s) :
    volume ((fun z : ℂ => gluingPolarPoint o (Circle.exp (-z.im)) (r + z.re)) '' s) =
      ∫⁻ z : ℂ in s, ENNReal.ofReal (Real.sinh (r + z.re)) := by
  rw [UpperHalfPlane.volume_eq_lintegral, image_image]
  change (∫⁻ w : ℂ in gluingIncomingPolarLift o r '' s,
    (↑((1 / ‖w.im‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞)) = _
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (fun z _ => ((gluingIncomingPolarLift_contDiff o r).differentiable
      (by simp)).differentiableAt.hasFDerivAt.hasFDerivWithinAt) hinj]
  apply setLIntegral_congr_fun hs
  intro z hz
  change ENNReal.ofReal |LinearMap.det
    (fderiv ℝ (gluingIncomingPolarLift o r) z).toLinearMap| *
      (↑((1 / ‖(gluingIncomingPolarLift o r z).im‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) = _
  rw [gluingIncomingPolarLift_fderiv_det_eq]
  exact polar_area_density_cancel (Real.sinh_pos_iff.mpr (hpos z hz)).le
    (gluingPolarPoint o (Circle.exp (-z.im)) (r + z.re)).im_pos

#print axioms volume_image_gluingOutgoingPolarPoint
#print axioms volume_image_gluingIncomingPolarPoint

/-- Actual hyperbolic spheres have zero area. This includes radius zero
and supplies the seam-area nullity needed by the genuine collar sheets. -/
theorem volume_hyperbolic_sphere_eq_zero (o : ℍ) (R : ℝ) :
    volume (Metric.sphere o R) = 0 := by
  have hcenter : volume (Metric.sphere o R) = volume (Metric.sphere (I : ℍ) R) := by
    let γ : SL(2, ℝ) := o.toSL2R
    have hsphere : γ • Metric.sphere (I : ℍ) R = Metric.sphere o R := by
      rw [Metric.smul_sphere, show γ • (I : ℍ) = o by simp [γ]]
    rw [← hsphere, measure_smul]
  have hsphere : hyperbolicCayleyImage
      (Metric.sphere (0 : ℂ) (Real.tanh (R / 2))) = Metric.sphere (I : ℍ) R := by
    ext τ
    simp only [hyperbolicCayleyImage, mem_setOf_eq, Metric.mem_sphere,
      dist_zero_right, norm_halfPlaneToCayley_eq_tanh_half_dist]
    constructor
    · intro h
      have hh := Real.tanh_injective h
      rw [dist_comm τ (I : ℍ)]
      linarith
    · intro h
      rw [dist_comm (I : ℍ) τ, h]
  have hsub : Metric.sphere (0 : ℂ) (Real.tanh (R / 2)) ⊆ Metric.ball (0 : ℂ) 1 := by
    intro z hz
    have hn := Metric.mem_sphere.mp hz
    rw [Metric.mem_ball, hn]
    exact Real.tanh_lt_one _
  rw [hcenter, ← hsphere,
    volume_hyperbolicCayleyImage Metric.isClosed_sphere.measurableSet hsub]
  exact setLIntegral_measure_zero _ _ (Measure.addHaar_sphere volume (0 : ℂ) _)

#print axioms volume_hyperbolic_sphere_eq_zero

end SystolicGrowth
