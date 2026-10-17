module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.UpperHalfPlaneRiemannianDistance
public import Geometry.GluingNativeConformalTransitions
public import Vendored.DoCarmo.LeeLib.Ch02.Isometry

@[expose] public section

/-!
# Analyticity of orientation-preserving Poincaré isometries

Metric preservation and positive real orientation imply complex-linearity of
the actual differential. Holomorphicity and analytic diffeomorphisms are then
constructed on mathlib's unchanged upper-half-plane atlas.
-/

open Bundle Manifold Set Filter UpperHalfPlane Riemannian
open scoped Manifold ContDiff Topology ComplexConjugate

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

namespace SystolicGrowth

noncomputable section

/-- **Math.** The inverse of the unchanged singleton chart has identity real
differential on its genuine upper-half-plane domain. -/
theorem upperHalfPlane_ofComplex_mfderiv_real (p : ℍ) :
    mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
      UpperHalfPlane.ofComplex (p : ℂ) = ContinuousLinearMap.id ℝ ℂ := by
  have hd := (upperHalfPlane_ofComplex_contMDiffAt_real p.im_pos).mdifferentiableAt (by simp)
  have hc := (upperHalfPlane_coe_contMDiff_real
    (UpperHalfPlane.ofComplex (p : ℂ))).mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp (p : ℂ) hc hd
  rw [upperHalfPlane_coe_mfderiv_real, mfderiv_eq_fderiv] at hcomp
  have heq : (fun z : ℂ => (UpperHalfPlane.ofComplex z : ℂ)) =ᶠ[𝓝 (p : ℂ)] id :=
    UpperHalfPlane.eventuallyEq_coe_comp_ofComplex p.im_pos
  change fderiv ℝ (fun z : ℂ => (UpperHalfPlane.ofComplex z : ℂ)) (p : ℂ) = _ at hcomp
  rw [heq.fderiv_eq, fderiv_id] at hcomp
  ext v
  have hv := congrArg (fun D : ℂ →L[ℝ] ℂ => D v) hcomp
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using! hv.symm

/-- **Math.** The actual manifold differential is the real differential of
the literal complex chart reading, with both inclusion derivatives derived. -/
theorem upperHalfPlane_chartReading_hasFDerivAt_real {f : ℍ → ℍ} {p : ℍ}
    (hf : MDifferentiableAt (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) f p) :
    HasFDerivAt (fun z : ℂ => (f (UpperHalfPlane.ofComplex z) : ℂ))
      (mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) f p) (p : ℂ) := by
  have hinv := (upperHalfPlane_ofComplex_contMDiffAt_real p.im_pos).mdifferentiableAt (by simp)
  have hfp : MDifferentiableAt (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
      f (UpperHalfPlane.ofComplex (p : ℂ)) := by simpa only [UpperHalfPlane.ofComplex_apply] using hf
  have hcoe := (upperHalfPlane_coe_contMDiff_real
    (f (UpperHalfPlane.ofComplex (p : ℂ)))).mdifferentiableAt (by simp)
  have h := hcoe.hasMFDerivAt.comp (p : ℂ) (hfp.hasMFDerivAt.comp (p : ℂ) hinv.hasMFDerivAt)
  rw [upperHalfPlane_coe_mfderiv_real, upperHalfPlane_ofComplex_mfderiv_real,
    UpperHalfPlane.ofComplex_apply] at h
  convert! h.hasFDerivAt using 1

/-- **Math.** Actual Poincaré metric preservation supplies the conformal
weighted-inner identity for the genuine real manifold differential. -/
theorem upperHalfPlane_metricPreserving_weighted_inner {f : ℍ → ℍ}
    (hmetric : LeeLib.Ch02.IsMetricPreserving
      upperHalfPlanePoincareMetric upperHalfPlanePoincareMetric f) (p : ℍ) (v w : ℂ) :
    let D : ℂ →L[ℝ] ℂ := mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) f p
    (((f p).im ^ 2)⁻¹) * (D v * conj (D w)).re =
      ((p.im ^ 2)⁻¹) * (v * conj w).re := by
  have h := hmetric.inner_mfderiv p v w
  rw [upperHalfPlanePoincareMetric_inner_eq_native,
    upperHalfPlanePoincareMetric_inner_eq_native,
    gluingComplexHalfPlaneTangentForm_apply, gluingComplexHalfPlaneTangentForm_apply] at h
  simpa only [UpperHalfPlane.im, div_eq_mul_inv, mul_comm] using! h

/-- **Math.** Positive actual orientation excludes the conjugate-linear
alternative forced by Poincaré metric preservation. -/
theorem upperHalfPlane_metricPreserving_mfderiv_complexLinear {f : ℍ → ℍ}
    (hmetric : LeeLib.Ch02.IsMetricPreserving
      upperHalfPlanePoincareMetric upperHalfPlanePoincareMetric f) (p : ℍ)
    (hdet : 0 < LinearMap.det
      (mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) f p).toLinearMap) :
    ∃ D : ℂ →L[ℂ] ℂ, D.restrictScalars ℝ =
      mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) f p := by
  apply complexLinear_of_isConformalMap_det_pos _ ?_ hdet
  apply isConformalMap_of_complex_weighted_inner _
    (A := ((f p).im ^ 2)⁻¹) (B := (p.im ^ 2)⁻¹)
    (by have := (f p).im_pos; positivity) (by have := p.im_pos; positivity)
  exact upperHalfPlane_metricPreserving_weighted_inner hmetric p

/-- **Math.** A genuine orientation-preserving smooth Poincaré isometry is
complex differentiable in the unchanged upper-half-plane atlas. -/
theorem upperHalfPlane_metricPreserving_chartReading_differentiableAt_complex
    {f : ℍ → ℍ}
    (hf : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ∞ f)
    (hmetric : LeeLib.Ch02.IsMetricPreserving
      upperHalfPlanePoincareMetric upperHalfPlanePoincareMetric f) (p : ℍ)
    (hdet : 0 < LinearMap.det
      (mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) f p).toLinearMap) :
    DifferentiableAt ℂ (fun z : ℂ => (f (UpperHalfPlane.ofComplex z) : ℂ)) (p : ℂ) := by
  have hreal := upperHalfPlane_chartReading_hasFDerivAt_real
    ((hf p).mdifferentiableAt (by simp))
  obtain ⟨D, hD⟩ := upperHalfPlane_metricPreserving_mfderiv_complexLinear hmetric p hdet
  exact (hasFDerivAt_of_restrictScalars ℝ hreal hD).differentiableAt

/-- **Math.** Holomorphicity on the actual open chart domain gives analytic
power-series expansions, rather than merely real smoothness. -/
theorem upperHalfPlane_metricPreserving_chartReading_analyticOnNhd
    {f : ℍ → ℍ}
    (hf : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ∞ f)
    (hmetric : LeeLib.Ch02.IsMetricPreserving
      upperHalfPlanePoincareMetric upperHalfPlanePoincareMetric f)
    (hdet : ∀ p : ℍ, 0 < LinearMap.det
      (mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) f p).toLinearMap) :
    AnalyticOnNhd ℂ (fun z : ℂ => (f (UpperHalfPlane.ofComplex z) : ℂ))
      {z : ℂ | 0 < z.im} := by
  apply DifferentiableOn.analyticOnNhd ?_ UpperHalfPlane.isOpen_upperHalfPlaneSet
  intro z hz
  exact (upperHalfPlane_metricPreserving_chartReading_differentiableAt_complex
    hf hmetric ⟨z, hz⟩ (hdet ⟨z, hz⟩)).differentiableWithinAt

/-- **Math.** The proved analytic chart readings yield an analytic manifold
map on the original complex upper-half-plane atlas. -/
theorem upperHalfPlane_metricPreserving_contMDiff_complex
    {f : ℍ → ℍ}
    (hf : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ∞ f)
    (hmetric : LeeLib.Ch02.IsMetricPreserving
      upperHalfPlanePoincareMetric upperHalfPlanePoincareMetric f)
    (hdet : ∀ p : ℍ, 0 < LinearMap.det
      (mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) f p).toLinearMap) :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f := by
  have hreading := upperHalfPlane_metricPreserving_chartReading_analyticOnNhd hf hmetric hdet
  have hcoe : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
      (fun p : ℍ => (f p : ℂ)) := by
    intro p
    apply UpperHalfPlane.contMDiffAt_iff.mpr
    exact (hreading (p : ℂ) p.im_pos).contDiffAt
  intro p
  have h := (UpperHalfPlane.contMDiffAt_ofComplex (n := ω) (f p).im_pos).comp p (hcoe p)
  simpa only [Function.comp_def, UpperHalfPlane.ofComplex_apply] using h

/-- **Math.** The genuine inverse-function chain rule forces positive
orientation of the inverse differential; it is not an independent input. -/
theorem upperHalfPlane_diffeomorph_symm_mfderiv_det_pos
    (Φ : Diffeomorph (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ℍ ℍ ∞)
    (hdet : ∀ p : ℍ, 0 < LinearMap.det
      (mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) (Φ : ℍ → ℍ) p).toLinearMap)
    (q : ℍ) :
    0 < LinearMap.det
      (mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) (Φ.symm : ℍ → ℍ) q).toLinearMap := by
  let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
  have hid : (Φ : ℍ → ℍ) ∘ (Φ.symm : ℍ → ℍ) = id := funext Φ.apply_symm_apply
  have hcomp := mfderiv_comp q (Φ.mdifferentiable (by simp) (Φ.symm q))
    (Φ.symm.mdifferentiable (by simp) q)
  rw [hid, mfderiv_id] at hcomp
  have hlin :
      (mfderiv I I (Φ : ℍ → ℍ) (Φ.symm q)).toLinearMap.comp
        (mfderiv I I (Φ.symm : ℍ → ℍ) q).toLinearMap = LinearMap.id := by
    exact congrArg ContinuousLinearMap.toLinearMap hcomp.symm
  have hprod := congrArg LinearMap.det hlin
  rw [LinearMap.det_comp, LinearMap.det_id] at hprod
  have hpos := hdet (Φ.symm q)
  change 0 < LinearMap.det (mfderiv I I (Φ.symm : ℍ → ℍ) q).toLinearMap
  have hprodpos := hprod.symm ▸ (show (0 : ℝ) < 1 by norm_num)
  exact pos_of_mul_pos_right hprodpos hpos.le

/-- **Math.** A real-smooth orientation-preserving Poincaré isometry defines
an analytic diffeomorphism with the very same forward and inverse functions. -/
def upperHalfPlaneIsometryToAnalyticDiffeomorph
    (Φ : Diffeomorph (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ℍ ℍ ∞)
    (hmetric : LeeLib.Ch02.IsMetricPreserving
      upperHalfPlanePoincareMetric upperHalfPlanePoincareMetric (Φ : ℍ → ℍ))
    (hdet : ∀ p : ℍ, 0 < LinearMap.det
      (mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) (Φ : ℍ → ℍ) p).toLinearMap) :
    Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ℍ ℍ ω where
  toEquiv := Φ.toEquiv
  contMDiff_toFun := upperHalfPlane_metricPreserving_contMDiff_complex Φ.contMDiff hmetric hdet
  contMDiff_invFun := upperHalfPlane_metricPreserving_contMDiff_complex Φ.symm.contMDiff
    (LeeLib.Ch02.IsIsometry.symm hmetric)
    (upperHalfPlane_diffeomorph_symm_mfderiv_det_pos Φ hdet)

@[simp] theorem upperHalfPlaneIsometryToAnalyticDiffeomorph_apply
    (Φ : Diffeomorph (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ℍ ℍ ∞)
    (hmetric : LeeLib.Ch02.IsMetricPreserving
      upperHalfPlanePoincareMetric upperHalfPlanePoincareMetric (Φ : ℍ → ℍ))
    (hdet : ∀ p : ℍ, 0 < LinearMap.det
      (mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) (Φ : ℍ → ℍ) p).toLinearMap)
    (q : ℍ) : upperHalfPlaneIsometryToAnalyticDiffeomorph Φ hmetric hdet q = Φ q := rfl

#print axioms upperHalfPlane_ofComplex_mfderiv_real
#print axioms upperHalfPlane_chartReading_hasFDerivAt_real
#print axioms upperHalfPlane_metricPreserving_weighted_inner
#print axioms upperHalfPlane_metricPreserving_mfderiv_complexLinear
#print axioms upperHalfPlane_metricPreserving_chartReading_differentiableAt_complex
#print axioms upperHalfPlane_metricPreserving_chartReading_analyticOnNhd
#print axioms upperHalfPlane_metricPreserving_contMDiff_complex
#print axioms upperHalfPlane_diffeomorph_symm_mfderiv_det_pos
#print axioms upperHalfPlaneIsometryToAnalyticDiffeomorph

end
end SystolicGrowth
