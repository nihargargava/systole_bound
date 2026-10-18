module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarModelBounds
public import Geometry.GluingCollarModelUpperBounds

@[expose] public section

/-!
# Exact seam distance in the actual collar metric

The explicit angular C¹ segment has native length `sinh r * |a - b|`.
The global angular lower bound makes this the actual seam distance. The
signed-radius-zero retraction is consequently nonexpanding for the native
collar metric; no curvature or regularity of limiting geodesics is assumed.
-/

open Set Bundle Manifold
open scoped Manifold Topology Bundle ENNReal

namespace SystolicGrowth

/-- Exact native length of the explicit purely angular C¹ segment at the seam. -/
theorem gluingCollarModelPathELength_seam_linearSegment {r : ℝ} (hr : 0 < r)
    (a b : ℝ) :
    gluingCollarModelPathELength hr
      (gluingCollarLinearSegment ((a : ℂ) * Complex.I) ((b : ℂ) * Complex.I)) 0 1 =
      ENNReal.ofReal (Real.sinh r * |a - b|) := by
  rw [gluingCollarModelPathELength_eq_lintegral]
  have hspeed (t : ℝ) :
      Real.sqrt (gluingComplexCollarTangentForm r
        (gluingCollarLinearSegment ((a : ℂ) * Complex.I) ((b : ℂ) * Complex.I) t)
        (deriv (gluingCollarLinearSegment ((a : ℂ) * Complex.I)
          ((b : ℂ) * Complex.I)) t)
        (deriv (gluingCollarLinearSegment ((a : ℂ) * Complex.I)
          ((b : ℂ) * Complex.I)) t)) = Real.sinh r * |a - b| := by
    rw [gluingCollarLinearSegment_deriv, gluingComplexCollarTangentForm_apply,
      gluingCollarTangentForm_self]
    simp only [gluingCollarLinearSegment, Complex.add_re, Complex.real_smul,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, mul_one, sub_zero, add_zero,
      gluingCollarWarp_zero]
    simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add]
    rw [← mul_pow, Real.sqrt_sq_eq_abs, abs_mul,
      abs_of_pos (Real.sinh_pos_iff.mpr hr), abs_sub_comm]
  simp only [hspeed, MeasureTheory.setLIntegral_const, Real.volume_Icc,
    sub_zero, ENNReal.ofReal_one, mul_one]

/-- The exact seam distance uses the genuine native collar path metric,
not the ordinary ambient complex distance. -/
theorem gluingCollarModelMetric_dist_seam {r : ℝ} (hr : 0 < r) (a b : ℝ) :
    letI := gluingCollarModelMetricSpace hr
    letI := (gluingCollarModelMetricSpace hr).toPseudoMetricSpace
    letI := (gluingCollarModelMetricSpace hr).toUniformSpace
    dist ((a : ℂ) * Complex.I) ((b : ℂ) * Complex.I) = Real.sinh r * |a - b| := by
  letI collarMetric : MetricSpace ℂ := gluingCollarModelMetricSpace hr
  letI : PseudoMetricSpace ℂ := collarMetric.toPseudoMetricSpace
  letI : UniformSpace ℂ := collarMetric.toUniformSpace
  apply le_antisymm
  · have hpath := gluingCollarModelEDist_le_pathELength hr
      (gluingCollarLinearSegment_contDiff ((a : ℂ) * Complex.I)
        ((b : ℂ) * Complex.I)).contMDiff.contMDiffOn zero_le_one
    have h0 : gluingCollarLinearSegment ((a : ℂ) * Complex.I)
        ((b : ℂ) * Complex.I) 0 = (a : ℂ) * Complex.I := by
      simp [gluingCollarLinearSegment]
    have h1 : gluingCollarLinearSegment ((a : ℂ) * Complex.I)
        ((b : ℂ) * Complex.I) 1 = (b : ℂ) * Complex.I := by
      simp [gluingCollarLinearSegment]
    rw [h0, h1, gluingCollarModelPathELength_seam_linearSegment] at hpath
    change edist ((a : ℂ) * Complex.I) ((b : ℂ) * Complex.I) ≤ _ at hpath
    rw [@edist_dist ℂ collarMetric.toPseudoMetricSpace] at hpath
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hpath
  · have h := (gluingCollarModelMetric_coordinates_le_dist hr
      ((a : ℂ) * Complex.I) ((b : ℂ) * Complex.I)).2
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, zero_mul, add_zero] using h

/-- Retraction to signed radius zero is 1-Lipschitz for the constructed
collar metric, so an excursion cannot shorten lifted seam displacement. -/
theorem gluingCollarModelMetric_seam_retraction_lipschitz {r : ℝ} (hr : 0 < r) :
    letI := gluingCollarModelMetricSpace hr
    letI := (gluingCollarModelMetricSpace hr).toPseudoMetricSpace
    letI := (gluingCollarModelMetricSpace hr).toUniformSpace
    LipschitzWith 1 (fun z : ℂ => (z.im : ℂ) * Complex.I) := by
  letI collarMetric : MetricSpace ℂ := gluingCollarModelMetricSpace hr
  letI : PseudoMetricSpace ℂ := collarMetric.toPseudoMetricSpace
  letI : UniformSpace ℂ := collarMetric.toUniformSpace
  apply LipschitzWith.mk_one
  intro z w
  rw [gluingCollarModelMetric_dist_seam]
  exact (gluingCollarModelMetric_coordinates_le_dist hr z w).2

#print axioms gluingCollarModelPathELength_seam_linearSegment
#print axioms gluingCollarModelMetric_dist_seam
#print axioms gluingCollarModelMetric_seam_retraction_lipschitz

end SystolicGrowth
