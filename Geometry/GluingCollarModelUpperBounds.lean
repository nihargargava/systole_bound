module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarModelMetric
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-!
# Quantitative upper bounds for the actual collar length metric

Ordinary affine C¹ segments stay inside the radial strip containing their
endpoints. Their native collar speed is bounded by an explicit multiple of
coordinate displacement; integrating over the unit interval gives an upper
bound for the genuine path-infimum metric. Distance contracts explicitly
select the constructed metric, pseudo-metric and uniform space. Ordinary
coordinate derivatives retain their usual real-vector-space meaning.
-/

open Set Bundle Manifold
open scoped Manifold Topology Bundle ENNReal

namespace SystolicGrowth

/-- A uniform bound for the actual tangent speed in a bounded radial strip. -/
theorem gluingCollarModel_speed_le_on_strip {r R : ℝ} (hr : 0 < r)
    (z v : ℂ) (hz : |z.re| ≤ R) :
    Real.sqrt (gluingComplexCollarTangentForm r z v v) ≤
      max 1 (Real.sinh (r + R)) * (|v.re| + |v.im|) := by
  have hwpos : 0 ≤ gluingCollarWarp r z.re := (gluingCollarWarp_pos hr z.re).le
  have hwle : gluingCollarWarp r z.re ≤ Real.sinh (r + R) := by
    exact Real.sinh_le_sinh.mpr (by linarith)
  have hbase : Real.sqrt (gluingComplexCollarTangentForm r z v v) ≤
      |v.re| + gluingCollarWarp r z.re * |v.im| := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · rw [gluingComplexCollarTangentForm_apply, gluingCollarTangentForm_self]
      have hprod : 0 ≤ |v.re| * (gluingCollarWarp r z.re * |v.im|) := by positivity
      nlinarith [sq_abs v.re, sq_abs v.im]
  have hc1 : (1 : ℝ) ≤ max 1 (Real.sinh (r + R)) := le_max_left _ _
  have hcw : gluingCollarWarp r z.re ≤ max 1 (Real.sinh (r + R)) :=
    hwle.trans (le_max_right _ _)
  apply hbase.trans
  have hreal := mul_le_mul_of_nonneg_right hc1 (abs_nonneg v.re)
  have him := mul_le_mul_of_nonneg_right hcw (abs_nonneg v.im)
  nlinarith

/-- The explicit ordinary affine segment used to bound native path distance. -/
noncomputable def gluingCollarLinearSegment (z w : ℂ) (t : ℝ) : ℂ := (1 - t) • z + t • w

theorem gluingCollarLinearSegment_contDiff (z w : ℂ) :
    ContDiff ℝ 1 (gluingCollarLinearSegment z w) := by
  unfold gluingCollarLinearSegment
  fun_prop

set_option backward.isDefEq.respectTransparency false in
theorem gluingCollarLinearSegment_deriv (z w : ℂ) (t : ℝ) :
    deriv (gluingCollarLinearSegment z w) t = w - z := by
  unfold gluingCollarLinearSegment
  have h := (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).smul_const z).add
    ((hasDerivAt_id t).smul_const w)
  convert h.deriv using 1 <;> first
  | rfl
  | simp [sub_eq_add_neg, add_comm]

/-- Convex radial strips contain the whole explicit segment, not only its
endpoints. Angular displacement is unrestricted. -/
theorem gluingCollarLinearSegment_radial_bound {R : ℝ} (z w : ℂ)
    (hz : |z.re| ≤ R) (hw : |w.re| ≤ R) {t : ℝ} (ht : t ∈ Icc 0 1) :
    |(gluingCollarLinearSegment z w t).re| ≤ R := by
  simp only [gluingCollarLinearSegment, Complex.add_re, Complex.real_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have ha : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
  calc
    |(1 - t) * z.re + t * w.re| ≤ |(1 - t) * z.re| + |t * w.re| := abs_add_le _ _
    _ = (1 - t) * |z.re| + t * |w.re| := by rw [abs_mul, abs_mul,
      abs_of_nonneg ha, abs_of_nonneg ht.1]
    _ ≤ (1 - t) * R + t * R :=
      add_le_add (mul_le_mul_of_nonneg_left hz ha) (mul_le_mul_of_nonneg_left hw ht.1)
    _ = R := by ring

/-- The actual collar length of the explicit C¹ segment obeys a quantitative
coordinate bound. No approximation or density premise is used. -/
theorem gluingCollarModelPathELength_linearSegment_le {r R : ℝ} (hr : 0 < r)
    (z w : ℂ) (hz : |z.re| ≤ R) (hw : |w.re| ≤ R) :
    gluingCollarModelPathELength hr (gluingCollarLinearSegment z w) 0 1 ≤
      ENNReal.ofReal (max 1 (Real.sinh (r + R)) *
        (|z.re - w.re| + |z.im - w.im|)) := by
  rw [gluingCollarModelPathELength_eq_lintegral]
  calc
    _ ≤ ∫⁻ _t in Icc (0 : ℝ) 1,
        ENNReal.ofReal (max 1 (Real.sinh (r + R)) *
          (|z.re - w.re| + |z.im - w.im|)) := by
      apply MeasureTheory.setLIntegral_mono' measurableSet_Icc
      intro t ht
      apply ENNReal.ofReal_le_ofReal
      rw [gluingCollarLinearSegment_deriv]
      have h := gluingCollarModel_speed_le_on_strip hr
        (gluingCollarLinearSegment z w t) (w - z)
        (gluingCollarLinearSegment_radial_bound z w hz hw ht)
      simpa only [Complex.sub_re, Complex.sub_im, abs_sub_comm] using h
    _ = _ := by
      simp only [MeasureTheory.setLIntegral_const, Real.volume_Icc, sub_zero,
        ENNReal.ofReal_one, mul_one]

/-- Native collar distance is bounded on every radial strip by a genuine
ordinary C¹ path and an explicit coordinate-Lipschitz constant. -/
theorem gluingCollarModelMetric_dist_le_on_strip {r R : ℝ} (hr : 0 < r)
    (z w : ℂ) (hz : |z.re| ≤ R) (hw : |w.re| ≤ R) :
    letI := gluingCollarModelMetricSpace hr
    letI := (gluingCollarModelMetricSpace hr).toPseudoMetricSpace
    letI := (gluingCollarModelMetricSpace hr).toUniformSpace
    dist z w ≤ max 1 (Real.sinh (r + R)) *
      (|z.re - w.re| + |z.im - w.im|) := by
  letI collarMetric : MetricSpace ℂ := gluingCollarModelMetricSpace hr
  letI : PseudoMetricSpace ℂ := collarMetric.toPseudoMetricSpace
  letI : UniformSpace ℂ := collarMetric.toUniformSpace
  have hpath := gluingCollarModelEDist_le_pathELength hr
    (gluingCollarLinearSegment_contDiff z w).contMDiff.contMDiffOn zero_le_one
  have hend0 : gluingCollarLinearSegment z w 0 = z := by simp [gluingCollarLinearSegment]
  have hend1 : gluingCollarLinearSegment z w 1 = w := by simp [gluingCollarLinearSegment]
  rw [hend0, hend1] at hpath
  have hbound := hpath.trans (gluingCollarModelPathELength_linearSegment_le hr z w hz hw)
  change edist z w ≤ _ at hbound
  rw [@edist_dist ℂ collarMetric.toPseudoMetricSpace z w] at hbound
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hbound

/-- Equivalent upper control by the ordinary ambient complex norm. The norm
on the right is not the newly constructed intrinsic distance. -/
theorem gluingCollarModelMetric_dist_le_ambient_norm_on_strip {r R : ℝ} (hr : 0 < r)
    (z w : ℂ) (hz : |z.re| ≤ R) (hw : |w.re| ≤ R) :
    letI := gluingCollarModelMetricSpace hr
    letI := (gluingCollarModelMetricSpace hr).toPseudoMetricSpace
    letI := (gluingCollarModelMetricSpace hr).toUniformSpace
    dist z w ≤ 2 * max 1 (Real.sinh (r + R)) * ‖z - w‖ := by
  letI collarMetric : MetricSpace ℂ := gluingCollarModelMetricSpace hr
  letI : PseudoMetricSpace ℂ := collarMetric.toPseudoMetricSpace
  letI : UniformSpace ℂ := collarMetric.toUniformSpace
  have hcoord := gluingCollarModelMetric_dist_le_on_strip hr z w hz hw
  have hre : |z.re - w.re| ≤ ‖z - w‖ := by
    simpa only [Complex.sub_re] using Complex.abs_re_le_norm (z - w)
  have him : |z.im - w.im| ≤ ‖z - w‖ := by
    simpa only [Complex.sub_im] using Complex.abs_im_le_norm (z - w)
  have hC : 0 ≤ max 1 (Real.sinh (r + R)) :=
    zero_le_one.trans (le_max_left _ _)
  apply hcoord.trans
  nlinarith [mul_le_mul_of_nonneg_left hre hC, mul_le_mul_of_nonneg_left him hC]

#print axioms gluingCollarModel_speed_le_on_strip
#print axioms gluingCollarLinearSegment_contDiff
#print axioms gluingCollarLinearSegment_deriv
#print axioms gluingCollarLinearSegment_radial_bound
#print axioms gluingCollarModelPathELength_linearSegment_le
#print axioms gluingCollarModelMetric_dist_le_on_strip
#print axioms gluingCollarModelMetric_dist_le_ambient_norm_on_strip

end SystolicGrowth
