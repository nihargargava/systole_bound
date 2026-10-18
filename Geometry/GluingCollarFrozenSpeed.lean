module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarModelUpperBounds

@[expose] public section

/-!
# Frozen-speed estimates for the actual collar metric

Freezing the warp coefficient gives a concrete real continuous linear map
on coordinate velocities. Its ordinary complex norm equals the collar speed.
Changing the coefficient costs only its variation times angular speed.
Applying this estimate to actual affine C¹ segments bounds their native
lengths and native endpoint distances; no admissible-curve metric premise is
used.
-/

open Set Bundle Manifold
open scoped Manifold Topology Bundle ENNReal

namespace SystolicGrowth

/-- The Euclidean velocity whose norm is the collar speed with its coefficient
frozen at `z`. The norm on the target is the ordinary complex norm. -/
noncomputable def gluingCollarFrozenVelocity (r : ℝ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  Complex.reCLM.smulRight (1 : ℂ) +
    gluingCollarWarp r z.re • Complex.imCLM.smulRight Complex.I

@[simp] theorem gluingCollarFrozenVelocity_apply (r : ℝ) (z v : ℂ) :
    gluingCollarFrozenVelocity r z v =
      (v.re : ℂ) + (gluingCollarWarp r z.re * v.im : ℂ) * Complex.I := by
  simp [gluingCollarFrozenVelocity, Complex.real_smul, mul_assoc]

/-- The frozen Euclidean norm is exactly the square-root of the actual
collar tangent form at its freezing point. -/
theorem gluingCollarFrozenVelocity_norm (r : ℝ) (z v : ℂ) :
    ‖gluingCollarFrozenVelocity r z v‖ =
      Real.sqrt (gluingComplexCollarTangentForm r z v v) := by
  rw [Complex.norm_def, Complex.normSq_apply,
    gluingComplexCollarTangentForm_apply, gluingCollarTangentForm_self]
  simp only [gluingCollarFrozenVelocity_apply, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
    zero_mul, sub_zero, add_zero, Complex.add_im, Complex.mul_im, mul_one]
  congr 1
  ring

/-- Changing a frozen warp coefficient changes a tangent speed by at most
the coefficient difference times the absolute angular velocity. -/
theorem gluingCollarModel_speed_sub_le (r : ℝ) (z w v : ℂ) :
    |Real.sqrt (gluingComplexCollarTangentForm r z v v) -
      Real.sqrt (gluingComplexCollarTangentForm r w v v)| ≤
      |gluingCollarWarp r z.re - gluingCollarWarp r w.re| * |v.im| := by
  rw [← gluingCollarFrozenVelocity_norm, ← gluingCollarFrozenVelocity_norm]
  have hdiff : gluingCollarFrozenVelocity r z v - gluingCollarFrozenVelocity r w v =
      ((gluingCollarWarp r z.re - gluingCollarWarp r w.re) * v.im : ℂ) *
        Complex.I := by
    apply Complex.ext
    · simp [gluingCollarFrozenVelocity_apply]
    · simp [gluingCollarFrozenVelocity_apply]
      ring
  calc
    _ ≤ ‖gluingCollarFrozenVelocity r z v - gluingCollarFrozenVelocity r w v‖ :=
      abs_norm_sub_norm_le _ _
    _ = _ := by
      rw [hdiff]
      simp only [norm_mul, Complex.norm_I, mul_one, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs]

/-- A scalar warp oscillation bound on an actual affine segment pays for
the difference between its native length and its frozen tangent speed. -/
theorem gluingCollarModelPathELength_linearSegment_le_frozen {r η : ℝ}
    (hr : 0 < r) (_hη : 0 ≤ η) (z w : ℂ)
    (hwarp : ∀ t ∈ Icc (0 : ℝ) 1,
      |gluingCollarWarp r (gluingCollarLinearSegment z w t).re -
        gluingCollarWarp r z.re| ≤ η) :
    gluingCollarModelPathELength hr (gluingCollarLinearSegment z w) 0 1 ≤
      ENNReal.ofReal (Real.sqrt (gluingComplexCollarTangentForm r z (w - z) (w - z)) +
        η * |w.im - z.im|) := by
  rw [gluingCollarModelPathELength_eq_lintegral]
  calc
    _ ≤ ∫⁻ _t in Icc (0 : ℝ) 1,
        ENNReal.ofReal (Real.sqrt (gluingComplexCollarTangentForm r z (w - z) (w - z)) +
          η * |w.im - z.im|) := by
      apply MeasureTheory.setLIntegral_mono' measurableSet_Icc
      intro t ht
      apply ENNReal.ofReal_le_ofReal
      rw [gluingCollarLinearSegment_deriv]
      have hspeed := gluingCollarModel_speed_sub_le r
        (gluingCollarLinearSegment z w t) z (w - z)
      have hosc := mul_le_mul_of_nonneg_right (hwarp t ht) (abs_nonneg (w - z).im)
      simp only [Complex.sub_im] at hspeed hosc
      linarith [le_abs_self (Real.sqrt (gluingComplexCollarTangentForm r
        (gluingCollarLinearSegment z w t) (w - z) (w - z)) -
          Real.sqrt (gluingComplexCollarTangentForm r z (w - z) (w - z)))]
    _ = _ := by
      simp only [MeasureTheory.setLIntegral_const, Real.volume_Icc, sub_zero,
        ENNReal.ofReal_one, mul_one]

/-- The literal native endpoint distance has the same frozen-speed bound,
proved by a genuine ordinary affine C¹ segment. -/
theorem gluingCollarModelMetric_dist_le_frozen {r η : ℝ} (hr : 0 < r)
    (hη : 0 ≤ η) (z w : ℂ)
    (hwarp : ∀ t ∈ Icc (0 : ℝ) 1,
      |gluingCollarWarp r (gluingCollarLinearSegment z w t).re -
        gluingCollarWarp r z.re| ≤ η) :
    letI := gluingCollarModelMetricSpace hr
    letI := (gluingCollarModelMetricSpace hr).toPseudoMetricSpace
    letI := (gluingCollarModelMetricSpace hr).toUniformSpace
    dist z w ≤ Real.sqrt (gluingComplexCollarTangentForm r z (w - z) (w - z)) +
      η * |w.im - z.im| := by
  letI collarMetric : MetricSpace ℂ := gluingCollarModelMetricSpace hr
  letI : PseudoMetricSpace ℂ := collarMetric.toPseudoMetricSpace
  letI : UniformSpace ℂ := collarMetric.toUniformSpace
  have hpath := gluingCollarModelEDist_le_pathELength hr
    (gluingCollarLinearSegment_contDiff z w).contMDiff.contMDiffOn zero_le_one
  have hend0 : gluingCollarLinearSegment z w 0 = z := by simp [gluingCollarLinearSegment]
  have hend1 : gluingCollarLinearSegment z w 1 = w := by simp [gluingCollarLinearSegment]
  rw [hend0, hend1] at hpath
  have hbound := hpath.trans
    (gluingCollarModelPathELength_linearSegment_le_frozen hr hη z w hwarp)
  change edist z w ≤ _ at hbound
  rw [@edist_dist ℂ collarMetric.toPseudoMetricSpace z w] at hbound
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hbound

#print axioms gluingCollarFrozenVelocity_norm
#print axioms gluingCollarModel_speed_sub_le
#print axioms gluingCollarModelPathELength_linearSegment_le_frozen
#print axioms gluingCollarModelMetric_dist_le_frozen

end SystolicGrowth
