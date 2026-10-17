module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarLocalizedCurvature

@[expose] public section

/-!
# Exact signed curvature mass of localized collar smoothing

Native equality on a closed exterior half-line determines the genuine
ordinary derivative at its boundary by uniqueness of the one-sided
derivative. Thus even the cutoff endpoint needs no flat-bump assumption.
The actual signed curvature mass is independent of the smoothing parameter;
this does not assert equality of total variations.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace SystolicGrowth

/-- Equality on the actual exterior half-line gives the true endpoint
derivative, including the boundary of the bump support. -/
theorem gluingCollarLocalizedSmoothWarp_deriv_eq_native_of_radius_ge
    (r : ℝ) {ε R : ℝ} (hε : 0 < ε) (b : ContDiffBump (0 : ℝ))
    (hR : b.rOut ≤ R) :
    deriv (gluingCollarLocalizedSmoothWarp r ε b) R = Real.cosh (r + R) := by
  have hRpos : 0 < R := b.rOut_pos.trans_le hR
  have hW := (gluingCollarLocalizedSmoothWarp_contDiff r hε b 1).differentiable
    (by norm_num) R
  have hwithin : HasDerivWithinAt (gluingCollarLocalizedSmoothWarp r ε b)
      (Real.cosh (r + R)) (Ici R) R := by
    apply (gluingCollarWarp_hasDerivAt_pos r hRpos).hasDerivWithinAt.congr_of_mem
    · intro t ht
      apply gluingCollarLocalizedSmoothWarp_eq_native r ε b
      exact hR.trans (ht.trans (le_abs_self t))
    · exact self_mem_Ici
  exact (hW.hasDerivAt.hasDerivWithinAt.derivWithin
    (uniqueDiffWithinAt_Ici R)).symm.trans
      (hwithin.derivWithin (uniqueDiffWithinAt_Ici R))

/-- The left endpoint is handled by the actual exterior left half-line,
again including equality with the bump support radius. -/
theorem gluingCollarLocalizedSmoothWarp_deriv_neg_eq_native_of_radius_ge
    (r : ℝ) {ε R : ℝ} (hε : 0 < ε) (b : ContDiffBump (0 : ℝ))
    (hR : b.rOut ≤ R) :
    deriv (gluingCollarLocalizedSmoothWarp r ε b) (-R) = -Real.cosh (r + R) := by
  have hRpos : 0 < R := b.rOut_pos.trans_le hR
  have hW := (gluingCollarLocalizedSmoothWarp_contDiff r hε b 1).differentiable
    (by norm_num) (-R)
  have hwithin : HasDerivWithinAt (gluingCollarLocalizedSmoothWarp r ε b)
      (-Real.cosh (r - (-R))) (Iic (-R)) (-R) := by
    apply (gluingCollarWarp_hasDerivAt_neg r (by linarith : -R < 0)).hasDerivWithinAt.congr_of_mem
    · intro t ht
      change t ≤ -R at ht
      apply gluingCollarLocalizedSmoothWarp_eq_native r ε b
      have htneg : t < 0 := lt_of_le_of_lt ht (by linarith)
      rw [abs_of_neg htneg]
      linarith
    · exact self_mem_Iic
  have h := (hW.hasDerivAt.hasDerivWithinAt.derivWithin
    (uniqueDiffWithinAt_Iic (-R))).symm.trans
      (hwithin.derivWithin (uniqueDiffWithinAt_Iic (-R)))
  simpa only [sub_neg_eq_add] using h

/-- The exact radial second-derivative mass, independent of ε, at every
window containing the entire actual cutoff support. -/
theorem gluingCollarLocalizedSmoothWarp_second_deriv_integral_eq
    (r : ℝ) {ε R : ℝ} (hε : 0 < ε) (b : ContDiffBump (0 : ℝ))
    (hR : b.rOut ≤ R) :
    (∫ t : ℝ in Icc (-R) R,
      deriv (deriv (gluingCollarLocalizedSmoothWarp r ε b)) t) = 2 * Real.cosh (r + R) := by
  have hRpos : 0 < R := b.rOut_pos.trans_le hR
  have hW := gluingCollarLocalizedSmoothWarp_contDiff r hε b 2
  have hW' : ContDiff ℝ 1 (deriv (gluingCollarLocalizedSmoothWarp r ε b)) := hW.deriv'
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show -R ≤ R by linarith),
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (show -R ≤ R by linarith) hW'.continuous.continuousOn
      (fun t _ => (hW.differentiable_deriv_two t).hasDerivAt)
      (hW'.continuous_deriv_one.intervalIntegrable (-R) R),
    gluingCollarLocalizedSmoothWarp_deriv_eq_native_of_radius_ge r hε b hR,
    gluingCollarLocalizedSmoothWarp_deriv_neg_eq_native_of_radius_ge r hε b hR]
  ring

/-- The same exact mass on the open native thin interval. Original volume
has no endpoint atoms, so the closed support-boundary case is included. -/
theorem gluingCollarLocalizedSmoothWarp_second_deriv_integral_Ioo_eq
    (r : ℝ) {ε R : ℝ} (hε : 0 < ε) (b : ContDiffBump (0 : ℝ))
    (hR : b.rOut ≤ R) :
    (∫ t : ℝ in Ioo (-R) R,
      deriv (deriv (gluingCollarLocalizedSmoothWarp r ε b)) t) = 2 * Real.cosh (r + R) := by
  rw [restrict_Ioo_eq_restrict_Icc]
  exact gluingCollarLocalizedSmoothWarp_second_deriv_integral_eq r hε b hR

/-- The original radial signed curvature has its exact signed mass,
including the genuine negative seam atom. -/
theorem gluingCollarRadialCurvatureMeasureOnWindow_univ
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    gluingCollarRadialCurvatureMeasureOnWindow r R univ = -2 * Real.cosh (r + R) := by
  rw [gluingCollarRadialCurvatureMeasureOnWindow, neg_apply,
    Measure.toSignedMeasure_apply_measurable MeasurableSet.univ, measureReal_def,
    Measure.restrict_apply_univ, gluingCollarRadialSecondDerivativeMeasure_Icc hr hR,
    ENNReal.toReal_ofReal (show 0 ≤ 2 * Real.cosh (r + R) by positivity)]
  ring

/-- The actual smoothed signed Gaussian density integrates to exactly
the original native signed radial curvature mass. Its variation may differ. -/
theorem gluingCollarLocalizedSmoothWarp_curvature_integral_eq_native
    {r ε R : ℝ} (hr : 0 < r) (hε : 0 < ε) (b : ContDiffBump (0 : ℝ))
    (hR : b.rOut ≤ R) :
    (∫ t : ℝ in Icc (-R) R,
      -deriv (deriv (gluingCollarLocalizedSmoothWarp r ε b)) t) =
        gluingCollarRadialCurvatureMeasureOnWindow r R univ := by
  rw [integral_neg, gluingCollarLocalizedSmoothWarp_second_deriv_integral_eq r hε b hR,
    gluingCollarRadialCurvatureMeasureOnWindow_univ hr (b.rOut_pos.trans_le hR)]
  ring

#print axioms gluingCollarLocalizedSmoothWarp_deriv_eq_native_of_radius_ge
#print axioms gluingCollarLocalizedSmoothWarp_deriv_neg_eq_native_of_radius_ge
#print axioms gluingCollarLocalizedSmoothWarp_second_deriv_integral_eq
#print axioms gluingCollarLocalizedSmoothWarp_second_deriv_integral_Ioo_eq
#print axioms gluingCollarRadialCurvatureMeasureOnWindow_univ
#print axioms gluingCollarLocalizedSmoothWarp_curvature_integral_eq_native

end SystolicGrowth
