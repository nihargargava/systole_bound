module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarModelUpperBounds
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Function.SpecialFunctions.RCLike

@[expose] public section

/-!
# Integrability of the actual collar speed of Lipschitz curves

The Lipschitz predicate and coordinate derivatives here use the ordinary
complex norm, not the native collar distance. Interior derivative bounds,
restricted measurability and an actual bounded radial strip prove that every
Lipschitz coordinate curve has finite weighted speed integral. No derivative
at the endpoints or differentiability everywhere is assumed.
-/

open Set MeasureTheory
open scoped Topology

namespace SystolicGrowth

/-- The angular derivative of every ordinary Lipschitz coordinate curve is
interval integrable. Full derivatives are bounded only at interior times. -/
theorem gluingCollarCurve_abs_im_deriv_intervalIntegrable {a b : ℝ} {K : NNReal}
    {α : ℝ → ℂ} (hab : a ≤ b) (hα : LipschitzOnWith K α (Icc a b)) :
    IntervalIntegrable (fun t => |(deriv α t).im|) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab]
  have hm : AEStronglyMeasurable (fun t => |(deriv α t).im|)
      (volume.restrict (Ioo a b)) := by
    exact ((measurable_deriv α).aemeasurable.im.abs).aestronglyMeasurable
  have hc : Integrable (fun _t : ℝ => (K : ℝ)) (volume.restrict (Ioo a b)) :=
    integrableOn_const (measure_Ioo_lt_top.ne)
  apply hc.mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  simpa only [Real.norm_eq_abs, abs_abs] using
    (Complex.abs_im_le_norm (deriv α t)).trans
      (norm_deriv_le_of_lipschitzOn (Icc_mem_nhds ht.1 ht.2) hα)

/-- The actual weighted collar speed is integrable for every ordinary
Lipschitz coordinate curve, including curves that touch or cross the seam. -/
theorem gluingCollarCurve_speed_intervalIntegrable {r a b : ℝ} {K : NNReal}
    (hr : 0 < r) {α : ℝ → ℂ} (hab : a ≤ b)
    (hα : LipschitzOnWith K α (Icc a b)) :
    IntervalIntegrable
      (fun t => Real.sqrt (gluingComplexCollarTangentForm r (α t) (deriv α t) (deriv α t)))
      volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab]
  let R : ℝ := ‖α a‖ + K * (b - a)
  have hstrip {t : ℝ} (ht : t ∈ Icc a b) : |(α t).re| ≤ R := by
    have hdist := hα.dist_le_mul t ht a ⟨le_rfl, hab⟩
    have hta : |t - a| ≤ b - a := by
      rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
      linarith [ht.2]
    calc
      |(α t).re| ≤ ‖α t‖ := Complex.abs_re_le_norm _
      _ ≤ ‖α t - α a‖ + ‖α a‖ := norm_le_norm_sub_add _ _
      _ ≤ K * |t - a| + ‖α a‖ := by
        gcongr
        simpa only [dist_eq_norm, Real.norm_eq_abs] using hdist
      _ ≤ K * (b - a) + ‖α a‖ := by gcongr
      _ = R := by dsimp [R]; ring
  have hαm : AEMeasurable α (volume.restrict (Ioo a b)) :=
    (hα.continuousOn.mono Ioo_subset_Icc_self).aemeasurable measurableSet_Ioo
  have hdm : AEMeasurable (deriv α) (volume.restrict (Ioo a b)) :=
    (measurable_deriv α).aemeasurable
  have hm : AEStronglyMeasurable
      (fun t => Real.sqrt (gluingComplexCollarTangentForm r (α t) (deriv α t) (deriv α t)))
      (volume.restrict (Ioo a b)) := by
    have hwm : AEMeasurable (fun t => gluingCollarWarp r (α t).re)
        (volume.restrict (Ioo a b)) :=
      (gluingCollarWarp_continuous r).measurable.comp_aemeasurable hαm.re
    simpa only [gluingComplexCollarTangentForm_apply, gluingCollarTangentForm_self,
      Pi.add_apply, Pi.mul_apply, RCLike.re_to_complex, RCLike.im_to_complex] using
      ((hdm.re.pow_const 2).add ((hwm.pow_const 2).mul (hdm.im.pow_const 2))).sqrt
        |>.aestronglyMeasurable
  have hc : Integrable (fun _t : ℝ => 2 * max 1 (Real.sinh (r + R)) * K)
      (volume.restrict (Ioo a b)) :=
    integrableOn_const (measure_Ioo_lt_top.ne)
  apply hc.mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hd := norm_deriv_le_of_lipschitzOn (Icc_mem_nhds ht.1 ht.2) hα
  have hre := (Complex.abs_re_le_norm (deriv α t)).trans hd
  have him := (Complex.abs_im_le_norm (deriv α t)).trans hd
  have hs := gluingCollarModel_speed_le_on_strip hr (α t) (deriv α t)
    (hstrip ⟨ht.1.le, ht.2.le⟩)
  have hC : 0 ≤ max 1 (Real.sinh (r + R)) := zero_le_one.trans (le_max_left _ _)
  apply hs.trans
  nlinarith [mul_le_mul_of_nonneg_left hre hC, mul_le_mul_of_nonneg_left him hC]

#print axioms gluingCollarCurve_abs_im_deriv_intervalIntegrable
#print axioms gluingCollarCurve_speed_intervalIntegrable

end SystolicGrowth
