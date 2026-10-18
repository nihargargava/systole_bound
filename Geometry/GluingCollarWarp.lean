module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.TangentCone.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-!
# The actual warping function at a glued circular seam

The collar metric has warping function `sinh (r + |t|)`, with `r` the
unscaled hyperbolic radius. Its one-sided derivative jump is `2 cosh r`.
Away from the seam its second derivative equals the function itself.
These calculus facts identify the positive atom in the distributional
second derivative; they do not assert a warped-metric curvature theorem.
-/

open Filter Set MeasureTheory
open scoped Topology

namespace SystolicGrowth

/-- The actual circular-seam warping function, in hyperbolic radius units. -/
noncomputable def gluingCollarWarp (r t : ℝ) : ℝ := Real.sinh (r + |t|)

@[simp] theorem gluingCollarWarp_zero (r : ℝ) :
    gluingCollarWarp r 0 = Real.sinh r := by simp [gluingCollarWarp]

theorem gluingCollarWarp_eq_of_nonneg (r : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    gluingCollarWarp r t = Real.sinh (r + t) := by
  rw [gluingCollarWarp, abs_of_nonneg ht]

theorem gluingCollarWarp_eq_of_nonpos (r : ℝ) {t : ℝ} (ht : t ≤ 0) :
    gluingCollarWarp r t = Real.sinh (r - t) := by
  rw [gluingCollarWarp, abs_of_nonpos ht, sub_eq_add_neg]

theorem gluingCollarWarp_continuous (r : ℝ) : Continuous (gluingCollarWarp r) :=
  Real.continuous_sinh.comp (continuous_const.add continuous_abs)

theorem gluingCollarWarp_pos {r : ℝ} (hr : 0 < r) (t : ℝ) :
    0 < gluingCollarWarp r t := by
  apply Real.sinh_pos_iff.mpr
  exact add_pos_of_pos_of_nonneg hr (abs_nonneg t)

theorem gluingCollarWarp_hasDerivAt_pos (r : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (gluingCollarWarp r) (Real.cosh (r + t)) t := by
  have h : HasDerivAt (fun u : ℝ => Real.sinh (r + u)) (Real.cosh (r + t)) t := by
    simpa using ((hasDerivAt_id t).const_add r).sinh
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with u hu
  exact gluingCollarWarp_eq_of_nonneg r hu.le

theorem gluingCollarWarp_hasDerivAt_neg (r : ℝ) {t : ℝ} (ht : t < 0) :
    HasDerivAt (gluingCollarWarp r) (-Real.cosh (r - t)) t := by
  have h : HasDerivAt (fun u : ℝ => Real.sinh (r - u)) (-Real.cosh (r - t)) t := by
    simpa using ((hasDerivAt_id t).const_sub r).sinh
  apply h.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds ht] with u hu
  exact gluingCollarWarp_eq_of_nonpos r hu.le

theorem gluingCollarWarp_deriv_pos (r : ℝ) {t : ℝ} (ht : 0 < t) :
    deriv (gluingCollarWarp r) t = Real.cosh (r + t) :=
  (gluingCollarWarp_hasDerivAt_pos r ht).deriv

theorem gluingCollarWarp_deriv_neg (r : ℝ) {t : ℝ} (ht : t < 0) :
    deriv (gluingCollarWarp r) t = -Real.cosh (r - t) :=
  (gluingCollarWarp_hasDerivAt_neg r ht).deriv

/-- The actual first derivative of the collar warp exists at every point away
from the seam, with its value expressed using `deriv`. -/
theorem gluingCollarWarp_hasDerivAt_of_ne (r : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (gluingCollarWarp r) (deriv (gluingCollarWarp r) t) t := by
  rcases lt_or_gt_of_ne ht with ht | ht
  · simpa only [gluingCollarWarp_deriv_neg r ht] using
      gluingCollarWarp_hasDerivAt_neg r ht
  · simpa only [gluingCollarWarp_deriv_pos r ht] using
      gluingCollarWarp_hasDerivAt_pos r ht

theorem gluingCollarWarp_hasDerivWithinAt_zero_right (r : ℝ) :
    HasDerivWithinAt (gluingCollarWarp r) (Real.cosh r) (Ici 0) 0 := by
  have h : HasDerivAt (fun t : ℝ => Real.sinh (r + t)) (Real.cosh r) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_add r).sinh
  exact h.hasDerivWithinAt.congr_of_mem
    (fun t ht => gluingCollarWarp_eq_of_nonneg r ht) (by simp)

theorem gluingCollarWarp_hasDerivWithinAt_zero_left (r : ℝ) :
    HasDerivWithinAt (gluingCollarWarp r) (-Real.cosh r) (Iic 0) 0 := by
  have h : HasDerivAt (fun t : ℝ => Real.sinh (r - t)) (-Real.cosh r) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_sub r).sinh
  exact h.hasDerivWithinAt.congr_of_mem
    (fun t ht => gluingCollarWarp_eq_of_nonpos r ht) (by simp)

/-- The actual one-sided derivatives have a positive jump at the seam. -/
theorem gluingCollarWarp_deriv_jump (r : ℝ) :
    derivWithin (gluingCollarWarp r) (Ici 0) 0 -
      derivWithin (gluingCollarWarp r) (Iic 0) 0 = 2 * Real.cosh r := by
  rw [(gluingCollarWarp_hasDerivWithinAt_zero_right r).derivWithin
    (uniqueDiffWithinAt_Ici 0),
    (gluingCollarWarp_hasDerivWithinAt_zero_left r).derivWithin
      (uniqueDiffWithinAt_Iic 0)]
  ring

theorem gluingCollarWarp_deriv_jump_pos (r : ℝ) :
    0 < derivWithin (gluingCollarWarp r) (Ici 0) 0 -
      derivWithin (gluingCollarWarp r) (Iic 0) 0 := by
  rw [gluingCollarWarp_deriv_jump]
  exact mul_pos (by norm_num) (Real.cosh_pos _)

/-- The smooth second derivative is the warping function on either side
of the seam, with no assertion about a two-sided derivative at zero. -/
theorem gluingCollarWarp_hasDerivAt_deriv (r : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (deriv (gluingCollarWarp r)) (gluingCollarWarp r t) t := by
  rcases lt_or_gt_of_ne ht with ht | ht
  · have h : HasDerivAt (fun u : ℝ => -Real.cosh (r - u)) (Real.sinh (r - t)) t := by
      have hc : HasDerivAt (fun u : ℝ => Real.cosh (r - u)) (-Real.sinh (r - t)) t := by
        simpa using ((hasDerivAt_id t).const_sub r).cosh
      simpa using hc.const_mul (-1)
    rw [gluingCollarWarp_eq_of_nonpos r ht.le]
    apply h.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds ht] with u hu
    exact gluingCollarWarp_deriv_neg r hu
  · have h : HasDerivAt (fun u : ℝ => Real.cosh (r + u)) (Real.sinh (r + t)) t := by
      simpa using ((hasDerivAt_id t).const_add r).cosh
    rw [gluingCollarWarp_eq_of_nonneg r ht.le]
    apply h.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds ht] with u hu
    exact gluingCollarWarp_deriv_pos r hu

/-- The actual distributional second-derivative identity on a collar:
the smooth part is the warping function and the seam atom is `2 cosh r`.
Endpoint values and derivatives vanish, as for compactly supported tests. -/
theorem gluingCollarWarp_integral_second_deriv_sub
    (r : ℝ) {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφa : φ a = 0) (hφb : φ b = 0)
    (hφ'a : deriv φ a = 0) (hφ'b : deriv φ b = 0) :
    (∫ t in a..b, gluingCollarWarp r t * (deriv (deriv φ) t - φ t)) =
      2 * Real.cosh r * φ 0 := by
  have hφ' : ContDiff ℝ 1 (deriv φ) := hφ.deriv'
  have hdφ : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hdφ' : Differentiable ℝ (deriv φ) := hφ.differentiable_deriv_two
  have hφc : Continuous φ := hφ.continuous
  have hφ'c : Continuous (deriv φ) := hφ'.continuous
  have hφ''c : Continuous (deriv (deriv φ)) := hφ'.continuous_deriv_one
  let Wminus : ℝ → ℝ := fun t =>
    Real.sinh (r - t) * deriv φ t + Real.cosh (r - t) * φ t
  let Wplus : ℝ → ℝ := fun t =>
    Real.sinh (r + t) * deriv φ t - Real.cosh (r + t) * φ t
  have hminusDeriv (t : ℝ) : HasDerivAt Wminus
      (Real.sinh (r - t) * (deriv (deriv φ) t - φ t)) t := by
    have hfs : HasDerivAt (fun u : ℝ => Real.sinh (r - u)) (-Real.cosh (r - t)) t := by
      simpa using ((hasDerivAt_id t).const_sub r).sinh
    have hfc : HasDerivAt (fun u : ℝ => Real.cosh (r - u)) (-Real.sinh (r - t)) t := by
      simpa using ((hasDerivAt_id t).const_sub r).cosh
    convert (hfs.mul (hdφ' t).hasDerivAt).add (hfc.mul (hdφ t).hasDerivAt) using 1 <;>
      first | rfl | ring
  have hplusDeriv (t : ℝ) : HasDerivAt Wplus
      (Real.sinh (r + t) * (deriv (deriv φ) t - φ t)) t := by
    have hfs : HasDerivAt (fun u : ℝ => Real.sinh (r + u)) (Real.cosh (r + t)) t := by
      simpa using ((hasDerivAt_id t).const_add r).sinh
    have hfc : HasDerivAt (fun u : ℝ => Real.cosh (r + u)) (Real.sinh (r + t)) t := by
      simpa using ((hasDerivAt_id t).const_add r).cosh
    convert (hfs.mul (hdφ' t).hasDerivAt).sub (hfc.mul (hdφ t).hasDerivAt) using 1 <;>
      first | rfl | ring
  have hminusCont : Continuous Wminus := by
    exact ((Real.continuous_sinh.comp (continuous_const.sub continuous_id)).mul hφ'c).add
      ((Real.continuous_cosh.comp (continuous_const.sub continuous_id)).mul hφc)
  have hplusCont : Continuous Wplus := by
    exact ((Real.continuous_sinh.comp (continuous_const.add continuous_id)).mul hφ'c).sub
      ((Real.continuous_cosh.comp (continuous_const.add continuous_id)).mul hφc)
  have hcont : Continuous (fun t => gluingCollarWarp r t * (deriv (deriv φ) t - φ t)) :=
    (gluingCollarWarp_continuous r).mul (hφ''c.sub hφc)
  have hminusIntegral :
      (∫ t in a..0, gluingCollarWarp r t * (deriv (deriv φ) t - φ t)) =
        Wminus 0 - Wminus a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha.le hminusCont.continuousOn
    · intro t ht
      rw [gluingCollarWarp_eq_of_nonpos r ht.2.le]
      exact hminusDeriv t
    · exact hcont.intervalIntegrable a 0
  have hplusIntegral :
      (∫ t in 0..b, gluingCollarWarp r t * (deriv (deriv φ) t - φ t)) =
        Wplus b - Wplus 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hb.le hplusCont.continuousOn
    · intro t ht
      rw [gluingCollarWarp_eq_of_nonneg r ht.1.le]
      exact hplusDeriv t
    · exact hcont.intervalIntegrable 0 b
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable a 0) (hcont.intervalIntegrable 0 b), hminusIntegral, hplusIntegral]
  simp only [Wminus, Wplus, hφa, hφb, hφ'a, hφ'b, add_zero, sub_zero,
    mul_zero, zero_sub]
  ring

/-- The distribution `f'' - f` of the actual collar warp is nonnegative:
against a nonnegative compactly supported test function it evaluates to the
positive seam atom. This is the weak `F_{-1}`-convexity input for the
finite-strip curvature argument. -/
theorem gluingCollarWarp_distributional_FMinusOneConvex
    (r : ℝ) {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφa : φ a = 0) (hφb : φ b = 0)
    (hφ'a : deriv φ a = 0) (hφ'b : deriv φ b = 0)
    (hφnonneg : ∀ t ∈ Icc a b, 0 ≤ φ t) :
    0 ≤ ∫ t in a..b, gluingCollarWarp r t *
      (deriv (deriv φ) t - φ t) := by
  rw [gluingCollarWarp_integral_second_deriv_sub r ha hb hφ hφa hφb hφ'a hφ'b]
  exact mul_nonneg (mul_nonneg (by norm_num) (Real.cosh_pos r).le)
    (hφnonneg 0 ⟨ha.le, hb.le⟩)

#print axioms gluingCollarWarp_deriv_jump
#print axioms gluingCollarWarp_hasDerivAt_deriv
#print axioms gluingCollarWarp_integral_second_deriv_sub
#print axioms gluingCollarWarp_distributional_FMinusOneConvex

end SystolicGrowth
