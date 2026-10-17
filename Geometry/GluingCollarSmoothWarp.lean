module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarWarp
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-!
# Explicit smooth approximations of the literal collar warp

Replacing `|sinh t|` by `sqrt (sinh t ^ 2 + ε ^ 2)` gives a positive smooth
warp, uniformly within `cosh r * ε` of `sinh (r + |t|)`. Its actual second
derivative minus itself has an explicit nonnegative density for `0 < ε ≤ 1`.
These are radial smoothing facts, not a surface curvature theorem.
-/

namespace SystolicGrowth

/-- The explicit smoothing of the unchanged radial collar coefficient. -/
noncomputable def gluingCollarSmoothWarp (r ε t : ℝ) : ℝ :=
  Real.sinh r * Real.cosh t + Real.cosh r * Real.sqrt (Real.sinh t ^ 2 + ε ^ 2)

noncomputable def Internal.GluingCollarSmoothWarpHelpers.smoothCollarRoot (ε t : ℝ) : ℝ :=
  Real.sqrt (Real.sinh t ^ 2 + ε ^ 2)

private theorem smoothCollarRoot_pos {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    0 < Internal.GluingCollarSmoothWarpHelpers.smoothCollarRoot ε t := by
  apply Real.sqrt_pos.mpr
  exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hε)

private theorem smoothCollarRoot_sq (ε t : ℝ) :
    Internal.GluingCollarSmoothWarpHelpers.smoothCollarRoot ε t ^ 2 = Real.sinh t ^ 2 + ε ^ 2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The original nonsmooth coefficient has this exact hyperbolic expansion. -/
theorem gluingCollarWarp_eq_sinh_cosh_abs (r t : ℝ) :
    gluingCollarWarp r t = Real.sinh r * Real.cosh t + Real.cosh r * |Real.sinh t| := by
  rw [gluingCollarWarp, Real.sinh_add, Real.cosh_abs, ← Real.abs_sinh]

/-- Positivity does not require a restriction on the smoothing parameter. -/
theorem gluingCollarSmoothWarp_pos {r : ℝ} (hr : 0 < r) (ε t : ℝ) :
    0 < gluingCollarSmoothWarp r ε t := by
  exact add_pos_of_pos_of_nonneg
    (mul_pos (Real.sinh_pos_iff.mpr hr) (Real.cosh_pos t))
    (mul_nonneg (Real.cosh_pos r).le (Real.sqrt_nonneg _))

/-- Every differentiability order is valid because the square-root argument
stays strictly positive on the whole radial line. -/
theorem gluingCollarSmoothWarp_contDiff (r : ℝ) {ε : ℝ} (hε : 0 < ε)
    (n : WithTop ℕ∞) : ContDiff ℝ n (gluingCollarSmoothWarp r ε) := by
  have hroot : ContDiff ℝ n (Internal.GluingCollarSmoothWarpHelpers.smoothCollarRoot ε) := by
    apply ((Real.contDiff_sinh.pow 2).add contDiff_const).sqrt
    intro t
    exact (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hε)).ne'
  exact (contDiff_const.mul Real.contDiff_cosh).add (contDiff_const.mul hroot)

private theorem smoothCollarRoot_sub_abs_bounds {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) :
    0 ≤ Internal.GluingCollarSmoothWarpHelpers.smoothCollarRoot ε t - |Real.sinh t| ∧
      Internal.GluingCollarSmoothWarpHelpers.smoothCollarRoot ε t - |Real.sinh t| ≤ ε := by
  have hlo : |Real.sinh t| ≤ Internal.GluingCollarSmoothWarpHelpers.smoothCollarRoot ε t := by
    have h := Real.sqrt_le_sqrt
      (le_add_of_nonneg_right (a := Real.sinh t ^ 2) (sq_nonneg ε))
    rw [Real.sqrt_sq_eq_abs] at h
    exact h
  have hhi : Internal.GluingCollarSmoothWarpHelpers.smoothCollarRoot ε t ≤ |Real.sinh t| + ε := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨add_nonneg (abs_nonneg _) hε, ?_⟩
    nlinarith [sq_abs (Real.sinh t), mul_nonneg (abs_nonneg (Real.sinh t)) hε]
  exact ⟨sub_nonneg.mpr hlo, by linarith⟩

/-- The smoothing increases the original coefficient by at most `cosh r * ε`
at every radial point, with a bound independent of the point. -/
theorem gluingCollarSmoothWarp_sub_warp_bounds (r : ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) (t : ℝ) :
    0 ≤ gluingCollarSmoothWarp r ε t - gluingCollarWarp r t ∧
      gluingCollarSmoothWarp r ε t - gluingCollarWarp r t ≤ Real.cosh r * ε := by
  obtain ⟨hlo, hhi⟩ := smoothCollarRoot_sub_abs_bounds hε t
  rw [gluingCollarWarp_eq_sinh_cosh_abs]
  have heq : gluingCollarSmoothWarp r ε t -
      (Real.sinh r * Real.cosh t + Real.cosh r * |Real.sinh t|) =
      Real.cosh r * (Internal.GluingCollarSmoothWarpHelpers.smoothCollarRoot ε t - |Real.sinh t|) := by
    unfold gluingCollarSmoothWarp Internal.GluingCollarSmoothWarpHelpers.smoothCollarRoot
    ring
  rw [heq]
  exact ⟨mul_nonneg (Real.cosh_pos r).le hlo,
    mul_le_mul_of_nonneg_left hhi (Real.cosh_pos r).le⟩

/-- Global uniform approximation to the literal warp, including the seam. -/
theorem gluingCollarSmoothWarp_uniform_bound (r : ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) (t : ℝ) :
    |gluingCollarSmoothWarp r ε t - gluingCollarWarp r t| ≤ Real.cosh r * ε := by
  obtain ⟨hlo, hhi⟩ := gluingCollarSmoothWarp_sub_warp_bounds r hε t
  rwa [abs_of_nonneg hlo]

private theorem smoothCollarRoot_hasDerivAt {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    HasDerivAt (Internal.GluingCollarSmoothWarpHelpers.smoothCollarRoot ε)
      (Real.sinh t * Real.cosh t / Internal.GluingCollarSmoothWarpHelpers.smoothCollarRoot ε t) t := by
  have hpos : 0 < Real.sinh t ^ 2 + ε ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hε)
  have h := (((Real.hasDerivAt_sinh t).pow 2).add_const (ε ^ 2)).sqrt hpos.ne'
  have hne : Real.sqrt (Real.sinh t ^ 2 + ε ^ 2) ≠ 0 := (smoothCollarRoot_pos hε t).ne'
  convert h using 1
  · rfl
  · simp only [Internal.GluingCollarSmoothWarpHelpers.smoothCollarRoot, Pi.pow_apply]
    field_simp [hne]
    ring

/-- Exact first derivative of the smooth radial coefficient. -/
theorem gluingCollarSmoothWarp_hasDerivAt (r : ℝ) {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    HasDerivAt (gluingCollarSmoothWarp r ε)
      (Real.sinh r * Real.sinh t + Real.cosh r *
        (Real.sinh t * Real.cosh t / Real.sqrt (Real.sinh t ^ 2 + ε ^ 2))) t :=
  ((Real.hasDerivAt_cosh t).const_mul (Real.sinh r)).add
    ((smoothCollarRoot_hasDerivAt hε t).const_mul (Real.cosh r))

theorem gluingCollarSmoothWarp_deriv (r : ℝ) {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    deriv (gluingCollarSmoothWarp r ε) t =
      Real.sinh r * Real.sinh t + Real.cosh r *
        (Real.sinh t * Real.cosh t / Real.sqrt (Real.sinh t ^ 2 + ε ^ 2)) :=
  (gluingCollarSmoothWarp_hasDerivAt r hε t).deriv

private theorem smoothCollarRoot_hasDerivAt_derivative {ε : ℝ}
    (hε : 0 < ε) (t : ℝ) :
    HasDerivAt (fun s => Real.sinh s * Real.cosh s / Internal.GluingCollarSmoothWarpHelpers.smoothCollarRoot ε s)
      ((Real.cosh t ^ 2 + Real.sinh t ^ 2) / Internal.GluingCollarSmoothWarpHelpers.smoothCollarRoot ε t -
        (Real.sinh t ^ 2 * Real.cosh t ^ 2) / Internal.GluingCollarSmoothWarpHelpers.smoothCollarRoot ε t ^ 3) t := by
  have hn := (Real.hasDerivAt_sinh t).mul (Real.hasDerivAt_cosh t)
  have h := hn.div (smoothCollarRoot_hasDerivAt hε t) (smoothCollarRoot_pos hε t).ne'
  convert h using 1
  all_goals first
    | rfl
    | (dsimp only [Pi.mul_apply]; field_simp [(smoothCollarRoot_pos hε t).ne'])

/-- The genuine second derivative minus the warp has the explicit density
`cosh r * ε² * (1-ε²) / sqrt(sinh² t+ε²)³`. -/
theorem gluingCollarSmoothWarp_second_deriv_sub (r : ℝ) {ε : ℝ}
    (hε : 0 < ε) (t : ℝ) :
    deriv (deriv (gluingCollarSmoothWarp r ε)) t - gluingCollarSmoothWarp r ε t =
      Real.cosh r * ε ^ 2 * (1 - ε ^ 2) /
        Real.sqrt (Real.sinh t ^ 2 + ε ^ 2) ^ 3 := by
  have hfirst : deriv (gluingCollarSmoothWarp r ε) = fun s =>
      Real.sinh r * Real.sinh s + Real.cosh r *
        (Real.sinh s * Real.cosh s / Internal.GluingCollarSmoothWarpHelpers.smoothCollarRoot ε s) := by
    funext s
    exact gluingCollarSmoothWarp_deriv r hε s
  have hsecond := ((Real.hasDerivAt_sinh t).const_mul (Real.sinh r)).add
    ((smoothCollarRoot_hasDerivAt_derivative hε t).const_mul (Real.cosh r))
  have hsecondDeriv := hsecond.deriv
  change deriv (fun s => Real.sinh r * Real.sinh s + Real.cosh r *
    (Real.sinh s * Real.cosh s / Internal.GluingCollarSmoothWarpHelpers.smoothCollarRoot ε s)) t = _ at hsecondDeriv
  rw [hfirst, hsecondDeriv]
  change (Real.sinh r * Real.cosh t + Real.cosh r *
      ((Real.cosh t ^ 2 + Real.sinh t ^ 2) / Internal.GluingCollarSmoothWarpHelpers.smoothCollarRoot ε t -
        (Real.sinh t ^ 2 * Real.cosh t ^ 2) / Internal.GluingCollarSmoothWarpHelpers.smoothCollarRoot ε t ^ 3)) -
      (Real.sinh r * Real.cosh t + Real.cosh r * Internal.GluingCollarSmoothWarpHelpers.smoothCollarRoot ε t) =
    Real.cosh r * ε ^ 2 * (1 - ε ^ 2) / Internal.GluingCollarSmoothWarpHelpers.smoothCollarRoot ε t ^ 3
  have hsquare := smoothCollarRoot_sq ε t
  have hcosh := Real.cosh_sq t
  have hpoly : (Real.cosh t ^ 2 + Real.sinh t ^ 2) * Internal.GluingCollarSmoothWarpHelpers.smoothCollarRoot ε t ^ 2 -
      Real.sinh t ^ 2 * Real.cosh t ^ 2 - Internal.GluingCollarSmoothWarpHelpers.smoothCollarRoot ε t ^ 4 =
      ε ^ 2 * (1 - ε ^ 2) := by
    rw [show Internal.GluingCollarSmoothWarpHelpers.smoothCollarRoot ε t ^ 4 = (Internal.GluingCollarSmoothWarpHelpers.smoothCollarRoot ε t ^ 2) ^ 2 by ring,
      hsquare, hcosh]
    ring
  field_simp [(smoothCollarRoot_pos hε t).ne']
  linear_combination Real.cosh r * hpoly

/-- These actual smooth approximations satisfy the required radial curvature
inequality whenever their positive smoothing parameter is at most one. -/
theorem gluingCollarSmoothWarp_second_deriv_sub_nonneg (r : ℝ) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (t : ℝ) :
    0 ≤ deriv (deriv (gluingCollarSmoothWarp r ε)) t - gluingCollarSmoothWarp r ε t := by
  rw [gluingCollarSmoothWarp_second_deriv_sub r hε t]
  have hfactor : 0 ≤ 1 - ε ^ 2 := by nlinarith
  exact div_nonneg
    (mul_nonneg (mul_nonneg (Real.cosh_pos r).le (sq_nonneg ε)) hfactor)
    (pow_nonneg (Real.sqrt_nonneg _) 3)

#print axioms gluingCollarSmoothWarp_contDiff
#print axioms gluingCollarSmoothWarp_uniform_bound
#print axioms gluingCollarSmoothWarp_second_deriv_sub
#print axioms gluingCollarSmoothWarp_second_deriv_sub_nonneg

end SystolicGrowth
