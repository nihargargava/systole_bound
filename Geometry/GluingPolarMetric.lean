module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingPolarSmooth
public import Geometry.GluingCollarRiemannian

@[expose] public section

/-!
# The actual polar pullback of the Poincare tangent form

The already differentiated polar map pulls the actual half-plane tangent
form back to `dt² + sinh(t)² dθ²`. This is an identity on arbitrary tangent
vectors, not merely radial or angular unit vectors. The final theorem uses
the actual `fderiv` of the actual polar point. No gluing distance or global
atlas assertion is made.
-/

open Set Metric UpperHalfPlane
open scoped UpperHalfPlane ComplexConjugate

namespace SystolicGrowth

/-- The actual disk differential in the radial/angular orthogonal frame. -/
theorem gluingPolarDiskLiftFDeriv_frame (p v : ℝ × ℝ) :
    gluingPolarDiskLiftFDeriv p v =
      Complex.exp ((p.2 : ℂ) * Complex.I) /
        (2 * (Real.cosh (p.1 / 2) : ℂ) ^ 2) *
          ((v.1 : ℂ) + Complex.I * (Real.sinh p.1 : ℂ) * (v.2 : ℂ)) := by
  have hc : (Real.cosh (p.1 / 2) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne'
  have hs : Real.sinh p.1 =
      2 * Real.sinh (p.1 / 2) * Real.cosh (p.1 / 2) := by
    convert Real.sinh_two_mul (p.1 / 2) using 1
    congr 1
    ring
  rw [gluingPolarDiskLiftFDeriv_apply, gluingPolarDiskLift, Real.tanh_eq_sinh_div_cosh, hs]
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat]
  field_simp [hc]

/-- The exact radial denominator of the disk Poincare form. -/
theorem one_sub_norm_gluingPolarDiskLift_sq (p : ℝ × ℝ) :
    1 - ‖gluingPolarDiskLift p‖ ^ 2 = 1 / Real.cosh (p.1 / 2) ^ 2 := by
  have hc : Real.cosh (p.1 / 2) ≠ 0 := (Real.cosh_pos _).ne'
  rw [gluingPolarDiskLift, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.tanh_eq_sinh_div_cosh]
  field_simp [hc]
  nlinarith [Real.cosh_sq_sub_sinh_sq (p.1 / 2)]

private theorem re_polar_frame_mul_conj (t : ℝ) (v u : ℝ × ℝ) :
    (((v.1 : ℂ) + Complex.I * (Real.sinh t : ℂ) * (v.2 : ℂ)) *
      conj ((u.1 : ℂ) + Complex.I * (Real.sinh t : ℂ) * (u.2 : ℂ))).re =
        v.1 * u.1 + Real.sinh t ^ 2 * v.2 * u.2 := by
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im]
  ring

/-- The explicit disk differential pulls back its actual tangent form. -/
theorem gluingPolarDiskLift_tangentForm_pullback (p v u : ℝ × ℝ) :
    gluingDiskTangentForm (gluingPolarDiskLift p)
      (gluingPolarDiskLiftFDeriv p v) (gluingPolarDiskLiftFDeriv p u) =
        v.1 * u.1 + Real.sinh p.1 ^ 2 * v.2 * u.2 := by
  let a : ℂ := Complex.exp ((p.2 : ℂ) * Complex.I) /
    (2 * (Real.cosh (p.1 / 2) : ℂ) ^ 2)
  have hc : Real.cosh (p.1 / 2) ≠ 0 := (Real.cosh_pos _).ne'
  have ha : ‖a‖ ^ 2 = 1 / (4 * (Real.cosh (p.1 / 2) ^ 2) ^ 2) := by
    have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
    simp only [a, norm_div, norm_mul, norm_pow, htwo, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.cosh_pos _), Complex.norm_exp_ofReal_mul_I]
    ring
  have hscale (x y : ℂ) : ((a * x) * conj (a * y)).re =
      ‖a‖ ^ 2 * (x * conj y).re := by
    calc
      ((a * x) * conj (a * y)).re = (a * conj a * (x * conj y)).re := by
        rw [map_mul]
        congr 1
        ring
      _ = ‖a‖ ^ 2 * (x * conj y).re := by
        rw [Complex.mul_conj', ← Complex.ofReal_pow]
        exact Complex.re_ofReal_mul _ _
  unfold gluingDiskTangentForm
  rw [gluingPolarDiskLiftFDeriv_frame, gluingPolarDiskLiftFDeriv_frame]
  change 4 * ((a * _) * conj (a * _)).re / _ = _
  rw [hscale, re_polar_frame_mul_conj, ha, one_sub_norm_gluingPolarDiskLift_sq]
  field_simp [hc]

/-- The actual half-plane polar differential has the hyperbolic polar tangent form. -/
theorem gluingPolarLift_tangentForm_pullback (o : ℍ) (p v u : ℝ × ℝ) :
    gluingHalfPlaneTangentForm (gluingPolarPoint o (Circle.exp p.2) p.1)
      (gluingPolarLiftFDeriv o p v) (gluingPolarLiftFDeriv o p u) =
        v.1 * u.1 + Real.sinh p.1 ^ 2 * v.2 * u.2 := by
  have hw : gluingPolarDiskLift p ∈ ball (0 : ℂ) 1 := by
    simpa only [mem_ball, dist_zero_right] using norm_gluingPolarDiskLift_lt_one p
  change gluingHalfPlaneTangentForm (gluingDiscChartInverse o ⟨gluingPolarDiskLift p, hw⟩)
    (gluingCenteredCayleyFDeriv o (gluingPolarDiskLift p) (gluingPolarDiskLiftFDeriv p v))
    (gluingCenteredCayleyFDeriv o (gluingPolarDiskLift p) (gluingPolarDiskLiftFDeriv p u)) = _
  rw [gluingDiscChartInverse_tangentForm_pullback]
  exact gluingPolarDiskLift_tangentForm_pullback p v u

/-- The same pullback stated with the genuine analytic derivative, not an assumed tangent map. -/
theorem gluingPolarLift_fderiv_tangentForm_pullback (o : ℍ) (p v u : ℝ × ℝ) :
    gluingHalfPlaneTangentForm (gluingPolarPoint o (Circle.exp p.2) p.1)
      (fderiv ℝ (gluingPolarLift o) p v) (fderiv ℝ (gluingPolarLift o) p u) =
        v.1 * u.1 + Real.sinh p.1 ^ 2 * v.2 * u.2 := by
  rw [(gluingPolarLift_hasFDerivAt o p).fderiv]
  exact gluingPolarLift_tangentForm_pullback o p v u

/-- In the outgoing signed collar frame `(r-t, θ)`, radial tangent components change sign. -/
theorem gluingPolarLift_outgoing_tangentForm_pullback (o : ℍ) (r t θ : ℝ)
    (ht : t ≤ 0) (v u : ℝ × ℝ) :
    gluingHalfPlaneTangentForm (gluingPolarPoint o (Circle.exp θ) (r - t))
      (gluingPolarLiftFDeriv o (r - t, θ) (-v.1, v.2))
      (gluingPolarLiftFDeriv o (r - t, θ) (-u.1, u.2)) =
        gluingCollarTangentForm r (t, θ) v u := by
  rw [gluingPolarLift_tangentForm_pullback o (r - t, θ) (-v.1, v.2) (-u.1, u.2),
    gluingCollarTangentForm_apply,
    gluingCollarWarp_eq_of_nonpos r ht]
  simp

/-- In the incoming reflected frame `(r+t, -θ)`, angular tangent components change sign. -/
theorem gluingPolarLift_incoming_tangentForm_pullback (o : ℍ) (r t θ : ℝ)
    (ht : 0 ≤ t) (v u : ℝ × ℝ) :
    gluingHalfPlaneTangentForm (gluingPolarPoint o (Circle.exp (-θ)) (r + t))
      (gluingPolarLiftFDeriv o (r + t, -θ) (v.1, -v.2))
      (gluingPolarLiftFDeriv o (r + t, -θ) (u.1, -u.2)) =
        gluingCollarTangentForm r (t, θ) v u := by
  rw [gluingPolarLift_tangentForm_pullback o (r + t, -θ) (v.1, -v.2) (u.1, -u.2),
    gluingCollarTangentForm_apply,
    gluingCollarWarp_eq_of_nonneg r ht]
  simp

#print axioms gluingPolarDiskLift_tangentForm_pullback
#print axioms gluingPolarLift_tangentForm_pullback
#print axioms gluingPolarLift_fderiv_tangentForm_pullback
#print axioms gluingPolarLift_outgoing_tangentForm_pullback
#print axioms gluingPolarLift_incoming_tangentForm_pullback

end SystolicGrowth
