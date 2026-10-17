module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCayleyMetric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Complex.RealDeriv

@[expose] public section

/-!
# Smooth explicit angular lifts of the hyperbolic polar coordinates

The actual polar point, with its `Circle` angle lifted by `Circle.exp`, is a
globally smooth complex-valued map of the real radial and angular parameters.
Its proof uses the explicit centered Cayley formula and the strict disk norm
bound, not an assumed smooth polar chart. This file makes no global atlas or
glued-metric assertion.
-/

open UpperHalfPlane
open scoped UpperHalfPlane

namespace SystolicGrowth

/-- The actual lifted radial and angular coordinate in the centered disk. -/
noncomputable def gluingPolarDiskLift (p : ℝ × ℝ) : ℂ :=
  (Real.tanh (p.1 / 2) : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)

/-- The actual complex coordinate of the angularly lifted polar point. -/
noncomputable def gluingPolarLift (o : ℍ) (p : ℝ × ℝ) : ℂ :=
  (gluingPolarPoint o (Circle.exp p.2) p.1 : ℂ)

/-- Exact affine Cayley formula for the lifted polar coordinates. -/
theorem gluingPolarLift_eq (o : ℍ) (p : ℝ × ℝ) :
    gluingPolarLift o p = (o.re : ℂ) + (o.im : ℂ) *
      (Complex.I * (1 + gluingPolarDiskLift p) / (1 - gluingPolarDiskLift p)) := rfl

/-- Every lifted disk point is strictly inside the actual unit disk. -/
theorem norm_gluingPolarDiskLift_lt_one (p : ℝ × ℝ) :
    ‖gluingPolarDiskLift p‖ < 1 := by
  rw [gluingPolarDiskLift, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs]
  exact Real.abs_tanh_lt_one _

/-- The denominator in the actual polar formula never vanishes. -/
theorem one_sub_gluingPolarDiskLift_ne_zero (p : ℝ × ℝ) :
    1 - gluingPolarDiskLift p ≠ 0 := by
  apply Vendored.RiemannDynamics.one_sub_ne_zero_of_mem_ball
  simpa only [Metric.mem_ball, dist_zero_right] using norm_gluingPolarDiskLift_lt_one p

/-- Smoothness of the radial coefficient, obtained from its sinh/cosh ratio. -/
theorem gluingPolarRadius_contDiff :
    ContDiff ℝ ⊤ (fun t : ℝ => Real.tanh (t / 2)) := by
  simp_rw [Real.tanh_eq_sinh_div_cosh]
  exact (Real.contDiff_sinh.comp (contDiff_id.div_const 2)).div
    (Real.contDiff_cosh.comp (contDiff_id.div_const 2))
    (fun t => (Real.cosh_pos (t / 2)).ne')

/-- Smoothness of the actual lifted disk coordinates over the real scalars. -/
theorem gluingPolarDiskLift_contDiff : ContDiff ℝ ⊤ gluingPolarDiskLift := by
  have hr : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => (Real.tanh (p.1 / 2) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (gluingPolarRadius_contDiff.comp contDiff_fst)
  have hθ : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => (p.2 : ℂ) * Complex.I) :=
    (Complex.ofRealCLM.contDiff.comp contDiff_snd).mul contDiff_const
  exact hr.mul hθ.cexp

/-- The explicit polar map is smooth after lifting the angular coordinate. -/
theorem gluingPolarLift_contDiff (o : ℍ) : ContDiff ℝ ⊤ (gluingPolarLift o) := by
  change ContDiff ℝ ⊤ (fun p : ℝ × ℝ => (o.re : ℂ) + (o.im : ℂ) *
    (Complex.I * (1 + gluingPolarDiskLift p) / (1 - gluingPolarDiskLift p)))
  simp only [div_eq_mul_inv]
  exact contDiff_const.add (contDiff_const.mul
    ((contDiff_const.mul (contDiff_const.add gluingPolarDiskLift_contDiff)).mul
      ((contDiff_const.sub gluingPolarDiskLift_contDiff).inv
      one_sub_gluingPolarDiskLift_ne_zero)))

/-- The actual radial coefficient has the elementary hyperbolic derivative. -/
theorem gluingPolarRadius_hasDerivAt (t : ℝ) :
    HasDerivAt (fun x : ℝ => Real.tanh (x / 2))
      (1 / (2 * Real.cosh (t / 2) ^ 2)) t := by
  have hh : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) t :=
    (hasDerivAt_id t).div_const 2
  have h := hh.sinh.div hh.cosh (Real.cosh_pos (t / 2)).ne'
  have hcoeff :
      (Real.cosh (t / 2) * (1 / 2) * Real.cosh (t / 2) -
        Real.sinh (t / 2) * (Real.sinh (t / 2) * (1 / 2))) /
        Real.cosh (t / 2) ^ 2 = 1 / (2 * Real.cosh (t / 2) ^ 2) := by
    field_simp
    nlinarith [Real.cosh_sq_sub_sinh_sq (t / 2)]
  rw [hcoeff] at h
  simpa only [Real.tanh_eq_sinh_div_cosh, Pi.div_apply] using! h

/-- The explicit real differential of the lifted disk coordinates. -/
noncomputable def gluingPolarDiskLiftFDeriv (p : ℝ × ℝ) :
    (ℝ × ℝ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight
      (Complex.exp ((p.2 : ℂ) * Complex.I) /
        (2 * (Real.cosh (p.1 / 2) : ℂ) ^ 2)) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
      (Complex.I * gluingPolarDiskLift p)

/-- The radial and angular coefficients of the actual disk differential. -/
theorem gluingPolarDiskLiftFDeriv_apply (p v : ℝ × ℝ) :
    gluingPolarDiskLiftFDeriv p v =
      Complex.exp ((p.2 : ℂ) * Complex.I) /
          (2 * (Real.cosh (p.1 / 2) : ℂ) ^ 2) * (v.1 : ℂ) +
        Complex.I * gluingPolarDiskLift p * (v.2 : ℂ) := by
  simp only [gluingPolarDiskLiftFDeriv, add_apply,
    ContinuousLinearMap.smulRight_apply, Complex.real_smul]
  change (v.1 : ℂ) * (Complex.exp ((p.2 : ℂ) * Complex.I) /
      (2 * (Real.cosh (p.1 / 2) : ℂ) ^ 2)) +
      (v.2 : ℂ) * (Complex.I * gluingPolarDiskLift p) = _
  ring

/-- Differentiation of the actual disk lift, with explicit real coordinates. -/
theorem gluingPolarDiskLift_hasFDerivAt (p : ℝ × ℝ) :
    HasFDerivAt gluingPolarDiskLift (gluingPolarDiskLiftFDeriv p) p := by
  have hr := (gluingPolarRadius_hasDerivAt p.1).ofReal_comp.hasFDerivAt.comp p
    (hasFDerivAt_fst (𝕜 := ℝ) (p := p))
  have hθ : HasFDerivAt (fun q : ℝ × ℝ => (q.2 : ℂ) * Complex.I)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight Complex.I) p := by
    simpa only [Complex.real_smul] using!
      (hasFDerivAt_snd (𝕜 := ℝ) (p := p)).smul_const Complex.I
  have h := hr.mul hθ.cexp
  have hd := h.congr_fderiv (g' := gluingPolarDiskLiftFDeriv p) (by
    apply ContinuousLinearMap.ext
    intro v
    simp [gluingPolarDiskLiftFDeriv, gluingPolarDiskLift, Complex.real_smul]
    ring)
  exact hd

/-- The differential of the actual lifted polar point, composing the proved
disk differential with the actual centered inverse Cayley differential. -/
noncomputable def gluingPolarLiftFDeriv (o : ℍ) (p : ℝ × ℝ) :
    (ℝ × ℝ) →L[ℝ] ℂ :=
  (gluingCenteredCayleyFDeriv o (gluingPolarDiskLift p)).comp
    (gluingPolarDiskLiftFDeriv p)

/-- Real differentiation of the actual complex-valued lifted polar map. -/
theorem gluingPolarLift_hasFDerivAt (o : ℍ) (p : ℝ × ℝ) :
    HasFDerivAt (gluingPolarLift o) (gluingPolarLiftFDeriv o p) p := by
  have hw : gluingPolarDiskLift p ∈ Metric.ball (0 : ℂ) 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using norm_gluingPolarDiskLift_lt_one p
  change HasFDerivAt (gluingCenteredCayley o ∘ gluingPolarDiskLift)
    ((gluingCenteredCayleyFDeriv o (gluingPolarDiskLift p)).comp
      (gluingPolarDiskLiftFDeriv p)) p
  exact (gluingCenteredCayley_hasFDerivAt o hw).comp p
    (gluingPolarDiskLift_hasFDerivAt p)

/-- Explicit radial and angular coefficients of the actual polar differential. -/
theorem gluingPolarLiftFDeriv_apply (o : ℍ) (p v : ℝ × ℝ) :
    gluingPolarLiftFDeriv o p v =
      (o.im : ℂ) * 2 * Complex.I *
        (Complex.exp ((p.2 : ℂ) * Complex.I) /
            (2 * (Real.cosh (p.1 / 2) : ℂ) ^ 2) * (v.1 : ℂ) +
          Complex.I * gluingPolarDiskLift p * (v.2 : ℂ)) /
        (1 - gluingPolarDiskLift p) ^ 2 := by
  rw [gluingPolarLiftFDeriv, ContinuousLinearMap.comp_apply,
    gluingCenteredCayleyFDeriv_apply, gluingPolarDiskLiftFDeriv_apply]

#print axioms gluingPolarLift_contDiff
#print axioms gluingPolarRadius_hasDerivAt
#print axioms gluingPolarDiskLift_hasFDerivAt
#print axioms gluingPolarLift_hasFDerivAt
#print axioms gluingPolarLiftFDeriv_apply

end SystolicGrowth
