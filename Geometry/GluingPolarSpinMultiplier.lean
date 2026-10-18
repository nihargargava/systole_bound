module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingPolarMetric
public import Geometry.HalfPlaneSpinMultiplier

@[expose] public section

/-!
# The bounding spin multiplier of an actual polar disk

An explicit normalized denominator and half-angle construct the square
root of the genuine polar radial tangent direction. It is continuous in
the lifted angular coordinate and changes sign after one complete turn.
This is the bounding, antiperiodic collar restriction; no surface spin
structure or coherent holonomy lift is assumed.
-/

open UpperHalfPlane
open scoped UpperHalfPlane

namespace SystolicGrowth

noncomputable section

/-- The literal nonvanishing denominator of the centered polar disk. -/
def gluingPolarSpinDenominator (p : ℝ × ℝ) : ℂ :=
  1 - gluingPolarDiskLift p

theorem gluingPolarSpinDenominator_ne_zero (p : ℝ × ℝ) :
    gluingPolarSpinDenominator p ≠ 0 :=
  one_sub_gluingPolarDiskLift_ne_zero p

/-- An explicit unit square root of the polar radial direction. -/
def gluingPolarSpinMultiplier (p : ℝ × ℝ) : ℂ :=
  Complex.exp (((p.2 / 2 + Real.pi / 4 : ℝ) : ℂ) * Complex.I) *
    ((‖gluingPolarSpinDenominator p‖ : ℂ) / gluingPolarSpinDenominator p)

theorem norm_gluingPolarSpinMultiplier (p : ℝ × ℝ) :
    ‖gluingPolarSpinMultiplier p‖ = 1 := by
  simp only [gluingPolarSpinMultiplier, norm_mul, Complex.norm_exp_ofReal_mul_I,
    one_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)]
  exact div_self (norm_ne_zero_iff.mpr (gluingPolarSpinDenominator_ne_zero p))

private theorem polarHalfAngle_sq (θ : ℝ) :
    Complex.exp (((θ / 2 + Real.pi / 4 : ℝ) : ℂ) * Complex.I) ^ 2 =
      Complex.I * Complex.exp ((θ : ℂ) * Complex.I) := by
  rw [pow_two, ← Complex.exp_add]
  have hangle : (((θ / 2 + Real.pi / 4 : ℝ) : ℂ) * Complex.I) +
      (((θ / 2 + Real.pi / 4 : ℝ) : ℂ) * Complex.I) =
        (θ : ℂ) * Complex.I + (Real.pi : ℂ) / 2 * Complex.I := by
    push_cast
    ring
  rw [hangle, Complex.exp_add, Complex.exp_pi_div_two_mul_I, mul_comm]

/-- The original polar map's actual radial differential has this positive
scale times the centered denominator expression. -/
theorem gluingPolarLift_radial_fderiv_eq (o : ℍ) (p : ℝ × ℝ) :
    (fderiv ℝ (gluingPolarLift o) p) (1, 0) =
      (o.im / Real.cosh (p.1 / 2) ^ 2 : ℝ) *
        (Complex.I * Complex.exp ((p.2 : ℂ) * Complex.I) /
          gluingPolarSpinDenominator p ^ 2) := by
  rw [(gluingPolarLift_hasFDerivAt o p).fderiv, gluingPolarLiftFDeriv_apply]
  simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, add_zero]
  have hc : (Real.cosh (p.1 / 2) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne'
  simp only [Complex.ofReal_div, Complex.ofReal_pow, gluingPolarSpinDenominator]
  field_simp

private theorem polarRadialScale_pos (o : ℍ) (p : ℝ × ℝ) :
    0 < o.im / Real.cosh (p.1 / 2) ^ 2 :=
  div_pos o.im_pos (sq_pos_of_pos (Real.cosh_pos _))

/-- The metric-coordinate radial vector's norm is derived from its actual
differential and the positive centered Cayley scale. -/
theorem norm_gluingPolarLift_radial_fderiv (o : ℍ) (p : ℝ × ℝ) :
    ‖(fderiv ℝ (gluingPolarLift o) p) (1, 0)‖ =
      (o.im / Real.cosh (p.1 / 2) ^ 2) / ‖gluingPolarSpinDenominator p‖ ^ 2 := by
  rw [gluingPolarLift_radial_fderiv_eq, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (polarRadialScale_pos o p), norm_div, norm_mul,
    Complex.norm_I, Complex.norm_exp_ofReal_mul_I, norm_pow, one_mul]
  exact mul_one_div _ _

/-- The square root is of the actual radial tangent direction, obtained by
the verified differential of the literal original polar map. -/
theorem gluingPolarSpinMultiplier_sq_eq_normalized_radial_fderiv
    (o : ℍ) (p : ℝ × ℝ) :
    gluingPolarSpinMultiplier p ^ 2 =
      (fderiv ℝ (gluingPolarLift o) p) (1, 0) /
        (‖(fderiv ℝ (gluingPolarLift o) p) (1, 0)‖ : ℂ) := by
  have hd := gluingPolarSpinDenominator_ne_zero p
  have hn : (‖gluingPolarSpinDenominator p‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hd)
  have ho : (o.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr o.im_pos.ne'
  have hc : (Real.cosh (p.1 / 2) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne'
  rw [gluingPolarSpinMultiplier, mul_pow, polarHalfAngle_sq,
    norm_gluingPolarLift_radial_fderiv, gluingPolarLift_radial_fderiv_eq]
  simp only [Complex.ofReal_div, Complex.ofReal_pow]
  field_simp [hd, hn, ho, hc]

theorem gluingPolarSpinDenominator_add_two_pi (ρ θ : ℝ) :
    gluingPolarSpinDenominator (ρ, θ + 2 * Real.pi) =
      gluingPolarSpinDenominator (ρ, θ) := by
  simp only [gluingPolarSpinDenominator, gluingPolarDiskLift]
  congr 2
  push_cast
  rw [add_mul, Complex.exp_add]
  simp

/-- One literal angular turn reverses the actual square root while the
radial vector itself returns to its original direction. -/
theorem gluingPolarSpinMultiplier_add_two_pi (ρ θ : ℝ) :
    gluingPolarSpinMultiplier (ρ, θ + 2 * Real.pi) =
      -gluingPolarSpinMultiplier (ρ, θ) := by
  have hangle : (((θ + 2 * Real.pi) / 2 + Real.pi / 4 : ℝ) : ℂ) * Complex.I =
      (((θ / 2 + Real.pi / 4 : ℝ) : ℂ) * Complex.I) + (Real.pi : ℂ) * Complex.I := by
    push_cast
    ring
  simp only [gluingPolarSpinMultiplier, gluingPolarSpinDenominator_add_two_pi,
    hangle, Complex.exp_add_pi_mul_I, neg_mul]

/-- Antiperiodicity is proved for the actual explicit function, rather than
imposed as boundary spin data. -/
theorem gluingPolarSpinMultiplier_antiperiodic (ρ : ℝ) :
    Function.Antiperiodic (fun θ : ℝ => gluingPolarSpinMultiplier (ρ, θ))
      (2 * Real.pi) :=
  gluingPolarSpinMultiplier_add_two_pi ρ

theorem continuous_gluingPolarSpinMultiplier : Continuous gluingPolarSpinMultiplier := by
  have hD : Continuous gluingPolarSpinDenominator :=
    continuous_const.sub gluingPolarDiskLift_contDiff.continuous
  have hθ : Continuous (fun p : ℝ × ℝ =>
      (((p.2 / 2 + Real.pi / 4 : ℝ) : ℂ) * Complex.I)) :=
    (Complex.continuous_ofReal.comp ((continuous_snd.div_const 2).add continuous_const)).mul
      continuous_const
  exact hθ.cexp.mul ((Complex.continuous_ofReal.comp hD.norm).div hD
    gluingPolarSpinDenominator_ne_zero)

#print axioms gluingPolarLift_radial_fderiv_eq
#print axioms gluingPolarSpinMultiplier_sq_eq_normalized_radial_fderiv
#print axioms gluingPolarSpinMultiplier_add_two_pi
#print axioms gluingPolarSpinMultiplier_antiperiodic
#print axioms continuous_gluingPolarSpinMultiplier

end
end SystolicGrowth
