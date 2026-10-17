module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingFinFermiCoordinates

@[expose] public section

/-!
# The actual inverse of the finite-curvature Fermi map

The recovered radial and transverse coordinates give a concrete inverse of
the Fermi parametrization on the whole upper half-plane.
-/

open UpperHalfPlane
open scoped UpperHalfPlane

namespace SystolicGrowth

/-- The explicit inverse-coordinate map for the scaled Fermi parametrization. -/
noncomputable def gluingFinFermiInverse (α : ℝ) (z : ℍ) : ℝ × ℝ :=
  (gluingFinFermiRadialCoord α z, gluingFinFermiTransverseCoord α z)

/-- The exponential of the recovered radial coordinate is the Euclidean
modulus of the upper-half-plane point. -/
theorem gluingFinFermiInverse_radial_exp {α : ℝ} (hα : 0 < α) (z : ℍ) :
    Real.exp (α * gluingFinFermiRadialCoord α z) = ‖(z : ℂ)‖ := by
  rw [gluingFinFermiRadialCoord]
  have hscale : α * (Real.log ‖(z : ℂ)‖ / α) =
      Real.log ‖(z : ℂ)‖ := by
    field_simp [hα.ne']
  rw [hscale, Real.exp_log (norm_pos_iff.mpr z.ne_zero)]

/-- The hyperbolic cosine of the recovered transverse coordinate is the
modulus divided by the positive height. -/
theorem gluingFinFermiInverse_transverse_cosh {α : ℝ} (hα : 0 < α) (z : ℍ) :
    Real.cosh (α * gluingFinFermiTransverseCoord α z) =
      ‖(z : ℂ)‖ / z.im := by
  have hscale : α * gluingFinFermiTransverseCoord α z =
      Real.arsinh (z.re / z.im) := by
    unfold gluingFinFermiTransverseCoord
    field_simp [hα.ne']
  have hsqrt : Real.sqrt (1 + (z.re / z.im) ^ 2) =
      ‖(z : ℂ)‖ / z.im := by
    rw [Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)]
    field_simp [z.im_ne_zero]
    rw [Complex.sq_norm, Complex.normSq_apply, UpperHalfPlane.coe_re,
      UpperHalfPlane.coe_im]
    ring
  rw [hscale, Real.cosh_arsinh, hsqrt]

/-- The explicit inverse is a right inverse on every upper-half-plane point:
applying the Fermi map to its recovered coordinates returns the original
point, not merely an equivalent point or a point in a dense image. -/
theorem gluingFinFermiPoint_inverse_right {α : ℝ} (hα : 0 < α) (z : ℍ) :
    gluingFinFermiPoint α (gluingFinFermiInverse α z).1
      (gluingFinFermiInverse α z).2 = z := by
  have hrad := gluingFinFermiInverse_radial_exp hα z
  have htan := gluingFinFermiTransverseCoord_tanh hα z
  have hcosh := gluingFinFermiInverse_transverse_cosh hα z
  apply UpperHalfPlane.ext_re_im
  · rw [gluingFinFermiPoint_re]
    change Real.exp (α * gluingFinFermiRadialCoord α z) *
      Real.tanh (α * gluingFinFermiTransverseCoord α z) = z.re
    rw [hrad, htan]
    have hn : ‖(z : ℂ)‖ ≠ 0 := ne_of_gt (norm_pos_iff.mpr z.ne_zero)
    field_simp
  · rw [gluingFinFermiPoint_im]
    change Real.exp (α * gluingFinFermiRadialCoord α z) /
      Real.cosh (α * gluingFinFermiTransverseCoord α z) = z.im
    rw [hrad, hcosh]
    have hn : ‖(z : ℂ)‖ ≠ 0 := ne_of_gt (norm_pos_iff.mpr z.ne_zero)
    field_simp

/-- Every point of the upper half-plane is attained by the actual Fermi map. -/
theorem gluingFinFermiPoint_surjective {α : ℝ} (hα : 0 < α) :
    Function.Surjective (fun p : ℝ × ℝ =>
      gluingFinFermiPoint α p.1 p.2) := by
  intro z
  exact ⟨gluingFinFermiInverse α z,
    gluingFinFermiPoint_inverse_right hα z⟩

/-- The already established coordinate reconstruction laws combine to give
the left-inverse identity on every Fermi-coordinate pair. -/
theorem gluingFinFermiInverse_point {α t u : ℝ} (hα : 0 < α) :
    gluingFinFermiInverse α (gluingFinFermiPoint α t u) = (t, u) := by
  apply Prod.ext
  · exact gluingFinFermiRadialCoord_point hα
  · exact gluingFinFermiTransverseCoord_point hα

#print axioms gluingFinFermiInverse_radial_exp
#print axioms gluingFinFermiInverse_transverse_cosh
#print axioms gluingFinFermiPoint_inverse_right
#print axioms gluingFinFermiPoint_surjective
#print axioms gluingFinFermiInverse_point

end SystolicGrowth
