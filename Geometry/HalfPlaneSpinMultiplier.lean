module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingInteriorTransitions
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold

@[expose] public section

/-!
# The genuine Möbius tangent-action square root

The normalized inverse denominator gives an explicit SL₂ cocycle on the
original upper half-plane. Its square is the phase of the actual complex
derivative, and the central element `-I` acts by the opposite sign. These
identities construct the double-cover multiplier; they do not assume or
construct a spin trivialization of a surface.
-/

open UpperHalfPlane
open scoped MatrixGroups UpperHalfPlane

namespace SystolicGrowth

noncomputable section

/-- The denominator of the actual SL₂ Möbius action on the half-plane. -/
def halfPlaneSpinDenominator (A : SL(2, ℝ)) (z : ℍ) : ℂ :=
  (A 1 0 : ℂ) * (z : ℂ) + (A 1 1 : ℂ)

theorem halfPlaneSpinDenominator_ne_zero (A : SL(2, ℝ)) (z : ℍ) :
    halfPlaneSpinDenominator A z ≠ 0 :=
  gluingDeckComplex_denom_ne_zero A z.im_pos

/-- The denominator multiplication law uses the genuine intermediate
Möbius point, rather than a formal action or a chosen lift. -/
theorem halfPlaneSpinDenominator_mul (A B : SL(2, ℝ)) (z : ℍ) :
    halfPlaneSpinDenominator (A * B) z =
      halfPlaneSpinDenominator A (B • z) * halfPlaneSpinDenominator B z := by
  have h := denom_cocycle (Matrix.SpecialLinearGroup.mapGL ℝ A)
    (Matrix.SpecialLinearGroup.mapGL ℝ B) z.im_ne_zero
  rw [← map_mul] at h
  change halfPlaneSpinDenominator (A * B) z =
    ((A 1 0 : ℂ) * gluingDeckComplex B z + (A 1 1 : ℂ)) *
      halfPlaneSpinDenominator B z at h
  simpa only [gluingDeckComplex_coe, halfPlaneSpinDenominator] using h

@[simp] theorem halfPlaneSpinDenominator_one (z : ℍ) :
    halfPlaneSpinDenominator 1 z = 1 := by
  simp [halfPlaneSpinDenominator]

@[simp] theorem halfPlaneSpinDenominator_neg (A : SL(2, ℝ)) (z : ℍ) :
    halfPlaneSpinDenominator (-A) z = -halfPlaneSpinDenominator A z := by
  simp [halfPlaneSpinDenominator, Matrix.SpecialLinearGroup.coe_neg]
  ring

/-- The unit complex square-root multiplier of the genuine tangent action. -/
def halfPlaneSpinMultiplier (A : SL(2, ℝ)) (z : ℍ) : ℂ :=
  (‖halfPlaneSpinDenominator A z‖ : ℂ) / halfPlaneSpinDenominator A z

theorem norm_halfPlaneSpinMultiplier (A : SL(2, ℝ)) (z : ℍ) :
    ‖halfPlaneSpinMultiplier A z‖ = 1 := by
  rw [halfPlaneSpinMultiplier, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), div_self]
  exact norm_ne_zero_iff.mpr (halfPlaneSpinDenominator_ne_zero A z)

/-- The explicit multiplier obeys the full SL₂ cocycle identity. -/
theorem halfPlaneSpinMultiplier_mul (A B : SL(2, ℝ)) (z : ℍ) :
    halfPlaneSpinMultiplier (A * B) z =
      halfPlaneSpinMultiplier A (B • z) * halfPlaneSpinMultiplier B z := by
  simp only [halfPlaneSpinMultiplier, halfPlaneSpinDenominator_mul, norm_mul,
    Complex.ofReal_mul]
  rw [div_mul_div_comm]

@[simp] theorem halfPlaneSpinMultiplier_one (z : ℍ) :
    halfPlaneSpinMultiplier 1 z = 1 := by
  simp [halfPlaneSpinMultiplier]

/-- Negating the actual SL₂ representative negates its square-root
multiplier, even though it leaves the underlying Möbius map unchanged. -/
@[simp] theorem halfPlaneSpinMultiplier_neg (A : SL(2, ℝ)) (z : ℍ) :
    halfPlaneSpinMultiplier (-A) z = -halfPlaneSpinMultiplier A z := by
  simp [halfPlaneSpinMultiplier, div_neg]

@[simp] theorem halfPlaneSpinMultiplier_neg_one (z : ℍ) :
    halfPlaneSpinMultiplier (-1) z = -1 := by
  simp

/-- The square of the multiplier is the normalized coefficient of the
actual complex derivative computed from the genuine Möbius map. -/
theorem halfPlaneSpinMultiplier_sq_eq_normalized_coefficient
    (A : SL(2, ℝ)) (z : ℍ) :
    halfPlaneSpinMultiplier A z ^ 2 =
      gluingDeckComplexDeriv A z / (‖gluingDeckComplexDeriv A z‖ : ℂ) := by
  have hd := halfPlaneSpinDenominator_ne_zero A z
  have hn : (‖halfPlaneSpinDenominator A z‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hd)
  change ((‖halfPlaneSpinDenominator A z‖ : ℂ) / halfPlaneSpinDenominator A z) ^ 2 =
    (1 / halfPlaneSpinDenominator A z ^ 2) /
      (‖1 / halfPlaneSpinDenominator A z ^ 2‖ : ℂ)
  rw [norm_div, norm_one, norm_pow, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_pow]
  field_simp [hd, hn]

/-- The previous coefficient is the derivative of the literal complex
reading of the actual Möbius map, not an assumed tangent-action formula. -/
theorem halfPlaneSpinMultiplier_sq_eq_normalized_deriv
    (A : SL(2, ℝ)) (z : ℍ) :
    halfPlaneSpinMultiplier A z ^ 2 =
      deriv (gluingDeckComplex A) (z : ℂ) /
        (‖deriv (gluingDeckComplex A) (z : ℂ)‖ : ℂ) := by
  rw [(gluingDeckComplex_hasDerivAt A z.im_pos).deriv]
  exact halfPlaneSpinMultiplier_sq_eq_normalized_coefficient A z

/-- The square-root formula also holds for the unchanged native half-plane
action read through its actual inclusion and `ofComplex` chart inverse. -/
theorem halfPlaneSpinMultiplier_sq_eq_normalized_native_deriv
    (A : SL(2, ℝ)) (z : ℍ) :
    halfPlaneSpinMultiplier A z ^ 2 =
      deriv (fun w : ℂ => ((A • UpperHalfPlane.ofComplex w : ℍ) : ℂ)) (z : ℂ) /
        (‖deriv (fun w : ℂ => ((A • UpperHalfPlane.ofComplex w : ℍ) : ℂ))
          (z : ℂ)‖ : ℂ) := by
  have h := deriv_smul (g := Matrix.SpecialLinearGroup.mapGL ℝ A) (by simp) z
  have h' : deriv (fun w : ℂ => ((A • UpperHalfPlane.ofComplex w : ℍ) : ℂ)) (z : ℂ) =
      gluingDeckComplexDeriv A z := by
    simpa [gluingDeckComplexDeriv, denom, MulAction.compHom_smul_def] using h
  rw [h']
  exact halfPlaneSpinMultiplier_sq_eq_normalized_coefficient A z

/-- The explicit square-root multiplier varies continuously on the actual
half-plane, since its literal denominator never vanishes there. -/
theorem continuous_halfPlaneSpinMultiplier (A : SL(2, ℝ)) :
    Continuous (halfPlaneSpinMultiplier A) := by
  have hD : Continuous (halfPlaneSpinDenominator A) :=
    (continuous_const.mul UpperHalfPlane.continuous_coe).add continuous_const
  exact (Complex.continuous_ofReal.comp hD.norm).div hD
    (halfPlaneSpinDenominator_ne_zero A)

#print axioms halfPlaneSpinDenominator_mul
#print axioms norm_halfPlaneSpinMultiplier
#print axioms halfPlaneSpinMultiplier_mul
#print axioms halfPlaneSpinMultiplier_neg_one
#print axioms halfPlaneSpinMultiplier_sq_eq_normalized_deriv
#print axioms halfPlaneSpinMultiplier_sq_eq_normalized_native_deriv
#print axioms continuous_halfPlaneSpinMultiplier

end
end SystolicGrowth
