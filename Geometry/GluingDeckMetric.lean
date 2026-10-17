module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingInteriorTransitions
public import Geometry.GluingCayleyMetric

@[expose] public section

/-!
# Actual deck invariance of the Poincare tangent form

The determinant-one Moebius action has imaginary part divided by the
squared norm of its denominator and derivative equal to the inverse square
of that denominator. These actual formulas prove invariance of the
half-plane tangent form on arbitrary pairs of tangent vectors. The final
consumer uses the true real `fderiv`; no metric-invariance premise or
distance-equivalence claim is introduced.
-/

open UpperHalfPlane
open scoped UpperHalfPlane MatrixGroups ComplexConjugate

namespace SystolicGrowth

/-- The actual imaginary part under the determinant-one deck action. -/
theorem gluingDeckComplex_im_smul (γ : SL(2, ℝ)) (z : ℍ) :
    (γ • z : ℍ).im = z.im / ‖(γ 1 0 : ℂ) * (z : ℂ) + (γ 1 1 : ℂ)‖ ^ 2 := by
  simpa [MulAction.compHom_smul_def, denom, Complex.normSq_eq_norm_sq] using
    z.im_smul_eq_div_normSq (Matrix.SpecialLinearGroup.mapGL ℝ γ)

/-- The actual derivative scales the Euclidean tangent form by precisely
the inverse fourth power of the denominator norm. -/
theorem norm_gluingDeckComplexDeriv_sq (γ : SL(2, ℝ)) (z : ℂ) :
    ‖gluingDeckComplexDeriv γ z‖ ^ 2 =
      1 / (‖(γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)‖ ^ 2) ^ 2 := by
  simp [gluingDeckComplexDeriv, norm_pow]

/-- The constructed derivative equivalence is multiplication by the
proved complex derivative coefficient. -/
@[simp] theorem gluingDeckComplexDerivEquiv_apply
    (γ : SL(2, ℝ)) (z v : ℂ) (hz : 0 < z.im) :
    gluingDeckComplexDerivEquiv γ z hz v = gluingDeckComplexDeriv γ z * v := by
  rfl

/-- The actual real-linear deck derivative preserves the half-plane
Poincare tangent form on arbitrary tangent vectors. -/
theorem gluingDeckComplexDerivEquiv_tangentForm_pullback
    (γ : SL(2, ℝ)) (z : ℍ) (v u : ℂ) :
    gluingHalfPlaneTangentForm (γ • z)
      (gluingDeckComplexDerivEquiv γ (z : ℂ) z.im_pos v)
      (gluingDeckComplexDerivEquiv γ (z : ℂ) z.im_pos u) =
      gluingHalfPlaneTangentForm z v u := by
  have hd : ‖(γ 1 0 : ℂ) * (z : ℂ) + (γ 1 1 : ℂ)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (gluingDeckComplex_denom_ne_zero γ z.im_pos)
  have hscale (a : ℂ) : ((a * v) * conj (a * u)).re =
      ‖a‖ ^ 2 * (v * conj u).re := by
    calc
      ((a * v) * conj (a * u)).re = (a * conj a * (v * conj u)).re := by
        rw [map_mul]
        congr 1
        ring
      _ = ‖a‖ ^ 2 * (v * conj u).re := by
        rw [Complex.mul_conj', ← Complex.ofReal_pow]
        exact Complex.re_ofReal_mul _ _
  change ((gluingDeckComplexDeriv γ (z : ℂ) * v) *
    conj (gluingDeckComplexDeriv γ (z : ℂ) * u)).re / (γ • z : ℍ).im ^ 2 =
      (v * conj u).re / z.im ^ 2
  rw [hscale, norm_gluingDeckComplexDeriv_sq, gluingDeckComplex_im_smul]
  field_simp [hd, z.im_pos.ne']

/-- Deck invariance stated with the true real analytic derivative of the
actual rational deck map used by the native interior transitions. -/
theorem gluingDeckComplex_fderiv_tangentForm_pullback
    (γ : SL(2, ℝ)) (z : ℍ) (v u : ℂ) :
    gluingHalfPlaneTangentForm (γ • z)
      (fderiv ℝ (gluingDeckComplex γ) (z : ℂ) v)
      (fderiv ℝ (gluingDeckComplex γ) (z : ℂ) u) =
      gluingHalfPlaneTangentForm z v u := by
  rw [(gluingDeckComplex_hasFDerivAt_equiv γ z.im_pos).fderiv]
  exact gluingDeckComplexDerivEquiv_tangentForm_pullback γ z v u

#print axioms gluingDeckComplex_im_smul
#print axioms gluingDeckComplexDerivEquiv_tangentForm_pullback
#print axioms gluingDeckComplex_fderiv_tangentForm_pullback

end SystolicGrowth
