module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingInteriorMetric
public import Mathlib.LinearAlgebra.Complex.Orientation

@[expose] public section

/-!
# Orientation of the actual interior chart transitions

The native coordinate transition is locally one genuine SL₂ deck action.
Its real derivative is complex multiplication by `1 / (c z + d)²`, whose
determinant is the positive squared norm of that coefficient. Mathlib's
standard complex-plane orientation is therefore preserved on the exact
native overlap, without an oriented-transition hypothesis.
-/

open Set Filter UpperHalfPlane
open scoped Topology UpperHalfPlane MatrixGroups

namespace SystolicGrowth

/-- The real determinant of the actual deck differential is precisely the
squared norm of its complex derivative coefficient. -/
theorem gluingDeckComplexDerivEquiv_det (γ : SL(2, ℝ)) {z : ℂ} (hz : 0 < z.im) :
    LinearMap.det (gluingDeckComplexDerivEquiv γ z hz).toLinearEquiv.toLinearMap =
      Complex.normSq (gluingDeckComplexDeriv γ z) := by
  have heq : (gluingDeckComplexDerivEquiv γ z hz : ℂ →L[ℝ] ℂ) =
      (ContinuousLinearMap.toSpanSingleton ℂ (gluingDeckComplexDeriv γ z)).restrictScalars ℝ := by
    ext v
    change gluingDeckComplexDeriv γ z * v = v * gluingDeckComplexDeriv γ z
    exact mul_comm _ _
  change (gluingDeckComplexDerivEquiv γ z hz : ℂ →L[ℝ] ℂ).det = _
  rw [heq]
  simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_eq]

/-- The deck action's actual real Jacobian determinant is the exact
positive reciprocal fourth power of its denominator norm. -/
theorem gluingDeckComplex_fderiv_det (γ : SL(2, ℝ)) {z : ℂ} (hz : 0 < z.im) :
    LinearMap.det (fderiv ℝ (gluingDeckComplex γ) z).toLinearMap =
      1 / ‖(γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)‖ ^ 4 := by
  rw [(gluingDeckComplex_hasFDerivAt_equiv γ hz).fderiv]
  change LinearMap.det (gluingDeckComplexDerivEquiv γ z hz).toLinearEquiv.toLinearMap = _
  rw [gluingDeckComplexDerivEquiv_det, Complex.normSq_eq_norm_sq]
  simp [gluingDeckComplexDeriv, norm_pow, ← pow_mul]

/-- Every genuine upper-half-plane deck action has positive real
Jacobian determinant, including at arbitrary native interior coordinates. -/
theorem gluingDeckComplex_fderiv_det_pos (γ : SL(2, ℝ)) {z : ℂ} (hz : 0 < z.im) :
    0 < LinearMap.det (fderiv ℝ (gluingDeckComplex γ) z).toLinearMap := by
  rw [gluingDeckComplex_fderiv_det γ hz]
  exact div_pos zero_lt_one (pow_pos
    (norm_pos_iff.mpr (gluingDeckComplex_denom_ne_zero γ hz)) 4)

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- Actual interior-to-interior chart transitions have strictly positive
real Jacobian determinant on their literal native overlap. -/
theorem gluedInteriorComplexAtlas_transition_fderiv_det_pos
    (P : ExerciseGluingPreparation C g n genera X)
    (e e' : OpenPartialHomeomorph P.GluedCarrier ℂ)
    (he : P.IsGluedInteriorComplexChart e) (he' : P.IsGluedInteriorComplexChart e')
    (x : ℂ) (hx : x ∈ (e.symm.trans e').source) :
    0 < LinearMap.det (fderiv ℝ (e.symm.trans e') x).toLinearMap := by
  obtain ⟨hxim, γ, hγ⟩ :=
    P.gluedInteriorComplexAtlas_transition_eventually_eq_deck e e' he he' x hx
  rw [hγ.fderiv_eq]
  exact gluingDeckComplex_fderiv_det_pos γ hxim

/-- The actual derivative equivalence of each native interior transition
preserves Mathlib's standard complex-plane real orientation. -/
theorem gluedInteriorComplexAtlas_transition_hasFDerivAt_oriented
    (P : ExerciseGluingPreparation C g n genera X)
    (e e' : OpenPartialHomeomorph P.GluedCarrier ℂ)
    (he : P.IsGluedInteriorComplexChart e) (he' : P.IsGluedInteriorComplexChart e')
    (x : ℂ) (hx : x ∈ (e.symm.trans e').source) :
    ∃ D : ℂ ≃L[ℝ] ℂ,
      HasFDerivAt (e.symm.trans e') (D : ℂ →L[ℝ] ℂ) x ∧
      0 < LinearMap.det D.toLinearEquiv.toLinearMap ∧
      Orientation.map (Fin 2) D.toLinearEquiv Complex.orientation = Complex.orientation := by
  obtain ⟨hxim, γ, hγ⟩ :=
    P.gluedInteriorComplexAtlas_transition_eventually_eq_deck e e' he he' x hx
  let D := gluingDeckComplexDerivEquiv γ x hxim
  have hD : HasFDerivAt (e.symm.trans e') (D : ℂ →L[ℝ] ℂ) x :=
    (gluingDeckComplex_hasFDerivAt_equiv γ hxim).congr_of_eventuallyEq hγ
  have hdet : 0 < LinearMap.det D.toLinearEquiv.toLinearMap := by
    have h := P.gluedInteriorComplexAtlas_transition_fderiv_det_pos e e' he he' x hx
    rw [hD.fderiv] at h
    exact h
  refine ⟨D, hD, hdet, ?_⟩
  exact (Orientation.map_eq_iff_det_pos Complex.orientation D.toLinearEquiv
    (by simp [Complex.finrank_real_complex])).mpr hdet

end ExerciseGluingPreparation

#print axioms gluingDeckComplexDerivEquiv_det
#print axioms gluingDeckComplex_fderiv_det
#print axioms gluingDeckComplex_fderiv_det_pos
#print axioms ExerciseGluingPreparation.gluedInteriorComplexAtlas_transition_fderiv_det_pos
#print axioms ExerciseGluingPreparation.gluedInteriorComplexAtlas_transition_hasFDerivAt_oriented

end SystolicGrowth
