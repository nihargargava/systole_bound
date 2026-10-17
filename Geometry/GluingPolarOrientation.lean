module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingPolarMetric
public import Geometry.GluingPolarTransitions
public import Geometry.GluingInteriorOrientation
public import Mathlib.LinearAlgebra.Complex.Determinant

@[expose] public section

/-!
# Orientation signs of the actual signed polar coordinates

The positive-radius polar differential has positive real determinant.
The outgoing radial reflection and incoming angular reflection each reverse
that sign. Native seam-to-interior transitions therefore have negative
determinant, since their remaining factor is a genuine positive-determinant
deck action. This records the signs of the existing charts; it does not
assume their unreflected mixed transitions preserve orientation.
-/

open Set Filter UpperHalfPlane
open scoped Topology UpperHalfPlane MatrixGroups

namespace SystolicGrowth

private theorem complex_real_det (D : ℂ →L[ℝ] ℂ) :
    LinearMap.det D.toLinearMap =
      (D 1).re * (D Complex.I).im - (D Complex.I).re * (D 1).im := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply]

private theorem complex_frame_det (D : ℂ →L[ℝ] ℂ) (A : ℂ) (s u v : ℝ)
    (hD : ∀ z : ℂ, D z = A * ((u * z.re : ℝ) + Complex.I * (s * v * z.im : ℝ))) :
    LinearMap.det D.toLinearMap = u * v * ‖A‖ ^ 2 * s := by
  rw [complex_real_det, hD, hD, Complex.sq_norm]
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

noncomputable def Internal.GluingPolarOrientationHelpers.polarDerivativeCoefficient (o : ℍ) (p : ℝ × ℝ) : ℂ :=
  gluingCenteredCayleyDeriv o (gluingPolarDiskLift p) *
    (Complex.exp ((p.2 : ℂ) * Complex.I) /
      (2 * (Real.cosh (p.1 / 2) : ℂ) ^ 2))

private theorem polarDerivativeCoefficient_ne_zero (o : ℍ) (p : ℝ × ℝ) :
    Internal.GluingPolarOrientationHelpers.polarDerivativeCoefficient o p ≠ 0 := by
  exact mul_ne_zero (gluingPolarLift_cayley_coefficient_ne_zero o p)
    (div_ne_zero (Complex.exp_ne_zero _) (mul_ne_zero (by norm_num)
      (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne'))))

private theorem polar_derivative_frame (o : ℍ) (p v : ℝ × ℝ) :
    gluingPolarLiftFDeriv o p v =
      Internal.GluingPolarOrientationHelpers.polarDerivativeCoefficient o p *
        ((v.1 : ℂ) + Complex.I * (Real.sinh p.1 : ℂ) * (v.2 : ℂ)) := by
  have hC (w : ℂ) :
      gluingCenteredCayleyFDeriv o (gluingPolarDiskLift p) w =
        gluingCenteredCayleyDeriv o (gluingPolarDiskLift p) * w := by
    simp [gluingCenteredCayleyFDeriv, smul_eq_mul, mul_comm]
  rw [gluingPolarLiftFDeriv, ContinuousLinearMap.comp_apply, hC,
    gluingPolarDiskLiftFDeriv_frame]
  simp [Internal.GluingPolarOrientationHelpers.polarDerivativeCoefficient, mul_assoc]

/-- The actual positive-radius polar differential preserves the standard
orientation when its radial/angular coordinates are identified with `ℂ`. -/
theorem gluingPolarLiftFDeriv_det_pos (o : ℍ) (p : ℝ × ℝ) (hp : 0 < p.1) :
    0 < LinearMap.det
      ((gluingPolarLiftFDeriv o p).comp
        (Complex.equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ)).toLinearMap := by
  rw [complex_frame_det _ (Internal.GluingPolarOrientationHelpers.polarDerivativeCoefficient o p) (Real.sinh p.1) 1 1 (by
    intro z
    simp [polar_derivative_frame, mul_assoc])]
  simp only [one_mul]
  exact mul_pos
    (sq_pos_of_pos (norm_pos_iff.mpr (polarDerivativeCoefficient_ne_zero o p)))
    (Real.sinh_pos_iff.mpr hp)

/-- The outgoing signed radius reverses the sign of the actual polar Jacobian. -/
theorem gluingOutgoingPolarLift_fderiv_det_neg (o : ℍ) (r : ℝ) (z : ℂ)
    (hz : 0 < r - z.re) :
    LinearMap.det (fderiv ℝ (gluingOutgoingPolarLift o r) z).toLinearMap < 0 := by
  have hD := (gluingPolarLift_hasFDerivAt o (gluingOutgoingPolarCoordinates r z)).comp z
    (gluingOutgoingPolarCoordinates_hasFDerivAt r z)
  change HasFDerivAt (gluingOutgoingPolarLift o r) _ z at hD
  rw [hD.fderiv]
  rw [complex_frame_det _ (Internal.GluingPolarOrientationHelpers.polarDerivativeCoefficient o (gluingOutgoingPolarCoordinates r z))
    (Real.sinh (r - z.re)) (-1) 1 (by
      intro w
      simp [polar_derivative_frame, gluingOutgoingPolarCoordinateDeriv,
        gluingOutgoingPolarCoordinates, ContinuousLinearEquiv.smulLeft, mul_assoc])]
  have hpos : 0 < ‖Internal.GluingPolarOrientationHelpers.polarDerivativeCoefficient o (gluingOutgoingPolarCoordinates r z)‖ ^ 2 *
      Real.sinh (r - z.re) :=
    mul_pos (sq_pos_of_pos (norm_pos_iff.mpr (polarDerivativeCoefficient_ne_zero o _)))
      (Real.sinh_pos_iff.mpr hz)
  linarith

/-- The incoming angular reflection also reverses the actual polar Jacobian. -/
theorem gluingIncomingPolarLift_fderiv_det_neg (o : ℍ) (r : ℝ) (z : ℂ)
    (hz : 0 < r + z.re) :
    LinearMap.det (fderiv ℝ (gluingIncomingPolarLift o r) z).toLinearMap < 0 := by
  have hD := (gluingPolarLift_hasFDerivAt o (gluingIncomingPolarCoordinates r z)).comp z
    (gluingIncomingPolarCoordinates_hasFDerivAt r z)
  change HasFDerivAt (gluingIncomingPolarLift o r) _ z at hD
  rw [hD.fderiv]
  rw [complex_frame_det _ (Internal.GluingPolarOrientationHelpers.polarDerivativeCoefficient o (gluingIncomingPolarCoordinates r z))
    (Real.sinh (r + z.re)) 1 (-1) (by
      intro w
      simp [polar_derivative_frame, gluingIncomingPolarCoordinateDeriv,
        gluingIncomingPolarCoordinates, ContinuousLinearEquiv.smulLeft, mul_assoc])]
  have hpos : 0 < ‖Internal.GluingPolarOrientationHelpers.polarDerivativeCoefficient o (gluingIncomingPolarCoordinates r z)‖ ^ 2 *
      Real.sinh (r + z.re) :=
    mul_pos (sq_pos_of_pos (norm_pos_iff.mpr (polarDerivativeCoefficient_ne_zero o _)))
      (Real.sinh_pos_iff.mpr hz)
  linarith

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- Every actual unreflected seam-to-interior transition reverses orientation.
Its overlap selects the signed polar branch, whose negative determinant is
multiplied by the positive determinant of the actual deck action. -/
theorem seamInterior_transition_fderiv_det_neg
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : P.IsGluedInteriorComplexChart e)
    {x : ℂ} (hx : x ∈ ((P.seamAngularComplexChart k θ).symm.trans e).source) :
    LinearMap.det
      (fderiv ℝ ((P.seamAngularComplexChart k θ).symm.trans e) x).toLinearMap < 0 := by
  rcases P.seamInterior_transition_eventually_eq_deck_polar k θ e he hx with
    ⟨o, γ, hsign, hEq⟩ | ⟨o, γ, hsign, hEq⟩
  · have him : 0 < (gluingOutgoingPolarLift o (gluingRadius C g) x).im :=
      (gluingPolarPoint o (Circle.exp x.im) (gluingRadius C g - x.re)).im_pos
    have hrad : 0 < gluingRadius C g - x.re := by linarith [P.radius_pos]
    rw [hEq.fderiv_eq, fderiv_comp x
      (gluingDeckComplex_hasFDerivAt_equiv γ him).differentiableAt
      (gluingOutgoingPolarLift_hasFDerivAt_equiv o (gluingRadius C g) x hrad).differentiableAt,
      ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp]
    exact mul_neg_of_pos_of_neg (gluingDeckComplex_fderiv_det_pos γ him)
      (gluingOutgoingPolarLift_fderiv_det_neg o (gluingRadius C g) x hrad)
  · have him : 0 < (gluingIncomingPolarLift o (gluingRadius C g) x).im :=
      (gluingPolarPoint o (Circle.exp (-x.im)) (gluingRadius C g + x.re)).im_pos
    have hrad : 0 < gluingRadius C g + x.re := by linarith [P.radius_pos]
    rw [hEq.fderiv_eq, fderiv_comp x
      (gluingDeckComplex_hasFDerivAt_equiv γ him).differentiableAt
      (gluingIncomingPolarLift_hasFDerivAt_equiv o (gluingRadius C g) x hrad).differentiableAt,
      ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp]
    exact mul_neg_of_pos_of_neg (gluingDeckComplex_fderiv_det_pos γ him)
      (gluingIncomingPolarLift_fderiv_det_neg o (gluingRadius C g) x hrad)

end ExerciseGluingPreparation

end SystolicGrowth
