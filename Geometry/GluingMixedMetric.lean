module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingPolarTransitions
public import Geometry.GluingPolarMetric
public import Geometry.GluingDeckMetric

@[expose] public section

/-!
# Actual mixed-chart compatibility of the Poincare and collar forms

Every native seam-to-interior overlap is locally an actual deck map after
one of the two signed polar lifts. Its genuine real derivative therefore
pulls the half-plane Poincare form back to the unchanged collar form
`dt² + sinh(r + |t|)² dθ²`. No metric compatibility, component index,
nonzero radius, or differential formula is supplied as a hypothesis.
This is a coordinate tangent-form identity, not a gluing-distance theorem.
-/

open Set Metric UpperHalfPlane Filter
open scoped UpperHalfPlane Topology MatrixGroups

namespace SystolicGrowth

/-- The actual derivative in the outgoing signed frame has the collar form. -/
theorem gluingOutgoingPolarLift_fderiv_tangentForm_pullback
    (o : ℍ) (r : ℝ) (x v u : ℂ) (ht : x.re ≤ 0) :
    gluingHalfPlaneTangentForm (gluingPolarPoint o (Circle.exp x.im) (r - x.re))
      (fderiv ℝ (gluingOutgoingPolarLift o r) x v)
      (fderiv ℝ (gluingOutgoingPolarLift o r) x u) =
        gluingCollarTangentForm r (x.re, x.im) (v.re, v.im) (u.re, u.im) := by
  have hD := (gluingPolarLift_hasFDerivAt o (gluingOutgoingPolarCoordinates r x)).comp x
    (gluingOutgoingPolarCoordinates_hasFDerivAt r x)
  change HasFDerivAt (gluingOutgoingPolarLift o r) _ x at hD
  rw [hD.fderiv]
  simpa [gluingOutgoingPolarCoordinateDeriv, ContinuousLinearEquiv.smulLeft,
    gluingOutgoingPolarCoordinates] using
      gluingPolarLift_outgoing_tangentForm_pullback o r x.re x.im ht
        (v.re, v.im) (u.re, u.im)

/-- The reflected incoming signed frame has the same actual collar form. -/
theorem gluingIncomingPolarLift_fderiv_tangentForm_pullback
    (o : ℍ) (r : ℝ) (x v u : ℂ) (ht : 0 ≤ x.re) :
    gluingHalfPlaneTangentForm (gluingPolarPoint o (Circle.exp (-x.im)) (r + x.re))
      (fderiv ℝ (gluingIncomingPolarLift o r) x v)
      (fderiv ℝ (gluingIncomingPolarLift o r) x u) =
        gluingCollarTangentForm r (x.re, x.im) (v.re, v.im) (u.re, u.im) := by
  have hD := (gluingPolarLift_hasFDerivAt o (gluingIncomingPolarCoordinates r x)).comp x
    (gluingIncomingPolarCoordinates_hasFDerivAt r x)
  change HasFDerivAt (gluingIncomingPolarLift o r) _ x at hD
  rw [hD.fderiv]
  simpa [gluingIncomingPolarCoordinateDeriv, ContinuousLinearEquiv.smulLeft,
    gluingIncomingPolarCoordinates] using
      gluingPolarLift_incoming_tangentForm_pullback o r x.re x.im ht
        (v.re, v.im) (u.re, u.im)

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- The Poincare form in every actual interior chart pulls back through
the native mixed transition to the original signed collar form, on the
exact native source and arbitrary tangent vectors. -/
theorem seamInterior_transition_tangentForm_pullback
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : P.IsGluedInteriorComplexChart e)
    {x : ℂ} (hx : x ∈ ((P.seamAngularComplexChart k θ).symm.trans e).source)
    (v u : ℂ) :
    gluingHalfPlaneTangentForm
      (UpperHalfPlane.ofComplex (((P.seamAngularComplexChart k θ).symm.trans e) x))
      (fderiv ℝ ((P.seamAngularComplexChart k θ).symm.trans e) x v)
      (fderiv ℝ ((P.seamAngularComplexChart k θ).symm.trans e) x u) =
        gluingCollarTangentForm (gluingRadius C g) (x.re, x.im)
          (v.re, v.im) (u.re, u.im) := by
  rcases P.seamInterior_transition_eventually_eq_deck_polar k θ e he hx with
    ⟨o, γ, ht, hEq⟩ | ⟨o, γ, ht, hEq⟩
  · let z := gluingPolarPoint o (Circle.exp x.im) (gluingRadius C g - x.re)
    have hz : UpperHalfPlane.ofComplex
        (((P.seamAngularComplexChart k θ).symm.trans e) x) = γ • z := by
      rw [hEq.self_of_nhds]
      change UpperHalfPlane.ofComplex (gluingDeckComplex γ (z : ℂ)) = γ • z
      rw [gluingDeckComplex_coe, UpperHalfPlane.ofComplex_apply]
    rw [hz, hEq.fderiv_eq,
      fderiv_comp (f := gluingOutgoingPolarLift o (gluingRadius C g))
        (g := gluingDeckComplex γ) x
        (gluingDeckComplex_hasFDerivAt_equiv γ z.im_pos).differentiableAt
        ((gluingOutgoingPolarLift_contDiff o (gluingRadius C g)).differentiable
          (by simp)).differentiableAt]
    simp only [ContinuousLinearMap.comp_apply]
    exact (gluingDeckComplex_fderiv_tangentForm_pullback γ z _ _).trans
      (gluingOutgoingPolarLift_fderiv_tangentForm_pullback o (gluingRadius C g) x v u ht.le)
  · let z := gluingPolarPoint o (Circle.exp (-x.im)) (gluingRadius C g + x.re)
    have hz : UpperHalfPlane.ofComplex
        (((P.seamAngularComplexChart k θ).symm.trans e) x) = γ • z := by
      rw [hEq.self_of_nhds]
      change UpperHalfPlane.ofComplex (gluingDeckComplex γ (z : ℂ)) = γ • z
      rw [gluingDeckComplex_coe, UpperHalfPlane.ofComplex_apply]
    rw [hz, hEq.fderiv_eq,
      fderiv_comp (f := gluingIncomingPolarLift o (gluingRadius C g))
        (g := gluingDeckComplex γ) x
        (gluingDeckComplex_hasFDerivAt_equiv γ z.im_pos).differentiableAt
        ((gluingIncomingPolarLift_contDiff o (gluingRadius C g)).differentiable
          (by simp)).differentiableAt]
    simp only [ContinuousLinearMap.comp_apply]
    exact (gluingDeckComplex_fderiv_tangentForm_pullback γ z _ _).trans
      (gluingIncomingPolarLift_fderiv_tangentForm_pullback o (gluingRadius C g) x v u ht.le)

end ExerciseGluingPreparation

#print axioms gluingOutgoingPolarLift_fderiv_tangentForm_pullback
#print axioms gluingIncomingPolarLift_fderiv_tangentForm_pullback
#print axioms ExerciseGluingPreparation.seamInterior_transition_tangentForm_pullback

end SystolicGrowth
