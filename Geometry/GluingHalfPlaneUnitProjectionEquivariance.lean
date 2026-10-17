module

public import Geometry.GluingDeckProjectiveAction
public import Geometry.HalfPlaneProjectiveTangentAction
public import Geometry.GluingHalfPlaneUnitProjection

@[expose] public section

/-!
# Genuine deck invariance of the half-plane unit projection

The projective unit-frame action is the actual derivative of the transported
smooth deck diffeomorphism. Differentiating the original covering projection
identity gives the required tangent-projection invariance, with no equivariance
or unit-projection invariance supplied as an extra hypothesis.
-/

open Bundle Manifold Riemannian UpperHalfPlane Set
open scoped Manifold ContDiff Topology MatrixGroups UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- **Math.** The actual projective deck action on genuine Poincaré unit
frames is the full real manifold differential of the transported original
smooth deck map. -/
theorem gluedUniversalCoverProjectiveDeckHom_unit_vector
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (g0 : RiemannianMetric (modelWithCornersSelf ℝ ℂ) P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ)
    (hΦ : LeeLib.Ch02.IsIsometry
      ((P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).coveringMetric g0)
      upperHalfPlanePoincareMetric Φ)
    (τ : P.gluedUniversalCoverDeckGroup x) (q : HalfPlaneTangentFrame) :
    (halfPlaneUnitTangentHomeomorph
      (P.gluedUniversalCoverProjectiveDeckHom x g0 Φ hΦ τ • q)).val.snd =
      mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
        (P.gluedUniversalCoverDeckConjugateDiffeomorph x Φ τ) q.point
        (halfPlaneUnitTangentHomeomorph q).val.snd := by
  let d := P.gluedUniversalCoverDeckConjugateDiffeomorph x Φ τ
  have hd := upperHalfPlane_chartReading_hasFDerivAt_real
    (d.mdifferentiable (by simp) q.point)
  have heq : (fun w : ℂ => (d (UpperHalfPlane.ofComplex w) : ℂ)) =
      projectiveHalfPlaneComplex (P.gluedUniversalCoverProjectiveDeckHom x g0 Φ hΦ τ) := by
    funext w
    exact congrArg UpperHalfPlane.coe
      (P.gluedUniversalCoverProjectiveDeckHom_smul x g0 Φ hΦ τ
        (UpperHalfPlane.ofComplex w)).symm
  have hderiv := hd.fderiv
  rw [heq] at hderiv
  rw [projective_halfPlaneUnitTangentHomeomorph_smul_vector, hderiv]
  rfl

/-- **Math.** The literal transported endpoint projection is unchanged by
each actual deck-conjugate map. -/
theorem gluedUniversalCoverHalfPlaneProjection_comp_deckConjugate
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ) (τ : P.gluedUniversalCoverDeckGroup x) :
    (fun z : ℍ => P.gluedUniversalCoverSmoothProjection x (Φ.symm z)) ∘
      (P.gluedUniversalCoverDeckConjugateDiffeomorph x Φ τ) =
        (fun z : ℍ => P.gluedUniversalCoverSmoothProjection x (Φ.symm z)) := by
  funext z
  change P.gluedUniversalCoverSmoothProjection x
    (Φ.symm (Φ (τ.val (Φ.symm z)))) =
      P.gluedUniversalCoverSmoothProjection x (Φ.symm z)
  rw [Φ.symm_apply_apply]
  exact τ.property _

/-- **Math.** Differentiating the true endpoint projection identity gives
invariance of its full tangent pushforward under the original deck action.
Both differentiability inputs are the actual smooth projection and actual
deck-conjugate diffeomorphism. -/
theorem gluedUniversalCoverHalfPlaneProjection_mfderiv_deckConjugate
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ) (τ : P.gluedUniversalCoverDeckGroup x)
    (z : ℍ) (v : TangentSpace (modelWithCornersSelf ℝ ℂ) z) :
    mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
      (fun p : ℍ => P.gluedUniversalCoverSmoothProjection x (Φ.symm p))
      (P.gluedUniversalCoverDeckConjugateDiffeomorph x Φ τ z)
      (mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
        (P.gluedUniversalCoverDeckConjugateDiffeomorph x Φ τ) z v) =
      mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
        (fun p : ℍ => P.gluedUniversalCoverSmoothProjection x (Φ.symm p)) z v := by
  let f := fun p : ℍ => P.gluedUniversalCoverSmoothProjection x (Φ.symm p)
  let d := P.gluedUniversalCoverDeckConjugateDiffeomorph x Φ τ
  have hf : MDifferentiable (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) f := by
    have hproj := (P.gluedUniversalCoverSmoothProjection x).contMDiff
    exact (hproj.comp Φ.symm.contMDiff).mdifferentiable (by simp)
  have hd := d.mdifferentiable (by simp)
  have hchain := mfderiv_comp_apply z (hf (d z)) (hd z) v
  have hcomp : f ∘ d = f := P.gluedUniversalCoverHalfPlaneProjection_comp_deckConjugate x Φ τ
  rw [hcomp] at hchain
  exact hchain.symm

/-- **Math.** The actual half-plane unit tangent projection is invariant
under every genuine projective deck element. This is equality in the literal
base unit tangent total bundle, derived from the true projection identity
and its full derivative chain rule. -/
theorem gluedHalfPlaneUnitProjection_projective_deck_invariant
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (g0 : RiemannianMetric (modelWithCornersSelf ℝ ℂ) P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ)
    (hΦ : LeeLib.Ch02.IsIsometry
      ((P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).coveringMetric g0)
      upperHalfPlanePoincareMetric Φ)
    (τ : P.gluedUniversalCoverDeckGroup x) (q : HalfPlaneTangentFrame) :
    P.gluedHalfPlaneUnitProjection x g0 Φ hΦ
        (P.gluedUniversalCoverProjectiveDeckHom x g0 Φ hΦ τ • q) =
      P.gluedHalfPlaneUnitProjection x g0 Φ hΦ q := by
  let d := P.gluedUniversalCoverDeckConjugateDiffeomorph x Φ τ
  have hpoint : (P.gluedUniversalCoverProjectiveDeckHom x g0 Φ hΦ τ • q).point =
      d q.point := by
    rw [projective_halfPlaneTangentFrame_smul_point,
      P.gluedUniversalCoverProjectiveDeckHom_smul]
    rfl
  have hbase : P.gluedHalfPlaneSmoothProjection x Φ
      (P.gluedUniversalCoverProjectiveDeckHom x g0 Φ hΦ τ • q).point =
      P.gluedHalfPlaneSmoothProjection x Φ q.point := by
    rw [hpoint]
    exact congrFun (P.gluedUniversalCoverHalfPlaneProjection_comp_deckConjugate x Φ τ) q.point
  apply Subtype.ext
  rw [P.gluedHalfPlaneUnitProjection_val, P.gluedHalfPlaneUnitProjection_val]
  refine TotalSpace.ext hbase ?_
  apply heq_of_eq
  change mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
    (P.gluedHalfPlaneSmoothProjection x Φ)
    (P.gluedUniversalCoverProjectiveDeckHom x g0 Φ hΦ τ • q).point
    (halfPlaneUnitTangentHomeomorph
      (P.gluedUniversalCoverProjectiveDeckHom x g0 Φ hΦ τ • q)).val.snd =
    mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
      (P.gluedHalfPlaneSmoothProjection x Φ) q.point
      (halfPlaneUnitTangentHomeomorph q).val.snd
  rw [hpoint, P.gluedUniversalCoverProjectiveDeckHom_unit_vector]
  exact P.gluedUniversalCoverHalfPlaneProjection_mfderiv_deckConjugate x Φ τ
    q.point (halfPlaneUnitTangentHomeomorph q).val.snd

#print axioms gluedUniversalCoverProjectiveDeckHom_unit_vector
#print axioms gluedUniversalCoverHalfPlaneProjection_mfderiv_deckConjugate
#print axioms gluedHalfPlaneUnitProjection_projective_deck_invariant

end SystolicGrowth.ExerciseGluingPreparation
