module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCurvatureBoundedUniversalCover
public import Geometry.GluingOrientation
public import Mathlib.LinearAlgebra.Determinant

@[expose] public section

/-!
# Orientation of the actual smooth glued-cover deck transformations

The selected cover and base charts agree under the original endpoint
projection. Differentiating the actual deck projection identity therefore
makes its real differential the identity in these selected coordinates.
-/

open Bundle Manifold Riemannian Set
open scoped Manifold ContDiff Topology

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- **Math.** The original smooth deck transformation has identity
differential in the genuine projection-adapted selected charts. -/
theorem gluedUniversalCoverDeckDiffeomorph_mfderiv_eq_id
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (τ : P.gluedUniversalCoverDeckGroup x) (q : P.basedTopologicalUniversalCover x) :
    mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
      (P.gluedUniversalCoverDeckDiffeomorph x τ) q = ContinuousLinearMap.id ℝ ℂ := by
  let proj := P.gluedUniversalCoverProjection x
  let d := P.gluedUniversalCoverDeckDiffeomorph x τ
  have hproj : proj ∘ d = proj := funext τ.property
  have hd := mfderiv_comp q
    (((P.gluedUniversalCoverProjection_isLocalDiffeomorph x).contMDiff (d q)).mdifferentiableAt
      (by simp))
    ((d.contMDiff q).mdifferentiableAt (by simp))
  dsimp only [TangentSpace] at hd
  rw [P.gluedUniversalCoverProjection_mfderiv_eq_id x (d q),
    ContinuousLinearMap.id_comp] at hd
  rw [hproj,
    P.gluedUniversalCoverProjection_mfderiv_eq_id x q] at hd
  exact hd.symm

/-- **Math.** The actual deck differential's real Jacobian is exactly one. -/
theorem gluedUniversalCoverDeckDiffeomorph_mfderiv_det
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (τ : P.gluedUniversalCoverDeckGroup x) (q : P.basedTopologicalUniversalCover x) :
    LinearMap.det (mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
      (P.gluedUniversalCoverDeckDiffeomorph x τ) q).toLinearMap = 1 := by
  rw [P.gluedUniversalCoverDeckDiffeomorph_mfderiv_eq_id x τ q]
  exact LinearMap.det_id

/-- **Math.** Every original smooth deck transformation preserves the
local coordinate orientation, with no supplied orientation hypothesis. -/
theorem gluedUniversalCoverDeckDiffeomorph_mfderiv_det_pos
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (τ : P.gluedUniversalCoverDeckGroup x) (q : P.basedTopologicalUniversalCover x) :
    0 < LinearMap.det (mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
      (P.gluedUniversalCoverDeckDiffeomorph x τ) q).toLinearMap := by
  rw [P.gluedUniversalCoverDeckDiffeomorph_mfderiv_det x τ q]
  exact zero_lt_one

#print axioms gluedUniversalCoverDeckDiffeomorph_mfderiv_eq_id
#print axioms gluedUniversalCoverDeckDiffeomorph_mfderiv_det_pos

end
end SystolicGrowth.ExerciseGluingPreparation
