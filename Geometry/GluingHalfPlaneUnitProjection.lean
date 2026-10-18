module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingDeckProjectiveAction
public import Geometry.GluingMetricSpinCover
public import Geometry.UnitTangentIsometryDiffeomorph
public import Geometry.HalfPlaneUnitTangentFrame

@[expose] public section

/-!
# The actual half-plane unit tangent projection

A genuine isometric identification of the pulled-back base metric with the
Poincaré plane supplies a smooth projection back to the original surface.
Its actual differential maps physical half-plane unit frames to the literal
base unit tangent bundle. No unit-bundle projection or deck invariance is
assumed. Constructing the replacement metric remains a separate obligation.
-/

open Bundle Manifold Riemannian UpperHalfPlane
open scoped Manifold ContDiff Topology MatrixGroups UpperHalfPlane

namespace SystolicGrowth

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- **Math.** The actual smooth base projection through the genuine
half-plane identification, not an independently chosen developing map. -/
def gluedHalfPlaneSmoothProjection
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ) :
    C^∞⟮modelWithCornersSelf ℝ ℂ, ℍ;
      modelWithCornersSelf ℝ ℂ, P.GluedCarrier⟯ :=
  (P.gluedUniversalCoverSmoothProjection x).comp Φ.symm.toContMDiffMap

@[simp] theorem gluedHalfPlaneSmoothProjection_apply
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ) (z : ℍ) :
    P.gluedHalfPlaneSmoothProjection x Φ z =
      P.gluedUniversalCoverSmoothProjection x (Φ.symm z) := rfl

/-- **Math.** The full derivative chain rule for the actual projection,
on every physical tangent vector. -/
theorem gluedHalfPlaneSmoothProjection_mfderiv
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ) (z : ℍ)
    (v : TangentSpace (modelWithCornersSelf ℝ ℂ) z) :
    mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
      (P.gluedHalfPlaneSmoothProjection x Φ) z v =
    mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
      (P.gluedUniversalCoverSmoothProjection x) (Φ.symm z)
      (mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) Φ.symm z v) := by
  exact mfderiv_comp_apply z
    ((P.gluedUniversalCoverSmoothProjection x).contMDiff.mdifferentiable (by simp) _)
    (Φ.symm.mdifferentiable (by simp) _) v

/-- **Math.** The genuine projection preserves the metric on every vector
pair, by the actual covering metric and the same-map half-plane isometry. -/
theorem gluedHalfPlaneSmoothProjection_isMetricPreserving
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (g0 : RiemannianMetric (modelWithCornersSelf ℝ ℂ) P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ)
    (hΦ : LeeLib.Ch02.IsIsometry
      ((P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).coveringMetric g0)
      upperHalfPlanePoincareMetric Φ) :
    LeeLib.Ch02.IsMetricPreserving upperHalfPlanePoincareMetric g0
      (P.gluedHalfPlaneSmoothProjection x Φ) := by
  intro z
  ext v w
  rw [LeeLib.Ch02.pullbackForm_apply]
  change g0.inner (P.gluedUniversalCoverSmoothProjection x (Φ.symm z))
    (mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
      (P.gluedHalfPlaneSmoothProjection x Φ) z v)
    (mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
      (P.gluedHalfPlaneSmoothProjection x Φ) z w) = _
  rw [P.gluedHalfPlaneSmoothProjection_mfderiv, P.gluedHalfPlaneSmoothProjection_mfderiv]
  have hπ := ((P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).isRiemannianCovering_coveringMetric g0).2
  rw [hπ.inner_mfderiv, hΦ.symm.inner_mfderiv]

/-- **Math.** Project a physical Poincaré unit frame by the genuine
differential into the original base metric's real unit tangent bundle. -/
def gluedHalfPlaneUnitProjection
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (g0 : RiemannianMetric (modelWithCornersSelf ℝ ℂ) P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ)
    (hΦ : LeeLib.Ch02.IsIsometry
      ((P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).coveringMetric g0)
      upperHalfPlanePoincareMetric Φ) (q : HalfPlaneTangentFrame) :
    P.MetricUnitTangentCarrier g0.toContinuousRiemannianMetric :=
  ⟨tangentMap (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
      (P.gluedHalfPlaneSmoothProjection x Φ) (halfPlaneUnitTangentHomeomorph q).val,
    ((P.gluedHalfPlaneSmoothProjection_isMetricPreserving x g0 Φ hΦ).inner_mfderiv
      q.point (halfPlaneUnitTangentHomeomorph q).val.snd
        (halfPlaneUnitTangentHomeomorph q).val.snd).trans
      (halfPlaneUnitTangentHomeomorph q).property⟩

/-- **Math.** Continuity holds in the genuine tangent total-space topology,
not in a separately imposed product topology. -/
theorem gluedHalfPlaneUnitProjection_continuous
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (g0 : RiemannianMetric (modelWithCornersSelf ℝ ℂ) P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ)
    (hΦ : LeeLib.Ch02.IsIsometry
      ((P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).coveringMetric g0)
      upperHalfPlanePoincareMetric Φ) :
    Continuous (P.gluedHalfPlaneUnitProjection x g0 Φ hΦ) :=
  (((P.gluedHalfPlaneSmoothProjection x Φ).contMDiff.continuous_tangentMap
    (by simp)).comp
      (continuous_subtype_val.comp halfPlaneUnitTangentHomeomorph.continuous)).subtype_mk _

@[simp] theorem gluedHalfPlaneUnitProjection_val
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (g0 : RiemannianMetric (modelWithCornersSelf ℝ ℂ) P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ)
    (hΦ : LeeLib.Ch02.IsIsometry
      ((P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).coveringMetric g0)
      upperHalfPlanePoincareMetric Φ) (q : HalfPlaneTangentFrame) :
    (P.gluedHalfPlaneUnitProjection x g0 Φ hΦ q).val =
      ⟨P.gluedHalfPlaneSmoothProjection x Φ q.point,
        mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
          (P.gluedHalfPlaneSmoothProjection x Φ) q.point
          (halfPlaneUnitTangentHomeomorph q).val.snd⟩ := rfl

@[simp] theorem gluedHalfPlaneUnitProjection_proj
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (g0 : RiemannianMetric (modelWithCornersSelf ℝ ℂ) P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ)
    (hΦ : LeeLib.Ch02.IsIsometry
      ((P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).coveringMetric g0)
      upperHalfPlanePoincareMetric Φ) (q : HalfPlaneTangentFrame) :
    (P.gluedHalfPlaneUnitProjection x g0 Φ hΦ q).val.proj =
      P.gluedUniversalCoverSmoothProjection x (Φ.symm q.point) := rfl

end ExerciseGluingPreparation

#print axioms ExerciseGluingPreparation.gluedHalfPlaneSmoothProjection_isMetricPreserving
#print axioms ExerciseGluingPreparation.gluedHalfPlaneUnitProjection
#print axioms ExerciseGluingPreparation.gluedHalfPlaneUnitProjection_continuous
#print axioms ExerciseGluingPreparation.gluedHalfPlaneUnitProjection_val

end

end SystolicGrowth
