module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingHalfPlaneUnitProjection

@[expose] public section

/-!
# Actual physical unit-fiber identification

The actual differential of the smooth half-plane projection is invertible.
It therefore identifies its physical unit circle with the original metric's
literal unit tangent fiber, with the inherited tangent total-space topology.
-/

open Bundle Manifold Riemannian UpperHalfPlane
open scoped Manifold ContDiff Topology UpperHalfPlane

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- **Math.** The genuine invertible projection differential is the
composition of the inverse half-plane differential and the covering-sheet
differential, not a separately supplied linear map. -/
def gluedHalfPlaneProjectionTangentEquiv
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ) (z : ℍ) : ℂ ≃L[ℝ] ℂ :=
  (Φ.symm.mfderivToContinuousLinearEquiv (by simp) z).trans
    ((P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).mfderivEquiv (Φ.symm z))

theorem gluedHalfPlaneProjectionTangentEquiv_apply
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ) (z : ℍ) (v : ℂ) :
    P.gluedHalfPlaneProjectionTangentEquiv x Φ z v =
      mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
        (P.gluedHalfPlaneSmoothProjection x Φ) z v := by
  rw [gluedHalfPlaneProjectionTangentEquiv, ContinuousLinearEquiv.trans_apply]
  let L : ℂ ≃L[ℝ] ℂ := Φ.symm.mfderivToContinuousLinearEquiv (by simp) z
  let K : ℂ ≃L[ℝ] ℂ :=
    (P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).mfderivEquiv (Φ.symm z)
  have hL : (L : ℂ →L[ℝ] ℂ) =
      mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) Φ.symm z :=
    Φ.symm.mfderivToContinuousLinearEquiv_coe (by simp)
  have hK : (K : ℂ →L[ℝ] ℂ) =
      mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
        (P.gluedUniversalCoverSmoothProjection x) (Φ.symm z) :=
    IsLocalDiffeomorph.mfderivToContinuousLinearEquiv_coe
      (P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).isLocalDiffeomorph
      (by simp) (Φ.symm z)
  change K (L v) = _
  calc
    K (L v) = mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
        (P.gluedUniversalCoverSmoothProjection x) (Φ.symm z) (L v) :=
      congrArg (fun A : ℂ →L[ℝ] ℂ => A (L v)) hK
    _ = mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
        (P.gluedUniversalCoverSmoothProjection x) (Φ.symm z)
        (mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) Φ.symm z v) :=
      congrArg (mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
        (P.gluedUniversalCoverSmoothProjection x) (Φ.symm z))
        (congrArg (fun A : ℂ →L[ℝ] ℂ => A v) hL)
    _ = _ := (P.gluedHalfPlaneSmoothProjection_mfderiv x Φ z v).symm

variable (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
  (g0 : RiemannianMetric (modelWithCornersSelf ℝ ℂ) P.GluedCarrier)
  (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
    modelWithCornersSelf ℝ ℂ⟯ ℍ)
  (hΦ : LeeLib.Ch02.IsIsometry
    ((P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).coveringMetric g0)
    upperHalfPlanePoincareMetric Φ)

/-- **Math.** The literal metric unit-fiber subtype in the original
tangent total bundle, over the projected half-plane point. -/
abbrev HalfPlaneProjectedMetricUnitFiber (z : ℍ) :=
  {v : P.MetricUnitTangentCarrier g0.toContinuousRiemannianMetric //
    v.val.proj = P.gluedHalfPlaneSmoothProjection x Φ z}

/-- **Math.** The actual projection of a physical phase at a fixed point. -/
def gluedHalfPlaneMetricFiberParam (z : ℍ) (u : Circle) :
    P.HalfPlaneProjectedMetricUnitFiber x g0 Φ z :=
  ⟨P.gluedHalfPlaneUnitProjection x g0 Φ hΦ ⟨z, u⟩, rfl⟩

theorem gluedHalfPlaneMetricFiberParam_continuous (z : ℍ) :
    Continuous (P.gluedHalfPlaneMetricFiberParam x g0 Φ hΦ z) := by
  have hframe : Continuous (fun u : Circle => (⟨z, u⟩ : HalfPlaneTangentFrame)) :=
    halfPlaneTangentFrameHomeomorph.symm.continuous.comp (continuous_const.prodMk continuous_id)
  exact ((P.gluedHalfPlaneUnitProjection_continuous x g0 Φ hΦ).comp hframe).subtype_mk _

theorem gluedHalfPlaneMetricFiberParam_injective (z : ℍ) :
    Function.Injective (P.gluedHalfPlaneMetricFiberParam x g0 Φ hΦ z) := by
  intro u v huv
  have hvector := congrArg
    (fun w : P.HalfPlaneProjectedMetricUnitFiber x g0 Φ z => (w.val.val.snd : ℂ)) huv
  change mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
    (P.gluedHalfPlaneSmoothProjection x Φ) z (z.im • (u : ℂ)) =
      mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
        (P.gluedHalfPlaneSmoothProjection x Φ) z (z.im • (v : ℂ)) at hvector
  rw [← P.gluedHalfPlaneProjectionTangentEquiv_apply,
    ← P.gluedHalfPlaneProjectionTangentEquiv_apply] at hvector
  have hphysical := (P.gluedHalfPlaneProjectionTangentEquiv x Φ z).injective hvector
  have hphase := congrArg (fun w : ℂ => z.im⁻¹ • w) hphysical
  simp only [smul_smul, inv_mul_cancel₀ z.im_pos.ne', one_smul] at hphase
  exact Circle.coe_injective hphase

/-- **Math.** Every genuine base unit tangent has a physical phase
preimage, using the inverse of the actual full differential. -/
theorem gluedHalfPlaneMetricFiberParam_surjective (z : ℍ) :
    Function.Surjective (P.gluedHalfPlaneMetricFiberParam x g0 Φ hΦ z) := by
  intro v
  let L := P.gluedHalfPlaneProjectionTangentEquiv x Φ z
  let w : ℂ := L.symm v.val.val.snd
  have hunit : upperHalfPlanePoincareMetric.inner z w w = 1 := by
    have h := (P.gluedHalfPlaneSmoothProjection_isMetricPreserving x g0 Φ hΦ).inner_mfderiv z w w
    rw [← P.gluedHalfPlaneProjectionTangentEquiv_apply] at h
    have hL : L w = v.val.val.snd := L.apply_symm_apply _
    change g0.inner (P.gluedHalfPlaneSmoothProjection x Φ z) (L w) (L w) = _ at h
    rw [hL] at h
    have hv := v.val.property
    change g0.inner v.val.val.proj (v.val.val.snd : ℂ) (v.val.val.snd : ℂ) = 1 at hv
    rw [v.property] at hv
    exact h.symm.trans hv
  let wu : HalfPlaneUnitTangentCarrier := ⟨⟨z, w⟩, hunit⟩
  let u := (halfPlaneUnitTangentFrame wu).phase
  have hphysical : (halfPlaneUnitTangentHomeomorph ⟨z, u⟩).val.snd = w :=
    congrArg (fun q : HalfPlaneUnitTangentCarrier => (q.val.snd : ℂ))
      (halfPlaneFrameUnitTangent_frame wu)
  refine ⟨u, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  refine TotalSpace.ext v.property.symm ?_
  apply heq_of_eq
  change mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
    (P.gluedHalfPlaneSmoothProjection x Φ) z
    (halfPlaneUnitTangentHomeomorph ⟨z, u⟩).val.snd = v.val.val.snd
  rw [hphysical, ← P.gluedHalfPlaneProjectionTangentEquiv_apply]
  exact L.apply_symm_apply _

/-- **Math.** The physical half-plane unit circle is homeomorphic to the
actual projected metric unit fiber, with no fiber map supplied as data. -/
def gluedHalfPlaneMetricFiberHomeomorph (z : ℍ) :
    Circle ≃ₜ P.HalfPlaneProjectedMetricUnitFiber x g0 Φ z :=
  IsHomeomorph.homeomorph (P.gluedHalfPlaneMetricFiberParam x g0 Φ hΦ z)
    (isHomeomorph_iff_continuous_bijective.mpr
      ⟨P.gluedHalfPlaneMetricFiberParam_continuous x g0 Φ hΦ z,
        P.gluedHalfPlaneMetricFiberParam_injective x g0 Φ hΦ z,
        P.gluedHalfPlaneMetricFiberParam_surjective x g0 Φ hΦ z⟩)

@[simp] theorem gluedHalfPlaneMetricFiberHomeomorph_apply (z : ℍ) (u : Circle) :
    (P.gluedHalfPlaneMetricFiberHomeomorph x g0 Φ hΦ z u).val =
      P.gluedHalfPlaneUnitProjection x g0 Φ hΦ ⟨z, u⟩ := rfl

#print axioms gluedHalfPlaneProjectionTangentEquiv_apply
#print axioms gluedHalfPlaneMetricFiberParam_surjective
#print axioms gluedHalfPlaneMetricFiberHomeomorph
#print axioms gluedHalfPlaneMetricFiberHomeomorph_apply

end

end SystolicGrowth.ExerciseGluingPreparation
