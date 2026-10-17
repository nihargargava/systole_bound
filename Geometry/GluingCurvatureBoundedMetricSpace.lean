module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingChainBoundedCurvatureMetric
public import Vendored.DoCarmo.LeeLib.Ch02.Distance
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Metric.RiemannianDistance

@[expose] public section

/-!
# The complete intrinsic metric of the curvature-bounded glued surface

The canonical metric induced by the constructed smooth tensor preserves the
actual glued carrier topology. Its extended distance is the already defined
patched path distance, and compactness gives completeness.
-/

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold
open scoped Manifold Topology ContDiff

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- **Math.** The canonical finite metric induced by the actual smooth
curvature-bounded tensor. The quotient's existing preconnectedness proves
finiteness; no additional connectedness premise is needed. -/
@[instance_reducible]
def gluedCurvatureBoundedIntrinsicMetricSpace
    (P : ExerciseGluingPreparation C g n genera X) : MetricSpace P.GluedCarrier :=
  LeeLib.Ch02.RiemannianMetric.toMetricSpace P.gluedCurvatureBoundedSmoothRiemannianMetric

/-- **Math.** The metric topology is definitionally the original quotient
topology on the actual glued carrier. -/
theorem gluedCurvatureBoundedIntrinsicMetricSpace_topology
    (P : ExerciseGluingPreparation C g n genera X) :
    P.gluedCurvatureBoundedIntrinsicMetricSpace.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace P.GluedCarrier) := rfl

/-- **Math.** The canonical ambient extended distance is exactly the
previously constructed intrinsic distance of the patched tangent metric. -/
theorem gluedCurvatureBoundedIntrinsicMetricSpace_edist
    (P : ExerciseGluingPreparation C g n genera X) (x y : P.GluedCarrier) :
    letI := P.gluedCurvatureBoundedIntrinsicMetricSpace
    edist x y = P.gluedCurvatureBoundedIntrinsicEDist x y := rfl

/-- **Math.** The actual smooth metric induces its canonical ambient
distance, satisfying the compatibility contract of the exponential APIs. -/
theorem gluedCurvatureBoundedIntrinsicMetricSpace_isRiemannianDist
    (P : ExerciseGluingPreparation C g n genera X) :
    letI := P.gluedCurvatureBoundedIntrinsicMetricSpace
    Riemannian.RiemannianMetric.IsRiemannianDist
      P.gluedCurvatureBoundedSmoothRiemannianMetric := by
  letI := P.gluedCurvatureBoundedIntrinsicMetricSpace
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) :
      P.GluedCarrier → Type) :=
    ⟨P.gluedCurvatureBoundedSmoothRiemannianMetric.toRiemannianMetric⟩
  change IsRiemannianManifold (modelWithCornersSelf ℝ ℂ) P.GluedCarrier
  exact ⟨fun _ _ => rfl⟩

/-- **Math.** Original quotient compactness holds for the canonical metric,
because its topology has not changed. -/
theorem gluedCurvatureBoundedIntrinsicMetricSpace_compact
    (P : ExerciseGluingPreparation C g n genera X) :
    letI := P.gluedCurvatureBoundedIntrinsicMetricSpace
    CompactSpace P.GluedCarrier := by
  letI := P.gluedCurvatureBoundedIntrinsicMetricSpace
  infer_instance

/-- **Math.** Compactness of the actual carrier makes the smooth intrinsic
metric complete, with no assumed completeness or distance comparison. -/
theorem gluedCurvatureBoundedIntrinsicMetricSpace_complete
    (P : ExerciseGluingPreparation C g n genera X) :
    letI := P.gluedCurvatureBoundedIntrinsicMetricSpace
    CompleteSpace P.GluedCarrier := by
  letI := P.gluedCurvatureBoundedIntrinsicMetricSpace
  letI : CompactSpace P.GluedCarrier := P.gluedCurvatureBoundedIntrinsicMetricSpace_compact
  infer_instance

/-- **Math.** A nonempty chain is connected in this same canonical metric
topology, using the already constructed connectivity of its retained pieces. -/
theorem gluedCurvatureBoundedIntrinsicMetricSpace_connected
    (P : ExerciseGluingPreparation C g n genera X) (hn : 0 < n) :
    letI := P.gluedCurvatureBoundedIntrinsicMetricSpace
    ConnectedSpace P.GluedCarrier := P.gluedCarrierConnectedSpace hn

/-- **Math.** Every patched intrinsic distance is finite, since it is the
extended distance of the actual canonical metric space. -/
theorem gluedCurvatureBoundedIntrinsicEDist_lt_top
    (P : ExerciseGluingPreparation C g n genera X) (x y : P.GluedCarrier) :
    P.gluedCurvatureBoundedIntrinsicEDist x y < ⊤ := by
  letI := P.gluedCurvatureBoundedIntrinsicMetricSpace
  rw [← P.gluedCurvatureBoundedIntrinsicMetricSpace_edist]
  exact edist_lt_top x y

#print axioms gluedCurvatureBoundedIntrinsicMetricSpace
#print axioms gluedCurvatureBoundedIntrinsicMetricSpace_edist
#print axioms gluedCurvatureBoundedIntrinsicMetricSpace_isRiemannianDist
#print axioms gluedCurvatureBoundedIntrinsicMetricSpace_complete
#print axioms gluedCurvatureBoundedIntrinsicMetricSpace_connected

end
end SystolicGrowth.ExerciseGluingPreparation
