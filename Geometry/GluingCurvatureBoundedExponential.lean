module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCurvatureBoundedMetricSpace
public import Geometry.GluingIntrinsicCurvature
public import Geometry.ExponentialGlobalPolarMetric
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Manifold.HadamardComplete

@[expose] public section

/-!
# The actual global exponential map of the patched glued metric

Compactness supplies completeness, and the intrinsic curvature bound makes
the genuine global exponential map a smooth local diffeomorphism at every
tangent vector. This does not assert global injectivity on the closed surface.
-/

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Riemannian
open scoped Manifold ContDiff Topology

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

local instance : NeZero (Module.finrank ℝ ℂ) :=
  ⟨by rw [Complex.finrank_real_complex]; norm_num⟩

/-- **Math.** The time-one endpoint of the complete patched-metric geodesic,
defined on the whole tangent plane, rather than only inside one base chart. -/
def gluedCurvatureBoundedExpMap (P : ExerciseGluingPreparation C g n genera X)
    (p : P.GluedCarrier) (v : ℂ) : P.GluedCarrier :=
  letI := P.gluedCurvatureBoundedIntrinsicMetricSpace
  letI : CompleteSpace P.GluedCarrier := P.gluedCurvatureBoundedIntrinsicMetricSpace_complete
  Exponential.expMapGlobal (I := modelWithCornersSelf ℝ ℂ)
    P.gluedCurvatureBoundedSmoothRiemannianMetric
    P.gluedCurvatureBoundedIntrinsicMetricSpace_isRiemannianDist p v

/-- **Math.** The actual exponential map is globally smooth; the proof uses
the metric package constructed on the literal glued carrier. -/
theorem gluedCurvatureBoundedExpMap_contMDiff
    (P : ExerciseGluingPreparation C g n genera X) (p : P.GluedCarrier) :
    ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ∞
      (P.gluedCurvatureBoundedExpMap p) := by
  letI := P.gluedCurvatureBoundedIntrinsicMetricSpace
  letI : CompleteSpace P.GluedCarrier := P.gluedCurvatureBoundedIntrinsicMetricSpace_complete
  exact Exponential.contMDiff_expMapGlobal
    P.gluedCurvatureBoundedSmoothRiemannianMetric
    P.gluedCurvatureBoundedIntrinsicMetricSpace_isRiemannianDist p

/-- **Math.** At every vector the actual patched-metric exponential is a
local diffeomorphism. Curvature and completeness are proved inputs, not
additional hypotheses on the preparation. -/
theorem gluedCurvatureBoundedExpMap_isLocalDiffeomorph
    (P : ExerciseGluingPreparation C g n genera X) (p : P.GluedCarrier) :
    IsLocalDiffeomorph (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ∞
      (P.gluedCurvatureBoundedExpMap p) := by
  letI := P.gluedCurvatureBoundedIntrinsicMetricSpace
  letI : CompleteSpace P.GluedCarrier := P.gluedCurvatureBoundedIntrinsicMetricSpace_complete
  intro v
  exact Jacobi.isLocalDiffeomorphAt_expMapGlobal_of_nonpos
    P.gluedCurvatureBoundedSmoothRiemannianMetric
    P.gluedCurvatureBoundedIntrinsicMetricSpace_isRiemannianDist p v
    (P.gluedCurvatureBoundedExpMap_contMDiff p)
    P.gluedCurvatureBounded_curvatureOperatorAt_pair_nonneg

@[simp] theorem gluedCurvatureBoundedExpMap_zero
    (P : ExerciseGluingPreparation C g n genera X) (p : P.GluedCarrier) :
    P.gluedCurvatureBoundedExpMap p 0 = p := by
  letI := P.gluedCurvatureBoundedIntrinsicMetricSpace
  letI : CompleteSpace P.GluedCarrier := P.gluedCurvatureBoundedIntrinsicMetricSpace_complete
  exact Exponential.expMapGlobal_zero
    P.gluedCurvatureBoundedSmoothRiemannianMetric
    P.gluedCurvatureBoundedIntrinsicMetricSpace_isRiemannianDist p

/-- **Math.** The actual complete patched-metric exponential maps its
initial metric-length ball onto the actual intrinsic ball. Global
injectivity is not assumed or concluded here. -/
theorem gluedCurvatureBoundedExpMap_image_initialLength_ball
    (P : ExerciseGluingPreparation C g n genera X) (p : P.GluedCarrier) (R : ℝ) :
    letI := P.gluedCurvatureBoundedIntrinsicMetricSpace
    (P.gluedCurvatureBoundedExpMap p) ''
        {v : ℂ | Real.sqrt (chartMetricInner
          P.gluedCurvatureBoundedSmoothRiemannianMetric p
          (extChartAt (modelWithCornersSelf ℝ ℂ) p p) v v) < R} =
      Metric.ball p R := by
  letI := P.gluedCurvatureBoundedIntrinsicMetricSpace
  letI : CompleteSpace P.GluedCarrier := P.gluedCurvatureBoundedIntrinsicMetricSpace_complete
  letI : ConnectedSpace P.GluedCarrier :=
    { toPreconnectedSpace := P.gluedCarrierPreconnectedSpace
      toNonempty := ⟨p⟩ }
  exact expMapGlobal_image_initialLength_ball
    P.gluedCurvatureBoundedSmoothRiemannianMetric
    P.gluedCurvatureBoundedIntrinsicMetricSpace_isRiemannianDist p R

#print axioms gluedCurvatureBoundedExpMap_contMDiff
#print axioms gluedCurvatureBoundedExpMap_isLocalDiffeomorph
#print axioms gluedCurvatureBoundedExpMap_zero
#print axioms gluedCurvatureBoundedExpMap_image_initialLength_ball

end
end SystolicGrowth.ExerciseGluingPreparation
