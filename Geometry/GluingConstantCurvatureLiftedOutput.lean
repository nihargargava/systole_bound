module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingConstantCurvatureCoverModel
public import Geometry.GluingMetricSpinLiftedOutput

@[expose] public section

/-!
# The actual constant-curvature metric supplies all geometric output fields

The genuine base metric determines its half-plane model, faithful marked
holonomy and coherent spin lift internally. The only remaining geometric
input is the systole-preserving constant-curvature metric itself; neither
a model identification nor a representation is supplied to this consumer.
-/

open Manifold Riemannian UpperHalfPlane
open scoped Manifold ContDiff Topology MatrixGroups UpperHalfPlane ENNReal

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

set_option backward.isDefEq.respectTransparency false

local instance : NeZero (Module.finrank ℝ ℂ) :=
  ⟨by rw [Complex.finrank_real_complex]; norm_num⟩

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}
  (P : ExerciseGluingPreparation C g n genera X)
  (hn : 2 ≤ n) (hsum : (∑ i, genera i) = g) (x : P.GluedCarrier)
  (g0 : RiemannianMetric (modelWithCornersSelf ℝ ℂ) P.GluedCarrier)
  (hK : ∀ a u v,
    g0.metricInner a u u * g0.metricInner a v v - (g0.metricInner a u v) ^ 2 =
      g0.metricInner a (g0.leviCivitaConnection.curvatureOperatorAt a u v v) u)
  (L : ℝ) (hL : 0 < L)
  (hsys : letI : MetricSpace P.GluedCarrier := LeeLib.Ch02.RiemannianMetric.toMetricSpace g0
    ENNReal.ofReal L ≤ metricHomotopySystole P.GluedCarrier)

/-- **Math.** Construct the actual marked free discrete SL₂ surface from
the genuine constant-curvature base metric and its geometric systole bound. -/
def gluedConstantCurvatureLiftedSurface : ClosedHyperbolicSurface g :=
  P.gluedMetricSpinLiftedSurface hn hsum x g0
    (P.gluedConstantCurvatureHalfPlaneDiffeomorph x g0 hK)
    (P.gluedConstantCurvatureHalfPlaneDiffeomorph_isIsometry x g0 hK)
    L hL hsys

/-- **Math.** The actual marked surface retains the geometric lower bound
on the metric homotopy systole, with no assumed lift or deck displacement. -/
theorem le_gluedConstantCurvatureLiftedSurface_systole :
    L ≤ (P.gluedConstantCurvatureLiftedSurface hn hsum x g0 hK L hL hsys).systole :=
  P.le_gluedMetricSpinLiftedSurface_systole hn hsum x g0
    (P.gluedConstantCurvatureHalfPlaneDiffeomorph x g0 hK)
    (P.gluedConstantCurvatureHalfPlaneDiffeomorph_isIsometry x g0 hK)
    L hL hsys

/-- **Math.** Produce every lifted-chain output field from the actual base
metric. Constructing such a metric for every prepared chain is still open. -/
def gluedConstantCurvatureLiftedOutput : ExerciseLiftedChainOutput g L :=
  P.gluedMetricSpinLiftedOutput hn hsum x g0
    (P.gluedConstantCurvatureHalfPlaneDiffeomorph x g0 hK)
    (P.gluedConstantCurvatureHalfPlaneDiffeomorph_isIsometry x g0 hK)
    L hL hsys

#print axioms gluedConstantCurvatureLiftedSurface
#print axioms le_gluedConstantCurvatureLiftedSurface_systole
#print axioms gluedConstantCurvatureLiftedOutput

end

end SystolicGrowth.ExerciseGluingPreparation
