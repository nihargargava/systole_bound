module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingSeamDistance
public import Geometry.GluingCollarNativeMetricComparison
public import Geometry.MetricMidpointComparisonLocal

@[expose] public section

/-!
# Midpoint comparison in actual seam neighborhoods

The original seam charts locally preserve the intrinsic surface distance.
The native whole-collar comparison therefore gives small surface balls
with midpoint-cosh comparison, including at signed-radius zero. The
midpoint remains in the same surface ball and is fixed before its test point.
-/

open Set Metric

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- Every actual seam chart supplies a ball with midpoint-cosh comparison
for the original intrinsic surface metric, not the Euclidean chart metric. -/
theorem gluedIntrinsicMetric_seam_locally_midpoint_cosh_all_test
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (x : P.GluedCarrier) (hx : x ∈ (P.seamAngularComplexChart k θ).source) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    ∃ ε > 0, ∀ y ∈ ball x ε, ∀ z ∈ ball x ε,
      ∃ m ∈ ball x ε,
        dist y m = dist y z / 2 ∧ dist m z = dist y z / 2 ∧
        ∀ w ∈ ball x ε,
          2 * Real.cosh (dist y z / 2) * Real.cosh (dist w m) ≤
            Real.cosh (dist w y) + Real.cosh (dist w z) := by
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  letI : MetricSpace ℂ := gluingCollarModelMetricSpace P.radius_pos
  letI : PseudoMetricSpace ℂ :=
    (gluingCollarModelMetricSpace P.radius_pos).toPseudoMetricSpace
  exact exists_local_midpoint_cosh_all_test_of_local_isometry
    (P.seamAngularComplexChart k θ) x hx
    (P.gluedIntrinsicMetric_seam_locally_isometric k θ x hx)
    (gluingCollarModelMetric_exists_midpoint_cosh_all_test P.radius_pos)

#print axioms gluedIntrinsicMetric_seam_locally_midpoint_cosh_all_test

end SystolicGrowth.ExerciseGluingPreparation
