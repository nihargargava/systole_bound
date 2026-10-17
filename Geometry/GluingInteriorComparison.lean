module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingInteriorDistance
public import Geometry.HyperbolicMidpointComparison
public import Geometry.MetricMidpointComparisonLocal

@[expose] public section

/-!
# Native midpoint comparison in glued interior neighborhoods

The actual interior chart is composed with the upper half-plane coordinate
section. Its proved local metric identification transports the hyperbolic
midpoint identity to a small ball in the original glued intrinsic metric.
The midpoint is constructed inside that same ball before every test point.
-/

open Set Metric
open scoped UpperHalfPlane

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- Each actual interior point has a native intrinsic neighborhood with
all-test midpoint-cosh comparison and midpoints in the same neighborhood. -/
theorem gluedIntrinsicMetric_interior_locally_midpoint_cosh_all_test
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : P.IsGluedInteriorComplexChart e)
    (x : P.GluedCarrier) (hx : x ∈ e.source) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    ∃ ε > 0, ∀ y ∈ ball x ε, ∀ z ∈ ball x ε,
      ∃ m ∈ ball x ε, dist y m = dist y z / 2 ∧ dist m z = dist y z / 2 ∧
        ∀ w ∈ ball x ε,
          2 * Real.cosh (dist y z / 2) * Real.cosh (dist w m) ≤
            Real.cosh (dist w y) + Real.cosh (dist w z) := by
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  let f := e.trans UpperHalfPlane.ofComplex
  have hx' : x ∈ f.source := by
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨hx, ?_⟩
    change e x ∈ ((↑) : ℍ → ℂ) '' univ
    exact ⟨P.gluedInteriorChartPoint e he x hx, mem_univ _, rfl⟩
  have hlocal : ∃ ρ > 0, ball x ρ ⊆ f.source ∧
      ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ, dist (f y) (f z) = dist y z := by
    obtain ⟨ρ, hρ, hball, hmetric⟩ :=
      P.gluedIntrinsicMetric_interior_locally_isometric e he x hx
    have hsource : ball x ρ ⊆ f.source := by
      intro y hy
      rw [OpenPartialHomeomorph.trans_source]
      refine ⟨hball hy, ?_⟩
      change e y ∈ ((↑) : ℍ → ℂ) '' univ
      exact ⟨P.gluedInteriorChartPoint e he y (hball hy), mem_univ _, rfl⟩
    refine ⟨ρ, hρ, hsource, ?_⟩
    intro y hy z hz
    have hycoord : f y = P.gluedInteriorChartPoint e he y (hball hy) :=
      UpperHalfPlane.ofComplex_apply_of_im_pos
        (P.gluedInteriorComplexChart_target_im_pos e he (e.map_source (hball hy)))
    have hzcoord : f z = P.gluedInteriorChartPoint e he z (hball hz) :=
      UpperHalfPlane.ofComplex_apply_of_im_pos
        (P.gluedInteriorComplexChart_target_im_pos e he (e.map_source (hball hz)))
    rw [hycoord, hzcoord]
    exact hmetric y hy z hz
  have hmid : ∀ a b : ℍ, ∃ m : ℍ,
      dist a m = dist a b / 2 ∧ dist m b = dist a b / 2 ∧
      ∀ w : ℍ, 2 * Real.cosh (dist a b / 2) * Real.cosh (dist w m) ≤
        Real.cosh (dist w a) + Real.cosh (dist w b) := by
    intro a b
    obtain ⟨m, ham, hmb, hcomparison⟩ := exists_hyperbolic_midpoint_cosh a b
    exact ⟨m, ham, hmb, fun w => (hcomparison w).le⟩
  exact exists_local_midpoint_cosh_all_test_of_local_isometry f x hx' hlocal hmid

#print axioms gluedIntrinsicMetric_interior_locally_midpoint_cosh_all_test

end SystolicGrowth.ExerciseGluingPreparation
