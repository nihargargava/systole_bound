module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.MetricTriangleBoundaryComparison
public import Mathlib.Topology.Order.ProjIcc

@[expose] public section

/-!
# Uniqueness of genuine constant-speed segments

Two segments with the same endpoints are the two edges of a degenerate
triangle. The proved native boundary comparison against its hyperbolic model
forces their corresponding points to have distance zero. This includes
coincident endpoints, without a positive-length assumption.
-/

open Set

namespace SystolicGrowth

/-- All-test midpoint-cosh comparison makes actual unit-time constant-speed
segments with the same endpoints equal at every parameter in the interval. -/
theorem metric_segment_unique_of_midpoint_cosh_all_test
    {M : Type*} [MetricSpace M]
    (hmid : ∀ x y : M, ∃ m : M,
      dist x m = dist x y / 2 ∧ dist m y = dist x y / 2 ∧
      ∀ z : M, 2 * Real.cosh (dist x y / 2) * Real.cosh (dist z m) ≤
        Real.cosh (dist z x) + Real.cosh (dist z y))
    (α β : ℝ → M)
    (hαcont : ContinuousOn α (Icc 0 1)) (hβcont : ContinuousOn β (Icc 0 1))
    (hαdist : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      dist (α u) (α v) = dist (α 0) (α 1) * |u - v|)
    (hβdist : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      dist (β u) (β v) = dist (β 0) (β 1) * |u - v|)
    (hbase : α 0 = β 0) (hend : α 1 = β 1) :
    ∀ t ∈ Icc (0 : ℝ) 1, α t = β t := by
  let D := dist (α 0) (α 1)
  let a := hyperbolicVerticalSegmentPoint 0 0 D 0
  let b := hyperbolicVerticalSegmentPoint 0 0 D 1
  have hab : dist a b = dist (α 0) (α 1) := by
    simp [a, b, hyperbolicVerticalSegmentPoint_dist, D, abs_of_nonneg dist_nonneg]
  have hac : dist a b = dist (β 0) (β 1) := by
    rw [← hbase, ← hend]
    exact hab
  have hbc : dist b b = dist (α 1) (β 1) := by simp only [hend, dist_self]
  intro t ht
  have hbound := metric_triangle_boundary_dist_le_geodInterp hmid α β
    hαcont hβcont hαdist hβdist hbase a b b hab hac hbc t t ht ht
  simpa only [dist_self, dist_le_zero] using hbound

/-- Two genuine constant-speed paths with the same endpoints are equal
under all-test midpoint-cosh comparison. -/
theorem metric_path_unique_of_midpoint_cosh_all_test
    {M : Type*} [MetricSpace M] {x y : M}
    (hmid : ∀ a b : M, ∃ m : M,
      dist a m = dist a b / 2 ∧ dist m b = dist a b / 2 ∧
      ∀ z : M, 2 * Real.cosh (dist a b / 2) * Real.cosh (dist z m) ≤
        Real.cosh (dist z a) + Real.cosh (dist z b))
    (α β : Path x y)
    (hαdist : ∀ s t : unitInterval,
      dist (α s) (α t) = dist x y * |(s : ℝ) - (t : ℝ)|)
    (hβdist : ∀ s t : unitInterval,
      dist (β s) (β t) = dist x y * |(s : ℝ) - (t : ℝ)|) :
    α = β := by
  let A : ℝ → M := fun t => α (projIcc 0 1 zero_le_one t)
  let B : ℝ → M := fun t => β (projIcc 0 1 zero_le_one t)
  have hA (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : A t = α ⟨t, ht⟩ := by
    dsimp [A]
    rw [projIcc_of_mem zero_le_one ht]
  have hB (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : B t = β ⟨t, ht⟩ := by
    dsimp [B]
    rw [projIcc_of_mem zero_le_one ht]
  have hA0 : A 0 = x := by
    rw [hA 0 (by norm_num), show (⟨0, by norm_num⟩ : unitInterval) = 0 by
      apply Subtype.ext; rfl]
    exact α.source
  have hA1 : A 1 = y := by
    rw [hA 1 (by norm_num), show (⟨1, by norm_num⟩ : unitInterval) = 1 by
      apply Subtype.ext; rfl]
    exact α.target
  have hB0 : B 0 = x := by
    rw [hB 0 (by norm_num), show (⟨0, by norm_num⟩ : unitInterval) = 0 by
      apply Subtype.ext; rfl]
    exact β.source
  have hB1 : B 1 = y := by
    rw [hB 1 (by norm_num), show (⟨1, by norm_num⟩ : unitInterval) = 1 by
      apply Subtype.ext; rfl]
    exact β.target
  have hAdist : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      dist (A u) (A v) = dist (A 0) (A 1) * |u - v| := by
    intro u hu v hv
    rw [hA u hu, hA v hv, hA0, hA1]
    exact hαdist ⟨u, hu⟩ ⟨v, hv⟩
  have hBdist : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      dist (B u) (B v) = dist (B 0) (B 1) * |u - v| := by
    intro u hu v hv
    rw [hB u hu, hB v hv, hB0, hB1]
    exact hβdist ⟨u, hu⟩ ⟨v, hv⟩
  have heq := metric_segment_unique_of_midpoint_cosh_all_test hmid A B
    (α.continuous.comp continuous_projIcc).continuousOn
    (β.continuous.comp continuous_projIcc).continuousOn hAdist hBdist
    (hA0.trans hB0.symm) (hA1.trans hB1.symm)
  apply Path.ext
  funext t
  simpa only [hA t t.property, hB t t.property] using heq t t.property

end SystolicGrowth
