module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Exact midpoints from approximate midpoints in proper metric spaces

The maximum of the two endpoint distances attains a minimum on a bounded
closed ball. Approximate midpoints with small error lie in that same ball
and force the minimum down to half the endpoint distance. The triangle
inequality then makes both half-distance bounds equalities.
-/

open Set Metric

namespace SystolicGrowth

variable {M : Type*} [MetricSpace M] [ProperSpace M]

/-- Properness turns genuine approximate midpoints for the selected pair
into an exact midpoint; no compactness of the entire space is required. -/
theorem exists_midpoint_of_proper_approximate_midpoints (x y : M)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ z : M,
      dist x z ≤ dist x y / 2 + ε ∧ dist z y ≤ dist x y / 2 + ε) :
    ∃ z : M, dist x z = dist x y / 2 ∧ dist z y = dist x y / 2 := by
  have hd : 0 ≤ dist x y := dist_nonneg
  have hc : Continuous (fun z : M => max (dist x z) (dist z y)) :=
    (continuous_const.dist continuous_id).max (continuous_id.dist continuous_const)
  have hxball : x ∈ closedBall x (dist x y + 1) := by
    rw [mem_closedBall, dist_self]
    linarith
  obtain ⟨z, _, hmin⟩ := (isCompact_closedBall x (dist x y + 1)).exists_isMinOn
    ⟨x, hxball⟩ hc.continuousOn
  have hm : max (dist x z) (dist z y) ≤ dist x y / 2 := by
    by_contra h
    have hgap : 0 < (max (dist x z) (dist z y) - dist x y / 2) / 2 := by
      have := lt_of_not_ge h
      linarith
    have hε : 0 < min ((max (dist x z) (dist z y) - dist x y / 2) / 2) (1 / 2) :=
      lt_min hgap (by linarith)
    obtain ⟨w, hwx, hwy⟩ := happrox _ hε
    have hwball : w ∈ closedBall x (dist x y + 1) := by
      rw [mem_closedBall, dist_comm w x]
      have hεle := min_le_right
        ((max (dist x z) (dist z y) - dist x y / 2) / 2) (1 / 2 : ℝ)
      linarith
    have hzw : max (dist x z) (dist z y) ≤ max (dist x w) (dist w y) := hmin hwball
    have hw := max_le hwx hwy
    have hεgap := min_le_left
      ((max (dist x z) (dist z y) - dist x y / 2) / 2) (1 / 2 : ℝ)
    linarith
  have hx : dist x z ≤ dist x y / 2 := (le_max_left _ _).trans hm
  have hy : dist z y ≤ dist x y / 2 := (le_max_right _ _).trans hm
  have ht := dist_triangle x z y
  refine ⟨z, ?_, ?_⟩ <;> linarith

#print axioms exists_midpoint_of_proper_approximate_midpoints

end SystolicGrowth
