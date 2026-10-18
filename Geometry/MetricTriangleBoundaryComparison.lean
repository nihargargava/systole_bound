module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.MetricSplitPathCosh

@[expose] public section

/-!
# Comparison between actual triangle boundary segments

All-test midpoint-cosh comparison bounds the distance between points on two
actual constant-speed edges by the corresponding hyperbolic model distance.
The three vertex distances are matched, and zero-length edges are included.
This supplies boundary comparison, not triangle inheritance or model pasting.
-/

open Set

namespace SystolicGrowth

/-- Endpoint distance upper bounds pass to every point of an actual metric
segment through the matching hyperbolic model segment. A zero-length actual
edge and its matching model edge are both constant. -/
theorem metric_segment_dist_le_geodInterp_of_endpoint_bounds
    {M : Type*} [MetricSpace M]
    (hmid : ∀ x y : M, ∃ m : M,
      dist x m = dist x y / 2 ∧ dist m y = dist x y / 2 ∧
      ∀ z : M, 2 * Real.cosh (dist x y / 2) * Real.cosh (dist z m) ≤
        Real.cosh (dist z x) + Real.cosh (dist z y))
    (γ : ℝ → M) (hcont : ContinuousOn γ (Icc 0 1))
    (hdist : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      dist (γ u) (γ v) = dist (γ 0) (γ 1) * |u - v|)
    (x : M) (a b q : UpperHalfPlane)
    (hab : dist a b = dist (γ 0) (γ 1))
    (hx0 : dist x (γ 0) ≤ dist q a) (hx1 : dist x (γ 1) ≤ dist q b)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    dist x (γ t) ≤ dist q (Vendored.RiemannDynamics.geodInterp a b t) := by
  by_cases hD : dist (γ 0) (γ 1) = 0
  · have hγ : γ t = γ 0 := by
      apply dist_eq_zero.mp
      rw [hdist t ht 0 (by norm_num), hD, zero_mul]
    have hab' : a = b := dist_eq_zero.mp (hab.trans hD)
    rw [hγ, ← hab', Vendored.RiemannDynamics.geodInterp_self]
    exact hx0
  · have hDpos : 0 < dist (γ 0) (γ 1) := lt_of_le_of_ne dist_nonneg (Ne.symm hD)
    have hactual := cosh_sinh_interpolation_of_metric_path hDpos hmid γ hcont hdist x t ht
    have hmodel := geodInterp_sinh_cosh_interpolation a b q t
    rw [hab] at hmodel
    have hcosh0 : Real.cosh (dist x (γ 0)) ≤ Real.cosh (dist q a) := by
      apply Real.cosh_le_cosh.mpr
      simpa only [abs_of_nonneg dist_nonneg] using hx0
    have hcosh1 : Real.cosh (dist x (γ 1)) ≤ Real.cosh (dist q b) := by
      apply Real.cosh_le_cosh.mpr
      simpa only [abs_of_nonneg dist_nonneg] using hx1
    have hw0 : 0 ≤ Real.sinh ((1 - t) * dist (γ 0) (γ 1)) :=
      Real.sinh_nonneg_iff.mpr (mul_nonneg (by linarith [ht.2]) dist_nonneg)
    have hw1 : 0 ≤ Real.sinh (t * dist (γ 0) (γ 1)) :=
      Real.sinh_nonneg_iff.mpr (mul_nonneg ht.1 dist_nonneg)
    have hbound : Real.sinh (dist (γ 0) (γ 1)) * Real.cosh (dist x (γ t)) ≤
        Real.sinh (dist (γ 0) (γ 1)) *
          Real.cosh (dist q (Vendored.RiemannDynamics.geodInterp a b t)) := by
      calc
        _ ≤ _ := hactual
        _ ≤ Real.sinh ((1 - t) * dist (γ 0) (γ 1)) * Real.cosh (dist q a) +
            Real.sinh (t * dist (γ 0) (γ 1)) * Real.cosh (dist q b) :=
          add_le_add (mul_le_mul_of_nonneg_left hcosh0 hw0)
            (mul_le_mul_of_nonneg_left hcosh1 hw1)
        _ = _ := hmodel.symm
    have hc := (mul_le_mul_iff_right₀ (Real.sinh_pos_iff.mpr hDpos)).mp hbound
    have h := Real.cosh_le_cosh.mp hc
    simpa only [abs_of_nonneg dist_nonneg] using h

/-- The actual and model distances between two points on the same edge
agree exactly, including a degenerate edge. -/
theorem metric_segment_dist_eq_geodInterp
    {M : Type*} [MetricSpace M] (γ : ℝ → M)
    (hdist : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      dist (γ u) (γ v) = dist (γ 0) (γ 1) * |u - v|)
    (a b : UpperHalfPlane) (hab : dist a b = dist (γ 0) (γ 1))
    (s t : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    dist (γ s) (γ t) =
      dist (Vendored.RiemannDynamics.geodInterp a b s)
        (Vendored.RiemannDynamics.geodInterp a b t) := by
  rw [hdist s hs t ht, Vendored.RiemannDynamics.dist_geodInterp_pair, hab]
  ring

/-- Points on two actual constant-speed triangle edges sharing their initial
vertex satisfy comparison against the matching hyperbolic edges. All three
vertex distances are matched; neither edge is assumed to have positive length. -/
theorem metric_triangle_boundary_dist_le_geodInterp
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
    (hbase : α 0 = β 0) (a b c : UpperHalfPlane)
    (hab : dist a b = dist (α 0) (α 1))
    (hac : dist a c = dist (β 0) (β 1))
    (hbc : dist b c = dist (α 1) (β 1))
    (s t : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    dist (α s) (β t) ≤
      dist (Vendored.RiemannDynamics.geodInterp a b s)
        (Vendored.RiemannDynamics.geodInterp a c t) := by
  have hleft : dist (α 0) (β t) =
      dist a (Vendored.RiemannDynamics.geodInterp a c t) := by
    calc
      _ = dist (β 0) (β 1) * |0 - t| := by
        rw [hbase]
        exact hβdist 0 (by norm_num) t ht
      _ = t * dist a c := by
        rw [← hac, zero_sub, abs_neg, abs_of_nonneg ht.1]
        ring
      _ = _ := (Vendored.RiemannDynamics.dist_geodInterp_left a c ht).symm
  have hright : dist (α 1) (β t) ≤
      dist b (Vendored.RiemannDynamics.geodInterp a c t) := by
    apply metric_segment_dist_le_geodInterp_of_endpoint_bounds hmid β hβcont hβdist
      (α 1) a c b hac ?_ ?_ t ht
    · rw [← hbase, dist_comm (α 1) (α 0), dist_comm b a, hab]
    · exact hbc.ge
  have h := metric_segment_dist_le_geodInterp_of_endpoint_bounds hmid α hαcont hαdist
    (β t) a b (Vendored.RiemannDynamics.geodInterp a c t) hab
    (by simpa only [dist_comm] using hleft.le)
    (by simpa only [dist_comm] using hright) s hs
  simpa only [dist_comm] using h

#print axioms metric_segment_dist_le_geodInterp_of_endpoint_bounds
#print axioms metric_segment_dist_eq_geodInterp
#print axioms metric_triangle_boundary_dist_le_geodInterp

end SystolicGrowth
