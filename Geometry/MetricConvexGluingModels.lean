module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.MetricConvexGluingComparison

@[expose] public section

/-!
# Comparison models for the two mixed-triangle inheritance steps

The ordinary triangle inequalities in the actual metric gluing provide all
model vertices required by mixed boundary inheritance. Each shared model
base is chosen literally vertical; coincident vertices and zero legs are
included. No curvature property of the glued space is used here.
-/

namespace SystolicGrowth

private theorem exists_metric_triangle_vertical_model
    {M : Type*} [MetricSpace M] (a b c : M) :
    ∃ v : UpperHalfPlane,
      dist UpperHalfPlane.I v = dist a b ∧
        dist (hyperbolicTriangleModelAxisPoint (dist a c)) v = dist c b := by
  apply exists_hyperbolic_triangle_with_vertical_base dist_nonneg dist_nonneg dist_nonneg
  · simpa only [dist_comm c b, add_comm] using dist_triangle a c b
  · simpa only [dist_comm c a, add_comm] using dist_triangle c a b
  · simpa only [dist_comm b c] using dist_triangle a b c

/-- All model data for both actual mixed-triangle inheritance steps exist
from the native metric and its two minimizing seam crossings. In particular,
the shared base of the second step agrees literally with a side of the first
parent model, including every degenerate triangle case. -/
theorem exists_metricGlue_mixed_triangle_models
    {A B S : Type*} [MetricSpace A] [MetricSpace B] [MetricSpace S] [Nonempty S]
    {Φ : S → A} {Ψ : S → B} (hΦ : Isometry Φ) (hΨ : Isometry Ψ)
    (p q : S) (x : A) (y z : B)
    (hmin : dist (Metric.toGlueL hΦ hΨ x) (Metric.toGlueR hΦ hΨ y) =
      dist x (Φ q) + dist (Ψ q) y)
    (hminZ : dist (Metric.toGlueL hΦ hΨ x) (Metric.toGlueR hΦ hΨ z) =
      dist x (Φ p) + dist (Ψ p) z) :
    ∃ p' q' x' y' P X Y Z U V W : UpperHalfPlane,
      dist p' q' = dist p q ∧
      dist p' x' = dist (Φ p) x ∧ dist x' q' = dist x (Φ q) ∧
      dist p' y' = dist (Ψ p) y ∧ dist q' y' = dist (Ψ q) y ∧
      dist P X = dist p' x' ∧ dist P Y = dist p' y' ∧
      dist X Y = dist x' q' + dist q' y' ∧
      dist Y Z = dist y z ∧ dist P Z = dist (Ψ p) z ∧
      dist U V = dist Y X ∧ dist U W = dist Y Z ∧
      dist V W = dist X P + dist P Z := by
  let L := Metric.toGlueL hΦ hΨ
  let R := Metric.toGlueR hΦ hΨ
  have hL : Isometry L := Metric.toGlueL_isometry hΦ hΨ
  have hR : Isometry R := Metric.toGlueR_isometry hΦ hΨ
  have hseam : L (Φ p) = R (Ψ p) := congrFun (Metric.toGlue_commute hΦ hΨ) p
  obtain ⟨x', hpx, hqx⟩ := exists_metric_triangle_vertical_model (Φ p) x (Φ q)
  obtain ⟨y', hpy, hqy⟩ := exists_metric_triangle_vertical_model (Ψ p) y (Ψ q)
  let p' := UpperHalfPlane.I
  let q' := hyperbolicTriangleModelAxisPoint (dist p q)
  have hpq : dist p' q' = dist p q := hyperbolicTriangleModelAxisPoint_dist_base dist_nonneg
  have hxq : dist x' q' = dist x (Φ q) := by
    simpa only [q', hΦ.dist_eq, dist_comm] using hqx
  have hqy' : dist q' y' = dist (Ψ q) y := by
    simpa only [q', hΨ.dist_eq] using hqy
  obtain ⟨X, hYX, hPX⟩ := exists_metric_triangle_vertical_model (R y) (L x) (R (Ψ p))
  obtain ⟨Z, hYZ, hPZ⟩ := exists_metric_triangle_vertical_model y z (Ψ p)
  let Y := UpperHalfPlane.I
  let P := hyperbolicTriangleModelAxisPoint (dist (Ψ p) y)
  have hPX' : dist P X = dist p' x' := by
    calc
      dist P X = dist (R (Ψ p)) (L x) := by
        simpa only [P, hR.dist_eq, dist_comm y (Ψ p)] using hPX
      _ = dist (Φ p) x := by rw [← hseam, hL.dist_eq]
      _ = dist p' x' := hpx.symm
  have hPY : dist P Y = dist p' y' := by
    rw [dist_comm P Y]
    exact (hyperbolicTriangleModelAxisPoint_dist_base dist_nonneg).trans hpy.symm
  have hXY : dist X Y = dist x' q' + dist q' y' := by
    rw [hxq, hqy']
    calc
      dist X Y = dist UpperHalfPlane.I X := dist_comm X Y
      _ = dist (R y) (L x) := hYX
      _ = dist (L x) (R y) := dist_comm _ _
      _ = dist x (Φ q) + dist (Ψ q) y := hmin
  have hPZ' : dist P Z = dist (Ψ p) z := by
    simpa only [P, dist_comm y (Ψ p)] using hPZ
  obtain ⟨W, hUW, hVW⟩ := exists_metric_triangle_vertical_model (R y) (R z) (L x)
  let U := UpperHalfPlane.I
  let V := hyperbolicTriangleModelAxisPoint (dist (R y) (L x))
  have hUV : dist U V = dist Y X :=
    (hyperbolicTriangleModelAxisPoint_dist_base dist_nonneg).trans hYX.symm
  have hUW' : dist U W = dist Y Z := by
    exact hUW.trans ((hR.dist_eq y z).trans hYZ.symm)
  have hVW' : dist V W = dist X P + dist P Z := by
    calc
      dist V W = dist (L x) (R z) := hVW
      _ = dist x (Φ p) + dist (Ψ p) z := hminZ
      _ = dist X P + dist P Z := by
        rw [dist_comm X P, hPX', hpx, hPZ', dist_comm (Φ p) x]
  exact ⟨p', q', x', y', P, X, Y, Z, U, V, W, hpq, hpx, hxq, hpy, hqy',
    hPX', hPY, hXY, hYZ, hPZ', hUV, hUW', hVW'⟩

#print axioms exists_metricGlue_mixed_triangle_models

end SystolicGrowth
