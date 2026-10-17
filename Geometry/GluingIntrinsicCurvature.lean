module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingComplexBasisCurvature
public import Geometry.GluingInteriorIntrinsicCurvature

@[expose] public section

/-!
# Intrinsic curvature of the patched glued metric

The canonical glued atlas selects seam charts on closed smoothing collars.
Outside those collars, either chart type gives the same curvature bound.
Combining the actual Levi-Civita computations proves the global intrinsic
inequality needed by Jacobi comparison.
-/

open Bundle Manifold
open scoped Manifold Topology ContDiff

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

local instance : NeZero (Module.finrank ℝ ℂ) :=
  ⟨by rw [Complex.finrank_real_complex]; norm_num⟩

/-- **Math.** The actual patched metric has the hyperbolic curvature-operator
lower bound on all tangent pairs at every point of the glued carrier. -/
theorem gluedCurvatureBounded_curvatureOperatorAt_lower_bound
    (P : ExerciseGluingPreparation C g n genera X) (b : P.GluedCarrier) :
    let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
    let metric := P.gluedCurvatureBoundedSmoothRiemannianMetric
    ∀ u v : TangentSpace I b,
      Riemannian.RiemannianMetric.metricInner metric b u u *
          Riemannian.RiemannianMetric.metricInner metric b v v -
        Riemannian.RiemannianMetric.metricInner metric b u v *
          Riemannian.RiemannianMetric.metricInner metric b u v ≤
        Riemannian.RiemannianMetric.metricInner metric b
          ((Riemannian.RiemannianMetric.leviCivitaConnection metric).curvatureOperatorAt
            b u v v) u := by
  by_cases hcollar : ∃ k : Fin (n - 1), b ∈ P.closedThinSeamCollar k
  · obtain ⟨k, hk⟩ := hcollar
    exact P.gluedCurvatureBounded_curvatureOperatorAt_lower_bound_of_mem_closedThinSeamCollar
      b k hk
  · have houtside : ∀ k : Fin (n - 1), b ∉ P.closedThinSeamCollar k := by
      intro k hk
      exact hcollar ⟨k, hk⟩
    rcases P.gluedCurvatureBounded_chartAt_is_seam_or_interior b with
      hi | ⟨k, θ, hchart⟩
    · exact
        P.gluedCurvatureBounded_curvatureOperatorAt_lower_bound_of_interior_outside_closedThinSeamCollars
          b hi houtside
    · let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
      let y : ℂ := (extChartAt I b) b
      have hy : y ∈ (extChartAt I b).target := mem_extChartAt_target b
      have hpoint : (extChartAt I b).symm y = b :=
        (extChartAt I b).left_inv (mem_extChartAt_source b)
      have hotherClosed : ∀ l : Fin (n - 1), l ≠ k →
          (extChartAt I b).symm y ∉ P.closedThinSeamCollar l := by
        intro l _
        rw [hpoint]
        exact houtside l
      have h := P.gluedCurvatureBoundedSeam_curvatureOperatorAt_lower_bound
        k θ b hchart.symm hy hotherClosed
      dsimp only [I, y] at h
      rw [extChartAt_to_inv] at h
      exact h

/-- **Math.** In particular the curvature-operator sign consumed by the
no-conjugate-point theorem holds globally for the patched metric. -/
theorem gluedCurvatureBounded_curvatureOperatorAt_pair_nonneg
    (P : ExerciseGluingPreparation C g n genera X) (b : P.GluedCarrier) :
    let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
    let metric := P.gluedCurvatureBoundedSmoothRiemannianMetric
    ∀ u v : TangentSpace I b,
      0 ≤ Riemannian.RiemannianMetric.metricInner metric b
        ((Riemannian.RiemannianMetric.leviCivitaConnection metric).curvatureOperatorAt
          b u v v) u := by
  let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
  let metric := P.gluedCurvatureBoundedSmoothRiemannianMetric
  letI : Bundle.RiemannianBundle
      (fun q : P.GluedCarrier => TangentSpace I q) :=
    ⟨metric.toRiemannianMetric⟩
  dsimp only
  intro u v
  have hgram : 0 ≤ Riemannian.RiemannianMetric.metricInner metric b u u *
        Riemannian.RiemannianMetric.metricInner metric b v v -
      Riemannian.RiemannianMetric.metricInner metric b u v *
        Riemannian.RiemannianMetric.metricInner metric b u v :=
    Riemannian.wedgeSq_nonneg u v
  exact hgram.trans (P.gluedCurvatureBounded_curvatureOperatorAt_lower_bound b u v)

/-- **Math.** Every nondegenerate tangent plane of the actual patched metric
has intrinsic sectional curvature at most `-1`. -/
theorem gluedCurvatureBounded_sectionalCurvature_le_neg_one
    (P : ExerciseGluingPreparation C g n genera X) (b : P.GluedCarrier) :
    let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
    let metric := P.gluedCurvatureBoundedSmoothRiemannianMetric
    letI : Bundle.RiemannianBundle
        (fun q : P.GluedCarrier => TangentSpace I q) :=
      ⟨metric.toRiemannianMetric⟩
    ∀ u v : TangentSpace I b, 0 < Riemannian.wedgeSq u v →
      Riemannian.sectionalCurvature
        ((Riemannian.RiemannianMetric.leviCivitaConnection metric).curvatureFormAt
          metric b) u v ≤ -1 := by
  let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
  let metric := P.gluedCurvatureBoundedSmoothRiemannianMetric
  letI : Bundle.RiemannianBundle
      (fun q : P.GluedCarrier => TangentSpace I q) :=
    ⟨metric.toRiemannianMetric⟩
  let connection := Riemannian.RiemannianMetric.leviCivitaConnection
    (I := I) (M := P.GluedCarrier) metric
  have hLC : connection.IsLeviCivita metric :=
    connection.isLeviCivita_of_koszulDual metric
      (fun A B Z q =>
        Riemannian.RiemannianMetric.koszulDualSection_dual metric A B Z q)
  have hB := connection.isAlgCurvatureForm_curvatureFormAt metric hLC b
  dsimp only
  intro u v harea
  change connection.curvatureFormAt metric b u v u v / Riemannian.wedgeSq u v ≤ -1
  apply (div_le_iff₀ harea).2
  have hbound : Riemannian.wedgeSq u v ≤
      connection.curvatureFormAt metric b u v v u :=
    P.gluedCurvatureBounded_curvatureOperatorAt_lower_bound b u v
  have hskew := hB.antisymm₃₄ u v u v
  linarith

#print axioms gluedCurvatureBounded_curvatureOperatorAt_lower_bound
#print axioms gluedCurvatureBounded_curvatureOperatorAt_pair_nonneg
#print axioms gluedCurvatureBounded_sectionalCurvature_le_neg_one

end

end SystolicGrowth.ExerciseGluingPreparation
