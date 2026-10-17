module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingInteriorComparison
public import Geometry.GluingSeamComparison
public import Geometry.GluingGeodesics
public import Geometry.MetricSegmentUniqueness

@[expose] public section

/-!
# Local comparison on the original glued surface

The actual interior and seam charts cover the unchanged carrier. Their
native local metric identifications transport hyperbolic midpoint comparison
to genuine intrinsic neighborhoods, with one midpoint fixed before all test
points. Small closed balls then inherit comparison and metric segments.
-/

open Set Metric

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- Every point has an actual intrinsic ball with all-test midpoint-cosh
comparison. Coverage includes seam points, not only component interiors. -/
theorem gluedIntrinsicMetric_locally_midpoint_cosh_all_test
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    ∃ ε > 0, ∀ y ∈ ball x ε, ∀ z ∈ ball x ε,
      ∃ m ∈ ball x ε,
        dist y m = dist y z / 2 ∧ dist m z = dist y z / 2 ∧
        ∀ w ∈ ball x ε,
          2 * Real.cosh (dist y z / 2) * Real.cosh (dist w m) ≤
            Real.cosh (dist w y) + Real.cosh (dist w z) := by
  letI := P.gluedCarrierIntrinsicMetricSpace
  obtain ⟨e, he, hx⟩ := P.exists_gluedComplexAtlas_chart x
  rcases he with he | ⟨k, θ, rfl⟩
  · exact P.gluedIntrinsicMetric_interior_locally_midpoint_cosh_all_test e he x hx
  · exact P.gluedIntrinsicMetric_seam_locally_midpoint_cosh_all_test k θ x hx

/-- Every sufficiently small closed ball has comparison in its actual
restricted intrinsic metric. The midpoint's closed-ball membership follows
from comparison at the center, not from an assumed convexity premise. -/
theorem gluedIntrinsicMetric_locally_closedBall_midpoint_cosh_all_test
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    ∃ ε > 0, ∀ δ : ℝ, 0 ≤ δ → δ < ε →
      ∀ y z : closedBall x δ,
        ∃ m : closedBall x δ,
          dist y m = dist y z / 2 ∧ dist m z = dist y z / 2 ∧
          ∀ w : closedBall x δ,
            2 * Real.cosh (dist y z / 2) * Real.cosh (dist w m) ≤
              Real.cosh (dist w y) + Real.cosh (dist w z) := by
  letI := P.gluedCarrierIntrinsicMetricSpace
  obtain ⟨ε, hε, hlocal⟩ := P.gluedIntrinsicMetric_locally_midpoint_cosh_all_test x
  refine ⟨ε, hε, ?_⟩
  intro δ hδ hδε y z
  have hsmall : closedBall x δ ⊆ ball x ε := closedBall_subset_ball hδε
  obtain ⟨m, _hm, hym, hmz, hcomparison⟩ :=
    hlocal y.1 (hsmall y.2) z.1 (hsmall z.2)
  have hcenter : x ∈ ball x ε := mem_ball_self hε
  have hmδ : m ∈ closedBall x δ :=
    midpoint_cosh_comparison_mem_closedBall hδ y.2 z.2 (hcomparison x hcenter)
  exact ⟨⟨m, hmδ⟩, hym, hmz, fun w => hcomparison w.1 (hsmall w.2)⟩

/-- The complete small closed balls carry genuine isometric intervals
between all pairs. Their distances are inherited from the original surface,
and every constructed interval remains inside that same closed ball. -/
theorem gluedIntrinsicMetric_locally_closedBall_exists_isometric_segment
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    ∃ ε > 0, ∀ δ : ℝ, 0 ≤ δ → δ < ε →
      ∀ y z : closedBall x δ,
        ∃ σ : Icc (0 : ℝ) (dist y z) → closedBall x δ, Isometry σ ∧
          σ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = y ∧
          σ ⟨dist y z, ⟨dist_nonneg, le_rfl⟩⟩ = z := by
  letI := P.gluedCarrierIntrinsicMetricSpace
  letI : CompactSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace_compact
  obtain ⟨ε, hε, hcomparison⟩ :=
    P.gluedIntrinsicMetric_locally_closedBall_midpoint_cosh_all_test x
  refine ⟨ε, hε, ?_⟩
  intro δ hδ hδε y z
  letI : IsClosed (closedBall x δ) := isClosed_closedBall
  let m : closedBall x δ → closedBall x δ → closedBall x δ :=
    fun a b => (hcomparison δ hδ hδε a b).choose
  have hm : ∀ a b : closedBall x δ,
      dist a (m a b) = dist a b / 2 ∧ dist (m a b) b = dist a b / 2 :=
    fun a b => ⟨(hcomparison δ hδ hδε a b).choose_spec.1,
      (hcomparison δ hδ hδε a b).choose_spec.2.1⟩
  obtain ⟨γ, hγ⟩ := exists_midpoint_metric_path m hm y z
  exact metric_path_exists_isometric_interval γ hγ

/-- Close endpoint pairs have at most one ambient constant-speed metric
path. Every such path stays in a larger comparison ball by the triangle
inequality; uniqueness is not restricted to preselected local segments. -/
theorem gluedIntrinsicMetric_locally_unique_metric_path
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    ∃ ε > 0, ∀ y ∈ ball x ε, ∀ z ∈ ball x ε,
      ∀ α β : Path y z,
        (∀ s t : unitInterval,
          dist (α s) (α t) = dist y z * |(s : ℝ) - (t : ℝ)|) →
        (∀ s t : unitInterval,
          dist (β s) (β t) = dist y z * |(s : ℝ) - (t : ℝ)|) → α = β := by
  letI := P.gluedCarrierIntrinsicMetricSpace
  obtain ⟨R, hR, hcomparison⟩ := P.gluedIntrinsicMetric_locally_midpoint_cosh_all_test x
  refine ⟨R / 4, by linarith, ?_⟩
  intro y hy z hz α β hα hβ
  have hyR : y ∈ ball x R := ball_subset_ball (by linarith) hy
  have hzR : z ∈ ball x R := ball_subset_ball (by linarith) hz
  have hmid : ∀ a b : ball x R,
      ∃ m : ball x R,
        dist a m = dist a b / 2 ∧ dist m b = dist a b / 2 ∧
        ∀ w : ball x R,
          2 * Real.cosh (dist a b / 2) * Real.cosh (dist w m) ≤
            Real.cosh (dist w a) + Real.cosh (dist w b) := by
    intro a b
    obtain ⟨m, hm, ham, hmb, hcomp⟩ := hcomparison a.1 a.2 b.1 b.2
    exact ⟨⟨m, hm⟩, ham, hmb, fun w => hcomp w.1 w.2⟩
  have hinside (γ : Path y z)
      (hγ : ∀ s t : unitInterval,
        dist (γ s) (γ t) = dist y z * |(s : ℝ) - (t : ℝ)|)
      (t : unitInterval) : γ t ∈ ball x R := by
    have hyx : dist y x < R / 4 := mem_ball.mp hy
    have hzx : dist z x < R / 4 := mem_ball.mp hz
    have hyz : dist y z < R / 2 := by
      have h := dist_triangle y x z
      rw [dist_comm x z] at h
      linarith
    have hstep : dist (γ t) y ≤ dist y z := by
      have h := hγ t 0
      rw [γ.source] at h
      change dist (γ t) y = dist y z * |(t : ℝ) - 0| at h
      simp only [sub_zero, abs_of_nonneg t.2.1] at h
      rw [h]
      exact mul_le_of_le_one_right dist_nonneg t.2.2
    apply mem_ball.mpr
    have h := dist_triangle (γ t) y x
    linarith
  let lift (γ : Path y z) (hγ : ∀ t : unitInterval, γ t ∈ ball x R) :
      Path (⟨y, hyR⟩ : ball x R) ⟨z, hzR⟩ :=
    { toFun := fun t => ⟨γ t, hγ t⟩
      continuous_toFun := γ.continuous.subtype_mk _
      source' := Subtype.ext γ.source
      target' := Subtype.ext γ.target }
  have heq := metric_path_unique_of_midpoint_cosh_all_test hmid
    (lift α (hinside α hα)) (lift β (hinside β hβ)) hα hβ
  apply Path.ext
  funext t
  exact congrArg Subtype.val (congrArg (fun γ => γ t) heq)

/-- Every ambient metric segment with endpoints in a sufficiently small
closed ball stays there. This concerns all native minimizing segments,
not only those constructed by the closed-ball midpoint procedure. -/
theorem gluedIntrinsicMetric_locally_closedBall_geodesically_convex
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    ∃ ε > 0, ∀ δ : ℝ, 0 ≤ δ → δ < ε →
      ∀ y z : closedBall x δ, ∀ γ : Path y.1 z.1,
        (∀ s t : unitInterval,
          dist (γ s) (γ t) = dist y.1 z.1 * |(s : ℝ) - (t : ℝ)|) →
        ∀ t : unitInterval, γ t ∈ closedBall x δ := by
  letI := P.gluedCarrierIntrinsicMetricSpace
  letI : CompactSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace_compact
  obtain ⟨ε₁, hε₁, hcomparison⟩ :=
    P.gluedIntrinsicMetric_locally_closedBall_midpoint_cosh_all_test x
  obtain ⟨ε₂, hε₂, hunique⟩ := P.gluedIntrinsicMetric_locally_unique_metric_path x
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro δ hδ hδε y z γ hγ t
  have hδ₁ : δ < ε₁ := hδε.trans_le (min_le_left _ _)
  have hδ₂ : δ < ε₂ := hδε.trans_le (min_le_right _ _)
  letI : IsClosed (closedBall x δ) := isClosed_closedBall
  let m : closedBall x δ → closedBall x δ → closedBall x δ :=
    fun a b => (hcomparison δ hδ hδ₁ a b).choose
  have hm : ∀ a b : closedBall x δ,
      dist a (m a b) = dist a b / 2 ∧ dist (m a b) b = dist a b / 2 :=
    fun a b => ⟨(hcomparison δ hδ hδ₁ a b).choose_spec.1,
      (hcomparison δ hδ hδ₁ a b).choose_spec.2.1⟩
  obtain ⟨Γ, hΓ⟩ := exists_midpoint_metric_path m hm y z
  have heq : γ = Γ.map continuous_subtype_val :=
    hunique y.1 (closedBall_subset_ball hδ₂ y.2)
      z.1 (closedBall_subset_ball hδ₂ z.2) γ (Γ.map continuous_subtype_val) hγ hΓ
  rw [heq]
  exact (Γ t).2

#print axioms gluedIntrinsicMetric_locally_midpoint_cosh_all_test
#print axioms gluedIntrinsicMetric_locally_closedBall_midpoint_cosh_all_test
#print axioms gluedIntrinsicMetric_locally_closedBall_exists_isometric_segment
#print axioms gluedIntrinsicMetric_locally_unique_metric_path
#print axioms gluedIntrinsicMetric_locally_closedBall_geodesically_convex

end SystolicGrowth.ExerciseGluingPreparation
