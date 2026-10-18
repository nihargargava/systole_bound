module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCurvatureBoundedCoverHadamard

@[expose] public section

/-!
# Embedded balls from a genuine smooth-cover fiber gap

The radius cutoff is expressed using an arbitrary proved metric fiber gap,
not only the construction's target systole. The actual projection and global
exponential maps are unchanged.
-/

open Set Bundle Manifold Riemannian
open scoped Manifold ContDiff Topology

namespace SystolicGrowth

/-- **Math.** A map whose distinct points in one fiber are at least `L` apart
is injective on every open ball with `2 * R ≤ L`. -/
theorem injOn_ball_of_fiber_dist_le
    {M N : Type*} [PseudoMetricSpace M] (f : M → N) (q : M) (R L : ℝ)
    (hgap : ∀ a b : M, f a = f b → a ≠ b → L ≤ dist a b)
    (hR : 2 * R ≤ L) : Set.InjOn f (Metric.ball q R) := by
  intro a ha b hb hab
  by_contra hne
  have hsep := hgap a b hab hne
  have ha' : dist a q < R := Metric.mem_ball.mp ha
  have hb' : dist q b < R := by
    simpa only [dist_comm] using Metric.mem_ball.mp hb
  have hdist : dist a b < 2 * R := by
    calc
      dist a b ≤ dist a q + dist q b := dist_triangle a q b
      _ < R + R := add_lt_add ha' hb'
      _ = 2 * R := by ring
  linarith

/-- **Math.** A local homeomorphism with a genuine metric fiber gap openly
embeds every ball below the exact half-gap cutoff. -/
theorem isOpenEmbedding_restrict_ball_of_fiber_dist_le
    {M N : Type*} [PseudoMetricSpace M] [TopologicalSpace N]
    (f : M → N) (hf : IsLocalHomeomorph f) (q : M) (R L : ℝ)
    (hgap : ∀ a b : M, f a = f b → a ≠ b → L ≤ dist a b)
    (hR : 2 * R ≤ L) : Topology.IsOpenEmbedding ((Metric.ball q R).restrict f) := by
  have hball := (Metric.isOpen_ball (x := q) (ε := R)).isOpenEmbedding_subtypeVal
  have hinj := injOn_ball_of_fiber_dist_le f q R L hgap hR
  exact (hf.comp hball.isLocalHomeomorph).isOpenEmbedding_of_injective
    (fun a b h => Subtype.ext (hinj a.property b.property h))

namespace ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- **Math.** The actual smooth-cover projection is injective on any ball
whose diameter is bounded by a proved smooth-metric fiber separation. -/
theorem gluedCurvatureBoundedUniversalCoverProjection_injOn_ball_of_fiber_gap
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) (R L : ℝ)
    (hgap : letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
      ∀ a b : P.basedTopologicalUniversalCover x,
        P.gluedUniversalCoverProjection x a = P.gluedUniversalCoverProjection x b →
        a ≠ b → L ≤ dist a b)
    (hR : 2 * R ≤ L) :
    letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
    Set.InjOn (P.gluedUniversalCoverProjection x) (Metric.ball q R) := by
  letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
  exact injOn_ball_of_fiber_dist_le (P.gluedUniversalCoverProjection x) q R L hgap hR

/-- **Math.** The same genuine fiber gap makes the actual smooth-cover ball
projection an open embedding, without a target-systole restriction. -/
theorem gluedCurvatureBoundedUniversalCoverProjection_isOpenEmbedding_ball_of_fiber_gap
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) (R L : ℝ)
    (hgap : letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
      ∀ a b : P.basedTopologicalUniversalCover x,
        P.gluedUniversalCoverProjection x a = P.gluedUniversalCoverProjection x b →
        a ≠ b → L ≤ dist a b)
    (hR : 2 * R ≤ L) :
    letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
    Topology.IsOpenEmbedding
      ((Metric.ball q R).restrict (P.gluedUniversalCoverProjection x)) := by
  letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
  exact isOpenEmbedding_restrict_ball_of_fiber_dist_le
    (P.gluedUniversalCoverProjection x)
    (P.gluedUniversalCoverProjection_isCoveringMap x).isLocalHomeomorph q R L hgap hR

/-- **Math.** The actual projected exponential openly embeds its initial
metric disk whenever `2 * R ≤ L` and `L` is a genuine smooth-cover fiber gap. -/
theorem gluedCurvatureBoundedUniversalCover_projectedExpMap_isOpenEmbedding_initialLength_ball_of_fiber_gap
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) (R L : ℝ)
    (hgap : letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
      ∀ a b : P.basedTopologicalUniversalCover x,
        P.gluedUniversalCoverProjection x a = P.gluedUniversalCoverProjection x b →
        a ≠ b → L ≤ dist a b)
    (hR : 2 * R ≤ L) :
    Topology.IsOpenEmbedding
      (({v : ℂ | Real.sqrt (Riemannian.chartMetricInner
        (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x) q
        (extChartAt (modelWithCornersSelf ℝ ℂ) q q) v v) < R} : Set ℂ).restrict
        (P.gluedUniversalCoverProjection x ∘
          P.gluedCurvatureBoundedUniversalCoverExpMap x q)) := by
  letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
  let S : Set ℂ := {v : ℂ | Real.sqrt (Riemannian.chartMetricInner
    (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x) q
    (extChartAt (modelWithCornersSelf ℝ ℂ) q q) v v) < R}
  have hexp :=
    P.gluedCurvatureBoundedUniversalCoverExpMap_isOpenEmbedding_initialLength_ball x q R
  have hlocal := (P.gluedUniversalCoverProjection_isCoveringMap x).isLocalHomeomorph.comp
    hexp.isLocalHomeomorph
  have hinj :=
    P.gluedCurvatureBoundedUniversalCoverProjection_injOn_ball_of_fiber_gap x q R L hgap hR
  have hmem (v : S) : P.gluedCurvatureBoundedUniversalCoverExpMap x q v.val ∈
      Metric.ball q R := by
    rw [Metric.mem_ball, dist_comm,
      P.gluedCurvatureBoundedUniversalCoverExpMap_dist_eq_initialLength]
    exact v.property
  apply hlocal.isOpenEmbedding_of_injective
  intro a b hab
  apply Subtype.ext
  apply P.gluedCurvatureBoundedUniversalCoverExpMap_injective x q
  exact hinj (hmem a) (hmem b) hab

#print axioms SystolicGrowth.injOn_ball_of_fiber_dist_le
#print axioms SystolicGrowth.isOpenEmbedding_restrict_ball_of_fiber_dist_le
#print axioms gluedCurvatureBoundedUniversalCoverProjection_injOn_ball_of_fiber_gap
#print axioms gluedCurvatureBoundedUniversalCoverProjection_isOpenEmbedding_ball_of_fiber_gap
#print axioms gluedCurvatureBoundedUniversalCover_projectedExpMap_isOpenEmbedding_initialLength_ball_of_fiber_gap

end
end ExerciseGluingPreparation
end SystolicGrowth
