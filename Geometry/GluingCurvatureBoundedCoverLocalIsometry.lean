module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCurvatureBoundedCoverBalls
public import Geometry.GluingExcursionLength

@[expose] public section

/-!
# Actual local metric isometry of the smooth covering projection

Whole-ball projection and positive fiber separation identify the short smooth
cover distance with the actual base distance. Consequently the projection is
isometric on quarter-target balls and preserves every continuous path's metric
variation, including infinite variation.
-/

open Set Metric
open scoped ENNReal unitInterval Topology

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- **Math.** The genuine smooth covering projection is nonexpanding for
the actual smooth metrics on both the base and the universal cover. -/
theorem gluedCurvatureBoundedUniversalCoverProjection_lipschitz
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    letI := P.gluedCurvatureBoundedIntrinsicMetricSpace
    letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
    LipschitzWith 1 (P.gluedUniversalCoverProjection x) := by
  letI := P.gluedCurvatureBoundedIntrinsicMetricSpace
  letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
  apply LipschitzWith.of_edist_le
  intro a b
  have h := (P.gluedCurvatureBoundedUniversalCover_isRiemannianCovering x).2.riemannianEDist_le
    (P.gluedUniversalCoverProjection_isLocalDiffeomorph x).contMDiff a b
  exact h

/-- **Math.** Short distances of the actual smooth cover agree with actual
smooth base distances, derived from ball surjectivity and fiber separation. -/
theorem gluedCurvatureBoundedUniversalCoverProjection_dist_eq_of_lt_half_target
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (a b : P.basedTopologicalUniversalCover x) :
    letI := P.gluedCurvatureBoundedIntrinsicMetricSpace
    letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
    dist a b < targetSystole C g / 2 →
      dist (P.gluedUniversalCoverProjection x a) (P.gluedUniversalCoverProjection x b) =
        dist a b := by
  letI := P.gluedCurvatureBoundedIntrinsicMetricSpace
  letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
  intro hab
  have hle := (P.gluedCurvatureBoundedUniversalCoverProjection_lipschitz x).dist_le_mul a b
  simp only [NNReal.coe_one, one_mul] at hle
  apply le_antisymm hle
  by_contra hnot
  have hlt : dist (P.gluedUniversalCoverProjection x a) (P.gluedUniversalCoverProjection x b) <
      dist a b := lt_of_not_ge hnot
  let r := (dist (P.gluedUniversalCoverProjection x a) (P.gluedUniversalCoverProjection x b) +
    dist a b) / 2
  have hr : r < targetSystole C g / 2 := by dsimp only [r]; linarith
  have hbbase : P.gluedUniversalCoverProjection x b ∈
      ball (P.gluedUniversalCoverProjection x a) r := by
    rw [mem_ball, dist_comm]
    dsimp only [r]
    linarith
  rw [← P.gluedCurvatureBoundedUniversalCoverProjection_image_ball x a r] at hbbase
  obtain ⟨b', hb', hp⟩ := hbbase
  have hbinj := P.gluedCurvatureBoundedUniversalCoverProjection_injOn_ball x a
    (targetSystole C g / 2) (by linarith)
  have hbhalf : b ∈ ball a (targetSystole C g / 2) := by
    simpa only [mem_ball, dist_comm] using hab
  have hb'half : b' ∈ ball a (targetSystole C g / 2) :=
    ball_subset_ball hr.le hb'
  have hbeq : b' = b := hbinj hb'half hbhalf hp
  rw [hbeq, mem_ball, dist_comm] at hb'
  dsimp only [r] at hb'
  linarith

/-- **Math.** The actual projection is isometric on each quarter-target
cover ball. No local distance formula or native/smooth equality is assumed. -/
theorem gluedCurvatureBoundedUniversalCoverProjection_isometry_ball
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (a : P.basedTopologicalUniversalCover x) :
    letI := P.gluedCurvatureBoundedIntrinsicMetricSpace
    letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
    Isometry (fun b : ball a (targetSystole C g / 4) =>
      P.gluedUniversalCoverProjection x b.val) := by
  letI := P.gluedCurvatureBoundedIntrinsicMetricSpace
  letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
  apply Isometry.of_dist_eq
  intro b c
  change dist (P.gluedUniversalCoverProjection x b.val) (P.gluedUniversalCoverProjection x c.val) =
    dist b.val c.val
  apply P.gluedCurvatureBoundedUniversalCoverProjection_dist_eq_of_lt_half_target x b.val c.val
  have hb : dist b.val a < targetSystole C g / 4 := b.property
  have hc : dist a c.val < targetSystole C g / 4 := by
    simpa only [mem_ball, dist_comm] using c.property
  have htri := dist_triangle b.val a c.val
  linarith

/-- **Math.** The actual smooth projection preserves every continuous
unit-interval curve's metric variation, with no finite-variation premise. -/
theorem gluedCurvatureBoundedUniversalCoverProjection_eVariationOn
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (Γ : I → P.basedTopologicalUniversalCover x) (hΓ : Continuous Γ) :
    letI := P.gluedCurvatureBoundedIntrinsicMetricSpace
    letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
    eVariationOn (P.gluedUniversalCoverProjection x ∘ Γ) univ =
      eVariationOn Γ univ := by
  letI := P.gluedCurvatureBoundedIntrinsicMetricSpace
  letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
  apply eVariationOn_Icc_subtype_eq_of_interior_locally_edist_eq (by norm_num)
    _ _ ((P.gluedUniversalCoverProjection_isCoveringMap x).continuous.comp hΓ) hΓ
  intro t _ _
  have ht : Γ ⁻¹' ball (Γ t) (targetSystole C g / 4) ∈ 𝓝 t :=
    hΓ.continuousAt.preimage_mem_nhds (ball_mem_nhds _ (by linarith [P.target_pos]))
  obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhds_iff.mp ht
  refine ⟨η, hη, ?_⟩
  intro u v hu hv
  exact P.gluedCurvatureBoundedUniversalCoverProjection_isometry_ball x (Γ t)
    ⟨Γ u, hηsub hu⟩ ⟨Γ v, hηsub hv⟩

#print axioms gluedCurvatureBoundedUniversalCoverProjection_lipschitz
#print axioms gluedCurvatureBoundedUniversalCoverProjection_dist_eq_of_lt_half_target
#print axioms gluedCurvatureBoundedUniversalCoverProjection_isometry_ball
#print axioms gluedCurvatureBoundedUniversalCoverProjection_eVariationOn

end SystolicGrowth.ExerciseGluingPreparation

end
