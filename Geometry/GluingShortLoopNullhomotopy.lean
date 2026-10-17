module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingLocalContractibility
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

@[expose] public section

/-!
# A uniform native nullhomotopy radius

Actual compactness and the metric Lebesgue lemma place every sufficiently
short loop inside one proved contractible intrinsic closed ball. The
variation controls every point's distance to the original basepoint; no
essentiality or assumed uniform local-contractibility radius is used.
-/

open Set Metric
open scoped Topology unitInterval ENNReal

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- Every actual loop with variation below one uniform positive intrinsic
radius is nullhomotopic, with its original basepoint fixed. -/
theorem exists_nullhomotopy_radius
    (P : ExerciseGluingPreparation C g n genera X) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    ∃ r > 0, ∀ y : P.GluedCarrier, ∀ β : Path y y,
      eVariationOn β univ < ENNReal.ofReal r → β.Homotopic (Path.refl y) := by
  classical
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  letI : CompactSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace_compact
  choose ε hε hnull using P.gluedIntrinsicMetric_locally_nullhomotopic_loops_in_closedBall
  have hcover : (univ : Set P.GluedCarrier) ⊆
      ⋃ x : P.GluedCarrier, ball x (ε x / 2) := by
    intro x _
    exact mem_iUnion.mpr ⟨x, mem_ball_self (half_pos (hε x))⟩
  obtain ⟨r, hr, hLebesgue⟩ :=
    lebesgue_number_lemma_of_metric isCompact_univ (fun _ => isOpen_ball) hcover
  refine ⟨r, hr, ?_⟩
  intro y β hvariation
  obtain ⟨x, hball⟩ := hLebesgue y (mem_univ y)
  have hy : y ∈ closedBall x (ε x / 2) :=
    ball_subset_closedBall (hball (mem_ball_self hr))
  apply hnull x (ε x / 2) (half_pos (hε x)).le (half_lt_self (hε x)) y hy β
  intro t
  have hdist : edist (β t) y < ENNReal.ofReal r := by
    have hbound := eVariationOn.edist_le β (mem_univ t) (mem_univ (0 : unitInterval))
    rw [β.source] at hbound
    exact hbound.trans_lt hvariation
  exact ball_subset_closedBall (hball (mem_ball.mpr (edist_lt_ofReal.mp hdist)))

#print axioms exists_nullhomotopy_radius

end SystolicGrowth.ExerciseGluingPreparation
