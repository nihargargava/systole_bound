module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingIntrinsicMetric
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

/-!
# Midpoints for the actual glued intrinsic metric

A native C¹ path whose integral length is close to the actual intrinsic
distance is split where its distance from the first endpoint is half the
endpoint distance. The native subpath bound and length additivity then
control the remaining half. No metric-speed identity, curvature bound or
smoothness of the tangent metric across the seam is assumed.
Original compactness then turns these approximate midpoints into exact
midpoints for the same native intrinsic metric.
-/

open Set Bundle Manifold
open scoped Manifold Topology Bundle ENNReal

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- Actual near-minimizing C¹ paths give approximate midpoints for the
constructed intrinsic metric, with no additional geometric assumptions. -/
theorem gluedIntrinsicMetric_approximate_midpoint
    (P : ExerciseGluingPreparation C g n genera X) (x y : P.GluedCarrier)
    {ε : ℝ} (hε : 0 < ε) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    ∃ z : P.GluedCarrier,
      dist x z ≤ dist x y / 2 + ε ∧ dist z y ≤ dist x y / 2 + ε := by
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
    ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  have hd : 0 ≤ dist x y := dist_nonneg
  have hr : riemannianEDist (modelWithCornersSelf ℝ ℂ) x y <
      ENNReal.ofReal (dist x y + ε) := by
    change edist x y < ENNReal.ofReal (dist x y + ε)
    rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff (by linarith)]
    linarith
  obtain ⟨γ, hγ0, hγ1, hγ, hlen, _, _⟩ :=
    exists_lt_locally_constant_of_riemannianEDist_lt hr (show (0 : ℝ) < 1 by norm_num)
  have hhalf : dist x y / 2 ∈ Icc (dist x (γ 0)) (dist x (γ 1)) := by
    rw [hγ0, hγ1, dist_self]
    constructor <;> linarith
  obtain ⟨t, ht, htd⟩ := intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num)
    ((continuous_const.dist hγ.continuous).continuousOn) hhalf
  change dist x (γ t) = dist x y / 2 at htd
  have htot : pathELength (modelWithCornersSelf ℝ ℂ) γ 0 1 < ⊤ :=
    hlen.trans ENNReal.ofReal_lt_top
  have hleft : pathELength (modelWithCornersSelf ℝ ℂ) γ 0 t < ⊤ :=
    (pathELength_mono le_rfl ht.2).trans_lt htot
  have hright : pathELength (modelWithCornersSelf ℝ ℂ) γ t 1 < ⊤ :=
    (pathELength_mono ht.1 le_rfl).trans_lt htot
  have hsplit := congrArg ENNReal.toReal
    (pathELength_add (I := modelWithCornersSelf ℝ ℂ) (γ := γ) ht.1 ht.2)
  rw [ENNReal.toReal_add hleft.ne hright.ne] at hsplit
  have htotalReal : (pathELength (modelWithCornersSelf ℝ ℂ) γ 0 1).toReal <
      dist x y + ε := by
    have h := (ENNReal.toReal_lt_toReal htot.ne ENNReal.ofReal_ne_top).2 hlen
    simpa only [ENNReal.toReal_ofReal (by linarith : 0 ≤ dist x y + ε)] using h
  have hleftDist := P.gluedIntrinsicEDist_le_pathELength hγ.contMDiffOn ht.1
  change edist (γ 0) (γ t) ≤ pathELength (modelWithCornersSelf ℝ ℂ) γ 0 t at hleftDist
  have hleftReal := ENNReal.toReal_mono hleft.ne hleftDist
  rw [← dist_edist, hγ0, htd] at hleftReal
  have hrightDist := P.gluedIntrinsicEDist_le_pathELength hγ.contMDiffOn ht.2
  change edist (γ t) (γ 1) ≤ pathELength (modelWithCornersSelf ℝ ℂ) γ t 1 at hrightDist
  have hrightReal := ENNReal.toReal_mono hright.ne hrightDist
  rw [← dist_edist, hγ1] at hrightReal
  refine ⟨γ t, ?_, ?_⟩
  · rw [htd]
    linarith
  · linarith

/-- Compactness of the original carrier and actual approximate midpoints
give an exact midpoint for every pair in the constructed intrinsic metric. -/
theorem gluedIntrinsicMetric_midpoint
    (P : ExerciseGluingPreparation C g n genera X) (x y : P.GluedCarrier) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    ∃ z : P.GluedCarrier,
      dist x z = dist x y / 2 ∧ dist z y = dist x y / 2 := by
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  letI : CompactSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace_compact
  have hc : Continuous (fun z : P.GluedCarrier => max (dist x z) (dist z y)) :=
    (continuous_const.dist continuous_id).max (continuous_id.dist continuous_const)
  obtain ⟨z, _, hmin⟩ := isCompact_univ.exists_isMinOn ⟨x, mem_univ x⟩ hc.continuousOn
  have hm : max (dist x z) (dist z y) ≤ dist x y / 2 := by
    by_contra h
    have hgap : 0 < (max (dist x z) (dist z y) - dist x y / 2) / 2 := by
      have := lt_of_not_ge h
      linarith
    obtain ⟨w, hwx, hwy⟩ := P.gluedIntrinsicMetric_approximate_midpoint x y hgap
    have hzw : max (dist x z) (dist z y) ≤ max (dist x w) (dist w y) :=
      hmin (mem_univ w)
    have hw := max_le hwx hwy
    linarith
  have hx : dist x z ≤ dist x y / 2 := (le_max_left _ _).trans hm
  have hy : dist z y ≤ dist x y / 2 := (le_max_right _ _).trans hm
  have ht := dist_triangle x z y
  refine ⟨z, ?_, ?_⟩ <;> linarith

#print axioms gluedIntrinsicMetric_approximate_midpoint
#print axioms gluedIntrinsicMetric_midpoint

end SystolicGrowth.ExerciseGluingPreparation
