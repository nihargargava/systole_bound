module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.UnitInterval

@[expose] public section

/-!
# Compactness of native unit-interval metric segments

The metric-segment law is closed under pointwise limits. It also supplies a
common Lipschitz bound in a compact target, so Arzelà–Ascoli upgrades the
pointwise compactness to compactness in the continuous-map topology. No
existence or uniqueness of segments is needed for this compactness statement.
-/

open Set Filter Metric
open scoped Topology

namespace SystolicGrowth

/-- All continuous unit-interval segments with their native endpoint speed. -/
def metricUnitSegmentSet (M : Type*) [MetricSpace M] : Set C(unitInterval, M) :=
  {f | ∀ s t : unitInterval,
    dist (f s) (f t) = dist (f 0) (f 1) * |s.val - t.val|}

/-- Metric unit segments form a compact family in any compact metric target. -/
theorem isCompact_metricUnitSegmentSet (M : Type*) [MetricSpace M] [CompactSpace M] :
    IsCompact (metricUnitSegmentSet M) := by
  let S : Set (unitInterval → M) := {f | ∀ s t : unitInterval,
    dist (f s) (f t) = dist (f 0) (f 1) * |s.val - t.val|}
  have hSclosed : IsClosed S := by
    simpa only [S, setOf_forall, Pi.mul_apply] using
      (isClosed_iInter fun s : unitInterval => isClosed_iInter fun t : unitInterval =>
        isClosed_eq ((continuous_apply s).dist (continuous_apply t))
          (((continuous_apply (0 : unitInterval)).dist
            (continuous_apply (1 : unitInterval))).mul continuous_const))
  have himage : ContinuousMap.toFun '' metricUnitSegmentSet M = S := by
    ext f
    constructor
    · rintro ⟨F, hF, rfl⟩
      exact hF
    · intro hf
      have hmetric : ∀ s t : unitInterval,
          dist (f s) (f t) = dist (f 0) (f 1) * |s.val - t.val| := hf
      have hlip : LipschitzWith ⟨dist (f 0) (f 1), dist_nonneg⟩ f := by
        apply LipschitzWith.of_dist_le_mul
        intro s t
        change dist (f s) (f t) ≤ dist (f 0) (f 1) * dist s t
        rw [hmetric s t]
        simp only [Subtype.dist_eq, Real.dist_eq]
        exact le_rfl
      exact ⟨⟨f, hlip.continuous⟩, hf, rfl⟩
  have hpointwise : IsCompact (ContinuousMap.toFun '' metricUnitSegmentSet M) := by
    rw [himage]
    exact isCompact_univ.of_isClosed_subset hSclosed (subset_univ S)
  have hequicontinuous : Equicontinuous
      ((↑) : metricUnitSegmentSet M → unitInterval → M) := by
    refine Metric.equicontinuous_of_continuity_modulus
      (fun t : ℝ => Metric.diam (univ : Set M) * t) ?_ _ ?_
    · have hlim : Tendsto (fun t : ℝ => Metric.diam (univ : Set M) * t)
          (𝓝 0) (𝓝 (Metric.diam (univ : Set M) * 0)) :=
        tendsto_const_nhds.mul tendsto_id
      simpa only [mul_zero] using hlim
    · intro s t F
      have hmetric := F.2 s t
      change dist (F.1 s) (F.1 t) ≤ Metric.diam (univ : Set M) * dist s t
      rw [hmetric]
      have hdiam : dist (F.1 0) (F.1 1) ≤ Metric.diam (univ : Set M) :=
        Metric.dist_le_diam_of_mem isBounded_of_compactSpace (mem_univ _) (mem_univ _)
      simpa only [Subtype.dist_eq, Real.dist_eq] using
        mul_le_mul_of_nonneg_right hdiam (abs_nonneg (s.val - t.val))
  exact ArzelaAscoli.isCompact_of_equicontinuous _ hpointwise hequicontinuous

#print axioms isCompact_metricUnitSegmentSet

end SystolicGrowth
