module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Topology.MetricSpace.Gluing
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

/-!
# Attained seam distances in proper metric gluing

These are the metric prerequisites for iterating convex gluing beyond two
hyperbolic slabs. The actual Mathlib quotient is retained. Properness of the
pieces is preserved, and a complete seam attains every cross-piece distance.
No curvature or comparison conclusion is asserted here.
-/

open Set

namespace SystolicGrowth

/-- The actual cross-piece distance is the infimum of genuine seam routes. -/
theorem metricGlue_cross_dist_eq_iInf
    {A B S : Type*} [MetricSpace A] [MetricSpace B] [MetricSpace S] [Nonempty S]
    {Φ : S → A} {Ψ : S → B} (hΦ : Isometry Φ) (hΨ : Isometry Ψ)
    (x : A) (y : B) :
    dist (Metric.toGlueL hΦ hΨ x) (Metric.toGlueR hΦ hΨ y) =
      ⨅ q : S, dist x (Φ q) + dist y (Ψ q) := by
  change Metric.glueDist Φ Ψ 0 (.inl x) (.inr y) = _
  simp [Metric.glueDist]

/-- A complete seam in a proper first piece supplies an attained minimizing
route. The second piece need not be proper. -/
theorem metricGlue_cross_dist_attained
    {A B S : Type*} [MetricSpace A] [MetricSpace B] [MetricSpace S] [Nonempty S]
    [ProperSpace A] [CompleteSpace S]
    {Φ : S → A} {Ψ : S → B} (hΦ : Isometry Φ) (hΨ : Isometry Ψ)
    (x : A) (y : B) :
    ∃ q : S, dist (Metric.toGlueL hΦ hΨ x) (Metric.toGlueR hΦ hΨ y) =
      dist x (Φ q) + dist (Ψ q) y := by
  let q₀ : S := Classical.ofNonempty
  let f : S → ℝ := fun q => dist x (Φ q) + dist y (Ψ q)
  have hf : Continuous f :=
    (continuous_const.dist hΦ.continuous).add (continuous_const.dist hΨ.continuous)
  let K : Set S := f ⁻¹' Iic (f q₀)
  have hKclosed : IsClosed K := isClosed_Iic.preimage hf
  have hKsub : K ⊆ Φ ⁻¹' Metric.closedBall x (f q₀) := by
    intro q hq
    rw [mem_preimage, Metric.mem_closedBall, dist_comm]
    exact (le_add_of_nonneg_right (dist_nonneg : 0 ≤ dist y (Ψ q))).trans hq
  have hprecompact : IsCompact (Φ ⁻¹' Metric.closedBall x (f q₀)) :=
    hΦ.isClosedEmbedding.isCompact_preimage (isCompact_closedBall x (f q₀))
  have hKcompact : IsCompact K := hprecompact.of_isClosed_subset hKclosed hKsub
  have hKne : K.Nonempty := ⟨q₀, show f q₀ ≤ f q₀ from le_rfl⟩
  obtain ⟨q, hq, hmin⟩ := hKcompact.exists_isMinOn hKne hf.continuousOn
  have hminall (w : S) : f q ≤ f w := by
    by_cases hw : w ∈ K
    · exact hmin hw
    · have hwlarge : f q₀ < f w := lt_of_not_ge hw
      exact (hmin (show q₀ ∈ K from show f q₀ ≤ f q₀ from le_rfl)).trans hwlarge.le
  have hbounded : BddBelow (range f) := ⟨0, by rintro _ ⟨w, rfl⟩; positivity⟩
  refine ⟨q, ?_⟩
  rw [metricGlue_cross_dist_eq_iInf hΦ hΨ]
  have hinf : (⨅ w : S, f w) = f q :=
    le_antisymm (ciInf_le hbounded q) (le_ciInf hminall)
  simpa only [f, dist_comm y (Ψ q)] using hinf

/-- Gluing two proper metric pieces preserves properness on the actual
quotient. A ball is contained in the union of two compact copied balls. -/
theorem metricGlue_properSpace
    {A B S : Type*} [MetricSpace A] [MetricSpace B] [MetricSpace S] [Nonempty S]
    [ProperSpace A] [ProperSpace B]
    {Φ : S → A} {Ψ : S → B} (hΦ : Isometry Φ) (hΨ : Isometry Ψ) :
    ProperSpace (Metric.GlueSpace hΦ hΨ) := by
  let L := Metric.toGlueL hΦ hΨ
  let R := Metric.toGlueR hΦ hΨ
  have hL : Isometry L := Metric.toGlueL_isometry hΦ hΨ
  have hR : Isometry R := Metric.toGlueR_isometry hΦ hΨ
  let q₀ : S := Classical.ofNonempty
  have hcomm : L (Φ q₀) = R (Ψ q₀) := congrFun (Metric.toGlue_commute hΦ hΨ) q₀
  refine ⟨fun p r => ?_⟩
  let D := dist (L (Φ q₀)) p + r
  let K := L '' Metric.closedBall (Φ q₀) D ∪ R '' Metric.closedBall (Ψ q₀) D
  have hKcompact : IsCompact K :=
    ((isCompact_closedBall (Φ q₀) D).image hL.continuous).union
      ((isCompact_closedBall (Ψ q₀) D).image hR.continuous)
  apply hKcompact.of_isClosed_subset Metric.isClosed_closedBall
  intro z hz
  have hbound : dist (L (Φ q₀)) z ≤ D := by
    have hzp : dist p z ≤ r := by simpa only [Metric.mem_closedBall, dist_comm z p] using hz
    change dist (L (Φ q₀)) z ≤ dist (L (Φ q₀)) p + r
    exact (dist_triangle (L (Φ q₀)) p z).trans (add_le_add le_rfl hzp)
  induction z using Quotient.inductionOn with
  | h z =>
    cases z with
    | inl x =>
      change dist (L (Φ q₀)) (L x) ≤ D at hbound
      apply Or.inl
      refine ⟨x, ?_, rfl⟩
      rw [Metric.mem_closedBall, dist_comm]
      exact (hL.dist_eq (Φ q₀) x) ▸ hbound
    | inr y =>
      change dist (L (Φ q₀)) (R y) ≤ D at hbound
      apply Or.inr
      refine ⟨y, ?_, rfl⟩
      rw [Metric.mem_closedBall, dist_comm]
      rw [hcomm, hR.dist_eq] at hbound
      exact hbound

#print axioms metricGlue_cross_dist_attained
#print axioms metricGlue_properSpace

end SystolicGrowth
