module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingExcursionLength

@[expose] public section

/-!
# Local metric segments lifted through seam-free excursions

The actual continuous component lift preserves full metric variation.
Intersecting its native local isometry neighborhoods with the original
curve's local constant-speed neighborhoods preserves the same speed in the
component. No global endpoint-distance law is assumed or asserted.
-/

open Set Metric

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- An actual seam-avoiding excursion with a local metric-segment law lifts
to one original component with the same law and full metric variation. -/
theorem exists_locally_metric_segment_component_lift_of_excursion
    (P : ExerciseGluingPreparation C g n genera X) {a b speed : ℝ}
    (hab : a < b) (γ : ℝ → P.GluedCarrier) (hγ : ContinuousOn γ (Icc a b))
    (havoid : MapsTo γ (Ioo a b) P.gluedSeamSetᶜ)
    (hlocal :
      letI := P.gluedCarrierIntrinsicMetricSpace
      ∀ t : Icc a b, a < t.1 → t.1 < b → ∃ η > 0,
        ∀ u v : Icc a b, dist u t < η → dist v t < η →
          dist (γ u) (γ v) = speed * |(u : ℝ) - (v : ℝ)|) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    ∃ (i : Fin n) (δ : Icc a b → P.ChainComponent i),
      Continuous δ ∧ (∀ t : Icc a b, γ t = P.gluedMk ⟨i, δ t⟩) ∧
      eVariationOn (fun t : Icc a b => (δ t).1) univ = eVariationOn γ (Icc a b) ∧
      ∀ t : Icc a b, a < t.1 → t.1 < b → ∃ η > 0,
        ∀ u v : Icc a b, dist u t < η → dist v t < η →
          dist (δ u).1 (δ v).1 = speed * |(u : ℝ) - (v : ℝ)| := by
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  obtain ⟨i, δ, hδ, hlift, hvariation, _hbound, _hcost⟩ :=
    P.exists_variation_preserving_component_lift_of_excursion hab γ hγ havoid
  refine ⟨i, δ, hδ, hlift, hvariation, ?_⟩
  intro t hta htb
  have hnonseam : P.gluedMk ⟨i, δ t⟩ ∉ P.gluedSeamSet := by
    rw [← hlift t]
    exact havoid ⟨hta, htb⟩
  obtain ⟨η₁, hη₁, hmetric⟩ :=
    P.continuous_component_lift_locally_dist_eq i δ hδ t hnonseam
  obtain ⟨η₂, hη₂, hspeed⟩ := hlocal t hta htb
  refine ⟨min η₁ η₂, lt_min hη₁ hη₂, ?_⟩
  intro u v hut hvt
  have hdist : dist (δ u).1 (δ v).1 = dist (γ u) (γ v) := by
    simpa only [hlift u, hlift v] using
      hmetric u v (hut.trans_le (min_le_left _ _)) (hvt.trans_le (min_le_left _ _))
  exact hdist.trans
    (hspeed u v (hut.trans_le (min_le_right _ _)) (hvt.trans_le (min_le_right _ _)))

#print axioms exists_locally_metric_segment_component_lift_of_excursion

end SystolicGrowth.ExerciseGluingPreparation
