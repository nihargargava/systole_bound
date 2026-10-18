module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingExcursionLocalGeodesic
public import Geometry.SurfaceLocalGeodesicSystole

@[expose] public section

/-!
# Systolic cost of closed local metric segments missing the seams

The actual component lift preserves the local speed and full variation.
Injectivity of the original component in the glued quotient closes that
lift. The original surface covering then supplies a nonidentity endpoint
deck transformation and pays the component systole. No essentiality premise
is needed; seam contacts at the common basepoint are permitted.
-/

open Set Metric
open scoped ENNReal

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- A closed positive-speed local metric segment whose open parameter
interval misses every seam pays the full target systole. The actual
component lift, its closure and its nonidentity deck endpoint are derived
internally, including when the common basepoint lies on a seam. -/
theorem targetSystole_le_variation_of_closed_seam_avoiding_local_metric_segment
    (P : ExerciseGluingPreparation C g n genera X) {a b speed : ℝ}
    (hab : a < b) (hs : 0 < speed)
    (γ : ℝ → P.GluedCarrier) (hγ : ContinuousOn γ (Icc a b))
    (hclosed : γ a = γ b)
    (havoid : MapsTo γ (Ioo a b) P.gluedSeamSetᶜ)
    (hlocal :
      letI := P.gluedCarrierIntrinsicMetricSpace
      ∀ t : Icc a b, a < t.1 → t.1 < b → ∃ η > 0,
        ∀ u v : Icc a b, dist u t < η → dist v t < η →
          dist (γ u) (γ v) = speed * |(u : ℝ) - (v : ℝ)|) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    ENNReal.ofReal (targetSystole C g) ≤ eVariationOn γ (Icc a b) := by
  letI := P.gluedCarrierIntrinsicMetricSpace
  obtain ⟨i, δ, hδ, hlift, hvariation, hδlocal⟩ :=
    P.exists_locally_metric_segment_component_lift_of_excursion hab γ hγ havoid hlocal
  let s : Icc a b := ⟨a, le_rfl, hab.le⟩
  let t : Icc a b := ⟨b, hab.le, le_rfl⟩
  have hclosedδ : δ s = δ t := by
    apply P.gluedMk_injective_component i
    exact (hlift s).symm.trans (hclosed.trans (hlift t))
  have hclosedf : (δ s).1 = (δ t).1 := congrArg Subtype.val hclosedδ
  have hpay := (X i).systole_le_variation_of_closed_locally_metric_segment
    hab hs (fun u : Icc a b => (δ u).1)
    (continuous_subtype_val.comp hδ) hclosedf hδlocal
  exact ((ENNReal.ofReal_le_ofReal (P.component_systole i)).trans hpay).trans_eq hvariation

#print axioms targetSystole_le_variation_of_closed_seam_avoiding_local_metric_segment

end SystolicGrowth.ExerciseGluingPreparation
