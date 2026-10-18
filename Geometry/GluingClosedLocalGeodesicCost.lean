module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingSingleSeamCost
public import Geometry.GluingSeamWindingCost
public import Geometry.GluingNoSeamCost
public import Geometry.PeriodicPathVariation

@[expose] public section

/-!
# Global systolic payment by actual closed local metric geodesics

A loop based on a seam either stays in that seam and winds, or contains an
excursion paying the full target. A periodic local metric geodesic can be
rebased at any actual seam contact with the same full variation. If it has
no contact, the original component systole applies. Periodicity and a local
law on the real parameter line include geodesicity at the closing join.
-/

open Set Metric
open scoped ENNReal

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- A closed positive-speed local metric segment based on any actual seam
pays the target, without any restriction on its seam-contact set. -/
theorem targetSystole_le_variation_of_closed_local_metric_segment_based_on_seam
    (P : ExerciseGluingPreparation C g n genera X) {a b speed : ℝ}
    (hab : a < b) (hs : 0 < speed)
    (γ : ℝ → P.GluedCarrier) (hγ : ContinuousOn γ (Icc a b))
    (hclosed : γ a = γ b) {k : Fin (n - 1)}
    (ha : γ a ∈ P.gluedSeamCircle k)
    (hlocal :
      letI := P.gluedCarrierIntrinsicMetricSpace
      ∀ t : Icc a b, a < t.1 → t.1 < b → ∃ η > 0,
        ∀ u v : Icc a b, dist u t < η → dist v t < η →
          dist (γ u) (γ v) = speed * |(u : ℝ) - (v : ℝ)|) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    ENNReal.ofReal (targetSystole C g) ≤ eVariationOn γ (Icc a b) := by
  letI := P.gluedCarrierIntrinsicMetricSpace
  have hb : γ b ∈ P.gluedSeamCircle k := hclosed ▸ ha
  rcases P.mapsTo_seam_or_targetSystole_le_variation_of_same_seam_endpoints
    hab hs γ hγ hlocal ha hb with hseam | hpay
  · let β : Icc a b → P.GluedCarrier := fun t => γ t
    have hβ : Continuous β := continuousOn_iff_continuous_restrict.mp hγ
    have hpay := P.targetSystole_le_variation_of_closed_local_metric_segment_in_seam
      hab hs k β hβ hclosed (fun t => hseam t.2) hlocal
    have hvariation : eVariationOn β univ = eVariationOn γ (Icc a b) := by
      simpa only [β, Function.comp_def, image_univ, Subtype.range_coe_subtype,
        setOf_mem_eq] using
        eVariationOn.comp_eq_of_monotoneOn γ (t := univ)
          (fun t : Icc a b => (t : ℝ)) (fun _ _ _ _ h => h)
    exact hpay.trans_eq hvariation
  · exact hpay

/-- Every continuous periodic positive-speed local metric geodesic on the
actual glued carrier pays the full target over one period. The local law is
on the real parameter line, so the closing join is included. The proof
constructs any needed seam basepoint and makes no finite-contact assumption. -/
theorem targetSystole_le_variation_of_periodic_local_metric_geodesic
    (P : ExerciseGluingPreparation C g n genera X) {T speed : ℝ}
    (hT : 0 < T) (hs : 0 < speed)
    (γ : ℝ → P.GluedCarrier) (hγ : Continuous γ)
    (hperiod : Function.Periodic γ T)
    (hlocal :
      letI := P.gluedCarrierIntrinsicMetricSpace
      ∀ t : ℝ, ∃ η > 0, ∀ u v : ℝ, dist u t < η → dist v t < η →
        dist (γ u) (γ v) = speed * |u - v|) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    ENNReal.ofReal (targetSystole C g) ≤ eVariationOn γ (Icc 0 T) := by
  classical
  letI := P.gluedCarrierIntrinsicMetricSpace
  have hrestricted (a b : ℝ) :
      ∀ t : Icc a b, a < t.1 → t.1 < b → ∃ η > 0,
        ∀ u v : Icc a b, dist u t < η → dist v t < η →
          dist (γ u) (γ v) = speed * |(u : ℝ) - (v : ℝ)| := by
    intro t _ _
    obtain ⟨η, hη, hm⟩ := hlocal t
    exact ⟨η, hη, fun u v hu hv => hm u v hu hv⟩
  by_cases hcontact : ∃ s ∈ Icc (0 : ℝ) T, γ s ∈ P.gluedSeamSet
  · obtain ⟨s, hsIcc, hseam⟩ := hcontact
    obtain ⟨k, hk⟩ := mem_iUnion.mp hseam
    have hclosed : γ s = γ (s + T) := (hperiod s).symm
    have hpay := P.targetSystole_le_variation_of_closed_local_metric_segment_based_on_seam
      (show s < s + T by linarith) hs γ hγ.continuousOn hclosed hk
      (hrestricted s (s + T))
    have hvariation := eVariationOn_Icc_eq_of_periodic_of_mem_period
      γ hT hperiod hsIcc.1 (by simpa only [zero_add] using hsIcc.2)
    simpa only [zero_add] using hpay.trans_eq hvariation
  · have havoid : MapsTo γ (Ioo (0 : ℝ) T) P.gluedSeamSetᶜ := by
      intro t ht hseam
      exact hcontact ⟨t, Ioo_subset_Icc_self ht, hseam⟩
    exact P.targetSystole_le_variation_of_closed_seam_avoiding_local_metric_segment
      hT hs γ hγ.continuousOn (by simpa only [zero_add] using (hperiod 0).symm)
      havoid (hrestricted 0 T)

#print axioms targetSystole_le_variation_of_closed_local_metric_segment_based_on_seam
#print axioms targetSystole_le_variation_of_periodic_local_metric_geodesic

end SystolicGrowth.ExerciseGluingPreparation
