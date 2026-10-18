module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingExcursionLength
public import Geometry.SurfaceOrbitLocalIsometry

@[expose] public section

/-!
# Costs of same-circle excursions leaving the actual outer ball

The native circle has its exact inner radius in the original surface metric.
A point outside the actual outer orbit ball is at least the outer radius
from its center. Both legs of a returning excursion therefore pay the collar
depth. The constructed component lift preserves the full metric variation.
-/

open Set
open scoped ENNReal

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- Both radial legs of a returning component excursion that exits its
actual embedded outer orbit ball pay the full target systole together. -/
theorem targetSystole_le_component_variation_of_outer_excursion
    (P : ExerciseGluingPreparation C g n genera X) {a b : ℝ} (hab : a < b)
    (i : Fin n) (δ : Icc a b → P.ChainComponent i) (o : UpperHalfPlane)
    (ha : (δ ⟨a, le_rfl, hab.le⟩).1 ∈
      (X i).punctureCircle o (gluingRadius C g))
    (hb : (δ ⟨b, hab.le, le_rfl⟩).1 ∈
      (X i).punctureCircle o (gluingRadius C g))
    (hout : ∃ t : Icc a b,
      (δ t).1 ∉ (X i).orbitBall o (gluingEmbeddedRadius C g)) :
    ENNReal.ofReal (targetSystole C g) ≤
      eVariationOn (fun t : Icc a b => (δ t).1) univ := by
  let f : Icc a b → (X i).Carrier := fun t => (δ t).1
  let s : Icc a b := ⟨a, le_rfl, hab.le⟩
  let u : Icc a b := ⟨b, hab.le, le_rfl⟩
  let c : (X i).Carrier := Quotient.mk'' o
  have hr : 2 * gluingRadius C g < (X i).systole := by
    linarith [P.radius_lt_embeddedRadius, P.twice_outer_lt_systole i]
  have hrad (x : (X i).Carrier)
      (hx : x ∈ (X i).punctureCircle o (gluingRadius C g)) :
      dist c x = gluingRadius C g := by
    obtain ⟨z, hz, rfl⟩ := hx
    have hcenter := (X i).carrier_dist_mk_center_eq_of_mem_closedBall o
      (gluingRadius C g) hr (Metric.sphere_subset_closedBall hz)
    have hzrad : dist o z = gluingRadius C g := by
      simpa only [Metric.mem_sphere, dist_comm] using hz
    exact hcenter.trans hzrad
  obtain ⟨t, htout⟩ := hout
  have houter : gluingEmbeddedRadius C g ≤ dist c (f t) := by
    apply le_of_not_gt
    intro hlt
    apply htout
    rw [← (X i).carrier_ball_eq_orbitBall o (gluingEmbeddedRadius C g)]
    exact Metric.mem_ball.mpr (by simpa only [dist_comm] using hlt)
  have hpay (x : (X i).Carrier)
      (hx : x ∈ (X i).punctureCircle o (gluingRadius C g)) :
      ENNReal.ofReal (gluingDepth C g) ≤ edist x (f t) := by
    rw [edist_dist]
    apply ENNReal.ofReal_le_ofReal
    have htri := dist_triangle c x (f t)
    rw [hrad x hx] at htri
    dsimp only [gluingEmbeddedRadius] at houter
    linarith
  have hst : s ≤ t := t.2.1
  have htu : t ≤ u := t.2.2
  have hwhole : Icc s u = (univ : Set (Icc a b)) := by
    ext q
    simp only [mem_Icc, mem_univ, iff_true]
    exact q.2
  have hleft : edist (f s) (f t) ≤ eVariationOn f (Icc s t) :=
    eVariationOn.edist_le f ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩
  have hright : edist (f t) (f u) ≤ eVariationOn f (Icc t u) :=
    eVariationOn.edist_le f ⟨le_rfl, htu⟩ ⟨htu, le_rfl⟩
  have hdepth : gluingDepth C g + gluingDepth C g = targetSystole C g := by
    unfold gluingDepth
    ring
  calc
    ENNReal.ofReal (targetSystole C g) =
        ENNReal.ofReal (gluingDepth C g) + ENNReal.ofReal (gluingDepth C g) := by
      rw [← ENNReal.ofReal_add P.depth_pos.le P.depth_pos.le, hdepth]
    _ ≤ edist (f s) (f t) + edist (f t) (f u) := by
      apply add_le_add (hpay (f s) ha)
      simpa only [edist_comm] using hpay (f u) hb
    _ ≤ eVariationOn f (Icc s t) + eVariationOn f (Icc t u) := add_le_add hleft hright
    _ = eVariationOn f univ := by
      simpa only [univ_inter, hwhole] using
        eVariationOn.Icc_add_Icc f (s := univ) hst htu (mem_univ t)

/-- A seam-avoiding excursion has an actual continuous component lift with
exact variation. If that same lift returns to one native puncture circle
after leaving its embedded outer orbit ball, it pays the full target systole.
The exit is a geometric location condition, not an assumed length bound. -/
theorem exists_component_lift_with_outer_excursion_cost
    (P : ExerciseGluingPreparation C g n genera X) {a b : ℝ} (hab : a < b)
    (γ : ℝ → P.GluedCarrier) (hγ : ContinuousOn γ (Icc a b))
    (havoid : MapsTo γ (Ioo a b) P.gluedSeamSetᶜ) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    ∃ (i : Fin n) (δ : Icc a b → P.ChainComponent i),
      Continuous δ ∧ (∀ t : Icc a b, γ t = P.gluedMk ⟨i, δ t⟩) ∧
      eVariationOn (fun t : Icc a b => (δ t).1) univ = eVariationOn γ (Icc a b) ∧
      ∀ o : UpperHalfPlane,
        (δ ⟨a, le_rfl, hab.le⟩).1 ∈ (X i).punctureCircle o (gluingRadius C g) →
        (δ ⟨b, hab.le, le_rfl⟩).1 ∈ (X i).punctureCircle o (gluingRadius C g) →
        (∃ t : Icc a b, (δ t).1 ∉ (X i).orbitBall o (gluingEmbeddedRadius C g)) →
        ENNReal.ofReal (targetSystole C g) ≤ eVariationOn γ (Icc a b) := by
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  obtain ⟨i, δ, hδ, hlift, hvar, _, _⟩ :=
    P.exists_variation_preserving_component_lift_of_excursion hab γ hγ havoid
  refine ⟨i, δ, hδ, hlift, hvar, ?_⟩
  intro o ha hb hout
  rw [← hvar]
  exact targetSystole_le_component_variation_of_outer_excursion P hab i δ o ha hb hout

#print axioms exists_component_lift_with_outer_excursion_cost

end SystolicGrowth.ExerciseGluingPreparation
