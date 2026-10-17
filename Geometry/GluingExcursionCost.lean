module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingExcursionLength
public import Geometry.GluingSeamExcursionExtraction
public import Geometry.ClosedPathVariation

@[expose] public section

/-!
# Costs of excursions between distinct actual seams

The actual quotient incidence determines which puncture circle contains
each lifted endpoint. Distinct seam labels therefore force the two different
circles of the lifted component, without any extra premise on the lift.
-/

open Set
open scoped ENNReal

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- A component point on a specified glued seam is on exactly its outgoing
or incoming circle, with the corresponding actual edge index. -/
theorem component_mem_gluedSeamCircle_cases
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (x : P.ChainComponent i) (k : Fin (n - 1))
    (hx : P.gluedMk ⟨i, x⟩ ∈ P.gluedSeamCircle k) :
    (i = gluingChainEdgeLeft k ∧ x ∈ range (P.rightCirclePoint i)) ∨
      (i = gluingChainEdgeRight k ∧ x ∈ range (P.leftCirclePoint i)) := by
  obtain ⟨z, hz⟩ := hx
  change P.gluedMk (P.seamSource k z) = P.gluedMk ⟨i, x⟩ at hz
  have hrel : P.chainRelation (P.seamSource k z) (P.seamTarget k z) :=
    ⟨k, z, rfl, rfl⟩
  rcases (P.gluedMk_eq_iff ⟨i, x⟩ (P.seamSource k z)).mp hz.symm with
    heq | hforward | hbackward
  · have hi : i = gluingChainEdgeLeft k := congrArg Sigma.fst heq
    refine Or.inl ⟨hi, ?_⟩
    cases hi
    exact ⟨z, (eq_of_heq (Sigma.mk.inj_iff.mp heq).2).symm⟩
  · exact (P.chainRelation_no_two_step hforward hrel).elim
  · have heq := P.chainRelation_right_unique hbackward hrel
    have hi : i = gluingChainEdgeRight k := congrArg Sigma.fst heq
    refine Or.inr ⟨hi, ?_⟩
    cases hi
    exact ⟨_, (eq_of_heq (Sigma.mk.inj_iff.mp heq).2).symm⟩

/-- Distinct actual seam labels at the endpoints of a seam-avoiding
excursion force its full closed-interval variation to pay `gluingDepth`.
The component lift and both endpoint circles are constructed internally. -/
theorem gluingDepth_le_excursion_variation_of_distinct_seams
    (P : ExerciseGluingPreparation C g n genera X) {a b : ℝ} (hab : a < b)
    (γ : ℝ → P.GluedCarrier) (hγ : ContinuousOn γ (Icc a b))
    (havoid : MapsTo γ (Ioo a b) P.gluedSeamSetᶜ)
    {k l : Fin (n - 1)} (hkl : k ≠ l)
    (ha : γ a ∈ P.gluedSeamCircle k) (hb : γ b ∈ P.gluedSeamCircle l) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    ENNReal.ofReal (gluingDepth C g) ≤ eVariationOn γ (Icc a b) := by
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  obtain ⟨i, δ, _, hlift, _, hbound, _⟩ :=
    P.exists_variation_preserving_component_lift_of_excursion hab γ hγ havoid
  let s : Icc a b := ⟨a, le_rfl, hab.le⟩
  let t : Icc a b := ⟨b, hab.le, le_rfl⟩
  have hs : P.gluedMk ⟨i, δ s⟩ ∈ P.gluedSeamCircle k := by
    rw [← hlift s]
    exact ha
  have ht : P.gluedMk ⟨i, δ t⟩ ∈ P.gluedSeamCircle l := by
    rw [← hlift t]
    exact hb
  have hleft (x : P.ChainComponent i) (hx : x ∈ range (P.leftCirclePoint i)) :
      x.1 ∈ (X i).punctureCircle (P.centers i).1 (gluingRadius C g) := by
    obtain ⟨z, rfl⟩ := hx
    exact ⟨z.1, z.2, rfl⟩
  have hright (x : P.ChainComponent i) (hx : x ∈ range (P.rightCirclePoint i)) :
      x.1 ∈ (X i).punctureCircle (P.centers i).2 (gluingRadius C g) := by
    obtain ⟨z, rfl⟩ := hx
    exact ⟨z.1, z.2, rfl⟩
  have hpay (x y : P.ChainComponent i)
      (hx : x ∈ range (P.leftCirclePoint i))
      (hy : y ∈ range (P.rightCirclePoint i)) :
      ENNReal.ofReal (gluingDepth C g) ≤ edist x.1 y.1 := by
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal
      (P.gluingDepth_le_dist_of_mem_punctureCircles i (hleft x hx) (hright y hy))
  rcases P.component_mem_gluedSeamCircle_cases i (δ s) k hs with
    ⟨hik, hsk⟩ | ⟨hik, hsk⟩ <;>
    rcases P.component_mem_gluedSeamCircle_cases i (δ t) l ht with
      ⟨hil, htl⟩ | ⟨hil, htl⟩
  · have hindex := congrArg Fin.val (hik.symm.trans hil)
    exact (hkl (Fin.ext hindex)).elim
  · exact (hpay (δ t) (δ s) htl hsk).trans (by simpa only [edist_comm] using hbound s t)
  · exact (hpay (δ s) (δ t) hsk htl).trans (hbound s t)
  · have hindex := congrArg Fin.val (hik.symm.trans hil)
    have hkl' : k = l := Fin.ext (by change k.1 + 1 = l.1 + 1 at hindex; omega)
    exact (hkl hkl').elim

#print axioms component_mem_gluedSeamCircle_cases
#print axioms gluingDepth_le_excursion_variation_of_distinct_seams

/-- Every continuous path between different actual seam circles pays the
component-separation cost. Arbitrarily many intervening seam contacts are
allowed; the necessary seam-free excursion is extracted internally. -/
theorem gluingDepth_le_variation_of_distinct_seam_endpoints
    (P : ExerciseGluingPreparation C g n genera X) {A B : ℝ} (hAB : A ≤ B)
    (γ : ℝ → P.GluedCarrier) (hγ : ContinuousOn γ (Icc A B))
    {k l : Fin (n - 1)} (hkl : k ≠ l)
    (hA : γ A ∈ P.gluedSeamCircle k) (hB : γ B ∈ P.gluedSeamCircle l) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    ENNReal.ofReal (gluingDepth C g) ≤ eVariationOn γ (Icc A B) := by
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  obtain ⟨a, b, j, hAa, hab, hbB, hkj, ha, hb, havoid⟩ :=
    P.exists_seam_avoiding_excursion_of_distinct_seam_endpoints hAB γ hγ hkl hA hB
  have hsub : Icc a b ⊆ Icc A B := Icc_subset_Icc hAa hbB
  exact (P.gluingDepth_le_excursion_variation_of_distinct_seams
    hab γ (hγ.mono hsub) havoid hkj ha hb).trans (eVariationOn.mono γ hsub)

/-- A closed path based on an actual seam and meeting a different seam
pays the full target systole: both directions between the seams pay depth.
No regularity or finiteness of the seam-contact set is required. -/
theorem targetSystole_le_variation_of_closed_path_based_on_seam
    (P : ExerciseGluingPreparation C g n genera X) {A B t : ℝ}
    (hAt : A ≤ t) (htB : t ≤ B)
    (γ : ℝ → P.GluedCarrier) (hγ : ContinuousOn γ (Icc A B))
    (hclosed : γ A = γ B) {k l : Fin (n - 1)} (hkl : k ≠ l)
    (hA : γ A ∈ P.gluedSeamCircle k) (ht : γ t ∈ P.gluedSeamCircle l) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    ENNReal.ofReal (targetSystole C g) ≤ eVariationOn γ (Icc A B) := by
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  have hB : γ B ∈ P.gluedSeamCircle k := hclosed ▸ hA
  have hfirst := P.gluingDepth_le_variation_of_distinct_seam_endpoints
    hAt γ (hγ.mono (Icc_subset_Icc le_rfl htB)) hkl hA ht
  have hsecond := P.gluingDepth_le_variation_of_distinct_seam_endpoints
    htB γ (hγ.mono (Icc_subset_Icc hAt le_rfl)) (Ne.symm hkl) ht hB
  have hsum := add_le_add hfirst hsecond
  have hdepth : gluingDepth C g + gluingDepth C g = targetSystole C g := by
    unfold gluingDepth
    ring
  rw [← ENNReal.ofReal_add P.depth_pos.le P.depth_pos.le, hdepth] at hsum
  have hadd : eVariationOn γ (Icc A t) + eVariationOn γ (Icc t B) =
      eVariationOn γ (Icc A B) := by
    simpa only [univ_inter] using
      eVariationOn.Icc_add_Icc (s := univ) γ hAt htB (mem_univ t)
  exact hsum.trans hadd.le

#print axioms gluingDepth_le_variation_of_distinct_seam_endpoints
#print axioms targetSystole_le_variation_of_closed_path_based_on_seam

/-- Any continuous closed path meeting two distinct actual seams pays the
full target systole, regardless of its starting point or seam-contact set.
The direct arc and its constructed complementary arc each pay depth. -/
theorem targetSystole_le_variation_of_closed_path_meeting_distinct_seams
    (P : ExerciseGluingPreparation C g n genera X) {A B u v : ℝ}
    (hAu : A ≤ u) (huv : u ≤ v) (hvB : v ≤ B)
    (γ : ℝ → P.GluedCarrier) (hγ : ContinuousOn γ (Icc A B))
    (hclosed : γ A = γ B) {k l : Fin (n - 1)} (hkl : k ≠ l)
    (hu : γ u ∈ P.gluedSeamCircle k) (hv : γ v ∈ P.gluedSeamCircle l) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    ENNReal.ofReal (targetSystole C g) ≤ eVariationOn γ (Icc A B) := by
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  have hfirst := P.gluingDepth_le_variation_of_distinct_seam_endpoints
    huv γ (hγ.mono (Icc_subset_Icc hAu hvB)) hkl hu hv
  obtain ⟨κ, hκ, hκ0, hκ1, hvar⟩ :=
    exists_closed_path_complementary_arc γ hγ hclosed hAu huv hvB
  have hlen : 0 ≤ (B - v) + (u - A) := add_nonneg (sub_nonneg.mpr hvB)
    (sub_nonneg.mpr hAu)
  have hreturn := P.gluingDepth_le_variation_of_distinct_seam_endpoints
    hlen κ hκ (Ne.symm hkl) (hκ0.symm ▸ hv) (hκ1.symm ▸ hu)
  rw [hvar] at hreturn
  have hsum := add_le_add hfirst hreturn
  have hdepth : gluingDepth C g + gluingDepth C g = targetSystole C g := by
    unfold gluingDepth
    ring
  rw [← ENNReal.ofReal_add P.depth_pos.le P.depth_pos.le, hdepth] at hsum
  have hrest : eVariationOn γ (Icc u v) + eVariationOn γ (Icc v B) =
      eVariationOn γ (Icc u B) := by
    simpa only [univ_inter] using
      eVariationOn.Icc_add_Icc (s := univ) γ huv hvB (mem_univ v)
  have hwhole : eVariationOn γ (Icc A u) + eVariationOn γ (Icc u B) =
      eVariationOn γ (Icc A B) := by
    simpa only [univ_inter] using
      eVariationOn.Icc_add_Icc (s := univ) γ hAu (huv.trans hvB) (mem_univ u)
  calc
    _ ≤ eVariationOn γ (Icc u v) +
        (eVariationOn γ (Icc v B) + eVariationOn γ (Icc A u)) := hsum
    _ = eVariationOn γ (Icc A u) +
        (eVariationOn γ (Icc u v) + eVariationOn γ (Icc v B)) := by ac_rfl
    _ = eVariationOn γ (Icc A B) := by rw [hrest, hwhole]

#print axioms targetSystole_le_variation_of_closed_path_meeting_distinct_seams

end SystolicGrowth.ExerciseGluingPreparation
