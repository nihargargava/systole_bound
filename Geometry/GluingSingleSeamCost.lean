module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingInnerExcursionCost

@[expose] public section

/-!
# Local metric segments returning to one seam

Every segment between two contacts with the same actual seam either stays
in that seam or pays the full target systole. Other-seam contacts pay both
separation legs; otherwise an attained gap in the arbitrary closed contact
set supplies a returning seam-free excursion. No finite crossing list is used.
-/

open Set Metric
open scoped ENNReal

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- Any path from an actual seam back to that seam and visiting a different
seam pays both separation legs. The two endpoint images need not coincide. -/
theorem targetSystole_le_variation_of_same_seam_endpoints_meeting_other_seam
    (P : ExerciseGluingPreparation C g n genera X) {A B u : ℝ}
    (hAu : A ≤ u) (huB : u ≤ B)
    (γ : ℝ → P.GluedCarrier) (hγ : ContinuousOn γ (Icc A B))
    {k l : Fin (n - 1)} (hkl : k ≠ l)
    (hA : γ A ∈ P.gluedSeamCircle k) (hB : γ B ∈ P.gluedSeamCircle k)
    (hu : γ u ∈ P.gluedSeamCircle l) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    ENNReal.ofReal (targetSystole C g) ≤ eVariationOn γ (Icc A B) := by
  letI := P.gluedCarrierIntrinsicMetricSpace
  have hfirst := P.gluingDepth_le_variation_of_distinct_seam_endpoints
    hAu γ (hγ.mono (Icc_subset_Icc le_rfl huB)) hkl hA hu
  have hsecond := P.gluingDepth_le_variation_of_distinct_seam_endpoints
    huB γ (hγ.mono (Icc_subset_Icc hAu le_rfl)) hkl.symm hu hB
  have hsum := add_le_add hfirst hsecond
  have hdepth : gluingDepth C g + gluingDepth C g = targetSystole C g := by
    unfold gluingDepth
    ring
  rw [← ENNReal.ofReal_add P.depth_pos.le P.depth_pos.le, hdepth] at hsum
  have hadd : eVariationOn γ (Icc A u) + eVariationOn γ (Icc u B) =
      eVariationOn γ (Icc A B) := by
    simpa only [univ_inter] using
      eVariationOn.Icc_add_Icc (s := univ) γ hAu huB (mem_univ u)
  exact hsum.trans hadd.le

/-- A positive-speed local metric segment between two contacts with one
actual seam either stays in that seam or pays the full target systole.
Arbitrarily accumulating seam contacts are permitted. -/
theorem mapsTo_seam_or_targetSystole_le_variation_of_same_seam_endpoints
    (P : ExerciseGluingPreparation C g n genera X) {A B speed : ℝ}
    (_hAB : A < B) (hs : 0 < speed)
    (γ : ℝ → P.GluedCarrier) (hγ : ContinuousOn γ (Icc A B))
    (hlocal :
      letI := P.gluedCarrierIntrinsicMetricSpace
      ∀ t : Icc A B, A < t.1 → t.1 < B → ∃ η > 0,
        ∀ u v : Icc A B, dist u t < η → dist v t < η →
          dist (γ u) (γ v) = speed * |(u : ℝ) - (v : ℝ)|)
    {k : Fin (n - 1)} (hA : γ A ∈ P.gluedSeamCircle k)
    (hB : γ B ∈ P.gluedSeamCircle k) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    MapsTo γ (Icc A B) (P.gluedSeamCircle k) ∨
      ENNReal.ofReal (targetSystole C g) ≤ eVariationOn γ (Icc A B) := by
  classical
  letI := P.gluedCarrierIntrinsicMetricSpace
  by_cases hmaps : MapsTo γ (Icc A B) (P.gluedSeamCircle k)
  · exact Or.inl hmaps
  right
  by_cases hcontacts : ∀ t ∈ Icc A B,
      γ t ∈ P.gluedSeamSet → γ t ∈ P.gluedSeamCircle k
  · change ¬ ∀ u ∈ Icc A B, γ u ∈ P.gluedSeamCircle k at hmaps
    push Not at hmaps
    obtain ⟨u, huIcc, hunotk⟩ := hmaps
    have hunot : γ u ∉ P.gluedSeamSet := fun h => hunotk (hcontacts u huIcc h)
    obtain ⟨a, b, hAa, hau, hub, hbB, ha, hb, havoid⟩ :=
      P.exists_seam_avoiding_excursion_through_of_single_seam_contacts
        huIcc.1 huIcc.2 γ hγ hA hB hunot hcontacts
    have hab : a < b := hau.trans hub
    have hsub : Icc a b ⊆ Icc A B := Icc_subset_Icc hAa hbB
    have hrestricted : ∀ t : Icc a b, a < t.1 → t.1 < b → ∃ η > 0,
        ∀ u v : Icc a b, dist u t < η → dist v t < η →
          dist (γ u) (γ v) = speed * |(u : ℝ) - (v : ℝ)| := by
      intro t hta htb
      obtain ⟨η, hη, hm⟩ := hlocal ⟨t.1, hsub t.2⟩ (hAa.trans_lt hta)
        (htb.trans_le hbB)
      refine ⟨η, hη, ?_⟩
      intro u v hu hv
      exact hm ⟨u.1, hsub u.2⟩ ⟨v.1, hsub v.2⟩ hu hv
    exact (P.targetSystole_le_excursion_variation_of_same_seam hab hs γ
      (hγ.mono hsub) havoid hrestricted ha hb).trans (eVariationOn.mono γ hsub)
  · push Not at hcontacts
    obtain ⟨u, huIcc, huseam, hunotk⟩ := hcontacts
    obtain ⟨l, hul⟩ := mem_iUnion.mp huseam
    have hkl : k ≠ l := by
      intro h
      exact hunotk (h ▸ hul)
    exact P.targetSystole_le_variation_of_same_seam_endpoints_meeting_other_seam
      huIcc.1 huIcc.2 γ hγ hkl hA hB hul

#print axioms targetSystole_le_variation_of_same_seam_endpoints_meeting_other_seam
#print axioms mapsTo_seam_or_targetSystole_le_variation_of_same_seam_endpoints

end SystolicGrowth.ExerciseGluingPreparation
