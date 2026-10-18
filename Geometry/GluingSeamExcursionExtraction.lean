module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingSeamNeighborhoods
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-!
# Extracting an actual excursion between distinct seams

The first contact with any seam different from the initial seam is attained
on the compact parameter interval. The last contact with the initial seam
before that time is also attained. The intervening open interval avoids the
entire actual seam set, with no assumption on the number or kind of contacts.
-/

open Set

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- Any continuous path between distinct actual seams contains a nonempty
seam-avoiding excursion from its initial seam to a different actual seam.
The latter may be an earlier seam than the path's final seam. -/
theorem exists_seam_avoiding_excursion_of_distinct_seam_endpoints
    (P : ExerciseGluingPreparation C g n genera X) {A B : ℝ} (hAB : A ≤ B)
    (γ : ℝ → P.GluedCarrier) (hγ : ContinuousOn γ (Icc A B))
    {k l : Fin (n - 1)} (hkl : k ≠ l)
    (hA : γ A ∈ P.gluedSeamCircle k) (hB : γ B ∈ P.gluedSeamCircle l) :
    ∃ (a b : ℝ) (j : Fin (n - 1)),
      A ≤ a ∧ a < b ∧ b ≤ B ∧ k ≠ j ∧
      γ a ∈ P.gluedSeamCircle k ∧ γ b ∈ P.gluedSeamCircle j ∧
      MapsTo γ (Ioo a b) P.gluedSeamSetᶜ := by
  classical
  let U : Set P.GluedCarrier :=
    ⋃ j : {j : Fin (n - 1) // j ≠ k}, P.gluedSeamCircle j.1
  have hUclosed : IsClosed U :=
    isClosed_iUnion_of_finite fun j => P.gluedSeamCircle_isClosed j.1
  let T : Set ℝ := Icc A B ∩ γ ⁻¹' U
  have hTclosed : IsClosed T :=
    hγ.preimage_isClosed_of_isClosed isClosed_Icc hUclosed
  have hTcompact : IsCompact T :=
    isCompact_Icc.of_isClosed_subset hTclosed inter_subset_left
  have hTne : T.Nonempty :=
    ⟨B, ⟨⟨hAB, le_rfl⟩, mem_iUnion.mpr ⟨⟨l, Ne.symm hkl⟩, hB⟩⟩⟩
  obtain ⟨b, hb, hfirst⟩ := hTcompact.exists_isMinOn hTne continuous_id.continuousOn
  have hbIcc : b ∈ Icc A B := hb.1
  obtain ⟨j, hj⟩ := mem_iUnion.mp hb.2
  have hkj : k ≠ j.1 := Ne.symm j.2
  have hbnotk : γ b ∉ P.gluedSeamCircle k := fun hk =>
    Set.disjoint_left.mp (P.gluedSeamCircle_disjoint hkj) hk hj
  let S : Set ℝ := Icc A b ∩ γ ⁻¹' P.gluedSeamCircle k
  have hγAb : ContinuousOn γ (Icc A b) :=
    hγ.mono (Icc_subset_Icc le_rfl hbIcc.2)
  have hSclosed : IsClosed S :=
    hγAb.preimage_isClosed_of_isClosed isClosed_Icc (P.gluedSeamCircle_isClosed k)
  have hScompact : IsCompact S :=
    isCompact_Icc.of_isClosed_subset hSclosed inter_subset_left
  have hSne : S.Nonempty := ⟨A, ⟨⟨le_rfl, hbIcc.1⟩, hA⟩⟩
  obtain ⟨a, ha, hlast⟩ := hScompact.exists_isMaxOn hSne continuous_id.continuousOn
  have haIcc : a ∈ Icc A b := ha.1
  have hab : a < b := lt_of_le_of_ne haIcc.2 (by
    intro heq
    exact hbnotk (heq ▸ ha.2))
  refine ⟨a, b, j.1, haIcc.1, hab, hbIcc.2, hkj, ha.2, hj, ?_⟩
  intro t ht
  change γ t ∉ P.gluedSeamSet
  intro hseam
  obtain ⟨m, hm⟩ := mem_iUnion.mp hseam
  by_cases hmk : m = k
  · have htS : t ∈ S :=
      ⟨⟨haIcc.1.trans ht.1.le, ht.2.le⟩, hmk ▸ hm⟩
    have hta : t ≤ a := hlast htS
    exact (not_le_of_gt ht.1) hta
  · have htT : t ∈ T :=
      ⟨⟨haIcc.1.trans ht.1.le, ht.2.le.trans hbIcc.2⟩,
        mem_iUnion.mpr ⟨⟨m, hmk⟩, hm⟩⟩
    have hbt : b ≤ t := hfirst htT
    exact (not_le_of_gt ht.2) hbt

#print axioms exists_seam_avoiding_excursion_of_distinct_seam_endpoints

/-- A point outside the full seam set lies in an actual open excursion
between two contacts with the single visited seam. The entire closed contact
set is retained, including infinitely many or accumulating contacts. -/
theorem exists_seam_avoiding_excursion_through_of_single_seam_contacts
    (P : ExerciseGluingPreparation C g n genera X) {A B u : ℝ}
    (hAu : A ≤ u) (huB : u ≤ B) (γ : ℝ → P.GluedCarrier)
    (hγ : ContinuousOn γ (Icc A B)) {k : Fin (n - 1)}
    (hA : γ A ∈ P.gluedSeamCircle k) (hB : γ B ∈ P.gluedSeamCircle k)
    (hu : γ u ∉ P.gluedSeamSet)
    (hcontacts : ∀ t ∈ Icc A B,
      γ t ∈ P.gluedSeamSet → γ t ∈ P.gluedSeamCircle k) :
    ∃ a b : ℝ, A ≤ a ∧ a < u ∧ u < b ∧ b ≤ B ∧
      γ a ∈ P.gluedSeamCircle k ∧ γ b ∈ P.gluedSeamCircle k ∧
      MapsTo γ (Ioo a b) P.gluedSeamSetᶜ := by
  classical
  let S : Set ℝ := Icc A u ∩ γ ⁻¹' P.gluedSeamSet
  let T : Set ℝ := Icc u B ∩ γ ⁻¹' P.gluedSeamSet
  have hγAu : ContinuousOn γ (Icc A u) :=
    hγ.mono (Icc_subset_Icc le_rfl huB)
  have hγuB : ContinuousOn γ (Icc u B) :=
    hγ.mono (Icc_subset_Icc hAu le_rfl)
  have hSclosed : IsClosed S :=
    hγAu.preimage_isClosed_of_isClosed isClosed_Icc P.gluedSeamSet_isClosed
  have hTclosed : IsClosed T :=
    hγuB.preimage_isClosed_of_isClosed isClosed_Icc P.gluedSeamSet_isClosed
  have hScompact : IsCompact S :=
    isCompact_Icc.of_isClosed_subset hSclosed inter_subset_left
  have hTcompact : IsCompact T :=
    isCompact_Icc.of_isClosed_subset hTclosed inter_subset_left
  have hSne : S.Nonempty :=
    ⟨A, ⟨⟨le_rfl, hAu⟩, mem_iUnion.mpr ⟨k, hA⟩⟩⟩
  have hTne : T.Nonempty :=
    ⟨B, ⟨⟨huB, le_rfl⟩, mem_iUnion.mpr ⟨k, hB⟩⟩⟩
  obtain ⟨a, ha, hlast⟩ := hScompact.exists_isMaxOn hSne continuous_id.continuousOn
  obtain ⟨b, hb, hfirst⟩ := hTcompact.exists_isMinOn hTne continuous_id.continuousOn
  have hau : a < u := lt_of_le_of_ne ha.1.2 (by
    intro heq
    exact hu (heq ▸ ha.2))
  have hub : u < b := lt_of_le_of_ne hb.1.1 (by
    intro heq
    exact hu (heq.symm ▸ hb.2))
  refine ⟨a, b, ha.1.1, hau, hub, hb.1.2,
    hcontacts a ⟨ha.1.1, ha.1.2.trans huB⟩ ha.2,
    hcontacts b ⟨hAu.trans hb.1.1, hb.1.2⟩ hb.2, ?_⟩
  intro t ht
  change γ t ∉ P.gluedSeamSet
  intro hseam
  rcases le_total t u with htu | hut
  · have htS : t ∈ S := ⟨⟨ha.1.1.trans ht.1.le, htu⟩, hseam⟩
    exact (not_le_of_gt ht.1) (hlast htS)
  · have htT : t ∈ T := ⟨⟨hut, ht.2.le.trans hb.1.2⟩, hseam⟩
    exact (not_le_of_gt ht.2) (hfirst htT)

#print axioms exists_seam_avoiding_excursion_through_of_single_seam_contacts

end SystolicGrowth.ExerciseGluingPreparation
