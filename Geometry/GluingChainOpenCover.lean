module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingSeamNeighborhoods

@[expose] public section

/-!
# Actual prefix/suffix open covers of the glued chain

At each seam, thicken the actual prefix and suffix by the same genuine seam
neighborhood. These are open subsets of the original quotient carrier, they
cover it, and their intersection is precisely the original seam neighborhood.
Representative membership is proved using the actual one-step seam relation;
no surface presentation or genus conclusion is assumed.
-/

open Set

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- The original closed prefix component images at an actual seam cut. -/
def gluedChainPrefix
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    Set P.GluedCarrier :=
  P.gluedMk '' {a | a.1.val ≤ k.val}

/-- The original closed suffix component images at the same cut. -/
def gluedChainSuffix
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    Set P.GluedCarrier :=
  P.gluedMk '' {a | k.val < a.1.val}

/-- Closedness is for the actual image of the original pieces. -/
theorem gluedChainPrefix_isClosed
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    IsClosed (P.gluedChainPrefix k) := by
  apply P.gluedMk_isClosedMap
  have hopen : IsOpen (Sigma.fst ⁻¹' ({i : Fin n | i.val ≤ k.val}ᶜ) : Set P.ChainPieces) :=
    isOpen_sigma_fst_preimage _
  simpa only [preimage_compl, compl_compl, preimage_setOf_eq] using hopen.isClosed_compl

/-- The actual suffix image is also closed in the original quotient. -/
theorem gluedChainSuffix_isClosed
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    IsClosed (P.gluedChainSuffix k) := by
  apply P.gluedMk_isClosedMap
  have hopen : IsOpen (Sigma.fst ⁻¹' ({i : Fin n | k.val < i.val}ᶜ) : Set P.ChainPieces) :=
    isOpen_sigma_fst_preimage _
  simpa only [preimage_compl, compl_compl, preimage_setOf_eq] using hopen.isClosed_compl

/-- The actual closed prefix and suffix exhaust the original glued carrier. -/
theorem gluedChainPrefix_union_suffix
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    P.gluedChainPrefix k ∪ P.gluedChainSuffix k = Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  refine Quotient.inductionOn q ?_
  intro a
  by_cases ha : a.1.val ≤ k.val
  · exact .inl ⟨a, ha, rfl⟩
  · exact .inr ⟨a, lt_of_not_ge ha, rfl⟩

/-- The closed chain sides meet in exactly the original identified circle,
not in a larger collection of seam or component points. -/
theorem gluedChainPrefix_inter_suffix
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    P.gluedChainPrefix k ∩ P.gluedChainSuffix k = P.gluedSeamCircle k := by
  ext q
  constructor
  · rintro ⟨⟨a, ha, haq⟩, ⟨b, hb, hbq⟩⟩
    rcases (P.gluedMk_eq_iff a b).mp (haq.trans hbq.symm) with heq | hrel | hrev
    · subst b
      change a.1.val ≤ k.val at ha
      change k.val < a.1.val at hb
      exact (not_lt_of_ge ha hb).elim
    · obtain ⟨l, z, rfl, rfl⟩ := hrel
      have hl : l = k := by
        apply Fin.ext
        change l.val ≤ k.val at ha
        change k.val < l.val + 1 at hb
        omega
      subst l
      exact ⟨z, haq⟩
    · obtain ⟨l, z, rfl, rfl⟩ := hrev
      change l.val + 1 ≤ k.val at ha
      change k.val < l.val at hb
      omega
  · rintro ⟨z, rfl⟩
    constructor
    · exact ⟨P.seamSource k z, by change k.val ≤ k.val; exact le_rfl, rfl⟩
    · exact ⟨P.seamTarget k z, by change k.val < k.val + 1; omega,
        (P.gluedMk_seamSource_eq_seamTarget k z).symm⟩

/-- The actual prefix through the left component of a cut, thickened by its
genuine two-sided seam neighborhood. -/
def gluedChainPrefixNeighborhood
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    Set P.GluedCarrier :=
  P.gluedChainPrefix k ∪ P.gluedMk '' P.seamNeighborhood k

/-- The actual suffix starting with the right component of a cut, thickened
by the same genuine two-sided seam neighborhood. -/
def gluedChainSuffixNeighborhood
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    Set P.GluedCarrier :=
  P.gluedChainSuffix k ∪ P.gluedMk '' P.seamNeighborhood k

private theorem prefix_or_seam_iff_of_chainRelation
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    {a b : P.ChainPieces} (hab : P.chainRelation a b) :
    (a.1.val ≤ k.val ∨ a ∈ P.seamNeighborhood k) ↔
      (b.1.val ≤ k.val ∨ b ∈ P.seamNeighborhood k) := by
  obtain ⟨l, z, rfl, rfl⟩ := hab
  change (l.val ≤ k.val ∨ P.seamSource l z ∈ P.seamNeighborhood k) ↔
    (l.val + 1 ≤ k.val ∨ P.seamTarget l z ∈ P.seamNeighborhood k)
  rw [P.seamSource_mem_seamNeighborhood_iff, P.seamTarget_mem_seamNeighborhood_iff]
  by_cases hl : l = k
  · simp only [hl, or_true]
  · have hval : l.val ≠ k.val := fun h => hl (Fin.ext h)
    simp only [hl, or_false]
    omega

private theorem suffix_or_seam_iff_of_chainRelation
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    {a b : P.ChainPieces} (hab : P.chainRelation a b) :
    (k.val < a.1.val ∨ a ∈ P.seamNeighborhood k) ↔
      (k.val < b.1.val ∨ b ∈ P.seamNeighborhood k) := by
  obtain ⟨l, z, rfl, rfl⟩ := hab
  change (k.val < l.val ∨ P.seamSource l z ∈ P.seamNeighborhood k) ↔
    (k.val < l.val + 1 ∨ P.seamTarget l z ∈ P.seamNeighborhood k)
  rw [P.seamSource_mem_seamNeighborhood_iff, P.seamTarget_mem_seamNeighborhood_iff]
  by_cases hl : l = k
  · simp only [hl, or_true]
  · have hval : l.val ≠ k.val := fun h => hl (Fin.ext h)
    simp only [hl, or_false]
    omega

private theorem prefix_or_seam_iff_of_chainSetoid
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    {a b : P.ChainPieces} (hab : P.chainSetoid.r a b) :
    (a.1.val ≤ k.val ∨ a ∈ P.seamNeighborhood k) ↔
      (b.1.val ≤ k.val ∨ b ∈ P.seamNeighborhood k) := by
  rcases (P.eqvGen_chainRelation_iff a b).mp hab with heq | hrel | hrev
  · rw [heq]
  · exact prefix_or_seam_iff_of_chainRelation P k hrel
  · exact (prefix_or_seam_iff_of_chainRelation P k hrev).symm

private theorem suffix_or_seam_iff_of_chainSetoid
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    {a b : P.ChainPieces} (hab : P.chainSetoid.r a b) :
    (k.val < a.1.val ∨ a ∈ P.seamNeighborhood k) ↔
      (k.val < b.1.val ∨ b ∈ P.seamNeighborhood k) := by
  rcases (P.eqvGen_chainRelation_iff a b).mp hab with heq | hrel | hrev
  · rw [heq]
  · exact suffix_or_seam_iff_of_chainRelation P k hrel
  · exact (suffix_or_seam_iff_of_chainRelation P k hrev).symm

/-- Exact prefix-cover membership on every original representative. The only
possible cross-cut representative change is in the included seam neighborhood. -/
theorem gluedMk_mem_gluedChainPrefixNeighborhood_iff
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (a : P.ChainPieces) :
    P.gluedMk a ∈ P.gluedChainPrefixNeighborhood k ↔
      a.1.val ≤ k.val ∨ a ∈ P.seamNeighborhood k := by
  constructor
  · rintro (⟨b, hb, hba⟩ | ⟨b, hb, hba⟩)
    · exact (prefix_or_seam_iff_of_chainSetoid P k (Quotient.exact hba)).mp (.inl hb)
    · exact (prefix_or_seam_iff_of_chainSetoid P k (Quotient.exact hba)).mp (.inr hb)
  · rintro (ha | ha)
    · exact .inl ⟨a, ha, rfl⟩
    · exact .inr ⟨a, ha, rfl⟩

/-- Exact suffix-cover membership on every original representative. -/
theorem gluedMk_mem_gluedChainSuffixNeighborhood_iff
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (a : P.ChainPieces) :
    P.gluedMk a ∈ P.gluedChainSuffixNeighborhood k ↔
      k.val < a.1.val ∨ a ∈ P.seamNeighborhood k := by
  constructor
  · rintro (⟨b, hb, hba⟩ | ⟨b, hb, hba⟩)
    · exact (suffix_or_seam_iff_of_chainSetoid P k (Quotient.exact hba)).mp (.inl hb)
    · exact (suffix_or_seam_iff_of_chainSetoid P k (Quotient.exact hba)).mp (.inr hb)
  · rintro (ha | ha)
    · exact .inl ⟨a, ha, rfl⟩
    · exact .inr ⟨a, ha, rfl⟩

/-- The original prefix-cover preimage is precisely the prefix pieces plus
the proved saturated seam domain. -/
theorem preimage_gluedMk_gluedChainPrefixNeighborhood
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    P.gluedMk ⁻¹' P.gluedChainPrefixNeighborhood k =
      {a | a.1.val ≤ k.val} ∪ P.seamNeighborhood k := by
  ext a
  exact P.gluedMk_mem_gluedChainPrefixNeighborhood_iff k a

/-- The original suffix-cover preimage has the corresponding exact form. -/
theorem preimage_gluedMk_gluedChainSuffixNeighborhood
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    P.gluedMk ⁻¹' P.gluedChainSuffixNeighborhood k =
      {a | k.val < a.1.val} ∪ P.seamNeighborhood k := by
  ext a
  exact P.gluedMk_mem_gluedChainSuffixNeighborhood_iff k a

/-- The actual collar-thickened prefix is open in the original quotient topology. -/
theorem gluedChainPrefixNeighborhood_isOpen
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    IsOpen (P.gluedChainPrefixNeighborhood k) := by
  apply isQuotientMap_quotient_mk'.isOpen_preimage.mp
  change IsOpen (P.gluedMk ⁻¹' P.gluedChainPrefixNeighborhood k)
  rw [P.preimage_gluedMk_gluedChainPrefixNeighborhood k]
  exact (isOpen_sigma_fst_preimage {i : Fin n | i.val ≤ k.val}).union
    (P.seamNeighborhood_isOpen k)

/-- The actual collar-thickened suffix is open in the same topology. -/
theorem gluedChainSuffixNeighborhood_isOpen
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    IsOpen (P.gluedChainSuffixNeighborhood k) := by
  apply isQuotientMap_quotient_mk'.isOpen_preimage.mp
  change IsOpen (P.gluedMk ⁻¹' P.gluedChainSuffixNeighborhood k)
  rw [P.preimage_gluedMk_gluedChainSuffixNeighborhood k]
  exact (isOpen_sigma_fst_preimage {i : Fin n | k.val < i.val}).union
    (P.seamNeighborhood_isOpen k)

/-- The two actual thickened chain sides cover the entire original carrier. -/
theorem gluedChainPrefixNeighborhood_union_suffix
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    P.gluedChainPrefixNeighborhood k ∪ P.gluedChainSuffixNeighborhood k = Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  refine Quotient.inductionOn q ?_
  intro a
  by_cases ha : a.1.val ≤ k.val
  · exact .inl ((P.gluedMk_mem_gluedChainPrefixNeighborhood_iff k a).mpr (.inl ha))
  · exact .inr ((P.gluedMk_mem_gluedChainSuffixNeighborhood_iff k a).mpr
      (.inl (lt_of_not_ge ha)))

/-- The overlap is exactly the actual original seam neighborhood, with no
additional component points or substitute cylinder carrier. -/
theorem gluedChainPrefixNeighborhood_inter_suffix
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    P.gluedChainPrefixNeighborhood k ∩ P.gluedChainSuffixNeighborhood k =
      P.gluedMk '' P.seamNeighborhood k := by
  ext q
  refine Quotient.inductionOn q ?_
  intro a
  change (P.gluedMk a ∈ P.gluedChainPrefixNeighborhood k ∧
      P.gluedMk a ∈ P.gluedChainSuffixNeighborhood k) ↔
    P.gluedMk a ∈ P.gluedMk '' P.seamNeighborhood k
  rw [P.gluedMk_mem_gluedChainPrefixNeighborhood_iff,
    P.gluedMk_mem_gluedChainSuffixNeighborhood_iff]
  have hseam : P.gluedMk a ∈ P.gluedMk '' P.seamNeighborhood k ↔
      a ∈ P.seamNeighborhood k := by
    change a ∈ P.gluedMk ⁻¹' (P.gluedMk '' P.seamNeighborhood k) ↔ _
    rw [P.preimage_gluedMk_image_seamNeighborhood k]
  rw [hseam]
  constructor
  · rintro ⟨ha | ha, hb | hb⟩
    · exact (not_lt_of_ge ha hb).elim
    · exact hb
    · exact ha
    · exact ha
  · intro h
    exact ⟨.inr h, .inr h⟩

/-- The closed-side intersection lies in the genuine open overlap. -/
theorem gluedChainPrefix_inter_suffix_subset_seamNeighborhood
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    P.gluedChainPrefix k ∩ P.gluedChainSuffix k ⊆
      P.gluedMk '' P.seamNeighborhood k := by
  rw [P.gluedChainPrefix_inter_suffix k]
  rintro q ⟨z, rfl⟩
  exact ⟨P.seamSource k z, P.seamSource_mem_seamNeighborhood k z, rfl⟩

/-- The opposite closed side meets the thickened prefix only in the overlap. -/
theorem gluedChainPrefixNeighborhood_inter_closedSuffix_subset
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    P.gluedChainPrefixNeighborhood k ∩ P.gluedChainSuffix k ⊆
      P.gluedMk '' P.seamNeighborhood k := by
  rintro q ⟨hq | hq, hsuffix⟩
  · exact P.gluedChainPrefix_inter_suffix_subset_seamNeighborhood k ⟨hq, hsuffix⟩
  · exact hq

/-- The opposite closed side meets the thickened suffix only in the overlap. -/
theorem gluedChainSuffixNeighborhood_inter_closedPrefix_subset
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    P.gluedChainSuffixNeighborhood k ∩ P.gluedChainPrefix k ⊆
      P.gluedMk '' P.seamNeighborhood k := by
  rintro q ⟨hq | hq, hprefix⟩
  · exact P.gluedChainPrefix_inter_suffix_subset_seamNeighborhood k ⟨hprefix, hq⟩
  · exact hq

#print axioms gluedChainPrefix_isClosed
#print axioms gluedChainSuffix_isClosed
#print axioms gluedChainPrefix_union_suffix
#print axioms gluedChainPrefix_inter_suffix
#print axioms gluedMk_mem_gluedChainPrefixNeighborhood_iff
#print axioms gluedMk_mem_gluedChainSuffixNeighborhood_iff
#print axioms gluedChainPrefixNeighborhood_isOpen
#print axioms gluedChainSuffixNeighborhood_isOpen
#print axioms gluedChainPrefixNeighborhood_union_suffix
#print axioms gluedChainPrefixNeighborhood_inter_suffix
#print axioms gluedChainPrefixNeighborhood_inter_closedSuffix_subset
#print axioms gluedChainSuffixNeighborhood_inter_closedPrefix_subset

end SystolicGrowth.ExerciseGluingPreparation
