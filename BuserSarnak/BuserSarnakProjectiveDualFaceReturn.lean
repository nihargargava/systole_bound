module

public import BuserSarnak.BuserSarnakProjectivePrimalSurvivorReturn
public import BuserSarnak.FiniteFaceMerge

@[expose] public section

/-!
# The physical dual-face first-return bridge

Swapping paired darts of the selected dual tree changes the face permutation
to its outgoing face-merge permutation. On deleted darts this permutation
agrees with the primal-contracted vertex permutation; from a paired retained
dart their first positive steps also agree. Their retained return endpoints
therefore coincide. This is a physical dynamics statement, not yet an
identification of the literal root-contour cyclic successor.
-/

namespace SystolicGrowth

noncomputable section

open scoped Classical

local instance dualFaceReturnDecidablePred
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    DecidablePred (canonicalProjectivePostConeSurvivorSet hp hp2) :=
  Classical.decPred _

/-- Physical side pairing as an involutive permutation of the original darts. -/
def projectivePolygonPartnerPerm
    {p : ℕ} [NeZero p] (S : BuserSarnakProjectiveQuotientSectionData p) :
    Equiv.Perm (CanonicalProjectivePolygonDart p) where
  toFun d := S.polygonSidePartner d.1 d.2
  invFun d := S.polygonSidePartner d.1 d.2
  left_inv d := S.polygonSidePartner_involutive d.1 d.2
  right_inv d := S.polygonSidePartner_involutive d.1 d.2

@[simp] theorem projectivePolygonPartnerPerm_apply
    {p : ℕ} [NeZero p] (S : BuserSarnakProjectiveQuotientSectionData p)
    (d : CanonicalProjectivePolygonDart p) :
    projectivePolygonPartnerPerm S d = S.polygonSidePartner d.1 d.2 := rfl

/-- The original same-face successor, packaged using `σ = φ * α`. -/
def projectivePolygonFaceSuccessorPerm
    {p : ℕ} [NeZero p] (S : BuserSarnakProjectiveQuotientSectionData p) :
    Equiv.Perm (CanonicalProjectivePolygonDart p) :=
  projectivePolygonVertexRotationPerm S * projectivePolygonPartnerPerm S

@[simp] theorem projectivePolygonFaceSuccessorPerm_apply
    {p : ℕ} [NeZero p] (S : BuserSarnakProjectiveQuotientSectionData p)
    (d : CanonicalProjectivePolygonDart p) :
    projectivePolygonFaceSuccessorPerm S d = (d.1, d.2.next) := by
  change ((S.polygonSidePartner (S.polygonSidePartner d.1 d.2).1
      (S.polygonSidePartner d.1 d.2).2).1,
    (S.polygonSidePartner (S.polygonSidePartner d.1 d.2).1
      (S.polygonSidePartner d.1 d.2).2).2.next) = _
  rw [S.polygonSidePartner_involutive]

/-- Swap the complete physical paired edges selected for dual elimination. -/
def canonicalProjectivePostConeDualTreeSwap
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d : CanonicalProjectivePolygonDart p) : CanonicalProjectivePolygonDart p :=
  if IsCanonicalProjectivePostConeDualTreeCarrier hp hp2 d then
    (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner d.1 d.2
  else d

theorem canonicalProjectivePostConeDualTreeSwap_involutive
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    Function.Involutive (canonicalProjectivePostConeDualTreeSwap hp hp2) := by
  intro d
  by_cases hd : IsCanonicalProjectivePostConeDualTreeCarrier hp hp2 d
  · have hpartner :=
      (canonicalProjectivePostConeDualTreeCarrier_partner_iff hp hp2 d).mpr hd
    simp only [canonicalProjectivePostConeDualTreeSwap, if_pos hd, if_pos hpartner,
      BuserSarnakProjectiveQuotientSectionData.polygonSidePartner_involutive]
  · simp only [canonicalProjectivePostConeDualTreeSwap, if_neg hd]

/-- The dual carrier swap is a genuine permutation, with itself as inverse. -/
def canonicalProjectivePostConeDualTreeSwapPerm
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    Equiv.Perm (CanonicalProjectivePolygonDart p) where
  toFun := canonicalProjectivePostConeDualTreeSwap hp hp2
  invFun := canonicalProjectivePostConeDualTreeSwap hp hp2
  left_inv := canonicalProjectivePostConeDualTreeSwap_involutive hp hp2
  right_inv := canonicalProjectivePostConeDualTreeSwap_involutive hp hp2

@[simp] theorem canonicalProjectivePostConeDualTreeSwapPerm_apply
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d : CanonicalProjectivePolygonDart p) :
    canonicalProjectivePostConeDualTreeSwapPerm hp hp2 d =
      canonicalProjectivePostConeDualTreeSwap hp hp2 d := rfl

/-- The physical outgoing-successor face merge along the selected dual tree. -/
def canonicalProjectivePostConeDualFacePerm
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    Equiv.Perm (CanonicalProjectivePolygonDart p) :=
  projectivePolygonFaceSuccessorPerm (canonicalBuserSarnakProjectiveQuotientSectionData p) *
    canonicalProjectivePostConeDualTreeSwapPerm hp hp2

/-- A selected dual side crosses to the paired face; other sides advance
within the same face. The paired sides themselves have not yet been erased. -/
theorem canonicalProjectivePostConeDualFacePerm_apply
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d : CanonicalProjectivePolygonDart p) :
    canonicalProjectivePostConeDualFacePerm hp hp2 d =
      if IsCanonicalProjectivePostConeDualTreeCarrier hp hp2 d then
        (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonVertexRotateDart d
      else (d.1, d.2.next) := by
  rw [canonicalProjectivePostConeDualFacePerm, Equiv.Perm.mul_apply,
    canonicalProjectivePostConeDualTreeSwapPerm_apply]
  unfold canonicalProjectivePostConeDualTreeSwap
  split_ifs <;> rw [projectivePolygonFaceSuccessorPerm_apply]
  rfl

/-- The face merge and primal-contracted vertex map have the same transitions
at every omitted physical dart. -/
theorem canonicalProjectivePostConeDualFacePerm_eq_primal_of_deleted
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d : CanonicalProjectivePolygonDart p)
    (hd : d ∉ canonicalProjectivePostConeSurvivorSet hp hp2) :
    canonicalProjectivePostConeDualFacePerm hp hp2 d =
      canonicalProjectivePrimalTreeModifiedVertexPerm p d := by
  rcases (not_mem_canonicalProjectivePostConeSurvivorSet_iff hp hp2 d).mp hd with
    hprimal | hdual
  · have hnotdual : ¬ IsCanonicalProjectivePostConeDualTreeCarrier hp hp2 d := by
      intro hdual
      exact canonicalProjectivePostConeDualTreeCarrier_not_primal hp hp2 d hdual hprimal
    rw [canonicalProjectivePostConeDualFacePerm_apply, if_neg hnotdual,
      canonicalProjectivePrimalTreeModifiedVertexPerm_apply_primalCarrier d hprimal]
  · rw [canonicalProjectivePostConeDualFacePerm_apply, if_pos hdual,
      canonicalProjectivePrimalTreeModifiedVertexPerm_apply_dualCarrier hp hp2 d hdual]

/-- Physical pairing on retained darts; it preserves the retained subtype. -/
def canonicalProjectivePostConeSurvivorPartner
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d : canonicalProjectivePostConeSurvivorSet hp hp2) :
    canonicalProjectivePostConeSurvivorSet hp hp2 :=
  ⟨(canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner d.1.1 d.1.2,
    (canonicalProjectivePostConeSurvivorSet_partner_iff hp hp2 d.1).mpr d.2⟩

/-- From a paired retained dart, the first face-merge step is the first
primal-contracted vertex step from the unpaired retained dart. -/
theorem canonicalProjectivePostConeDualFacePerm_partner_eq_primal
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d : canonicalProjectivePostConeSurvivorSet hp hp2) :
    canonicalProjectivePostConeDualFacePerm hp hp2
        (canonicalProjectivePostConeSurvivorPartner hp hp2 d).val =
      canonicalProjectivePrimalTreeModifiedVertexPerm p d.val := by
  have hnotdual :=
    ((mem_canonicalProjectivePostConeSurvivorSet_iff hp hp2
      (canonicalProjectivePostConeSurvivorPartner hp hp2 d).val).mp
      (canonicalProjectivePostConeSurvivorPartner hp hp2 d).property).2
  rw [canonicalProjectivePostConeDualFacePerm_apply, if_neg hnotdual,
    canonicalProjectivePrimalTreeModifiedVertexPerm_apply_survivor hp hp2 d.val d.property]
  rfl

/-- The least retained positive-hit times agree for the two physical traversals. -/
theorem canonicalProjectivePostConeDualFaceFirstReturnTime_partner_eq_primal
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d : canonicalProjectivePostConeSurvivorSet hp hp2) :
    finitePermutationFirstReturnTime (canonicalProjectivePostConeDualFacePerm hp hp2)
        (canonicalProjectivePostConeSurvivorSet hp hp2)
        (canonicalProjectivePostConeSurvivorPartner hp hp2 d) =
      finitePermutationFirstReturnTime (canonicalProjectivePrimalTreeModifiedVertexPerm p)
        (canonicalProjectivePostConeSurvivorSet hp hp2) d := by
  apply finiteOrbitFirstReturnTime_eq_of_deleted_transitions
  · exact canonicalProjectivePostConeDualFacePerm_partner_eq_primal hp hp2 d
  · exact canonicalProjectivePostConeDualFacePerm_eq_primal_of_deleted hp hp2

/-- Exact retained physical endpoint equality. Periodicity supplies both
return-existence proofs, with no orbit or nonempty-survivor hypothesis. -/
theorem canonicalProjectivePostConeDualFaceFirstReturn_partner_eq_primal
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d : canonicalProjectivePostConeSurvivorSet hp hp2) :
    finitePermutationFirstReturn (canonicalProjectivePostConeDualFacePerm hp hp2)
        (canonicalProjectivePostConeSurvivorSet hp hp2)
        (canonicalProjectivePostConeSurvivorPartner hp hp2 d) =
      finitePermutationFirstReturn (canonicalProjectivePrimalTreeModifiedVertexPerm p)
        (canonicalProjectivePostConeSurvivorSet hp hp2) d := by
  apply Subtype.ext
  apply finiteOrbitFirstReturn_val_eq_of_deleted_transitions
  · exact canonicalProjectivePostConeDualFacePerm_partner_eq_primal hp hp2 d
  · exact canonicalProjectivePostConeDualFacePerm_eq_primal_of_deleted hp hp2

/-- Decoded retained vertex return is the dual-face first return started at
the paired physical dart. Literal contour successor identification remains separate. -/
theorem canonicalProjectivePostConeDualFaceFirstReturn_embedding
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d : CanonicalProjectivePostConeSurvivingDart hp hp2) :
    (finitePermutationFirstReturn (canonicalProjectivePostConeDualFacePerm hp hp2)
      (canonicalProjectivePostConeSurvivorSet hp hp2)
      (canonicalProjectivePostConeSurvivorPartner hp hp2
        (canonicalProjectivePostConeSurvivorPhysicalEquiv hp hp2 d))).val =
      canonicalProjectivePostConeSurvivingDart_embedding hp hp2
        (canonicalProjectivePrimalSurvivorReturn hp hp2 d) := by
  rw [canonicalProjectivePostConeDualFaceFirstReturn_partner_eq_primal]
  exact (congrArg Subtype.val
    ((canonicalProjectivePostConeSurvivorPhysicalEquiv hp hp2).apply_symm_apply _)).symm

#print axioms canonicalProjectivePostConeDualTreeSwap_involutive
#print axioms projectivePolygonFaceSuccessorPerm_apply
#print axioms canonicalProjectivePostConeDualFacePerm_eq_primal_of_deleted
#print axioms canonicalProjectivePostConeDualFaceFirstReturnTime_partner_eq_primal
#print axioms canonicalProjectivePostConeDualFaceFirstReturn_partner_eq_primal
#print axioms canonicalProjectivePostConeDualFaceFirstReturn_embedding

end

end SystolicGrowth
