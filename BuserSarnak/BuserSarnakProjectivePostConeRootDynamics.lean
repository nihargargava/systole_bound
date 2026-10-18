module

public import BuserSarnak.BuserSarnakProjectivePostConeForwardTourDecode
public import BuserSarnak.BuserSarnakProjectivePostConeRootPhysicalDecode

@[expose] public section

/-!
# Literal root-contour dynamics

Identify the actual ordered endpoint list with the constructed physical
tour. Cyclic successor is first return of the dual-face map `G`; composing
with the literal partner is first return of the primal map `F`. Thus the
actual root rotation, not an auxiliary support permutation, has one orbit.
-/

namespace SystolicGrowth

noncomputable section

open scoped Classical

local instance rootDynamicsDecidablePred
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    DecidablePred (canonicalProjectivePostConeSurvivorSet hp hp2) :=
  Classical.decPred _

/-- Normalized root insertions decode as the constructed physical child
tours for either sign of each selected edge. -/
theorem canonicalProjectivePostConeRawForwardRootPhysicalTermOfCase_eq_forward
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide)
    (c : CanonicalProjectivePostConeRawRootContourTermCase hp hp2 q s) :
    canonicalProjectivePostConeRawForwardRootPhysicalTermOfCase hp hp2 q s c =
      canonicalProjectivePostConeForwardPhysicalRootTermOfCase hp hp2 q s c := by
  cases c with
  | one _ => rfl
  | finalSource _ _ _ => rfl
  | finalTarget _ _ _ => rfl
  | treeSource _ _ _ =>
      exact canonicalProjectivePostConeRawForwardTreePhysicalList_eq_forwardPhysicalTreeWord
        hp hp2 _
  | treeTarget _ _ _ =>
      exact canonicalProjectivePostConeRawForwardTreePhysicalList_eq_forwardPhysicalTreeWord
        hp hp2 _

/-- The literal occurrence decoder equals the physical tour as an ordered
list; no cyclic reindexing or reduction is hidden in this equality. -/
theorem canonicalProjectivePostConeRawRootPhysicalList_eq_forwardPhysicalRootWord
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    canonicalProjectivePostConeRawRootPhysicalList hp hp2 =
      canonicalProjectivePostConeForwardPhysicalRootWord hp hp2
        (canonicalProjectivePostConeTreeRoot hp hp2).state := by
  rw [canonicalProjectivePostConeRawRootPhysicalList_eq_forwardExpansion]
  unfold canonicalProjectivePostConeForwardPhysicalRootWord
  congr 1
  funext s
  exact canonicalProjectivePostConeRawForwardRootPhysicalTermOfCase_eq_forward hp hp2 _ s _

/-- The exact root endpoint list closes with a positive omitted-only gap,
including its last-to-first seam. -/
theorem canonicalProjectivePostConeRawRootPhysicalList_isChain
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    (canonicalProjectivePostConeRawRootPhysicalList hp hp2 ++
      (canonicalProjectivePostConeRawRootPhysicalList hp hp2).take 1).IsChain
        (PositiveOrbitGap (canonicalProjectivePostConeDualFacePerm hp hp2)
          (fun d => d ∈ canonicalProjectivePostConeSurvivorSet hp hp2)) := by
  rw [canonicalProjectivePostConeRawRootPhysicalList_eq_forwardPhysicalRootWord]
  exact canonicalProjectivePostConeForwardPhysicalRootWord_isChain hp hp2

/-- Every literal cyclic successor is the next retained physical point of
the actual dual-face traversal. -/
theorem canonicalProjectivePostConeRawRootContourPosition_successor_gap
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (i : Fin (canonicalProjectivePostConeRawRootContour hp hp2).length) :
    PositiveOrbitGap (canonicalProjectivePostConeDualFacePerm hp hp2)
      (fun d => d ∈ canonicalProjectivePostConeSurvivorSet hp hp2)
      (canonicalProjectivePostConeRawRootContourPosition_physicalEmbedding hp hp2 i)
      (canonicalProjectivePostConeRawRootContourPosition_physicalEmbedding hp hp2
        (cyclicSucc i)) :=
  isChain_cyclic_ofFn _ (canonicalProjectivePostConeRawRootPhysicalList_isChain hp hp2) i

/-- Literal cyclic successor equals exact positive first return of `G` on
the survivor subtype, without a supplied successor-law hypothesis. -/
theorem canonicalProjectivePostConeRawRootContourPosition_successor_firstReturn
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (i : Fin (canonicalProjectivePostConeRawRootContour hp hp2).length) :
    finitePermutationFirstReturn (canonicalProjectivePostConeDualFacePerm hp hp2)
        (canonicalProjectivePostConeSurvivorSet hp hp2)
        (canonicalProjectivePostConeRawRootContourPosition_physicalEquiv hp hp2 i) =
      canonicalProjectivePostConeRawRootContourPosition_physicalEquiv hp hp2
        (cyclicSucc i) := by
  apply Subtype.ext
  exact PositiveOrbitGap.firstReturn_val_eq _ _
    (canonicalProjectivePostConeRawRootContourPosition_successor_gap hp hp2 i)
    (canonicalProjectivePostConeRawRootContourPosition_physicalEquiv hp hp2
      (cyclicSucc i)).property

/-- Literal opposite-sign pairing is physical pairing on the retained
subtype as well as on its original dart values. -/
theorem canonicalProjectivePostConeRawRootContourPosition_partner_physicalEquiv
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (i : Fin (canonicalProjectivePostConeRawRootContour hp hp2).length) :
    canonicalProjectivePostConeRawRootContourPosition_physicalEquiv hp hp2
        (canonicalProjectivePostConeRawRootContour_partner hp hp2 i) =
      canonicalProjectivePostConeSurvivorPartner hp hp2
        (canonicalProjectivePostConeRawRootContourPosition_physicalEquiv hp hp2 i) := by
  apply Subtype.ext
  exact canonicalProjectivePostConeRawRootContourPosition_physicalEmbedding_partner hp hp2 i

/-- The actual successor-after-partner rotation is the retained first
return of the proved transitive primal-contracted vertex permutation. -/
theorem canonicalProjectivePostConeRawRootContourPosition_rotation_firstReturn
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (i : Fin (canonicalProjectivePostConeRawRootContour hp hp2).length) :
    canonicalProjectivePostConeRawRootContourPosition_physicalEquiv hp hp2
        (canonicalProjectivePostConeRawRootContour_rotation hp hp2 i) =
      finitePermutationFirstReturn (canonicalProjectivePrimalTreeModifiedVertexPerm p)
        (canonicalProjectivePostConeSurvivorSet hp hp2)
        (canonicalProjectivePostConeRawRootContourPosition_physicalEquiv hp hp2 i) := by
  have h := canonicalProjectivePostConeRawRootContourPosition_successor_firstReturn
    hp hp2 (canonicalProjectivePostConeRawRootContour_partner hp hp2 i)
  rw [canonicalProjectivePostConeRawRootContourPosition_partner_physicalEquiv,
    canonicalProjectivePostConeDualFaceFirstReturn_partner_eq_primal] at h
  exact h.symm

/-- The literal root-contour rotation has one orbit, with no orbit,
successor-compatibility, or global nonemptiness premise. -/
theorem canonicalProjectivePostConeRawRootContour_rotation_one_orbit
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    ∀ i j : Fin (canonicalProjectivePostConeRawRootContour hp hp2).length,
      ∃ n : ℕ, (canonicalProjectivePostConeRawRootContour_rotation hp hp2)^[n] i = j := by
  let e := canonicalProjectivePostConeRawRootContourPosition_physicalEquiv hp hp2
  apply one_orbit_of_conjugate
    (finitePermutationFirstReturn (canonicalProjectivePrimalTreeModifiedVertexPerm p)
      (canonicalProjectivePostConeSurvivorSet hp hp2))
    (canonicalProjectivePostConeRawRootContour_rotation hp hp2) e.symm
  · intro x
    apply e.injective
    rw [e.apply_symm_apply]
    have h := canonicalProjectivePostConeRawRootContourPosition_rotation_firstReturn
      hp hp2 (e.symm x)
    simpa only [e, Equiv.apply_symm_apply] using h.symm
  · exact finitePermutationFirstReturn_one_orbit _ _
      (canonicalProjectivePrimalTreeModifiedVertexPerm_one_orbit p)

#print axioms canonicalProjectivePostConeRawRootPhysicalList_eq_forwardPhysicalRootWord
#print axioms canonicalProjectivePostConeRawRootContourPosition_successor_firstReturn
#print axioms canonicalProjectivePostConeRawRootContourPosition_rotation_firstReturn
#print axioms canonicalProjectivePostConeRawRootContour_rotation_one_orbit

end

end SystolicGrowth
