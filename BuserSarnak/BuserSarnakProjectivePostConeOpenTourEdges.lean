module

public import BuserSarnak.BuserSarnakProjectiveDualFaceReturn
public import BuserSarnak.BuserSarnakProjectivePostConeRawContour

@[expose] public section

/-!
# Physical entry and exit edges for open child tours

The two occurrences of the incoming dual-tree edge act as sentinels for a
forward child contour. The outgoing face-merge permutation crosses from each
sentinel to the next side of its paired face. Trivial primal-tree factors and
retained singleton factors instead advance within their own face.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete
open scoped Classical

/-- Incoming pivot occurrence in the parent's face. -/
def canonicalProjectivePostConeTreeSlotLeftBoundaryDart
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    CanonicalProjectivePolygonDart p :=
  (slot.left.state, canonicalProjectivePostConeTreeSlot_leftBoundarySide hp hp2 slot)

/-- Incoming pivot occurrence in the child's face. -/
def canonicalProjectivePostConeTreeSlotRightBoundaryDart
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    CanonicalProjectivePolygonDart p :=
  (slot.right.state, canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)

/-- The two sentinels are the actual physical source and target occurrences,
in the orientation chosen by the rooted tree. -/
theorem canonicalProjectivePostConeTreeSlot_boundaryDarts_eq_physicalEndpoints
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    (canonicalProjectivePostConeTreeSlotLeftBoundaryDart hp hp2 slot =
        projectivePolygonPostConeEdgeSourceDart
          (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) ∧
      canonicalProjectivePostConeTreeSlotRightBoundaryDart hp hp2 slot =
        projectivePolygonPostConeEdgeTargetDart
          (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)) ∨
    (canonicalProjectivePostConeTreeSlotLeftBoundaryDart hp hp2 slot =
        projectivePolygonPostConeEdgeTargetDart
          (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) ∧
      canonicalProjectivePostConeTreeSlotRightBoundaryDart hp hp2 slot =
        projectivePolygonPostConeEdgeSourceDart
          (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)) := by
  rcases canonicalProjectivePostConeTreeSlot_endpoints_eq_physicalEndpoints hp hp2 slot with
    hforward | hreverse
  · have hnot : slot.right ≠ projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) := by
      rw [hforward.2]
      exact (canonicalProjectivePostConeTreeSlot_edgeSource_ne_edgeTarget hp hp2 slot).symm
    left
    constructor
    · simp only [canonicalProjectivePostConeTreeSlotLeftBoundaryDart,
        canonicalProjectivePostConeTreeSlot_leftBoundarySide_eq_source hp hp2 slot hforward.1,
        hforward.1, projectivePolygonPostConeEdgeSourceDart]
    · unfold canonicalProjectivePostConeTreeSlotRightBoundaryDart
        canonicalProjectivePostConeTreeSlotRightFactorSide
      rw [if_neg hnot, hforward.2]
      rfl
  · right
    constructor
    · simp only [canonicalProjectivePostConeTreeSlotLeftBoundaryDart,
        canonicalProjectivePostConeTreeSlot_leftBoundarySide_eq_target hp hp2 slot hreverse.1,
        hreverse.1, projectivePolygonPostConeEdgeTargetDart]
    · unfold canonicalProjectivePostConeTreeSlotRightBoundaryDart
        canonicalProjectivePostConeTreeSlotRightFactorSide
      rw [if_pos hreverse.2, hreverse.2]
      rfl

/-- Pairing the parent sentinel gives precisely the child sentinel. -/
theorem canonicalProjectivePostConeTreeSlotRightBoundaryDart_eq_partner
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    canonicalProjectivePostConeTreeSlotRightBoundaryDart hp hp2 slot =
      (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner
        (canonicalProjectivePostConeTreeSlotLeftBoundaryDart hp hp2 slot).1
        (canonicalProjectivePostConeTreeSlotLeftBoundaryDart hp hp2 slot).2 := by
  rcases canonicalProjectivePostConeTreeSlot_boundaryDarts_eq_physicalEndpoints hp hp2 slot with
    hforward | hreverse
  · rw [hforward.1, hforward.2]
    exact projectivePolygonPostConeEdgeTargetDart_eq_partner _
  · rw [hreverse.1, hreverse.2, projectivePolygonPostConeEdgeTargetDart_eq_partner,
      BuserSarnakProjectiveQuotientSectionData.polygonSidePartner_involutive]
    rfl

/-- Pairing the child sentinel returns precisely the parent sentinel. -/
theorem canonicalProjectivePostConeTreeSlotLeftBoundaryDart_eq_partner
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    canonicalProjectivePostConeTreeSlotLeftBoundaryDart hp hp2 slot =
      (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner
        (canonicalProjectivePostConeTreeSlotRightBoundaryDart hp hp2 slot).1
        (canonicalProjectivePostConeTreeSlotRightBoundaryDart hp hp2 slot).2 := by
  rw [canonicalProjectivePostConeTreeSlotRightBoundaryDart_eq_partner,
    BuserSarnakProjectiveQuotientSectionData.polygonSidePartner_involutive]

/-- The parent sentinel is removed by the selected dual tree. -/
theorem canonicalProjectivePostConeTreeSlotLeftBoundaryDart_is_dual_carrier
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    IsCanonicalProjectivePostConeDualTreeCarrier hp hp2
      (canonicalProjectivePostConeTreeSlotLeftBoundaryDart hp hp2 slot) := by
  refine ⟨slot, ?_⟩
  rcases canonicalProjectivePostConeTreeSlot_boundaryDarts_eq_physicalEndpoints hp hp2 slot with
    hforward | hreverse
  · exact Or.inl hforward.1
  · exact Or.inr hreverse.1

/-- The child sentinel is removed by the selected dual tree. -/
theorem canonicalProjectivePostConeTreeSlotRightBoundaryDart_is_dual_carrier
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    IsCanonicalProjectivePostConeDualTreeCarrier hp hp2
      (canonicalProjectivePostConeTreeSlotRightBoundaryDart hp hp2 slot) := by
  rw [canonicalProjectivePostConeTreeSlotRightBoundaryDart_eq_partner,
    canonicalProjectivePostConeDualTreeCarrier_partner_iff]
  exact canonicalProjectivePostConeTreeSlotLeftBoundaryDart_is_dual_carrier hp hp2 slot

/-- The parent sentinel cannot be a retained contour endpoint. -/
theorem canonicalProjectivePostConeTreeSlotLeftBoundaryDart_not_survivor
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    canonicalProjectivePostConeTreeSlotLeftBoundaryDart hp hp2 slot ∉
      canonicalProjectivePostConeSurvivorSet hp hp2 := by
  rw [not_mem_canonicalProjectivePostConeSurvivorSet_iff]
  exact Or.inr (canonicalProjectivePostConeTreeSlotLeftBoundaryDart_is_dual_carrier hp hp2 slot)

/-- The child sentinel cannot be a retained contour endpoint. -/
theorem canonicalProjectivePostConeTreeSlotRightBoundaryDart_not_survivor
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    canonicalProjectivePostConeTreeSlotRightBoundaryDart hp hp2 slot ∉
      canonicalProjectivePostConeSurvivorSet hp hp2 := by
  rw [not_mem_canonicalProjectivePostConeSurvivorSet_iff]
  exact Or.inr (canonicalProjectivePostConeTreeSlotRightBoundaryDart_is_dual_carrier hp hp2 slot)

/-- The parent sentinel enters the child's forward tour immediately after
the incoming pivot. -/
theorem canonicalProjectivePostConeDualFacePerm_leftBoundaryDart
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    canonicalProjectivePostConeDualFacePerm hp hp2
        (canonicalProjectivePostConeTreeSlotLeftBoundaryDart hp hp2 slot) =
      (slot.right.state, (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot).next) := by
  rw [canonicalProjectivePostConeDualFacePerm_apply,
    if_pos (canonicalProjectivePostConeTreeSlotLeftBoundaryDart_is_dual_carrier hp hp2 slot)]
  change (((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner
      (canonicalProjectivePostConeTreeSlotLeftBoundaryDart hp hp2 slot).1
      (canonicalProjectivePostConeTreeSlotLeftBoundaryDart hp hp2 slot).2).1,
    ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner
      (canonicalProjectivePostConeTreeSlotLeftBoundaryDart hp hp2 slot).1
      (canonicalProjectivePostConeTreeSlotLeftBoundaryDart hp hp2 slot).2).2.next) = _
  rw [← canonicalProjectivePostConeTreeSlotRightBoundaryDart_eq_partner]
  rfl

/-- The child sentinel exits into the parent's forward tour immediately
after the parent occurrence of the incoming edge. -/
theorem canonicalProjectivePostConeDualFacePerm_rightBoundaryDart
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    canonicalProjectivePostConeDualFacePerm hp hp2
        (canonicalProjectivePostConeTreeSlotRightBoundaryDart hp hp2 slot) =
      (slot.left.state, (canonicalProjectivePostConeTreeSlot_leftBoundarySide hp hp2 slot).next) := by
  rw [canonicalProjectivePostConeDualFacePerm_apply,
    if_pos (canonicalProjectivePostConeTreeSlotRightBoundaryDart_is_dual_carrier hp hp2 slot)]
  change (((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner
      (canonicalProjectivePostConeTreeSlotRightBoundaryDart hp hp2 slot).1
      (canonicalProjectivePostConeTreeSlotRightBoundaryDart hp hp2 slot).2).1,
    ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner
      (canonicalProjectivePostConeTreeSlotRightBoundaryDart hp hp2 slot).1
      (canonicalProjectivePostConeTreeSlotRightBoundaryDart hp hp2 slot).2).2.next) = _
  rw [← canonicalProjectivePostConeTreeSlotLeftBoundaryDart_eq_partner]
  rfl

/-- A trivial first-stage boundary factor skips a primal-tree side in its
own face, rather than crossing to another face. -/
theorem canonicalProjectivePostConeDualFacePerm_apply_of_boundaryTerm_eq_one
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d : CanonicalProjectivePolygonDart p)
    (hterm : canonicalProjectiveConePostConeBoundaryTerm p d.1 d.2 = 1) :
    canonicalProjectivePostConeDualFacePerm hp hp2 d = (d.1, d.2.next) := by
  obtain ⟨z, hz⟩ :=
    (canonicalProjectiveConePostConeBoundaryTerm_eq_one_iff_primal_carrier hp hp2 d).mp hterm
  have hnot : ¬ IsCanonicalProjectivePostConeDualTreeCarrier hp hp2 d := by
    intro hd
    exact canonicalProjectivePostConeDualTreeCarrier_not_primal hp hp2 d hd ⟨z, hz⟩
  rw [canonicalProjectivePostConeDualFacePerm_apply, if_neg hnot]

/-- A retained physical singleton advances to the next side in its face. -/
theorem canonicalProjectivePostConeDualFacePerm_apply_of_survivor
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d : CanonicalProjectivePolygonDart p)
    (hd : d ∈ canonicalProjectivePostConeSurvivorSet hp hp2) :
    canonicalProjectivePostConeDualFacePerm hp hp2 d = (d.1, d.2.next) := by
  rw [canonicalProjectivePostConeDualFacePerm_apply,
    if_neg ((mem_canonicalProjectivePostConeSurvivorSet_iff hp hp2 d).mp hd).2]

/-- An explicitly classified non-tree signed factor really is retained. -/
theorem canonicalProjectivePostConeBoundaryDart_mem_survivor_of_nonTreeCarrier
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d : CanonicalProjectivePolygonDart p) (z : CanonicalProjectiveConeKeptSymbol p)
    (hcarrier : CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrierBy p d.1 d.2 z)
    (hz : ¬ isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z) :
    d ∈ canonicalProjectivePostConeSurvivorSet hp hp2 := by
  rcases hcarrier with hsource | htarget
  · refine ⟨Sum.inl (⟨z, hz⟩ : CanonicalProjectivePostConeFinalGenerator hp hp2), ?_⟩
    exact Prod.ext (congrArg ProjectivePolygonPostConeFace.state hsource.1).symm
      hsource.2.1.symm
  · refine ⟨Sum.inr (⟨z, hz⟩ : CanonicalProjectivePostConeFinalGenerator hp hp2), ?_⟩
    exact Prod.ext (congrArg ProjectivePolygonPostConeFace.state htarget.1).symm
      htarget.2.1.symm

/-- Both signs of a non-tree singleton have the same physical next-side
rule; the sign does not reverse the face traversal. -/
theorem canonicalProjectivePostConeDualFacePerm_apply_of_nonTreeCarrier
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d : CanonicalProjectivePolygonDart p) (z : CanonicalProjectiveConeKeptSymbol p)
    (hcarrier : CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrierBy p d.1 d.2 z)
    (hz : ¬ isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z) :
    canonicalProjectivePostConeDualFacePerm hp hp2 d = (d.1, d.2.next) := by
  exact canonicalProjectivePostConeDualFacePerm_apply_of_survivor hp hp2 d
    (canonicalProjectivePostConeBoundaryDart_mem_survivor_of_nonTreeCarrier hp hp2 d z hcarrier hz)

/-- A carrier of a slot's label in its parent face identifies the left
sentinel, including its exact physical polygon side. -/
theorem canonicalProjectivePostConeTreeSlotLeftBoundaryDart_eq_of_physicalCarrier
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) (s : ProjectivePolygonSide)
    (hcarrier : CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrierBy p
      slot.left.state s (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)) :
    (slot.left.state, s) = canonicalProjectivePostConeTreeSlotLeftBoundaryDart hp hp2 slot := by
  rcases hcarrier with hsource | htarget
  · have hleft : slot.left = projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) := hsource.1
    unfold canonicalProjectivePostConeTreeSlotLeftBoundaryDart
    rw [canonicalProjectivePostConeTreeSlot_leftBoundarySide_eq_source hp hp2 slot hleft,
      hsource.2.1]
  · have hleft : slot.left = projectivePolygonPostConeEdgeTarget
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) := htarget.1
    unfold canonicalProjectivePostConeTreeSlotLeftBoundaryDart
    rw [canonicalProjectivePostConeTreeSlot_leftBoundarySide_eq_target hp hp2 slot hleft,
      htarget.2.1]

/-- A selected tree carrier at the root is necessarily an outgoing child
sentinel; a rooted arborescence has no incoming edge at its root. -/
theorem canonicalProjectivePostConeTreeSlot_rootBoundaryDart_of_physicalCarrier
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (child : CanonicalProjectivePostConeTreeSlot hp hp2) (s : ProjectivePolygonSide)
    (hcarrier : CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrierBy p
      (canonicalProjectivePostConeTreeRoot hp hp2).state s
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 child)) :
    child.left = canonicalProjectivePostConeTreeRoot hp hp2 ∧
      ((canonicalProjectivePostConeTreeRoot hp hp2).state, s) =
        canonicalProjectivePostConeTreeSlotLeftBoundaryDart hp hp2 child := by
  have hincident : canonicalProjectivePostConeTreeRoot hp hp2 =
        projectivePolygonPostConeEdgeSource (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) ∨
      canonicalProjectivePostConeTreeRoot hp hp2 =
        projectivePolygonPostConeEdgeTarget (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) := by
    rcases hcarrier with hsource | htarget
    · exact Or.inl hsource.1
    · exact Or.inr htarget.1
  have hleft : child.left = canonicalProjectivePostConeTreeRoot hp hp2 := by
    rcases canonicalProjectivePostConeTreeSlot_endpoints_eq_physicalEndpoints hp hp2 child with
      hforward | hreverse
    · rcases hincident with hsource | htarget
      · exact hforward.1.trans hsource.symm
      · exact (canonicalProjectivePostConeTreeSlot_right_ne_root hp hp2 child
          (hforward.2.trans htarget.symm)).elim
    · rcases hincident with hsource | htarget
      · exact (canonicalProjectivePostConeTreeSlot_right_ne_root hp hp2 child
          (hreverse.2.trans hsource.symm)).elim
      · exact hreverse.1.trans htarget.symm
  refine ⟨hleft, ?_⟩
  rw [← hleft] at hcarrier ⊢
  exact canonicalProjectivePostConeTreeSlotLeftBoundaryDart_eq_of_physicalCarrier
    hp hp2 child s hcarrier

/-- The root's tree-factor branch enters exactly after the child's incoming
pivot, independently of the preferred physical orientation of that edge. -/
theorem canonicalProjectivePostConeDualFacePerm_apply_of_root_treeCarrier
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (child : CanonicalProjectivePostConeTreeSlot hp hp2) (s : ProjectivePolygonSide)
    (hcarrier : CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrierBy p
      (canonicalProjectivePostConeTreeRoot hp hp2).state s
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 child)) :
    canonicalProjectivePostConeDualFacePerm hp hp2
        ((canonicalProjectivePostConeTreeRoot hp hp2).state, s) =
      (child.right.state, (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 child).next) := by
  rw [(canonicalProjectivePostConeTreeSlot_rootBoundaryDart_of_physicalCarrier
    hp hp2 child s hcarrier).2]
  exact canonicalProjectivePostConeDualFacePerm_leftBoundaryDart hp hp2 child

/-- A tree factor in a child's face, away from its own incoming pivot, is
precisely the parent-side sentinel of a strictly deeper child slot. -/
theorem canonicalProjectivePostConeTreeSlot_childBoundaryDart_of_nonpivot_carrier
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (parent child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (s : ProjectivePolygonSide)
    (hcarrier : CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrierBy p
      parent.right.state s (canonicalProjectivePostConeTreeSlotLabel hp hp2 child))
    (hs : s ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 parent) :
    parent.right = child.left ∧
      (parent.right.state, s) = canonicalProjectivePostConeTreeSlotLeftBoundaryDart hp hp2 child ∧
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 parent <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child := by
  have hne : child ≠ parent := by
    intro heq
    subst child
    exact hs (canonicalProjectivePostConeTreeSlotRightFactorSide_eq_of_physicalCarrier
      hp hp2 parent s hcarrier)
  have hincident : parent.right = projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) ∨
      parent.right = projectivePolygonPostConeEdgeTarget
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) := by
    rcases hcarrier with hsource | htarget
    · exact Or.inl hsource.1
    · exact Or.inr htarget.1
  have hdepth := (canonicalProjectivePostConeTreeSlot_eq_or_targetDepth_lt_of_incident_right
    hp hp2 parent child hincident).resolve_left hne
  have hright_ne : parent.right ≠ child.right := by
    intro heq
    unfold canonicalProjectivePostConeTreeSlotTargetDepth at hdepth
    rw [heq] at hdepth
    exact (lt_irrefl _) hdepth
  have hleft : parent.right = child.left := by
    rcases canonicalProjectivePostConeTreeSlot_endpoints_eq_physicalEndpoints hp hp2 child with
      hforward | hreverse
    · rcases hincident with hsource | htarget
      · exact hsource.trans hforward.1.symm
      · exact (hright_ne (htarget.trans hforward.2.symm)).elim
    · rcases hincident with hsource | htarget
      · exact (hright_ne (hsource.trans hreverse.2.symm)).elim
      · exact htarget.trans hreverse.1.symm
  refine ⟨hleft, ?_, hdepth⟩
  rcases hcarrier with hsource | htarget
  · have hchild_source : child.left = projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) :=
      hleft.symm.trans hsource.1
    unfold canonicalProjectivePostConeTreeSlotLeftBoundaryDart
    rw [canonicalProjectivePostConeTreeSlot_leftBoundarySide_eq_source hp hp2 child hchild_source]
    exact Prod.ext (congrArg ProjectivePolygonPostConeFace.state hleft) hsource.2.1
  · have hchild_target : child.left = projectivePolygonPostConeEdgeTarget
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) :=
      hleft.symm.trans htarget.1
    unfold canonicalProjectivePostConeTreeSlotLeftBoundaryDart
    rw [canonicalProjectivePostConeTreeSlot_leftBoundarySide_eq_target hp hp2 child hchild_target]
    exact Prod.ext (congrArg ProjectivePolygonPostConeFace.state hleft) htarget.2.1

/-- The deeper-child branch of a local classifier enters exactly after
that child's incoming pivot. -/
theorem canonicalProjectivePostConeDualFacePerm_apply_of_nonpivot_treeCarrier
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (parent child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (s : ProjectivePolygonSide)
    (hcarrier : CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrierBy p
      parent.right.state s (canonicalProjectivePostConeTreeSlotLabel hp hp2 child))
    (hs : s ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 parent) :
    canonicalProjectivePostConeDualFacePerm hp hp2 (parent.right.state, s) =
      (child.right.state, (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 child).next) := by
  rw [(canonicalProjectivePostConeTreeSlot_childBoundaryDart_of_nonpivot_carrier
    hp hp2 parent child s hcarrier hs).2.1]
  exact canonicalProjectivePostConeDualFacePerm_leftBoundaryDart hp hp2 child

#print axioms canonicalProjectivePostConeTreeSlotRightBoundaryDart_eq_partner
#print axioms canonicalProjectivePostConeDualFacePerm_leftBoundaryDart
#print axioms canonicalProjectivePostConeDualFacePerm_rightBoundaryDart
#print axioms canonicalProjectivePostConeDualFacePerm_apply_of_boundaryTerm_eq_one
#print axioms canonicalProjectivePostConeDualFacePerm_apply_of_nonTreeCarrier
#print axioms canonicalProjectivePostConeTreeSlot_childBoundaryDart_of_nonpivot_carrier
#print axioms canonicalProjectivePostConeDualFacePerm_apply_of_nonpivot_treeCarrier

end

end SystolicGrowth
