module

public import BuserSarnak.BuserSarnakProjectivePostConeLeafOrder
public import BuserSarnak.BuserSarnakProjectivePostConeTreeIncidence
public import BuserSarnak.BuserSarnakProjectivePostConePolygonTargetFactors

@[expose] public section

/-!
# Local polygon relations for post-cone tree elimination

A physical tree edge has a preferred orientation, while the canonical
arborescence may traverse it in either direction. This module supplies the
orientation-uniform factor in the polygon relator at a tree slot's target and
the depth comparison which makes all distinct incident tree slots earlier in
the leaf-to-root elimination order.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete

/-- At the arborescence target of a canonical tree slot, the retained label
appears in its incident polygon relator with the sign forced by the physical
orientation of that edge. -/
theorem canonicalProjectivePostConeTreeSlot_polygonWord_factor_at_right
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    (slot.right = projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) ∧
      canonicalProjectiveConePostConePolygonWord p slot.right.state =
        canonicalProjectiveConePostConeBoundaryPrefix p slot.right.state
          (projectivePolygonPostConeEdgeSide
            (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)) *
          FreeGroup.of (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) *
            canonicalProjectiveConePostConeBoundarySuffix p slot.right.state
              (projectivePolygonPostConeEdgeSide
                (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot))) ∨
    (slot.right = projectivePolygonPostConeEdgeTarget
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) ∧
      canonicalProjectiveConePostConePolygonWord p slot.right.state =
        canonicalProjectiveConePostConeBoundaryPrefix p slot.right.state
          (projectivePolygonPostConeEdgeTargetSide
            (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)) *
          (FreeGroup.of (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot))⁻¹ *
            canonicalProjectiveConePostConeBoundarySuffix p slot.right.state
              (projectivePolygonPostConeEdgeTargetSide
                (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot))) := by
  rcases canonicalProjectivePostConeTreeSlot_endpoints_eq_physicalEndpoints hp hp2 slot with
    hforward | hreverse
  · right
    refine ⟨hforward.2, ?_⟩
    simpa only [hforward.2] using
      canonicalProjectiveConePostConePolygonWord_edgeTarget_factor hp hp2
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)
  · left
    refine ⟨hreverse.2, ?_⟩
    simpa only [hreverse.2] using
      canonicalProjectiveConePostConePolygonWord_edgeSource_factor
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)

/-- Whether a tree slot's arborescence target is the preferred physical source
of its retained label. -/
noncomputable def canonicalProjectivePostConeTreeSlotRightIsPhysicalSource
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) : Bool := by
  classical
  exact decide (slot.right = projectivePolygonPostConeEdgeSource
    (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot))

/-- The Boolean right-source flag records exactly the tree-slot endpoint
equality to the label's preferred physical source. -/
theorem canonicalProjectivePostConeTreeSlotRightIsPhysicalSource_eq_true_iff
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    canonicalProjectivePostConeTreeSlotRightIsPhysicalSource hp hp2 slot = true ↔
      slot.right = projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) := by
  classical
  simp [canonicalProjectivePostConeTreeSlotRightIsPhysicalSource]

/-- The polygon side realizing the distinguished tree-label factor at a
slot's arborescence target. -/
noncomputable def canonicalProjectivePostConeTreeSlotRightFactorSide
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) : ProjectivePolygonSide := by
  classical
  exact if slot.right = projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)
    then projectivePolygonPostConeEdgeSide
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)
    else projectivePolygonPostConeEdgeTargetSide
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)

/-- The signed retained-generator factor selected at the target of a tree
slot. -/
noncomputable def canonicalProjectivePostConeTreeSlotRightFactorWord
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    FreeGroup (CanonicalProjectiveConeKeptSymbol p) := by
  classical
  exact if slot.right = projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)
    then FreeGroup.of (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)
    else (FreeGroup.of (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot))⁻¹

/-- A direct orientation-uniform factorization of the polygon relation used
to eliminate a canonical tree slot. -/
theorem canonicalProjectivePostConeTreeSlot_polygonWord_right_factor
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    canonicalProjectiveConePostConePolygonWord p slot.right.state =
      canonicalProjectiveConePostConeBoundaryPrefix p slot.right.state
        (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot) *
        canonicalProjectivePostConeTreeSlotRightFactorWord hp hp2 slot *
          canonicalProjectiveConePostConeBoundarySuffix p slot.right.state
            (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot) := by
  classical
  unfold canonicalProjectivePostConeTreeSlotRightFactorSide
    canonicalProjectivePostConeTreeSlotRightFactorWord
  split_ifs with hsource
  · simpa only [hsource] using
      canonicalProjectiveConePostConePolygonWord_edgeSource_factor
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)
  · have htarget : slot.right = projectivePolygonPostConeEdgeTarget
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) := by
      rcases canonicalProjectivePostConeTreeSlot_right_eq_physicalSource_or_target hp hp2 slot with
        h | h
      · exact (hsource h).elim
      · exact h
    simpa only [htarget] using
      canonicalProjectiveConePostConePolygonWord_edgeTarget_factor hp hp2
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)

/-- A distinct canonical tree slot incident to a slot's target face points
strictly farther from the root. This is the order-theoretic half of the
leaf-elimination invariant. -/
theorem canonicalProjectivePostConeTreeSlot_eq_or_targetDepth_lt_of_incident_right
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot other : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hincident :
      slot.right = projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 other) ∨
      slot.right = projectivePolygonPostConeEdgeTarget
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 other)) :
    other = slot ∨
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other := by
  rcases hincident with hsource | htarget
  · rcases canonicalProjectivePostConeTreeSlot_endpoints_eq_physicalEndpoints hp hp2 other with
      hforward | hreverse
    · right
      exact canonicalProjectivePostConeTreeSlot_targetDepth_lt_of_right_eq_left hp hp2
        (parent := slot) (child := other) (hsource.trans hforward.1.symm)
    · left
      apply canonicalProjectivePostConeTreeSlot_injective_right hp hp2
      exact hreverse.2.trans hsource.symm
  · rcases canonicalProjectivePostConeTreeSlot_endpoints_eq_physicalEndpoints hp hp2 other with
      hforward | hreverse
    · left
      apply canonicalProjectivePostConeTreeSlot_injective_right hp hp2
      exact hforward.2.trans htarget.symm
    · right
      exact canonicalProjectivePostConeTreeSlot_targetDepth_lt_of_right_eq_left hp hp2
        (parent := slot) (child := other) (htarget.trans hreverse.1.symm)

end

end SystolicGrowth
