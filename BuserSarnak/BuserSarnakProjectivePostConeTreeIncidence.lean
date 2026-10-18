module

public import BuserSarnak.BuserSarnakProjectivePostConePolygonFactors

@[expose] public section

/-!
# Incidence of canonical post-cone tree slots

The canonical physical spanning tree lives in the symmetrization of the
post-cone edge quiver, whereas each retained label has a preferred physical
orientation.  This module makes the underlying physical edge of a tree slot
explicit, records its endpoints, and packages the arborescence's unique
incoming-arrow property for later leaf-to-root elimination.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete

/-- Forget the arborescence orientation of a canonical tree slot and recover
the corresponding positively oriented physical post-cone edge. -/
noncomputable def canonicalProjectivePostConeTreeSlotUnderlyingPhysicalArrow
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    Quiver.Total (ProjectivePolygonPostConeFace p) := by
  letI : Quiver.Arborescence (projectivePolygonPostConeCanonicalSpanningTree hp hp2) :=
    projectivePolygonPostConeCanonicalSpanningTreeArborescence hp hp2
  exact ((ReidemeisterSchreier.Quiver.coveredArrowEquivTotal
    (projectivePolygonPostConeCanonicalSpanningTree hp hp2)).symm slot).1

/-- The retained label of a tree slot is the label of its recovered physical
edge. -/
theorem canonicalProjectivePostConeTreeSlotUnderlyingPhysicalArrow_label
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    (canonicalProjectivePostConeTreeSlotUnderlyingPhysicalArrow hp hp2 slot).hom.1 =
      canonicalProjectivePostConeTreeSlotLabel hp hp2 slot := by
  rfl

/-- The underlying physical arrow is the inverse image of its retained label
under the total-arrow/label equivalence. -/
theorem canonicalProjectivePostConeTreeSlotUnderlyingPhysicalArrow_eq_symm_label
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    (projectivePolygonPostConeTotalEquivKept p).symm
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) =
      canonicalProjectivePostConeTreeSlotUnderlyingPhysicalArrow hp hp2 slot := by
  exact (projectivePolygonPostConeTotalEquivKept p).symm_apply_apply _

/-- The recovered physical arrow starts at the preferred physical source of
the retained label. -/
theorem canonicalProjectivePostConeTreeSlotUnderlyingPhysicalArrow_left
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    (canonicalProjectivePostConeTreeSlotUnderlyingPhysicalArrow hp hp2 slot).left =
      projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) := by
  have h := congrArg Quiver.Total.left
    (canonicalProjectivePostConeTreeSlotUnderlyingPhysicalArrow_eq_symm_label
      hp hp2 slot)
  simpa [projectivePolygonPostConeTotalEquivKept] using h.symm

/-- The recovered physical arrow ends at the preferred physical target of
the retained label. -/
theorem canonicalProjectivePostConeTreeSlotUnderlyingPhysicalArrow_right
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    (canonicalProjectivePostConeTreeSlotUnderlyingPhysicalArrow hp hp2 slot).right =
      projectivePolygonPostConeEdgeTarget
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) := by
  have h := congrArg Quiver.Total.right
    (canonicalProjectivePostConeTreeSlotUnderlyingPhysicalArrow_eq_symm_label
      hp hp2 slot)
  simpa [projectivePolygonPostConeTotalEquivKept] using h.symm

/-- A canonical tree arrow follows the preferred physical orientation of its
label or its formal reverse. -/
theorem canonicalProjectivePostConeTreeSlot_endpoints_eq_physicalEndpoints
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    (slot.left = projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) ∧
      slot.right = projectivePolygonPostConeEdgeTarget
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)) ∨
    (slot.left = projectivePolygonPostConeEdgeTarget
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) ∧
      slot.right = projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)) := by
  letI : Quiver.Arborescence (projectivePolygonPostConeCanonicalSpanningTree hp hp2) :=
    projectivePolygonPostConeCanonicalSpanningTreeArborescence hp hp2
  rcases slot with ⟨left, right, ⟨edge, hedge⟩⟩
  change (@Quiver.Hom (ProjectivePolygonPostConeFace p) _ left right) ⊕
    (@Quiver.Hom (ProjectivePolygonPostConeFace p) _ right left) at edge
  cases edge with
  | inl edge =>
      rcases edge with ⟨z, hsource, htarget⟩
      left
      constructor
      · change left = projectivePolygonPostConeEdgeSource z
        exact hsource.symm
      · change right = projectivePolygonPostConeEdgeTarget z
        exact htarget.symm
  | inr edge =>
      rcases edge with ⟨z, hsource, htarget⟩
      right
      constructor
      · change left = projectivePolygonPostConeEdgeTarget z
        exact htarget.symm
      · change right = projectivePolygonPostConeEdgeSource z
        exact hsource.symm

/-- The arborescence source of a tree slot is one endpoint of its retained
physical edge. -/
theorem canonicalProjectivePostConeTreeSlot_left_eq_physicalSource_or_target
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    slot.left = projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) ∨
      slot.left = projectivePolygonPostConeEdgeTarget
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) := by
  rcases canonicalProjectivePostConeTreeSlot_endpoints_eq_physicalEndpoints hp hp2 slot with
    hforward | hreverse
  · exact Or.inl hforward.1
  · exact Or.inr hreverse.1

/-- The arborescence target of a tree slot is one endpoint of its retained
physical edge. -/
theorem canonicalProjectivePostConeTreeSlot_right_eq_physicalSource_or_target
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    slot.right = projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) ∨
      slot.right = projectivePolygonPostConeEdgeTarget
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) := by
  rcases canonicalProjectivePostConeTreeSlot_endpoints_eq_physicalEndpoints hp hp2 slot with
    hforward | hreverse
  · exact Or.inr hforward.2
  · exact Or.inl hreverse.2

/-- The polygon word containing a tree-slot label is based at one endpoint of
the arborescence arrow; the label remains an explicit positive factor there.
The disjunction is essential because the geodesic arborescence may orient a
physical edge either way. -/
theorem canonicalProjectivePostConeTreeSlot_polygonWord_factor_at_left_or_right
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    (canonicalProjectiveConePostConePolygonWord p slot.left.state =
        canonicalProjectiveConePostConeBoundaryPrefix p slot.left.state
          (projectivePolygonPostConeEdgeSide
            (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)) *
          FreeGroup.of (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) *
            canonicalProjectiveConePostConeBoundarySuffix p slot.left.state
              (projectivePolygonPostConeEdgeSide
                (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot))) ∨
      (canonicalProjectiveConePostConePolygonWord p slot.right.state =
        canonicalProjectiveConePostConeBoundaryPrefix p slot.right.state
          (projectivePolygonPostConeEdgeSide
            (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)) *
          FreeGroup.of (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) *
            canonicalProjectiveConePostConeBoundarySuffix p slot.right.state
              (projectivePolygonPostConeEdgeSide
                (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot))) := by
  have hfactor := canonicalProjectiveConePostConePolygonWord_edgeSource_factor
    (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)
  rcases canonicalProjectivePostConeTreeSlot_endpoints_eq_physicalEndpoints hp hp2 slot with
    hforward | hreverse
  · left
    simpa only [hforward.1] using hfactor
  · right
    simpa only [hreverse.2] using hfactor

/-- The designated root face of the canonical physical spanning tree.  This
explicit name avoids requiring an arborescence instance merely to mention the
root in downstream statements. -/
abbrev canonicalProjectivePostConeTreeRoot
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    projectivePolygonPostConeCanonicalSpanningTree hp hp2 :=
  projectivePolygonPostConeRoot p

/-- Every canonical tree slot ends away from the arborescence root. -/
theorem canonicalProjectivePostConeTreeSlot_right_ne_root
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    slot.right ≠ canonicalProjectivePostConeTreeRoot hp hp2 := by
  letI : Quiver.Arborescence (projectivePolygonPostConeCanonicalSpanningTree hp hp2) :=
    projectivePolygonPostConeCanonicalSpanningTreeArborescence hp hp2
  change slot.right ≠ Quiver.root (projectivePolygonPostConeCanonicalSpanningTree hp hp2)
  exact (ReidemeisterSchreier.Quiver.Arborescence.totalEquivNonRoot
    (projectivePolygonPostConeCanonicalSpanningTree hp hp2) slot).2

/-- A canonical physical-tree arrow is uniquely determined by its
arborescence target face. -/
theorem canonicalProjectivePostConeTreeSlot_injective_right
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    Function.Injective (fun slot : CanonicalProjectivePostConeTreeSlot hp hp2 => slot.right) := by
  letI : Quiver.Arborescence (projectivePolygonPostConeCanonicalSpanningTree hp hp2) :=
    projectivePolygonPostConeCanonicalSpanningTreeArborescence hp hp2
  intro s t hright
  apply (ReidemeisterSchreier.Quiver.Arborescence.totalEquivNonRoot
    (projectivePolygonPostConeCanonicalSpanningTree hp hp2)).injective
  apply Subtype.ext
  exact hright

/-- The unique incoming canonical physical-tree slot at a non-root face. -/
noncomputable def canonicalProjectivePostConeTreeIncomingSlot
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : projectivePolygonPostConeCanonicalSpanningTree hp hp2)
    (hq : q ≠ canonicalProjectivePostConeTreeRoot hp hp2) :
    CanonicalProjectivePostConeTreeSlot hp hp2 := by
  letI : Quiver.Arborescence (projectivePolygonPostConeCanonicalSpanningTree hp hp2) :=
    projectivePolygonPostConeCanonicalSpanningTreeArborescence hp hp2
  change q ≠ Quiver.root (projectivePolygonPostConeCanonicalSpanningTree hp hp2) at hq
  exact (ReidemeisterSchreier.Quiver.Arborescence.totalEquivNonRoot
    (projectivePolygonPostConeCanonicalSpanningTree hp hp2)).symm ⟨q, hq⟩

/-- The chosen incoming slot has the requested target face. -/
theorem canonicalProjectivePostConeTreeIncomingSlot_right
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : projectivePolygonPostConeCanonicalSpanningTree hp hp2)
    (hq : q ≠ canonicalProjectivePostConeTreeRoot hp hp2) :
    (canonicalProjectivePostConeTreeIncomingSlot hp hp2 q hq).right = q := by
  letI : Quiver.Arborescence (projectivePolygonPostConeCanonicalSpanningTree hp hp2) :=
    projectivePolygonPostConeCanonicalSpanningTreeArborescence hp hp2
  exact congrArg Subtype.val
    ((ReidemeisterSchreier.Quiver.Arborescence.totalEquivNonRoot
      (projectivePolygonPostConeCanonicalSpanningTree hp hp2)).apply_symm_apply ⟨q, hq⟩)

/-- Every non-root face has exactly one incoming canonical physical-tree
slot. -/
theorem existsUnique_canonicalProjectivePostConeTreeSlot_right_eq
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : projectivePolygonPostConeCanonicalSpanningTree hp hp2)
    (hq : q ≠ canonicalProjectivePostConeTreeRoot hp hp2) :
    ∃! slot : CanonicalProjectivePostConeTreeSlot hp hp2, slot.right = q := by
  refine ⟨canonicalProjectivePostConeTreeIncomingSlot hp hp2 q hq,
    canonicalProjectivePostConeTreeIncomingSlot_right hp hp2 q hq, ?_⟩
  intro slot hslot
  apply canonicalProjectivePostConeTreeSlot_injective_right hp hp2
  exact hslot.trans
    (canonicalProjectivePostConeTreeIncomingSlot_right hp hp2 q hq).symm

end

end SystolicGrowth
