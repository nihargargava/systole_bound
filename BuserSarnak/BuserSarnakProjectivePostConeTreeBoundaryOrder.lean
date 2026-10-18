module

public import BuserSarnak.BuserSarnakProjectivePostConeBoundaryCarriers
public import BuserSarnak.BuserSarnakProjectivePostConeTreeLeafRelations
public import BuserSarnak.BuserSarnakProjectivePolygonTreeEliminationPlan

@[expose] public section

/-!
# Boundary order at post-cone tree targets

At the target face of a physical-tree slot, every surviving polygon boundary
term is either final-alphabet data, the current pivot, or a strictly deeper
tree label. This is the local triangularity input for recursive tree
elimination.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete
open ReidemeisterSchreier.Discrete.Presentations

private theorem treeVertex_eq_face_of_state_eq
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (face : ProjectivePolygonPostConeFace p)
    (h : (⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p) =
      face) :
    slot.right = face := by
  apply ProjectivePolygonPostConeFace.stateEquiv.injective
  exact congrArg ProjectivePolygonPostConeFace.state h

/-- The exact signed physical-carrier alternative for one specified retained
label. This refines the existing existential carrier predicate. -/
def CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrierBy
    (p : ℕ) [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide)
    (z : CanonicalProjectiveConeKeptSymbol p) : Prop :=
  ((⟨q⟩ : ProjectivePolygonPostConeFace p) =
      projectivePolygonPostConeEdgeSource z ∧
    s = projectivePolygonPostConeEdgeSide z ∧
    canonicalProjectiveConePostConeBoundaryTerm p q s = FreeGroup.of z) ∨
  ((⟨q⟩ : ProjectivePolygonPostConeFace p) =
      projectivePolygonPostConeEdgeTarget z ∧
    s = projectivePolygonPostConeEdgeTargetSide z ∧
    canonicalProjectiveConePostConeBoundaryTerm p q s = (FreeGroup.of z)⁻¹)

/-- Every boundary factor at the target face of a current tree slot is either
trivial, carried by a non-tree label, is the current slot label, or is carried
by a strictly deeper tree slot. -/
theorem canonicalProjectiveConePostConeBoundaryTerm_at_treeTarget_eq_one_or_nonTree_or_self_or_deeper
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (s : ProjectivePolygonSide) :
    canonicalProjectiveConePostConeBoundaryTerm p slot.right.state s = 1 ∨
      (∃ z : CanonicalProjectiveConeKeptSymbol p,
        CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrierBy p slot.right.state s z ∧
          ¬ isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z) ∨
      (∃ z : CanonicalProjectiveConeKeptSymbol p,
        CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrierBy p slot.right.state s z ∧
          canonicalProjectivePostConeTreeSlotLabel hp hp2 slot = z) ∨
      ∃ (z : CanonicalProjectiveConeKeptSymbol p)
        (other : CanonicalProjectivePostConeTreeSlot hp hp2),
        CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrierBy p slot.right.state s z ∧
          canonicalProjectivePostConeTreeSlotLabel hp hp2 other = z ∧
          canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
            canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other := by
  rcases canonicalProjectiveConePostConeBoundaryTerm_eq_one_or_physicalCarrier
      hp hp2 slot.right.state s with hterm | ⟨z, hsource | htarget⟩
  · exact Or.inl hterm
  · let hcarrier : CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrierBy p
        slot.right.state s z := Or.inl hsource
    by_cases htree : isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z
    · rcases htree with ⟨other, hother⟩
      subst z
      have hincident :
          slot.right = projectivePolygonPostConeEdgeSource
              (canonicalProjectivePostConeTreeSlotLabel hp hp2 other) ∨
            slot.right = projectivePolygonPostConeEdgeTarget
              (canonicalProjectivePostConeTreeSlotLabel hp hp2 other) := by
        left
        exact treeVertex_eq_face_of_state_eq hp hp2 slot _ hsource.1
      rcases canonicalProjectivePostConeTreeSlot_eq_or_targetDepth_lt_of_incident_right
          hp hp2 slot other hincident with hself | hdeeper
      · refine Or.inr (Or.inr (Or.inl
          ⟨canonicalProjectivePostConeTreeSlotLabel hp hp2 other, hcarrier, ?_⟩))
        simp [hself]
      · exact Or.inr (Or.inr (Or.inr
          ⟨canonicalProjectivePostConeTreeSlotLabel hp hp2 other,
            other, hcarrier, rfl, hdeeper⟩))
    · exact Or.inr (Or.inl ⟨z, hcarrier, htree⟩)
  · let hcarrier : CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrierBy p
        slot.right.state s z := Or.inr htarget
    by_cases htree : isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z
    · rcases htree with ⟨other, hother⟩
      subst z
      have hincident :
          slot.right = projectivePolygonPostConeEdgeSource
              (canonicalProjectivePostConeTreeSlotLabel hp hp2 other) ∨
            slot.right = projectivePolygonPostConeEdgeTarget
              (canonicalProjectivePostConeTreeSlotLabel hp hp2 other) := by
        right
        exact treeVertex_eq_face_of_state_eq hp hp2 slot _ htarget.1
      rcases canonicalProjectivePostConeTreeSlot_eq_or_targetDepth_lt_of_incident_right
          hp hp2 slot other hincident with hself | hdeeper
      · refine Or.inr (Or.inr (Or.inl
          ⟨canonicalProjectivePostConeTreeSlotLabel hp hp2 other, hcarrier, ?_⟩))
        simp [hself]
      · exact Or.inr (Or.inr (Or.inr
          ⟨canonicalProjectivePostConeTreeSlotLabel hp hp2 other,
            other, hcarrier, rfl, hdeeper⟩))
    · exact Or.inr (Or.inl ⟨z, hcarrier, htree⟩)

/-- A canonical tree slot cannot be a loop, since its target depth is one
greater than its source depth. -/
theorem canonicalProjectivePostConeTreeSlot_left_ne_right
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    slot.left ≠ slot.right := by
  intro h
  have hdepth := canonicalProjectivePostConeTreeSlot_depth_succ hp hp2 slot
  unfold canonicalProjectivePostConeTreeSlotSourceDepth
    canonicalProjectivePostConeTreeSlotTargetDepth at hdepth
  rw [h] at hdepth
  omega

/-- The physical endpoints of the label selected by a tree slot are distinct. -/
theorem canonicalProjectivePostConeTreeSlot_edgeSource_ne_edgeTarget
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) ≠
      projectivePolygonPostConeEdgeTarget
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) := by
  intro hsource_target
  rcases canonicalProjectivePostConeTreeSlot_endpoints_eq_physicalEndpoints hp hp2 slot with
    hforward | hreverse
  · apply canonicalProjectivePostConeTreeSlot_left_ne_right hp hp2 slot
    exact hforward.1.trans (hsource_target.trans hforward.2.symm)
  · apply canonicalProjectivePostConeTreeSlot_left_ne_right hp hp2 slot
    exact hreverse.1.trans (hsource_target.symm.trans hreverse.2.symm)

/-- A carrier for the pivot label at a tree target occurs exactly at the
distinguished factor side of that target polygon relation. -/
theorem canonicalProjectivePostConeTreeSlotRightFactorSide_eq_of_physicalCarrier
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (s : ProjectivePolygonSide)
    (hcarrier :
      CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrierBy p
        slot.right.state s
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)) :
    s = canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot := by
  rcases hcarrier with hsource | htarget
  · have hright : slot.right = projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) := by
      exact hsource.1
    unfold canonicalProjectivePostConeTreeSlotRightFactorSide
    rw [if_pos hright]
    exact hsource.2.1
  · have hright : slot.right = projectivePolygonPostConeEdgeTarget
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) := by
      exact htarget.1
    have hnot : slot.right ≠ projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) := by
      intro hsource
      apply canonicalProjectivePostConeTreeSlot_edgeSource_ne_edgeTarget hp hp2 slot
      exact hsource.symm.trans hright
    unfold canonicalProjectivePostConeTreeSlotRightFactorSide
    rw [if_neg hnot]
    exact htarget.2.1

/-- Away from its distinguished pivot side, a target-face boundary term is
trivial, final-alphabet data, or carried by a strictly deeper tree slot. -/
theorem canonicalProjectiveConePostConeBoundaryTerm_at_treeTarget_eq_one_or_nonTree_or_deeper_of_ne_rightFactorSide
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (s : ProjectivePolygonSide)
    (hs : s ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot) :
    canonicalProjectiveConePostConeBoundaryTerm p slot.right.state s = 1 ∨
      (∃ z : CanonicalProjectiveConeKeptSymbol p,
        CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrierBy p slot.right.state s z ∧
          ¬ isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z) ∨
      ∃ (z : CanonicalProjectiveConeKeptSymbol p)
        (other : CanonicalProjectivePostConeTreeSlot hp hp2),
        CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrierBy p slot.right.state s z ∧
          canonicalProjectivePostConeTreeSlotLabel hp hp2 other = z ∧
          canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
            canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other := by
  rcases canonicalProjectiveConePostConeBoundaryTerm_at_treeTarget_eq_one_or_nonTree_or_self_or_deeper
      hp hp2 slot s with hterm | hnonTree | hself | hdeeper
  · exact Or.inl hterm
  · exact Or.inr (Or.inl hnonTree)
  · rcases hself with ⟨z, hcarrier, hlabel⟩
    rw [← hlabel] at hcarrier
    exact (hs (canonicalProjectivePostConeTreeSlotRightFactorSide_eq_of_physicalCarrier
      hp hp2 slot s hcarrier)).elim
  · exact Or.inr (Or.inr hdeeper)

end

end SystolicGrowth
