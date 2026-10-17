module

public import BuserSarnak.BuserSarnakProjectivePostConeTreeEliminationData
public import Mathlib.Data.Fintype.OfMap

@[expose] public section

/-!
# Direct post-cone tree words

This module begins the boundary-explicit replacement for the quotient-chosen
tree words.  The two pivot lemmas are the algebraic step used at each target
face: a polygon relation solves its distinguished tree letter as a word in
the other boundary terms.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete
open ReidemeisterSchreier.Discrete.Presentations

/-- Solve a positively occurring pivot in a relator `P * x * S = 1`.
The supplied word is `P⁻¹ * S⁻¹`, so its defining relation is a consequence
of the original relator. -/
theorem canonicalProjectivePostCone_definingRelator_of_positive_pivot
    {G : Type*} [Group G] {R : Set G} {P x S : G}
    (h : RelatorEquivalent R (P * x * S) 1) :
    RelatorEquivalent R (x * (P⁻¹ * S⁻¹)⁻¹) 1 := by
  have hconj := RelatorEquivalent.conj_eq_one h P⁻¹
  convert hconj using 1
  group

/-- Solve a negatively occurring pivot in a relator `P * x⁻¹ * S = 1`.
The supplied word is `S * P`, so its defining relation is a consequence of
the original relator. -/
theorem canonicalProjectivePostCone_definingRelator_of_negative_pivot
    {G : Type*} [Group G] {R : Set G} {P x S : G}
    (h : RelatorEquivalent R (P * x⁻¹ * S) 1) :
    RelatorEquivalent R (x * (S * P)⁻¹) 1 := by
  have hinv : RelatorEquivalent R (P * x⁻¹ * S)⁻¹ 1 := by
    simpa using h.inv
  have hconj := RelatorEquivalent.conj_eq_one hinv S
  convert hconj using 1
  group

noncomputable local instance canonicalProjectivePostConeDirectTreeDecidable
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    DecidablePred (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2) :=
  canonicalProjectivePostConeTreeEliminationDecidable hp hp2

/-- Reverse target-depth order is well founded on the finite canonical dual
tree.  It is the recursion order for the boundary-explicit tree words. -/
theorem canonicalProjectivePostConeDirectTreeDependencyWellFounded
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    WellFounded (fun child parent : CanonicalProjectivePostConeTreeSlot hp hp2 =>
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 parent <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child) := by
  let : DecidableEq (CanonicalProjectivePostConeTreeSlot hp hp2) := Classical.decEq _
  let : Fintype (CanonicalProjectivePostConeTreeSlot hp hp2) :=
    Fintype.ofList (canonicalProjectivePostConeTreeSlotEliminationOrder hp hp2)
      (mem_canonicalProjectivePostConeTreeSlotEliminationOrder hp hp2)
  let : IsTrans (CanonicalProjectivePostConeTreeSlot hp hp2)
      (fun child parent : CanonicalProjectivePostConeTreeSlot hp hp2 =>
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 parent <
          canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child) :=
    ⟨by
      intro a b c hab hbc
      exact lt_trans hbc hab⟩
  let : Std.Irrefl (fun child parent : CanonicalProjectivePostConeTreeSlot hp hp2 =>
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 parent <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child) :=
    ⟨by
      intro x hx
      exact Nat.lt_irrefl _ hx⟩
  exact Finite.wellFounded_of_trans_of_irrefl _

/-- Recover the unique dual-tree slot carrying a selected deleted label. -/
noncomputable def canonicalProjectivePostConeDirectTreeSlotOfDeleted
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : CanonicalProjectiveConeKeptSymbol p)
    (hz : isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z) :
    CanonicalProjectivePostConeTreeSlot hp hp2 :=
  (canonicalProjectivePostConeTreeSlotEquivDeleted hp hp2).symm ⟨z, hz⟩

@[simp] theorem canonicalProjectivePostConeDirectTreeSlotOfDeleted_label
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : CanonicalProjectiveConeKeptSymbol p)
    (hz : isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z) :
    canonicalProjectivePostConeTreeSlotLabel hp hp2
      (canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz) = z := by
  have h := (canonicalProjectivePostConeTreeSlotEquivDeleted hp hp2).apply_symm_apply ⟨z, hz⟩
  exact congrArg Subtype.val h

theorem canonicalProjectivePostConeDirectTreeSlotOfDeleted_eq_of_label
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : CanonicalProjectiveConeKeptSymbol p)
    (hz : isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z)
    (other : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hlabel : canonicalProjectivePostConeTreeSlotLabel hp hp2 other = z) :
    canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz = other := by
  apply canonicalProjectivePostConeTreeSlotLabel_injective hp hp2
  rw [canonicalProjectivePostConeDirectTreeSlotOfDeleted_label]
  exact hlabel.symm

/-- One reverse-depth substitution step. Non-tree letters remain visible;
strictly deeper tree letters use their already constructed final words. -/
noncomputable def canonicalProjectivePostConeDirectTreeSubstitution
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      FreeGroup (Presented.GeneratorPartition.Kept
        (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)))
    (z : CanonicalProjectiveConeKeptSymbol p) :
    FreeGroup (Presented.GeneratorPartition.Kept
      (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)) := by
  classical
  by_cases hz : isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z
  · let other := canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz
    exact if hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other then
      ih other hdeep
    else 1
  · exact FreeGroup.of ⟨z, hz⟩

noncomputable def canonicalProjectivePostConeDirectTreeSubstitutionHom
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      FreeGroup (Presented.GeneratorPartition.Kept
        (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2))) :
    FreeGroup (CanonicalProjectiveConeKeptSymbol p) →*
      FreeGroup (Presented.GeneratorPartition.Kept
        (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)) :=
  FreeGroup.lift (canonicalProjectivePostConeDirectTreeSubstitution hp hp2 slot ih)

@[simp] theorem canonicalProjectivePostConeDirectTreeSubstitution_of_nonTree
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      FreeGroup (Presented.GeneratorPartition.Kept
        (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)))
    (z : CanonicalProjectiveConeKeptSymbol p)
    (hz : ¬ isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z) :
    canonicalProjectivePostConeDirectTreeSubstitution hp hp2 slot ih z =
      FreeGroup.of ⟨z, hz⟩ := by
  simp [canonicalProjectivePostConeDirectTreeSubstitution, hz]

theorem canonicalProjectivePostConeDirectTreeSubstitution_of_deeper
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot other : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      FreeGroup (Presented.GeneratorPartition.Kept
        (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)))
    (z : CanonicalProjectiveConeKeptSymbol p)
    (hz : isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z)
    (hlabel : canonicalProjectivePostConeTreeSlotLabel hp hp2 other = z)
    (hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other) :
    canonicalProjectivePostConeDirectTreeSubstitution hp hp2 slot ih z = ih other hdeep := by
  unfold canonicalProjectivePostConeDirectTreeSubstitution
  rw [dite_eq_left hz]
  have hslot : canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz = other :=
    canonicalProjectivePostConeDirectTreeSlotOfDeleted_eq_of_label hp hp2 z hz other hlabel
  dsimp only
  rw [hslot]
  simp [hdeep]

@[simp] theorem canonicalProjectivePostConeDirectTreeSubstitutionHom_of
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      FreeGroup (Presented.GeneratorPartition.Kept
        (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)))
    (z : CanonicalProjectiveConeKeptSymbol p) :
    canonicalProjectivePostConeDirectTreeSubstitutionHom hp hp2 slot ih (FreeGroup.of z) =
      canonicalProjectivePostConeDirectTreeSubstitution hp hp2 slot ih z := by
  simp [canonicalProjectivePostConeDirectTreeSubstitutionHom]

private theorem canonicalProjectivePostConeDirectTreeSubstitutionHom_boundaryTerm_eval
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      FreeGroup (Presented.GeneratorPartition.Kept
        (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)))
    (hih : ∀ (other : CanonicalProjectivePostConeTreeSlot hp hp2)
      (hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other),
      canonicalProjectivePostConeFinalQuotientMap hp hp2 (ih other hdeep) =
        (QuotientGroup.mk' (Subgroup.normalClosure
          (CanonicalProjectiveConeFirstStageRelators p)))
          (FreeGroup.of (canonicalProjectivePostConeTreeSlotLabel hp hp2 other)))
    (s : ProjectivePolygonSide)
    (hs : s ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot) :
    canonicalProjectivePostConeFinalQuotientMap hp hp2
      (canonicalProjectivePostConeDirectTreeSubstitutionHom hp hp2 slot ih
        (canonicalProjectiveConePostConeBoundaryTerm p slot.right.state s)) =
      (QuotientGroup.mk' (Subgroup.normalClosure
        (CanonicalProjectiveConeFirstStageRelators p)))
        (canonicalProjectiveConePostConeBoundaryTerm p slot.right.state s) := by
  rcases canonicalProjectiveConePostConeBoundaryTerm_at_treeTarget_eq_one_or_nonTree_or_deeper_of_ne_rightFactorSide
      hp hp2 slot s hs with hterm | ⟨z, hcarrier, hz⟩ | ⟨z, other, hcarrier, hlabel, hdeep⟩
  · rw [hterm]
    simp
  · rcases hcarrier with hsource | htarget
    · rw [hsource.2.2, canonicalProjectivePostConeDirectTreeSubstitutionHom_of,
        canonicalProjectivePostConeDirectTreeSubstitution_of_nonTree hp hp2 slot ih z hz]
      let k : Presented.GeneratorPartition.Kept
          (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2) := ⟨z, hz⟩
      exact canonicalProjectivePostConeFinalQuotientMap_of hp hp2 k
    · rw [htarget.2.2]
      simp only [map_inv]
      rw [canonicalProjectivePostConeDirectTreeSubstitutionHom_of,
        canonicalProjectivePostConeDirectTreeSubstitution_of_nonTree hp hp2 slot ih z hz]
      let k : Presented.GeneratorPartition.Kept
          (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2) := ⟨z, hz⟩
      rw [canonicalProjectivePostConeFinalQuotientMap_of hp hp2 k]
  · have hz : isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z :=
      ⟨other, hlabel⟩
    rcases hcarrier with hsource | htarget
    · rw [hsource.2.2, canonicalProjectivePostConeDirectTreeSubstitutionHom_of,
        canonicalProjectivePostConeDirectTreeSubstitution_of_deeper hp hp2 slot other ih z hz
          hlabel hdeep,
        hih other hdeep, hlabel]
    · rw [htarget.2.2]
      simp only [map_inv]
      rw [canonicalProjectivePostConeDirectTreeSubstitutionHom_of,
        canonicalProjectivePostConeDirectTreeSubstitution_of_deeper hp hp2 slot other ih z hz
          hlabel hdeep,
        hih other hdeep, hlabel]

private theorem canonicalProjectivePostConeDirectTreeSubstitutionHom_prefixSuffix_eval
    {p : ℕ} [NeZero p] {Q : Type*} [Group Q]
    (hp : p.Prime) (hp2 : p ≠ 2)
    (M : FreeGroup (Presented.GeneratorPartition.Kept
      (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)) →* Q)
    (pi : FreeGroup (CanonicalProjectiveConeKeptSymbol p) →* Q)
    (φ : FreeGroup (CanonicalProjectiveConeKeptSymbol p) →*
      FreeGroup (Presented.GeneratorPartition.Kept
        (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)))
    (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide)
    (h : ∀ t : ProjectivePolygonSide, t ≠ s →
      M (φ (canonicalProjectiveConePostConeBoundaryTerm p q t)) =
        pi (canonicalProjectiveConePostConeBoundaryTerm p q t)) :
    M (φ (canonicalProjectiveConePostConeBoundaryPrefix p q s)) =
      pi (canonicalProjectiveConePostConeBoundaryPrefix p q s) ∧
      M (φ (canonicalProjectiveConePostConeBoundarySuffix p q s)) =
        pi (canonicalProjectiveConePostConeBoundarySuffix p q s) := by
  cases s <;>
    simp only [canonicalProjectiveConePostConeBoundaryPrefix,
      canonicalProjectiveConePostConeBoundarySuffix, map_one, map_mul] <;>
    constructor <;>
    repeat' first
      | rw [h .a (by decide)]
      | rw [h .e1 (by decide)]
      | rw [h .cInv (by decide)]
      | rw [h .e2 (by decide)]
      | rw [h .aInv (by decide)]
      | rw [h .e3 (by decide)]
      | rw [h .c (by decide)]
      | rw [h .e4 (by decide)]
  all_goals trivial

/-- The exact one-step splice at a dual-tree slot.  It rewrites the prefix
and suffix of the target-face boundary using deeper slots, then solves the
distinguished factor according to its source or target orientation. -/
noncomputable def canonicalProjectivePostConeDirectTreeWordStep
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      FreeGroup (Presented.GeneratorPartition.Kept
        (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2))) :
      FreeGroup (Presented.GeneratorPartition.Kept
        (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)) := by
  classical
  let φ := canonicalProjectivePostConeDirectTreeSubstitutionHom hp hp2 slot ih
  exact if hsource : slot.right = projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)
    then
      (φ (canonicalProjectiveConePostConeBoundaryPrefix p slot.right.state
        (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)))⁻¹ *
      (φ (canonicalProjectiveConePostConeBoundarySuffix p slot.right.state
        (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)))⁻¹
    else
      φ (canonicalProjectiveConePostConeBoundarySuffix p slot.right.state
        (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) *
      φ (canonicalProjectiveConePostConeBoundaryPrefix p slot.right.state
        (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))

/-- The source-oriented branch of the public one-step splice. -/
theorem canonicalProjectivePostConeDirectTreeWordStep_of_source
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      FreeGroup (Presented.GeneratorPartition.Kept
        (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)))
    (hsource : slot.right = projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)) :
    canonicalProjectivePostConeDirectTreeWordStep hp hp2 slot ih =
      (canonicalProjectivePostConeDirectTreeSubstitutionHom hp hp2 slot ih
        (canonicalProjectiveConePostConeBoundaryPrefix p slot.right.state
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)))⁻¹ *
      (canonicalProjectivePostConeDirectTreeSubstitutionHom hp hp2 slot ih
        (canonicalProjectiveConePostConeBoundarySuffix p slot.right.state
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)))⁻¹ := by
  unfold canonicalProjectivePostConeDirectTreeWordStep
  dsimp only
  rw [dite_eq_left hsource]

/-- The target-oriented branch of the public one-step splice. -/
theorem canonicalProjectivePostConeDirectTreeWordStep_of_target
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      FreeGroup (Presented.GeneratorPartition.Kept
        (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)))
    (htarget : slot.right ≠ projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)) :
    canonicalProjectivePostConeDirectTreeWordStep hp hp2 slot ih =
      canonicalProjectivePostConeDirectTreeSubstitutionHom hp hp2 slot ih
        (canonicalProjectiveConePostConeBoundarySuffix p slot.right.state
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) *
      canonicalProjectivePostConeDirectTreeSubstitutionHom hp hp2 slot ih
        (canonicalProjectiveConePostConeBoundaryPrefix p slot.right.state
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) := by
  unfold canonicalProjectivePostConeDirectTreeWordStep
  dsimp only
  rw [dite_eq_right htarget]

/-- Boundary-explicit defining words for all selected dual-tree labels,
obtained by reverse target-depth recursion. -/
noncomputable def canonicalProjectivePostConeDirectTreeEliminationWordBySlot
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    CanonicalProjectivePostConeTreeSlot hp hp2 →
      FreeGroup (Presented.GeneratorPartition.Kept
        (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)) :=
  (canonicalProjectivePostConeDirectTreeDependencyWellFounded hp hp2).fix
    (fun slot ih => canonicalProjectivePostConeDirectTreeWordStep hp hp2 slot ih)

theorem canonicalProjectivePostConeDirectTreeEliminationWordBySlot_unfold
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    canonicalProjectivePostConeDirectTreeEliminationWordBySlot hp hp2 slot =
      canonicalProjectivePostConeDirectTreeWordStep hp hp2 slot
        (fun other _hdeep =>
          canonicalProjectivePostConeDirectTreeEliminationWordBySlot hp hp2 other) := by
  unfold canonicalProjectivePostConeDirectTreeEliminationWordBySlot
  rw [WellFounded.fix_eq]

/-- The recursive tree word at a source-oriented slot is the inverse-prefix,
inverse-suffix splice, with calls only at strictly deeper slots. -/
theorem canonicalProjectivePostConeDirectTreeEliminationWordBySlot_of_source
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hsource : slot.right = projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)) :
    canonicalProjectivePostConeDirectTreeEliminationWordBySlot hp hp2 slot =
      (canonicalProjectivePostConeDirectTreeSubstitutionHom hp hp2 slot
        (fun other _hdeep =>
          canonicalProjectivePostConeDirectTreeEliminationWordBySlot hp hp2 other)
        (canonicalProjectiveConePostConeBoundaryPrefix p slot.right.state
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)))⁻¹ *
      (canonicalProjectivePostConeDirectTreeSubstitutionHom hp hp2 slot
        (fun other _hdeep =>
          canonicalProjectivePostConeDirectTreeEliminationWordBySlot hp hp2 other)
        (canonicalProjectiveConePostConeBoundarySuffix p slot.right.state
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)))⁻¹ := by
  rw [canonicalProjectivePostConeDirectTreeEliminationWordBySlot_unfold]
  exact canonicalProjectivePostConeDirectTreeWordStep_of_source hp hp2 slot _ hsource

/-- The recursive tree word at a target-oriented slot is the suffix-prefix
splice, with calls only at strictly deeper slots. -/
theorem canonicalProjectivePostConeDirectTreeEliminationWordBySlot_of_target
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (htarget : slot.right ≠ projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)) :
    canonicalProjectivePostConeDirectTreeEliminationWordBySlot hp hp2 slot =
      canonicalProjectivePostConeDirectTreeSubstitutionHom hp hp2 slot
        (fun other _hdeep =>
          canonicalProjectivePostConeDirectTreeEliminationWordBySlot hp hp2 other)
        (canonicalProjectiveConePostConeBoundarySuffix p slot.right.state
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) *
      canonicalProjectivePostConeDirectTreeSubstitutionHom hp hp2 slot
        (fun other _hdeep =>
          canonicalProjectivePostConeDirectTreeEliminationWordBySlot hp hp2 other)
        (canonicalProjectiveConePostConeBoundaryPrefix p slot.right.state
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) := by
  rw [canonicalProjectivePostConeDirectTreeEliminationWordBySlot_unfold]
  exact canonicalProjectivePostConeDirectTreeWordStep_of_target hp hp2 slot _ htarget

/-- Each boundary-explicit tree word represents its deleted label in the
first-stage polygon quotient. -/
theorem canonicalProjectivePostConeDirectTreeEliminationWordBySlot_spec
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    canonicalProjectivePostConeFinalQuotientMap hp hp2
      (canonicalProjectivePostConeDirectTreeEliminationWordBySlot hp hp2 slot) =
        (QuotientGroup.mk' (Subgroup.normalClosure
          (CanonicalProjectiveConeFirstStageRelators p)))
          (FreeGroup.of (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)) := by
  let pi : FreeGroup (CanonicalProjectiveConeKeptSymbol p) →*
      FreeGroup (CanonicalProjectiveConeKeptSymbol p) ⧸
        Subgroup.normalClosure (CanonicalProjectiveConeFirstStageRelators p) :=
    QuotientGroup.mk' (Subgroup.normalClosure
      (CanonicalProjectiveConeFirstStageRelators p))
  let M := canonicalProjectivePostConeFinalQuotientMap hp hp2
  change M (canonicalProjectivePostConeDirectTreeEliminationWordBySlot hp hp2 slot) =
    pi (FreeGroup.of (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot))
  refine (canonicalProjectivePostConeDirectTreeDependencyWellFounded hp hp2).induction
    (C := fun slot => M (canonicalProjectivePostConeDirectTreeEliminationWordBySlot hp hp2 slot) =
      pi (FreeGroup.of (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot))) slot ?_
  intro slot ih
  rw [canonicalProjectivePostConeDirectTreeEliminationWordBySlot_unfold]
  let φ := canonicalProjectivePostConeDirectTreeSubstitutionHom hp hp2 slot
    (fun other _hdeep => canonicalProjectivePostConeDirectTreeEliminationWordBySlot hp hp2 other)
  have hterm : ∀ t : ProjectivePolygonSide,
      t ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot →
      M (φ (canonicalProjectiveConePostConeBoundaryTerm p slot.right.state t)) =
        pi (canonicalProjectiveConePostConeBoundaryTerm p slot.right.state t) := by
    intro t ht
    exact canonicalProjectivePostConeDirectTreeSubstitutionHom_boundaryTerm_eval
      hp hp2 slot _ (fun other hdeep => ih other hdeep) t ht
  obtain ⟨hprefix, hsuffix⟩ :=
    canonicalProjectivePostConeDirectTreeSubstitutionHom_prefixSuffix_eval hp hp2 M pi φ
      slot.right.state (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot) hterm
  have hrel : pi (canonicalProjectiveConePostConePolygonWord p slot.right.state) = 1 := by
    have hrel' : RelatorEquivalent (CanonicalProjectiveConeFirstStageRelators p)
        (canonicalProjectiveConePostConePolygonWord p slot.right.state) 1 :=
      RelatorEquivalent.of_mem
        (canonicalProjectiveConePostConePolygonWord_mem_firstStageRelators slot.right.state)
    rw [relatorEquivalent_iff_eq_in_presentedQuotient] at hrel'
    exact hrel'
  rw [canonicalProjectivePostConeTreeSlot_polygonWord_right_factor hp hp2 slot] at hrel
  unfold canonicalProjectivePostConeDirectTreeWordStep
  dsimp only
  by_cases hsource : slot.right = projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)
  · rw [dite_eq_left hsource]
    simp only [map_mul, map_inv]
    rw [hprefix, hsuffix]
    have hrel' := hrel
    unfold canonicalProjectivePostConeTreeSlotRightFactorWord at hrel'
    rw [ite_eq_left hsource] at hrel'
    rw [hsource] at hrel'
    simp only [map_mul] at hrel'
    have hfactor :
        pi (canonicalProjectiveConePostConeBoundaryPrefix p slot.right.state
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) *
          pi (FreeGroup.of (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)) *
          pi (canonicalProjectiveConePostConeBoundarySuffix p slot.right.state
            (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) = 1 := by
      rw [hsource]
      exact hrel'
    symm
    calc
      pi (FreeGroup.of (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)) =
          (pi (canonicalProjectiveConePostConeBoundaryPrefix p slot.right.state
            (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)))⁻¹ *
            (pi (canonicalProjectiveConePostConeBoundaryPrefix p slot.right.state
              (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) *
              pi (FreeGroup.of (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)) *
              pi (canonicalProjectiveConePostConeBoundarySuffix p slot.right.state
                (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))) *
              (pi (canonicalProjectiveConePostConeBoundarySuffix p slot.right.state
                (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)))⁻¹ := by group
      _ = (pi (canonicalProjectiveConePostConeBoundaryPrefix p slot.right.state
            (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)))⁻¹ *
          (pi (canonicalProjectiveConePostConeBoundarySuffix p slot.right.state
            (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)))⁻¹ := by
        rw [hfactor]
        simp
  · rw [dite_eq_right hsource]
    simp only [map_mul]
    rw [hprefix, hsuffix]
    have hfactor :
        pi (canonicalProjectiveConePostConeBoundaryPrefix p slot.right.state
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) *
          (pi (FreeGroup.of (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)))⁻¹ *
          pi (canonicalProjectiveConePostConeBoundarySuffix p slot.right.state
            (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) = 1 := by
      simpa [canonicalProjectivePostConeTreeSlotRightFactorWord, hsource] using hrel
    symm
    calc
      pi (FreeGroup.of (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)) =
          pi (canonicalProjectiveConePostConeBoundarySuffix p slot.right.state
            (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) *
            (pi (canonicalProjectiveConePostConeBoundaryPrefix p slot.right.state
              (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) *
              (pi (FreeGroup.of (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)))⁻¹ *
              pi (canonicalProjectiveConePostConeBoundarySuffix p slot.right.state
                (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)))⁻¹ *
              pi (canonicalProjectiveConePostConeBoundaryPrefix p slot.right.state
                (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) := by group
      _ = pi (canonicalProjectiveConePostConeBoundarySuffix p slot.right.state
            (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) *
          pi (canonicalProjectiveConePostConeBoundaryPrefix p slot.right.state
            (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) := by
              rw [hfactor]
              simp

/-- The explicit final-alphabet defining word for a deleted tree generator. -/
noncomputable def canonicalProjectivePostConeDirectTreeEliminationWord
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : Presented.GeneratorPartition.Deleted
      (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)) :
    FreeGroup (Presented.GeneratorPartition.Kept
      (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)) :=
  canonicalProjectivePostConeDirectTreeEliminationWordBySlot hp hp2
    (canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z.1 z.2)

theorem canonicalProjectivePostConeDirectTreeEliminationWord_spec
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : Presented.GeneratorPartition.Deleted
      (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)) :
    canonicalProjectivePostConeFinalQuotientMap hp hp2
      (canonicalProjectivePostConeDirectTreeEliminationWord hp hp2 z) =
        (QuotientGroup.mk' (Subgroup.normalClosure
          (CanonicalProjectiveConeFirstStageRelators p))) (FreeGroup.of z.1) := by
  rw [canonicalProjectivePostConeDirectTreeEliminationWord]
  rw [canonicalProjectivePostConeDirectTreeEliminationWordBySlot_spec]
  rw [canonicalProjectivePostConeDirectTreeSlotOfDeleted_label]

/-- The direct defining relation for a tree label follows from the first-stage
polygon relators. -/
theorem canonicalProjectivePostConeDirectTreeEliminationWord_directRelator
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : Presented.GeneratorPartition.Deleted
      (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)) :
    RelatorEquivalent (CanonicalProjectiveConeFirstStageRelators p)
      (FreeGroup.of z.1 *
        (canonicalProjectivePostConeFinalInclusion hp hp2
          (canonicalProjectivePostConeDirectTreeEliminationWord hp hp2 z))⁻¹) 1 := by
  let pi : FreeGroup (CanonicalProjectiveConeKeptSymbol p) →*
      FreeGroup (CanonicalProjectiveConeKeptSymbol p) ⧸
        Subgroup.normalClosure (CanonicalProjectiveConeFirstStageRelators p) :=
    QuotientGroup.mk' (Subgroup.normalClosure
      (CanonicalProjectiveConeFirstStageRelators p))
  let M := canonicalProjectivePostConeFinalQuotientMap hp hp2
  have hword := canonicalProjectivePostConeDirectTreeEliminationWord_spec hp hp2 z
  rw [relatorEquivalent_iff_eq_in_presentedQuotient]
  change pi (FreeGroup.of z.1 *
    (canonicalProjectivePostConeFinalInclusion hp hp2
      (canonicalProjectivePostConeDirectTreeEliminationWord hp hp2 z))⁻¹) = 1
  rw [map_mul, map_inv]
  change pi (FreeGroup.of z.1) *
    (M (canonicalProjectivePostConeDirectTreeEliminationWord hp hp2 z))⁻¹ = 1
  rw [hword]
  simp [pi]

theorem canonicalProjectivePostConeDirectTreeEliminationPulledBackDefinedRelator
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : Presented.GeneratorPartition.Deleted
      (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)) :
    (FreeGroup.freeGroupCongr
      (Presented.GeneratorPartition.equiv
        (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2))).symm
      (FreeGroup.of (Sum.inr z) *
        (Presented.includeAdjoinedGenerators
          (Presented.GeneratorPartition.Kept
            (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2))
          (Presented.GeneratorPartition.Deleted
            (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2))
          (canonicalProjectivePostConeDirectTreeEliminationWord hp hp2 z))⁻¹) =
      FreeGroup.of z.1 *
        (canonicalProjectivePostConeFinalInclusion hp hp2
          (canonicalProjectivePostConeDirectTreeEliminationWord hp hp2 z))⁻¹ := by
  simp [FreeGroup.freeGroupCongr, Presented.GeneratorPartition.equiv,
    Presented.includeAdjoinedGenerators, canonicalProjectivePostConeFinalInclusion]
  rw [← MonoidHom.comp_apply]
  congr 1
  ext x
  simp

/-- All direct defining relators are redundant in the first-stage polygon
presentation. -/
theorem canonicalProjectivePostConeDirectTreeDefinedGeneratorRelators_subset_normalClosure
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    @Presented.definedGeneratorRelatorsOfPredicate
      (CanonicalProjectiveConeKeptSymbol p)
      (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)
      (canonicalProjectivePostConeTreeEliminationDecidable hp hp2)
      (canonicalProjectivePostConeDirectTreeEliminationWord hp hp2) ⊆
      Subgroup.normalClosure (CanonicalProjectiveConeFirstStageRelators p) := by
  intro r hr
  change r ∈ (FreeGroup.freeGroupCongr
    (Presented.GeneratorPartition.equiv
      (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2))).symm ''
      Presented.definedGeneratorRelators
        (canonicalProjectivePostConeDirectTreeEliminationWord hp hp2) at hr
  rcases hr with ⟨q, ⟨z, rfl⟩, rfl⟩
  rw [canonicalProjectivePostConeDirectTreeEliminationPulledBackDefinedRelator hp hp2 z]
  exact RelatorEquivalent.mem_normalClosure_of_eq_one
    (canonicalProjectivePostConeDirectTreeEliminationWord_directRelator hp hp2 z)

/-- The boundary-explicit direct words provide a complete second-stage tree
elimination package, suitable for later literal post-substitution analysis. -/
noncomputable def canonicalProjectivePostConeDirectTreeEliminationData
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    CanonicalProjectivePostConeTreeEliminationData hp hp2 where
  eliminationOrder := canonicalProjectivePostConeTreeSlotEliminationOrder hp hp2
  eliminationOrder_nodup := canonicalProjectivePostConeTreeSlotEliminationOrder_nodup hp hp2
  mem_eliminationOrder := mem_canonicalProjectivePostConeTreeSlotEliminationOrder hp hp2
  word := canonicalProjectivePostConeDirectTreeEliminationWord hp hp2
  definingRelatorsRedundant :=
    canonicalProjectivePostConeDirectTreeDefinedGeneratorRelators_subset_normalClosure hp hp2

/-- Simultaneously substitute the boundary-explicit direct words for every
selected post-cone tree generator. -/
noncomputable def canonicalProjectivePostConeDirectFinalSubstitution
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    FreeGroup (CanonicalProjectiveConeKeptSymbol p) →*
      FreeGroup (Presented.GeneratorPartition.Kept
        (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)) :=
  (Presented.eliminateAdjoinedGeneratorsHom
    (canonicalProjectivePostConeDirectTreeEliminationWord hp hp2)).comp
    (FreeGroup.freeGroupCongr
      (Presented.GeneratorPartition.equiv
        (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)))

/-- The direct final substitution sends a deleted tree label to its explicit
reverse-depth word. -/
@[simp] theorem canonicalProjectivePostConeDirectFinalSubstitution_of_deleted
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : CanonicalProjectiveConeKeptSymbol p)
    (hz : isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z) :
    canonicalProjectivePostConeDirectFinalSubstitution hp hp2 (FreeGroup.of z) =
      canonicalProjectivePostConeDirectTreeEliminationWord hp hp2 ⟨z, hz⟩ := by
  simp only [canonicalProjectivePostConeDirectFinalSubstitution,
    MonoidHom.coe_comp, MonoidHom.coe_ofClass, Function.comp_apply,
    FreeGroup.freeGroupCongr_apply, FreeGroup.map.of,
    Presented.GeneratorPartition.equiv_apply_of_delete
      (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2) hz]
  exact Presented.eliminateAdjoinedGeneratorsHom_inr
    (X := Presented.GeneratorPartition.Kept
      (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2))
    (Y := Presented.GeneratorPartition.Deleted
      (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2))
    (canonicalProjectivePostConeDirectTreeEliminationWord hp hp2) ⟨z, hz⟩

/-- The direct final substitution leaves a surviving physical edge letter
unchanged. -/
@[simp] theorem canonicalProjectivePostConeDirectFinalSubstitution_of_kept
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : Presented.GeneratorPartition.Kept
      (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)) :
    canonicalProjectivePostConeDirectFinalSubstitution hp hp2 (FreeGroup.of z.1) =
      FreeGroup.of z := by
  simp only [canonicalProjectivePostConeDirectFinalSubstitution,
    MonoidHom.coe_comp, MonoidHom.coe_ofClass, Function.comp_apply,
    FreeGroup.freeGroupCongr_apply, FreeGroup.map.of,
    Presented.GeneratorPartition.equiv_apply_of_not_delete
      (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2) z.2]
  exact Presented.eliminateAdjoinedGeneratorsHom_inl
    (X := Presented.GeneratorPartition.Kept
      (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2))
    (Y := Presented.GeneratorPartition.Deleted
      (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2))
    (canonicalProjectivePostConeDirectTreeEliminationWord hp hp2) z

@[simp] theorem canonicalProjectivePostConeDirectFinalSubstitution_of_treeSlotLabel
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    canonicalProjectivePostConeDirectFinalSubstitution hp hp2
      (FreeGroup.of (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)) =
      canonicalProjectivePostConeDirectTreeEliminationWordBySlot hp hp2 slot := by
  let z := canonicalProjectivePostConeTreeSlotLabel hp hp2 slot
  have hz : isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z := ⟨slot, rfl⟩
  rw [canonicalProjectivePostConeDirectFinalSubstitution_of_deleted hp hp2 z hz]
  unfold canonicalProjectivePostConeDirectTreeEliminationWord
  congr 1
  exact canonicalProjectivePostConeDirectTreeSlotOfDeleted_eq_of_label hp hp2 z hz slot rfl

private theorem canonicalProjectivePostConeDirectFinalSubstitution_boundaryTerm_eq_local
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (s : ProjectivePolygonSide)
    (hs : s ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot) :
    canonicalProjectivePostConeDirectFinalSubstitution hp hp2
      (canonicalProjectiveConePostConeBoundaryTerm p slot.right.state s) =
      canonicalProjectivePostConeDirectTreeSubstitutionHom hp hp2 slot
        (fun other _hdeep =>
          canonicalProjectivePostConeDirectTreeEliminationWordBySlot hp hp2 other)
        (canonicalProjectiveConePostConeBoundaryTerm p slot.right.state s) := by
  rcases canonicalProjectiveConePostConeBoundaryTerm_at_treeTarget_eq_one_or_nonTree_or_deeper_of_ne_rightFactorSide
      hp hp2 slot s hs with hterm | ⟨z, hcarrier, hz⟩ | ⟨z, other, hcarrier, hlabel, hdeep⟩
  · rw [hterm]
    simp
  · rcases hcarrier with hsource | htarget
    · rw [hsource.2.2, canonicalProjectivePostConeDirectFinalSubstitution_of_kept hp hp2
          ⟨z, hz⟩,
        canonicalProjectivePostConeDirectTreeSubstitutionHom_of,
        canonicalProjectivePostConeDirectTreeSubstitution_of_nonTree hp hp2 slot _ z hz]
    · rw [htarget.2.2]
      simp only [map_inv]
      rw [canonicalProjectivePostConeDirectFinalSubstitution_of_kept hp hp2 ⟨z, hz⟩,
        canonicalProjectivePostConeDirectTreeSubstitutionHom_of,
        canonicalProjectivePostConeDirectTreeSubstitution_of_nonTree hp hp2 slot _ z hz]
  · rcases hcarrier with hsource | htarget
    · rw [hsource.2.2]
      have hz : isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z :=
        ⟨other, hlabel⟩
      have hleft : canonicalProjectivePostConeDirectFinalSubstitution hp hp2
          (FreeGroup.of z) =
          canonicalProjectivePostConeDirectTreeEliminationWordBySlot hp hp2 other := by
        rw [← hlabel,
          canonicalProjectivePostConeDirectFinalSubstitution_of_treeSlotLabel hp hp2 other]
      rw [hleft, canonicalProjectivePostConeDirectTreeSubstitutionHom_of]
      exact (canonicalProjectivePostConeDirectTreeSubstitution_of_deeper
        (ih := fun other _hdeep =>
          canonicalProjectivePostConeDirectTreeEliminationWordBySlot hp hp2 other)
        hp hp2 slot other z hz hlabel hdeep).symm
    · rw [htarget.2.2]
      simp only [map_inv]
      have hz : isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z :=
        ⟨other, hlabel⟩
      have hleft : canonicalProjectivePostConeDirectFinalSubstitution hp hp2
          (FreeGroup.of z) =
          canonicalProjectivePostConeDirectTreeEliminationWordBySlot hp hp2 other := by
        rw [← hlabel,
          canonicalProjectivePostConeDirectFinalSubstitution_of_treeSlotLabel hp hp2 other]
      rw [hleft, canonicalProjectivePostConeDirectTreeSubstitutionHom_of]
      rw [canonicalProjectivePostConeDirectTreeSubstitution_of_deeper
        (ih := fun other _hdeep =>
          canonicalProjectivePostConeDirectTreeEliminationWordBySlot hp hp2 other)
        hp hp2 slot other z hz hlabel hdeep]

/-- Substituting the explicit direct tree words makes every non-root target
face relator literally trivial. -/
theorem canonicalProjectivePostConeDirectFinalSubstitution_polygonWord_at_treeTarget_eq_one
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    canonicalProjectivePostConeDirectFinalSubstitution hp hp2
      (canonicalProjectiveConePostConePolygonWord p slot.right.state) = 1 := by
  let φ := canonicalProjectivePostConeDirectTreeSubstitutionHom hp hp2 slot
    (fun other _hdeep =>
      canonicalProjectivePostConeDirectTreeEliminationWordBySlot hp hp2 other)
  have hterm : ∀ t : ProjectivePolygonSide,
      t ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot →
      (MonoidHom.id (FreeGroup (Presented.GeneratorPartition.Kept
        (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2))))
        (φ (canonicalProjectiveConePostConeBoundaryTerm p slot.right.state t)) =
        canonicalProjectivePostConeDirectFinalSubstitution hp hp2
          (canonicalProjectiveConePostConeBoundaryTerm p slot.right.state t) := by
    intro t ht
    simpa using
      (canonicalProjectivePostConeDirectFinalSubstitution_boundaryTerm_eq_local
        hp hp2 slot t ht).symm
  obtain ⟨hprefix, hsuffix⟩ :=
    canonicalProjectivePostConeDirectTreeSubstitutionHom_prefixSuffix_eval hp hp2
      (MonoidHom.id (FreeGroup (Presented.GeneratorPartition.Kept
        (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2))))
      (canonicalProjectivePostConeDirectFinalSubstitution hp hp2) φ
      slot.right.state (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot) hterm
  simp only [MonoidHom.id_apply] at hprefix hsuffix
  rw [canonicalProjectivePostConeTreeSlot_polygonWord_right_factor hp hp2 slot]
  simp only [map_mul]
  unfold canonicalProjectivePostConeTreeSlotRightFactorWord
  by_cases hsource : slot.right = projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)
  · rw [ite_eq_left hsource,
      canonicalProjectivePostConeDirectFinalSubstitution_of_treeSlotLabel hp hp2 slot,
      canonicalProjectivePostConeDirectTreeEliminationWordBySlot_unfold]
    unfold canonicalProjectivePostConeDirectTreeWordStep
    dsimp only
    rw [dite_eq_left hsource]
    dsimp [φ] at hprefix hsuffix
    rw [hprefix, hsuffix]
    group
  · rw [ite_eq_right hsource]
    simp only [map_inv]
    rw [canonicalProjectivePostConeDirectFinalSubstitution_of_treeSlotLabel hp hp2 slot,
      canonicalProjectivePostConeDirectTreeEliminationWordBySlot_unfold]
    unfold canonicalProjectivePostConeDirectTreeWordStep
    dsimp only
    rw [dite_eq_right hsource]
    dsimp [φ] at hprefix hsuffix
    rw [hprefix, hsuffix]
    group

/-- Every non-root face of the canonical physical dual tree has a polygon
relator that becomes literally trivial under direct substitution. -/
theorem canonicalProjectivePostConeDirectFinalSubstitution_polygonWord_eq_one_of_ne_root
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : projectivePolygonPostConeCanonicalSpanningTree hp hp2)
    (hq : q ≠ canonicalProjectivePostConeTreeRoot hp hp2) :
    canonicalProjectivePostConeDirectFinalSubstitution hp hp2
      (canonicalProjectiveConePostConePolygonWord p q.state) = 1 := by
  let slot := canonicalProjectivePostConeTreeIncomingSlot hp hp2 q hq
  have hright : slot.right = q :=
    canonicalProjectivePostConeTreeIncomingSlot_right hp hp2 q hq
  rw [← hright]
  exact canonicalProjectivePostConeDirectFinalSubstitution_polygonWord_at_treeTarget_eq_one
    hp hp2 slot

/-- After the direct tree substitution, the complete post-cone polygon
relator family has the same normal closure as the one polygon word at the
physical tree root.  Every other face word is literally trivial. -/
theorem canonicalProjectivePostConeDirectFinalSubstitution_polygonRelators_normalClosure_eq_singleton_root
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    Subgroup.normalClosure
      (canonicalProjectivePostConeDirectFinalSubstitution hp hp2 ''
        CanonicalProjectiveConePostConePolygonRelators p) =
      Subgroup.normalClosure
        ({(canonicalProjectivePostConeDirectFinalSubstitution hp hp2
          (canonicalProjectiveConePostConePolygonWord p
            (canonicalProjectivePostConeTreeRoot hp hp2).state))} :
          Set (FreeGroup (Presented.GeneratorPartition.Kept
            (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)))) := by
  apply normalClosure_eq_of_subset_normalClosure
  · rintro r ⟨x, ⟨q, rfl⟩, rfl⟩
    let qTree : projectivePolygonPostConeCanonicalSpanningTree hp hp2 :=
      (⟨q⟩ : ProjectivePolygonPostConeFace p)
    by_cases hq : qTree = canonicalProjectivePostConeTreeRoot hp hp2
    · have hstate : q = (canonicalProjectivePostConeTreeRoot hp hp2).state := by
        simpa [qTree] using congrArg ProjectivePolygonPostConeFace.state hq
      rw [hstate]
      exact Subgroup.subset_normalClosure (by simp)
    · rw [show canonicalProjectivePostConeDirectFinalSubstitution hp hp2
          (canonicalProjectiveConePostConePolygonWord p q) = 1 by
        simpa [qTree] using
          canonicalProjectivePostConeDirectFinalSubstitution_polygonWord_eq_one_of_ne_root
            hp hp2 qTree hq]
      exact Subgroup.one_mem _
  · intro r hr
    rw [Set.mem_singleton_iff.mp hr]
    apply Subgroup.subset_normalClosure
    exact ⟨_, ⟨_, rfl⟩, rfl⟩

end

end SystolicGrowth
