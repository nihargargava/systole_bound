module

public import BuserSarnak.BuserSarnakProjectivePostConeDirectPresentation
public import BuserSarnak.BuserSarnakProjectivePostConeRootContourList
public import BuserSarnak.OrientableWicksNielsen
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.GroupTheory.FreeGroup.Reduce

@[expose] public section

/-!
# Boundary words and paired polygon edges

This module records the unreduced signed letters in polygon boundaries and
expands edges of a spanning tree recursively. Paired edges contribute opposite
orientations, represented by `FreeGroup.invRev`. Occurrence indices retain the
original edge and vertex data throughout the expansion.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete
open ReidemeisterSchreier.Discrete.Presentations

noncomputable local instance rawAllFacesContourRangeFintype
    (p : ℕ) [NeZero p] : Fintype (BuserSarnakProjectiveReductionRange p) :=
  Fintype.ofFinite _

/-- The root's ordered octagon boundary contains each directed side once.
This is the side-occurrence separation needed when comparing root tags. -/
theorem canonicalProjectivePostConeBoundarySideCycle_nodup :
    canonicalProjectivePostConeBoundarySideCycle.Nodup := by
  decide

/-- A positive free generator cannot equal the inverse of any positive
generator; this literal one-letter separation rules out opposite-orientation
classifications of a fixed polygon side. -/
theorem BoundaryWords.Internal.freeGroup_of_ne_inv
    {X : Type*} [DecidableEq X] (x y : X) :
    FreeGroup.of x ≠ (FreeGroup.of y)⁻¹ := by
  classical
  intro h
  have hletters := congrArg FreeGroup.toWord h
  simp only [FreeGroup.toWord_of, FreeGroup.toWord_inv] at hletters
  simp [FreeGroup.invRev] at hletters

/-- A classifier for an off-pivot boundary term at a tree target. The
constructors retain whether the occurrence is a positive source or an
inverse target; the cases are proved unique below, so the classical choice
used to select one is independent of its existence proof. -/
inductive CanonicalProjectivePostConeRawContourTermCase
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (s : ProjectivePolygonSide) : Type where
  | one : canonicalProjectiveConePostConeBoundaryTerm p slot.right.state s = 1 →
      CanonicalProjectivePostConeRawContourTermCase hp hp2 slot s
  | finalSource (z : CanonicalProjectiveConeKeptSymbol p)
      (hsource :
        (⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p) =
            projectivePolygonPostConeEdgeSource z ∧
          s = projectivePolygonPostConeEdgeSide z ∧
          canonicalProjectiveConePostConeBoundaryTerm p slot.right.state s = FreeGroup.of z)
      (hz : ¬ isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z) :
      CanonicalProjectivePostConeRawContourTermCase hp hp2 slot s
  | finalTarget (z : CanonicalProjectiveConeKeptSymbol p)
      (htarget :
        (⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p) =
            projectivePolygonPostConeEdgeTarget z ∧
          s = projectivePolygonPostConeEdgeTargetSide z ∧
          canonicalProjectiveConePostConeBoundaryTerm p slot.right.state s =
            (FreeGroup.of z)⁻¹)
      (hz : ¬ isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z) :
      CanonicalProjectivePostConeRawContourTermCase hp hp2 slot s
  | deeperSource (z : CanonicalProjectiveConeKeptSymbol p)
      (other : CanonicalProjectivePostConeTreeSlot hp hp2)
      (hsource :
        (⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p) =
            projectivePolygonPostConeEdgeSource z ∧
          s = projectivePolygonPostConeEdgeSide z ∧
          canonicalProjectiveConePostConeBoundaryTerm p slot.right.state s = FreeGroup.of z)
      (hlabel : canonicalProjectivePostConeTreeSlotLabel hp hp2 other = z)
      (hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other) :
      CanonicalProjectivePostConeRawContourTermCase hp hp2 slot s
  | deeperTarget (z : CanonicalProjectiveConeKeptSymbol p)
      (other : CanonicalProjectivePostConeTreeSlot hp hp2)
      (htarget :
        (⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p) =
            projectivePolygonPostConeEdgeTarget z ∧
          s = projectivePolygonPostConeEdgeTargetSide z ∧
          canonicalProjectiveConePostConeBoundaryTerm p slot.right.state s =
            (FreeGroup.of z)⁻¹)
      (hlabel : canonicalProjectivePostConeTreeSlotLabel hp hp2 other = z)
      (hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other) :
      CanonicalProjectivePostConeRawContourTermCase hp hp2 slot s

/-- Every off-pivot boundary side has at most one compatible raw-term
classification. The boundary word fixes its physical label and orientation;
if it is a tree label, injectivity of the slot-label map fixes the recursive
child as well. -/
theorem canonicalProjectivePostConeRawContourTermCase_unique
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (s : ProjectivePolygonSide)
    (a b : CanonicalProjectivePostConeRawContourTermCase hp hp2 slot s) :
    a = b := by
  classical
  cases a with
  | one hone =>
    cases b with
    | one hone' => rfl
    | finalSource z hsource hz =>
        exact False.elim ((FreeGroup.of_ne_one z) (hsource.2.2.symm.trans hone))
    | finalTarget z htarget hz =>
        have hz1 : FreeGroup.of z = 1 := inv_eq_one.mp (htarget.2.2.symm.trans hone)
        exact False.elim ((FreeGroup.of_ne_one z) hz1)
    | deeperSource z other hsource hlabel hdeep =>
        exact False.elim ((FreeGroup.of_ne_one z) (hsource.2.2.symm.trans hone))
    | deeperTarget z other htarget hlabel hdeep =>
        have hz1 : FreeGroup.of z = 1 := inv_eq_one.mp (htarget.2.2.symm.trans hone)
        exact False.elim ((FreeGroup.of_ne_one z) hz1)
  | finalSource z₁ hsource₁ hz₁ =>
    cases b with
    | one hone =>
        exact False.elim ((FreeGroup.of_ne_one z₁) (hsource₁.2.2.symm.trans hone))
    | finalSource z₂ hsource₂ hz₂ =>
        have hz : z₁ = z₂ := FreeGroup.of_injective (hsource₁.2.2.symm.trans hsource₂.2.2)
        subst z₂
        rfl
    | finalTarget z₂ htarget₂ hz₂ =>
        exact False.elim (BoundaryWords.Internal.freeGroup_of_ne_inv z₁ z₂ (hsource₁.2.2.symm.trans htarget₂.2.2))
    | deeperSource z₂ other hsource₂ hlabel₂ hdeep₂ =>
        have hz : z₁ = z₂ := FreeGroup.of_injective (hsource₁.2.2.symm.trans hsource₂.2.2)
        exact False.elim (hz₁ ⟨other, hlabel₂.trans hz.symm⟩)
    | deeperTarget z₂ other htarget₂ hlabel₂ hdeep₂ =>
        exact False.elim (BoundaryWords.Internal.freeGroup_of_ne_inv z₁ z₂ (hsource₁.2.2.symm.trans htarget₂.2.2))
  | finalTarget z₁ htarget₁ hz₁ =>
    cases b with
    | one hone =>
        have hz1 : FreeGroup.of z₁ = 1 := inv_eq_one.mp (htarget₁.2.2.symm.trans hone)
        exact False.elim ((FreeGroup.of_ne_one z₁) hz1)
    | finalSource z₂ hsource₂ hz₂ =>
        exact False.elim (BoundaryWords.Internal.freeGroup_of_ne_inv z₂ z₁ (hsource₂.2.2.symm.trans htarget₁.2.2))
    | finalTarget z₂ htarget₂ hz₂ =>
        have hz : z₁ = z₂ := FreeGroup.of_injective <| by
          apply inv_injective
          exact htarget₁.2.2.symm.trans htarget₂.2.2
        subst z₂
        rfl
    | deeperSource z₂ other hsource₂ hlabel₂ hdeep₂ =>
        exact False.elim (BoundaryWords.Internal.freeGroup_of_ne_inv z₂ z₁ (hsource₂.2.2.symm.trans htarget₁.2.2))
    | deeperTarget z₂ other htarget₂ hlabel₂ hdeep₂ =>
        have hz : z₁ = z₂ := FreeGroup.of_injective <| by
          apply inv_injective
          exact htarget₁.2.2.symm.trans htarget₂.2.2
        exact False.elim (hz₁ ⟨other, hlabel₂.trans hz.symm⟩)
  | deeperSource z₁ other₁ hsource₁ hlabel₁ hdeep₁ =>
    cases b with
    | one hone =>
        exact False.elim ((FreeGroup.of_ne_one z₁) (hsource₁.2.2.symm.trans hone))
    | finalSource z₂ hsource₂ hz₂ =>
        have hz : z₁ = z₂ := FreeGroup.of_injective (hsource₁.2.2.symm.trans hsource₂.2.2)
        exact False.elim (hz₂ ⟨other₁, hlabel₁.trans hz⟩)
    | finalTarget z₂ htarget₂ hz₂ =>
        exact False.elim (BoundaryWords.Internal.freeGroup_of_ne_inv z₁ z₂ (hsource₁.2.2.symm.trans htarget₂.2.2))
    | deeperSource z₂ other₂ hsource₂ hlabel₂ hdeep₂ =>
        have hz : z₁ = z₂ := FreeGroup.of_injective (hsource₁.2.2.symm.trans hsource₂.2.2)
        have hother : other₁ = other₂ :=
          canonicalProjectivePostConeTreeSlotLabel_injective hp hp2
            (hlabel₁.trans (hz.trans hlabel₂.symm))
        cases hz
        cases hother
        rfl
    | deeperTarget z₂ other₂ htarget₂ hlabel₂ hdeep₂ =>
        exact False.elim (BoundaryWords.Internal.freeGroup_of_ne_inv z₁ z₂ (hsource₁.2.2.symm.trans htarget₂.2.2))
  | deeperTarget z₁ other₁ htarget₁ hlabel₁ hdeep₁ =>
    cases b with
    | one hone =>
        have hz1 : FreeGroup.of z₁ = 1 := inv_eq_one.mp (htarget₁.2.2.symm.trans hone)
        exact False.elim ((FreeGroup.of_ne_one z₁) hz1)
    | finalSource z₂ hsource₂ hz₂ =>
        exact False.elim (BoundaryWords.Internal.freeGroup_of_ne_inv z₂ z₁ (hsource₂.2.2.symm.trans htarget₁.2.2))
    | finalTarget z₂ htarget₂ hz₂ =>
        have hz : z₁ = z₂ := FreeGroup.of_injective <| by
          apply inv_injective
          exact htarget₁.2.2.symm.trans htarget₂.2.2
        exact False.elim (hz₂ ⟨other₁, hlabel₁.trans hz⟩)
    | deeperSource z₂ other₂ hsource₂ hlabel₂ hdeep₂ =>
        exact False.elim (BoundaryWords.Internal.freeGroup_of_ne_inv z₂ z₁ (hsource₂.2.2.symm.trans htarget₁.2.2))
    | deeperTarget z₂ other₂ htarget₂ hlabel₂ hdeep₂ =>
        have hz : z₁ = z₂ := FreeGroup.of_injective <| by
          apply inv_injective
          exact htarget₁.2.2.symm.trans htarget₂.2.2
        have hother : other₁ = other₂ :=
          canonicalProjectivePostConeTreeSlotLabel_injective hp hp2
            (hlabel₁.trans (hz.trans hlabel₂.symm))
        cases hz
        cases hother
        rfl

theorem BoundaryWords.Internal.canonicalProjectivePostConeRawContourTermCase_nonempty
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (s : ProjectivePolygonSide)
    (hs : s ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot) :
    Nonempty (CanonicalProjectivePostConeRawContourTermCase hp hp2 slot s) := by
  rcases canonicalProjectiveConePostConeBoundaryTerm_at_treeTarget_eq_one_or_nonTree_or_deeper_of_ne_rightFactorSide
      hp hp2 slot s hs with hterm | ⟨z, hcarrier, hz⟩ | ⟨z, other, hcarrier, hlabel, hdeep⟩
  · exact ⟨.one hterm⟩
  · rcases hcarrier with hsource | htarget
    · exact ⟨.finalSource z hsource hz⟩
    · exact ⟨.finalTarget z htarget hz⟩
  · rcases hcarrier with hsource | htarget
    · exact ⟨.deeperSource z other hsource hlabel hdeep⟩
    · exact ⟨.deeperTarget z other htarget hlabel hdeep⟩

/-- Choose the exact source/target/depth classification of an off-pivot
boundary term.  The choice is only used to turn a proved finite alternative
into data; every constructor retains its correctness proof. -/
noncomputable def canonicalProjectivePostConeRawContourTermCase
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (s : ProjectivePolygonSide)
    (hs : s ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot) :
    CanonicalProjectivePostConeRawContourTermCase hp hp2 slot s :=
  Classical.choice (BoundaryWords.Internal.canonicalProjectivePostConeRawContourTermCase_nonempty hp hp2 slot s hs)

/-- The selected classification does not depend on which proof certifies that
the side is off-pivot. The case data itself is unique. -/
theorem canonicalProjectivePostConeRawContourTermCase_proof_irrel
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (s : ProjectivePolygonSide)
    (hs hs' : s ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot) :
    canonicalProjectivePostConeRawContourTermCase hp hp2 slot s hs =
      canonicalProjectivePostConeRawContourTermCase hp hp2 slot s hs' :=
  canonicalProjectivePostConeRawContourTermCase_unique hp hp2 slot s _ _

/-- Turn a certified off-pivot case into an unreduced signed-letter list. -/
noncomputable def canonicalProjectivePostConeRawContourTermOfCase
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool))
    (s : ProjectivePolygonSide)
    (c : CanonicalProjectivePostConeRawContourTermCase hp hp2 slot s) :
    List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool) :=
  match c with
  | .one _ => []
  | .finalSource z _ hz => [(⟨z, hz⟩, true)]
  | .finalTarget z _ hz => [(⟨z, hz⟩, false)]
  | .deeperSource _ other _ _ hdeep => ih other hdeep
  | .deeperTarget _ other _ _ hdeep => FreeGroup.invRev (ih other hdeep)

/-- Expand one boundary side without reduction.  At the pivot side the list
is empty; off the pivot, the selected case records either nothing, one final
signed letter, or a recursively spliced deeper list (inverted at a target). -/
noncomputable def canonicalProjectivePostConeRawContourTerm
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool))
    (s : ProjectivePolygonSide) :
    List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool) := by
  classical
  by_cases hs : s = canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot
  · exact []
  · exact canonicalProjectivePostConeRawContourTermOfCase hp hp2 slot ih s
      (canonicalProjectivePostConeRawContourTermCase hp hp2 slot s hs)

/-- The origin tag for a position inside one boundary-side expansion. Final
letters use their unique singleton index; recursive source and target terms
retain a position in the child word. -/
def CanonicalProjectivePostConeRawContourTermPositionTag
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool))
    {s : ProjectivePolygonSide}
    (c : CanonicalProjectivePostConeRawContourTermCase hp hp2 slot s) : Type :=
  match c with
  | .one _ => Empty
  | .finalSource _ _ _ => Fin 1
  | .finalTarget _ _ _ => Fin 1
  | .deeperSource _ other _ _ hdeep => Fin (ih other hdeep).length
  | .deeperTarget _ other _ _ hdeep => Fin (ih other hdeep).length

/-- Decode positions of a classified side term into its local final-letter
index or its exact child-word index. Target recursion uses the inverse of
`invRevPosition`, so the tag remains in the child's original order. -/
noncomputable def canonicalProjectivePostConeRawContourTermOfCase_positionEquiv
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool))
    {s : ProjectivePolygonSide}
    (c : CanonicalProjectivePostConeRawContourTermCase hp hp2 slot s) :
    Fin (canonicalProjectivePostConeRawContourTermOfCase hp hp2 slot ih s c).length ≃
      CanonicalProjectivePostConeRawContourTermPositionTag hp hp2 slot ih c := by
  cases c with
  | one hterm => exact finZeroEquiv
  | finalSource z hsource hz => exact Equiv.refl _
  | finalTarget z htarget hz => exact Equiv.refl _
  | deeperSource z other hsource hlabel hdeep => exact Equiv.refl _
  | deeperTarget z other htarget hlabel hdeep =>
      exact (Equiv.ofBijective (@invRevPosition _ (ih other hdeep))
        (invRevPosition_bijective (ih other hdeep))).symm

/-- The public side-term word is the list selected by its certified case;
the off-pivot proof is the only extra input. -/
theorem canonicalProjectivePostConeRawContourTerm_eq_termOfCase
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool))
    (s : ProjectivePolygonSide)
    (hs : s ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot) :
    canonicalProjectivePostConeRawContourTerm hp hp2 slot ih s =
      canonicalProjectivePostConeRawContourTermOfCase hp hp2 slot ih s
        (canonicalProjectivePostConeRawContourTermCase hp hp2 slot s hs) := by
  simp [canonicalProjectivePostConeRawContourTerm, hs]

/-- A side-term position has a canonical origin tag. This local decoder is
the next level beneath the recursive side-list position equivalence. -/
noncomputable def canonicalProjectivePostConeRawContourTerm_positionEquiv
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool))
    (s : ProjectivePolygonSide)
    (hs : s ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot) :
    Fin (canonicalProjectivePostConeRawContourTerm hp hp2 slot ih s).length ≃
      CanonicalProjectivePostConeRawContourTermPositionTag hp hp2 slot ih
        (canonicalProjectivePostConeRawContourTermCase hp hp2 slot s hs) := by
  let c := canonicalProjectivePostConeRawContourTermCase hp hp2 slot s hs
  exact (finCongr (congrArg List.length
      (canonicalProjectivePostConeRawContourTerm_eq_termOfCase hp hp2 slot ih s hs))).trans
    (canonicalProjectivePostConeRawContourTermOfCase_positionEquiv hp hp2 slot ih c)

/-- The signed letter denoted by a side-term origin tag. Child-target tags
read the corresponding child letter with its orientation toggled. -/
def canonicalProjectivePostConeRawContourTermPositionTag_letter
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool))
    {s : ProjectivePolygonSide}
    (c : CanonicalProjectivePostConeRawContourTermCase hp hp2 slot s) :
    CanonicalProjectivePostConeRawContourTermPositionTag hp hp2 slot ih c →
      CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool := by
  cases c with
  | one hterm => exact fun i => i.elim
  | finalSource z hsource hz => exact fun _ => (⟨z, hz⟩, true)
  | finalTarget z htarget hz => exact fun _ => (⟨z, hz⟩, false)
  | deeperSource z other hsource hlabel hdeep =>
      exact fun i => (ih other hdeep).get i
  | deeperTarget z other htarget hlabel hdeep =>
      exact fun i => (((ih other hdeep).get i).1, !((ih other hdeep).get i).2)

/-- The position equivalence followed by its origin decoder recovers the
exact letter in the classified side-term word. -/
theorem canonicalProjectivePostConeRawContourTermOfCase_positionEquiv_get
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool))
    {s : ProjectivePolygonSide}
    (c : CanonicalProjectivePostConeRawContourTermCase hp hp2 slot s)
    (i : Fin (canonicalProjectivePostConeRawContourTermOfCase hp hp2 slot ih s c).length) :
    (canonicalProjectivePostConeRawContourTermOfCase hp hp2 slot ih s c).get i =
      canonicalProjectivePostConeRawContourTermPositionTag_letter hp hp2 slot ih c
        (canonicalProjectivePostConeRawContourTermOfCase_positionEquiv
          hp hp2 slot ih c i) := by
  cases c with
  | one hterm => exact Fin.elim0 i
  | finalSource z hsource hz =>
      change Fin 1 at i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      rfl
  | finalTarget z htarget hz =>
      change Fin 1 at i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      rfl
  | deeperSource z other hsource hlabel hdeep => rfl
  | deeperTarget z other htarget hlabel hdeep =>
      let e := Equiv.ofBijective (@invRevPosition _ (ih other hdeep))
        (invRevPosition_bijective (ih other hdeep))
      have hi : invRevPosition (e.symm i) = i := e.apply_symm_apply i
      change (FreeGroup.invRev (ih other hdeep)).get i =
        (((ih other hdeep).get (e.symm i)).1,
          !((ih other hdeep).get (e.symm i)).2)
      calc
        (FreeGroup.invRev (ih other hdeep)).get i =
            (FreeGroup.invRev (ih other hdeep)).get (invRevPosition (e.symm i)) :=
          congrArg (FreeGroup.invRev (ih other hdeep)).get hi.symm
        _ = (((ih other hdeep).get (e.symm i)).1,
            !((ih other hdeep).get (e.symm i)).2) :=
          get_invRevPosition (ih other hdeep) (e.symm i)

/-- A source child position is read unchanged at the corresponding position
of its parent-side expansion. -/
theorem canonicalProjectivePostConeRawContourTermOfCase_get_deeperSource_position
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool))
    (z : CanonicalProjectiveConeKeptSymbol p) (s : ProjectivePolygonSide)
    (hsource :
      (⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p) =
        projectivePolygonPostConeEdgeSource z ∧
      s = projectivePolygonPostConeEdgeSide z ∧
      canonicalProjectiveConePostConeBoundaryTerm p slot.right.state s = FreeGroup.of z)
    (hlabel : canonicalProjectivePostConeTreeSlotLabel hp hp2 child = z)
    (hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child)
    (i : Fin (ih child hdeep).length) :
    (canonicalProjectivePostConeRawContourTermOfCase hp hp2 slot ih s
      (.deeperSource z child hsource hlabel hdeep)).get i =
        (ih child hdeep).get i := rfl

/-- A target child position is read in inverse-reversed order, with the sign
flipped in the parent-side expansion. -/
theorem canonicalProjectivePostConeRawContourTermOfCase_get_deeperTarget_position
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool))
    (z : CanonicalProjectiveConeKeptSymbol p) (s : ProjectivePolygonSide)
    (htarget :
      (⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p) =
        projectivePolygonPostConeEdgeTarget z ∧
      s = projectivePolygonPostConeEdgeTargetSide z ∧
      canonicalProjectiveConePostConeBoundaryTerm p slot.right.state s =
        (FreeGroup.of z)⁻¹)
    (hlabel : canonicalProjectivePostConeTreeSlotLabel hp hp2 child = z)
    (hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child)
    (i : Fin (ih child hdeep).length) :
    (canonicalProjectivePostConeRawContourTermOfCase hp hp2 slot ih s
      (.deeperTarget z child htarget hlabel hdeep)).get
        (invRevPosition i) =
      (((ih child hdeep).get i).1, !((ih child hdeep).get i).2) := by
  let e := Equiv.ofBijective (@invRevPosition _ (ih child hdeep))
    (invRevPosition_bijective (ih child hdeep))
  have hget := canonicalProjectivePostConeRawContourTermOfCase_positionEquiv_get
    hp hp2 slot ih (.deeperTarget z child htarget hlabel hdeep) (invRevPosition i)
  have hposition :
      canonicalProjectivePostConeRawContourTermOfCase_positionEquiv
        hp hp2 slot ih (.deeperTarget z child htarget hlabel hdeep)
        (invRevPosition i) = i := by
    change e.symm (e i) = i
    exact e.symm_apply_apply i
  rw [hget, hposition]
  rfl

/-- The public off-pivot side-term decoder recovers the exact signed letter
at every raw position, not merely its membership in the term. -/
theorem canonicalProjectivePostConeRawContourTerm_positionEquiv_get
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool))
    (s : ProjectivePolygonSide)
    (hs : s ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)
    (i : Fin (canonicalProjectivePostConeRawContourTerm hp hp2 slot ih s).length) :
    (canonicalProjectivePostConeRawContourTerm hp hp2 slot ih s).get i =
      canonicalProjectivePostConeRawContourTermPositionTag_letter hp hp2 slot ih
        (canonicalProjectivePostConeRawContourTermCase hp hp2 slot s hs)
        (canonicalProjectivePostConeRawContourTerm_positionEquiv
          hp hp2 slot ih s hs i) := by
  let c := canonicalProjectivePostConeRawContourTermCase hp hp2 slot s hs
  let hraw := canonicalProjectivePostConeRawContourTerm_eq_termOfCase
    hp hp2 slot ih s hs
  calc
    (canonicalProjectivePostConeRawContourTerm hp hp2 slot ih s).get i =
        (canonicalProjectivePostConeRawContourTermOfCase hp hp2 slot ih s c).get
          (Fin.cast (congrArg List.length hraw) i) :=
      (get_cast_eq_of_eq hraw i).symm
    _ = canonicalProjectivePostConeRawContourTermPositionTag_letter hp hp2 slot ih c
          (canonicalProjectivePostConeRawContourTermOfCase_positionEquiv
            hp hp2 slot ih c (Fin.cast (congrArg List.length hraw) i)) :=
      canonicalProjectivePostConeRawContourTermOfCase_positionEquiv_get
        hp hp2 slot ih c (Fin.cast (congrArg List.length hraw) i)
    _ = canonicalProjectivePostConeRawContourTermPositionTag_letter hp hp2 slot ih c
          (canonicalProjectivePostConeRawContourTerm_positionEquiv
            hp hp2 slot ih s hs i) := by
      rfl

/-- Evaluating an unreduced off-pivot expansion gives exactly the direct
one-step substitution of that boundary term. -/
theorem canonicalProjectivePostConeRawContourTerm_eval
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool))
    (s : ProjectivePolygonSide)
    (hs : s ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot) :
    FreeGroup.mk (canonicalProjectivePostConeRawContourTerm hp hp2 slot ih s) =
      canonicalProjectivePostConeDirectTreeSubstitutionHom hp hp2 slot
        (fun other hdeep => FreeGroup.mk (ih other hdeep))
        (canonicalProjectiveConePostConeBoundaryTerm p slot.right.state s) := by
  classical
  cases hcase : canonicalProjectivePostConeRawContourTermCase hp hp2 slot s hs with
  | one hterm =>
      simp only [canonicalProjectivePostConeRawContourTerm, dif_neg hs,
        canonicalProjectivePostConeRawContourTermOfCase, hcase]
      rw [hterm]
      simpa only [map_one] using (FreeGroup.one_eq_mk.symm :
        FreeGroup.mk ([] : List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool)) = 1)
  | finalSource z hsource hz =>
      simp only [canonicalProjectivePostConeRawContourTerm, dif_neg hs,
        canonicalProjectivePostConeRawContourTermOfCase, hcase]
      rw [hsource.2.2, canonicalProjectivePostConeDirectTreeSubstitutionHom_of,
        canonicalProjectivePostConeDirectTreeSubstitution_of_nonTree hp hp2 slot
          (fun other hdeep => FreeGroup.mk (ih other hdeep)) z hz]
      rfl
  | finalTarget z htarget hz =>
      simp only [canonicalProjectivePostConeRawContourTerm, dif_neg hs,
        canonicalProjectivePostConeRawContourTermOfCase, hcase]
      rw [htarget.2.2, map_inv,
        canonicalProjectivePostConeDirectTreeSubstitutionHom_of,
        canonicalProjectivePostConeDirectTreeSubstitution_of_nonTree hp hp2 slot
          (fun other hdeep => FreeGroup.mk (ih other hdeep)) z hz]
      rfl
  | deeperSource z other hsource hlabel hdeep =>
      simp only [canonicalProjectivePostConeRawContourTerm, dif_neg hs,
        canonicalProjectivePostConeRawContourTermOfCase, hcase]
      have hz : isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z :=
        ⟨other, hlabel⟩
      rw [hsource.2.2, canonicalProjectivePostConeDirectTreeSubstitutionHom_of,
        canonicalProjectivePostConeDirectTreeSubstitution_of_deeper hp hp2 slot other
          (fun other hdeep => FreeGroup.mk (ih other hdeep)) z hz hlabel hdeep]
  | deeperTarget z other htarget hlabel hdeep =>
      simp only [canonicalProjectivePostConeRawContourTerm, dif_neg hs,
        canonicalProjectivePostConeRawContourTermOfCase, hcase]
      have hz : isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z :=
        ⟨other, hlabel⟩
      rw [htarget.2.2, map_inv,
        canonicalProjectivePostConeDirectTreeSubstitutionHom_of,
        canonicalProjectivePostConeDirectTreeSubstitution_of_deeper hp hp2 slot other
          (fun other hdeep => FreeGroup.mk (ih other hdeep)) z hz hlabel hdeep]
      simp [FreeGroup.inv_mk]

/-- The displayed side list before a distinguished boundary side. -/
def canonicalProjectivePostConeBoundaryPrefixSides :
    ProjectivePolygonSide → List ProjectivePolygonSide
  | .a => []
  | .e1 => [.a]
  | .cInv => [.a, .e1]
  | .e2 => [.a, .e1, .cInv]
  | .aInv => [.a, .e1, .cInv, .e2]
  | .e3 => [.a, .e1, .cInv, .e2, .aInv]
  | .c => [.a, .e1, .cInv, .e2, .aInv, .e3]
  | .e4 => [.a, .e1, .cInv, .e2, .aInv, .e3, .c]

/-- The displayed side list after a distinguished boundary side. -/
def canonicalProjectivePostConeBoundarySuffixSides :
  ProjectivePolygonSide → List ProjectivePolygonSide
  | .a => [.e1, .cInv, .e2, .aInv, .e3, .c, .e4]
  | .e1 => [.cInv, .e2, .aInv, .e3, .c, .e4]
  | .cInv => [.e2, .aInv, .e3, .c, .e4]
  | .e2 => [.aInv, .e3, .c, .e4]
  | .aInv => [.e3, .c, .e4]
  | .e3 => [.c, .e4]
  | .c => [.e4]
  | .e4 => []

/-- The displayed prefix and suffix side lists contain no repeated polygon
side, so selected-side tags are unambiguous within either block. -/
theorem canonicalProjectivePostConeBoundaryPrefixSides_nodup
    (pivot : ProjectivePolygonSide) :
    (canonicalProjectivePostConeBoundaryPrefixSides pivot).Nodup := by
  cases pivot <;> decide

theorem canonicalProjectivePostConeBoundarySuffixSides_nodup
    (pivot : ProjectivePolygonSide) :
    (canonicalProjectivePostConeBoundarySuffixSides pivot).Nodup := by
  cases pivot <;> decide

/-- A boundary side belongs to at most one of the ordered prefix and suffix
blocks cut at the pivot. -/
theorem canonicalProjectivePostConeBoundaryPrefixSuffix_disjoint
    (pivot s : ProjectivePolygonSide) :
    ¬ (s ∈ canonicalProjectivePostConeBoundaryPrefixSides pivot ∧
      s ∈ canonicalProjectivePostConeBoundarySuffixSides pivot) := by
  cases pivot <;> cases s <;>
    simp [canonicalProjectivePostConeBoundaryPrefixSides,
      canonicalProjectivePostConeBoundarySuffixSides]

/-- The explicit prefix/suffix split exhausts every non-pivot octagon side. -/
theorem canonicalProjectivePostConeBoundarySide_mem_prefix_or_suffix
    (s pivot : ProjectivePolygonSide) (hs : s ≠ pivot) :
    s ∈ canonicalProjectivePostConeBoundaryPrefixSides pivot ∨
      s ∈ canonicalProjectivePostConeBoundarySuffixSides pivot := by
  cases s <;> cases pivot <;>
    simp_all [canonicalProjectivePostConeBoundaryPrefixSides,
      canonicalProjectivePostConeBoundarySuffixSides]

private theorem canonicalProjectivePostConeBoundaryPrefixSides_ne
    (s t : ProjectivePolygonSide)
    (ht : t ∈ canonicalProjectivePostConeBoundaryPrefixSides s) :
    t ≠ s := by
  cases s <;> cases t <;>
    simp [canonicalProjectivePostConeBoundaryPrefixSides] at ht ⊢

private theorem canonicalProjectivePostConeBoundarySuffixSides_ne
    (s t : ProjectivePolygonSide)
    (ht : t ∈ canonicalProjectivePostConeBoundarySuffixSides s) :
    t ≠ s := by
  cases s <;> cases t <;>
    simp [canonicalProjectivePostConeBoundarySuffixSides] at ht ⊢

private theorem canonicalProjectivePostConeBoundaryPrefixSides_prod
    {p : ℕ} [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide) :
    (List.map (canonicalProjectiveConePostConeBoundaryTerm p q)
      (canonicalProjectivePostConeBoundaryPrefixSides s)).prod =
      canonicalProjectiveConePostConeBoundaryPrefix p q s := by
  cases s <;>
    simp [canonicalProjectivePostConeBoundaryPrefixSides,
      canonicalProjectiveConePostConeBoundaryPrefix] <;>
    group

private theorem canonicalProjectivePostConeBoundarySuffixSides_prod
    {p : ℕ} [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide) :
    (List.map (canonicalProjectiveConePostConeBoundaryTerm p q)
      (canonicalProjectivePostConeBoundarySuffixSides s)).prod =
      canonicalProjectiveConePostConeBoundarySuffix p q s := by
  cases s <;>
    simp [canonicalProjectivePostConeBoundarySuffixSides,
      canonicalProjectiveConePostConeBoundarySuffix] <;>
    group

/-- Concatenate the unreduced expansions of a list of polygon sides. -/
noncomputable def canonicalProjectivePostConeRawContourTerms
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool)) :
    List ProjectivePolygonSide →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool)
  | [] => []
  | s :: ss => canonicalProjectivePostConeRawContourTerm hp hp2 slot ih s ++
      canonicalProjectivePostConeRawContourTerms hp hp2 slot ih ss

/-- Every index of a concatenated raw word belongs to exactly one of its two
blocks. This is the finite position decomposition used to build disjoint
offset embeddings through the recursive contour splices. -/
def canonicalProjectivePostConeRawAppendPositionSplit
    {α : Type*} (xs ys : List α) :
    Fin (xs ++ ys).length ≃ Fin xs.length ⊕ Fin ys.length :=
  (finCongr (by simp : (xs ++ ys).length = xs.length + ys.length)).trans
    finSumFinEquiv.symm

/-- Reading through the inverse append split at a left-block tag returns
the corresponding left element. -/
theorem canonicalProjectivePostConeRawAppendPositionSplit_get_left
    {α : Type*} (xs ys : List α) (i : Fin xs.length) :
    (xs ++ ys).get
      ((canonicalProjectivePostConeRawAppendPositionSplit xs ys).symm (Sum.inl i)) =
      xs.get i := by
  simp [canonicalProjectivePostConeRawAppendPositionSplit]

/-- Reading through the inverse append split at a right-block tag returns
the corresponding right element. -/
theorem canonicalProjectivePostConeRawAppendPositionSplit_get_right
    {α : Type*} (xs ys : List α) (i : Fin ys.length) :
    (xs ++ ys).get
      ((canonicalProjectivePostConeRawAppendPositionSplit xs ys).symm (Sum.inr i)) =
      ys.get i := by
  simp [canonicalProjectivePostConeRawAppendPositionSplit]

/-- Split a side-list expansion at its first side. Each position belongs
uniquely either to that side's term or to the expansion of the remaining
sides. -/
def canonicalProjectivePostConeRawContourTerms_positionSplit_cons
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool))
    (s : ProjectivePolygonSide) (ss : List ProjectivePolygonSide) :
    Fin (canonicalProjectivePostConeRawContourTerms hp hp2 slot ih (s :: ss)).length ≃
      Fin (canonicalProjectivePostConeRawContourTerm hp hp2 slot ih s).length ⊕
      Fin (canonicalProjectivePostConeRawContourTerms hp hp2 slot ih ss).length := by
  change Fin ((canonicalProjectivePostConeRawContourTerm hp hp2 slot ih s ++
    canonicalProjectivePostConeRawContourTerms hp hp2 slot ih ss).length) ≃ _
  exact canonicalProjectivePostConeRawAppendPositionSplit _ _

/-- The first-side branch of the side-list split recovers its exact letter. -/
theorem canonicalProjectivePostConeRawContourTerms_get_cons_left
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool))
    (s : ProjectivePolygonSide) (ss : List ProjectivePolygonSide)
    (i : Fin (canonicalProjectivePostConeRawContourTerm hp hp2 slot ih s).length) :
    (canonicalProjectivePostConeRawContourTerms hp hp2 slot ih (s :: ss)).get
      ((canonicalProjectivePostConeRawContourTerms_positionSplit_cons
        hp hp2 slot ih s ss).symm (Sum.inl i)) =
      (canonicalProjectivePostConeRawContourTerm hp hp2 slot ih s).get i := by
  change (canonicalProjectivePostConeRawContourTerm hp hp2 slot ih s ++
    canonicalProjectivePostConeRawContourTerms hp hp2 slot ih ss).get
      ((canonicalProjectivePostConeRawAppendPositionSplit
        (canonicalProjectivePostConeRawContourTerm hp hp2 slot ih s)
        (canonicalProjectivePostConeRawContourTerms hp hp2 slot ih ss)).symm
        (Sum.inl i)) = _
  exact canonicalProjectivePostConeRawAppendPositionSplit_get_left _ _ i

/-- The tail branch of the side-list split recovers its exact letter. -/
theorem canonicalProjectivePostConeRawContourTerms_get_cons_right
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool))
    (s : ProjectivePolygonSide) (ss : List ProjectivePolygonSide)
    (i : Fin (canonicalProjectivePostConeRawContourTerms hp hp2 slot ih ss).length) :
    (canonicalProjectivePostConeRawContourTerms hp hp2 slot ih (s :: ss)).get
      ((canonicalProjectivePostConeRawContourTerms_positionSplit_cons
        hp hp2 slot ih s ss).symm (Sum.inr i)) =
      (canonicalProjectivePostConeRawContourTerms hp hp2 slot ih ss).get i := by
  change (canonicalProjectivePostConeRawContourTerm hp hp2 slot ih s ++
    canonicalProjectivePostConeRawContourTerms hp hp2 slot ih ss).get
      ((canonicalProjectivePostConeRawAppendPositionSplit
        (canonicalProjectivePostConeRawContourTerm hp hp2 slot ih s)
        (canonicalProjectivePostConeRawContourTerms hp hp2 slot ih ss)).symm
        (Sum.inr i)) = _
  exact canonicalProjectivePostConeRawAppendPositionSplit_get_right _ _ i

/-- A recursively nested tag for a position in a side-list expansion. The
left summand stores a local term position for the head side; the right
summand stores a position in the tail expansion. This preserves repeated
side values as distinct occurrences. -/
def CanonicalProjectivePostConeRawContourTermsPositionTag
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool)) :
    List ProjectivePolygonSide → Type
  | [] => Empty
  | s :: ss =>
      Fin (canonicalProjectivePostConeRawContourTerm hp hp2 slot ih s).length ⊕
        CanonicalProjectivePostConeRawContourTermsPositionTag hp hp2 slot ih ss

/-- Every position of a side-list expansion is equivalent to exactly one
tag recording the side occurrence and its local term index. -/
noncomputable def canonicalProjectivePostConeRawContourTerms_positionEquiv
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool)) :
    (sides : List ProjectivePolygonSide) →
      Fin (canonicalProjectivePostConeRawContourTerms hp hp2 slot ih sides).length ≃
        CanonicalProjectivePostConeRawContourTermsPositionTag hp hp2 slot ih sides
  | [] => finZeroEquiv
  | s :: ss =>
      (canonicalProjectivePostConeRawContourTerms_positionSplit_cons
        hp hp2 slot ih s ss).trans
        (Equiv.sumCongr (Equiv.refl _)
          (canonicalProjectivePostConeRawContourTerms_positionEquiv
            hp hp2 slot ih ss))

/-- The local origin type for one polygon side. The eliminated pivot has no
raw positions; every other side uses its certified final-letter or child
position tag. -/
noncomputable def CanonicalProjectivePostConeRawContourSideOriginTag
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool))
    (s : ProjectivePolygonSide) : Type := by
  classical
  exact if hs : s = canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot then
    Empty
  else
    CanonicalProjectivePostConeRawContourTermPositionTag hp hp2 slot ih
      (canonicalProjectivePostConeRawContourTermCase hp hp2 slot s hs)

/-- Every local side-term position has its origin tag; the pivot case is
empty, and the other cases use the exact term decoder. -/
noncomputable def canonicalProjectivePostConeRawContourSide_positionEquiv
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool))
    (s : ProjectivePolygonSide) :
    Fin (canonicalProjectivePostConeRawContourTerm hp hp2 slot ih s).length ≃
      CanonicalProjectivePostConeRawContourSideOriginTag hp hp2 slot ih s := by
  classical
  by_cases hs : s = canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot
  · subst s
    simpa [CanonicalProjectivePostConeRawContourSideOriginTag,
      canonicalProjectivePostConeRawContourTerm] using (finZeroEquiv)
  · simpa [CanonicalProjectivePostConeRawContourSideOriginTag, hs] using
      canonicalProjectivePostConeRawContourTerm_positionEquiv hp hp2 slot ih s hs

/-- A recursively nested origin tag for the complete expansion of a side
list. Sum branches distinguish occurrences, even when side values repeat. -/
noncomputable def CanonicalProjectivePostConeRawContourTermsOriginTag
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool)) :
    List ProjectivePolygonSide → Type
  | [] => Empty
  | s :: ss => CanonicalProjectivePostConeRawContourSideOriginTag hp hp2 slot ih s ⊕
      CanonicalProjectivePostConeRawContourTermsOriginTag hp hp2 slot ih ss

/-- The complete side-list word is equivalent to nested tags carrying each
occurrence's side and recursively decoded local origin. -/
noncomputable def canonicalProjectivePostConeRawContourTerms_originEquiv
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool)) :
    (sides : List ProjectivePolygonSide) →
      Fin (canonicalProjectivePostConeRawContourTerms hp hp2 slot ih sides).length ≃
        CanonicalProjectivePostConeRawContourTermsOriginTag hp hp2 slot ih sides
  | [] => finZeroEquiv
  | s :: ss =>
      (canonicalProjectivePostConeRawContourTerms_positionSplit_cons
        hp hp2 slot ih s ss).trans
        (Equiv.sumCongr
          (canonicalProjectivePostConeRawContourSide_positionEquiv hp hp2 slot ih s)
          (canonicalProjectivePostConeRawContourTerms_originEquiv hp hp2 slot ih ss))

/-- The signed letter decoded from a single-side origin tag. -/
noncomputable def canonicalProjectivePostConeRawContourSideOriginTag_letter
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool))
    (s : ProjectivePolygonSide)
    (tag : CanonicalProjectivePostConeRawContourSideOriginTag hp hp2 slot ih s) :=
  (canonicalProjectivePostConeRawContourTerm hp hp2 slot ih s).get
    ((canonicalProjectivePostConeRawContourSide_positionEquiv
      hp hp2 slot ih s).symm tag)

/-- The signed letter decoded from a nested side-list origin tag. -/
noncomputable def canonicalProjectivePostConeRawContourTermsOriginTag_letter
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool)) :
    (sides : List ProjectivePolygonSide) →
      CanonicalProjectivePostConeRawContourTermsOriginTag hp hp2 slot ih sides →
        CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool
  | [] => fun tag => tag.elim
  | s :: ss => fun tag =>
      Sum.elim
        (canonicalProjectivePostConeRawContourSideOriginTag_letter hp hp2 slot ih s)
        (canonicalProjectivePostConeRawContourTermsOriginTag_letter hp hp2 slot ih ss)
        tag

/-- Each side-list origin tag decodes to the exact raw word element at its
inverse-image position. -/
theorem canonicalProjectivePostConeRawContourTerms_originEquiv_get
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool))
    (sides : List ProjectivePolygonSide)
    (tag : CanonicalProjectivePostConeRawContourTermsOriginTag hp hp2 slot ih sides) :
    (canonicalProjectivePostConeRawContourTerms hp hp2 slot ih sides).get
      ((canonicalProjectivePostConeRawContourTerms_originEquiv
        hp hp2 slot ih sides).symm tag) =
      canonicalProjectivePostConeRawContourTermsOriginTag_letter hp hp2 slot ih sides tag := by
  induction sides with
  | nil => cases tag
  | cons s ss ihs =>
      cases tag with
      | inl head =>
          have hindex :
              (canonicalProjectivePostConeRawContourTerms_originEquiv
                hp hp2 slot ih (s :: ss)).symm (Sum.inl head) =
                (canonicalProjectivePostConeRawContourTerms_positionSplit_cons
                  hp hp2 slot ih s ss).symm
                  (Sum.inl ((canonicalProjectivePostConeRawContourSide_positionEquiv
                    hp hp2 slot ih s).symm head)) := by
            change (canonicalProjectivePostConeRawContourTerms_positionSplit_cons
                hp hp2 slot ih s ss).symm
                ((Equiv.sumCongr
                  (canonicalProjectivePostConeRawContourSide_positionEquiv hp hp2 slot ih s)
                  (canonicalProjectivePostConeRawContourTerms_originEquiv
                    hp hp2 slot ih ss)).symm (Sum.inl head)) = _
            congr 1
          rw [hindex, canonicalProjectivePostConeRawContourTerms_get_cons_left]
          rfl
      | inr tail =>
          have hindex :
              (canonicalProjectivePostConeRawContourTerms_originEquiv
                hp hp2 slot ih (s :: ss)).symm (Sum.inr tail) =
                (canonicalProjectivePostConeRawContourTerms_positionSplit_cons
                  hp hp2 slot ih s ss).symm
                  (Sum.inr ((canonicalProjectivePostConeRawContourTerms_originEquiv
                    hp hp2 slot ih ss).symm tail)) := by
            change (canonicalProjectivePostConeRawContourTerms_positionSplit_cons
                hp hp2 slot ih s ss).symm
                ((Equiv.sumCongr
                  (canonicalProjectivePostConeRawContourSide_positionEquiv hp hp2 slot ih s)
                  (canonicalProjectivePostConeRawContourTerms_originEquiv
                    hp hp2 slot ih ss)).symm (Sum.inr tail)) = _
            congr 1
          rw [hindex, canonicalProjectivePostConeRawContourTerms_get_cons_right]
          exact ihs tail

/-- Decoding a head-side tag returns the indicated local raw term. -/
theorem canonicalProjectivePostConeRawContourTerms_positionEquiv_get_head
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool))
    (s : ProjectivePolygonSide) (ss : List ProjectivePolygonSide)
    (i : Fin (canonicalProjectivePostConeRawContourTerm hp hp2 slot ih s).length) :
    (canonicalProjectivePostConeRawContourTerms hp hp2 slot ih (s :: ss)).get
      ((canonicalProjectivePostConeRawContourTerms_positionEquiv
        hp hp2 slot ih (s :: ss)).symm (Sum.inl i)) =
      (canonicalProjectivePostConeRawContourTerm hp hp2 slot ih s).get i := by
  simp only [canonicalProjectivePostConeRawContourTerms_positionEquiv]
  exact canonicalProjectivePostConeRawContourTerms_get_cons_left
    hp hp2 slot ih s ss i

/-- Decoding a tail-side tag is the recursive decoder for the remaining
side occurrences. -/
theorem canonicalProjectivePostConeRawContourTerms_positionEquiv_get_tail
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool))
    (s : ProjectivePolygonSide) (ss : List ProjectivePolygonSide)
    (i : CanonicalProjectivePostConeRawContourTermsPositionTag hp hp2 slot ih ss) :
    (canonicalProjectivePostConeRawContourTerms hp hp2 slot ih (s :: ss)).get
      ((canonicalProjectivePostConeRawContourTerms_positionEquiv
        hp hp2 slot ih (s :: ss)).symm (Sum.inr i)) =
      (canonicalProjectivePostConeRawContourTerms hp hp2 slot ih ss).get
        ((canonicalProjectivePostConeRawContourTerms_positionEquiv
          hp hp2 slot ih ss).symm i) := by
  simp only [canonicalProjectivePostConeRawContourTerms_positionEquiv]
  exact canonicalProjectivePostConeRawContourTerms_get_cons_right
    hp hp2 slot ih s ss
    ((canonicalProjectivePostConeRawContourTerms_positionEquiv
      hp hp2 slot ih ss).symm i)

/-- Any side-term position embeds into the concatenated side-list word at
every occurrence of that side, preserving its exact signed letter. -/
theorem canonicalProjectivePostConeRawContourTerms_exists_position_of_mem
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool))
    (sides : List ProjectivePolygonSide) (s : ProjectivePolygonSide)
    (hs : s ∈ sides)
    (i : Fin (canonicalProjectivePostConeRawContourTerm hp hp2 slot ih s).length) :
    ∃ j : Fin (canonicalProjectivePostConeRawContourTerms hp hp2 slot ih sides).length,
      (canonicalProjectivePostConeRawContourTerms hp hp2 slot ih sides).get j =
        (canonicalProjectivePostConeRawContourTerm hp hp2 slot ih s).get i := by
  induction sides generalizing s i with
  | nil => cases hs
  | cons head tail ihs =>
      simp only [List.mem_cons] at hs
      rcases hs with hhead | htail
      · subst s
        refine ⟨(canonicalProjectivePostConeRawContourTerms_positionSplit_cons
          hp hp2 slot ih head tail).symm (Sum.inl i), ?_⟩
        exact canonicalProjectivePostConeRawContourTerms_get_cons_left
          hp hp2 slot ih head tail i
      · obtain ⟨j, hj⟩ := ihs s htail i
        refine ⟨(canonicalProjectivePostConeRawContourTerms_positionSplit_cons
          hp hp2 slot ih head tail).symm (Sum.inr j), ?_⟩
        rw [canonicalProjectivePostConeRawContourTerms_get_cons_right]
        exact hj

/-- The left summand of the append-position split is the canonical initial
offset. -/
theorem canonicalProjectivePostConeRawAppendPositionSplit_left
    {α : Type*} (xs ys : List α) (i : Fin xs.length) :
    canonicalProjectivePostConeRawAppendPositionSplit xs ys
      (Fin.cast (by simp) (Fin.castAdd ys.length i)) = Sum.inl i := by
  simp [canonicalProjectivePostConeRawAppendPositionSplit]

/-- The right summand of the append-position split is the canonical offset
past the left block. -/
theorem canonicalProjectivePostConeRawAppendPositionSplit_right
    {α : Type*} (xs ys : List α) (i : Fin ys.length) :
    canonicalProjectivePostConeRawAppendPositionSplit xs ys
      (Fin.cast (by simp) (Fin.natAdd xs.length i)) = Sum.inr i := by
  simp [canonicalProjectivePostConeRawAppendPositionSplit]

/-- The canonical index offset for the left block of a concatenated raw
word. Unlike a `List.Sublist` embedding, this identifies the exact initial
segment of the concatenation. -/
theorem canonicalProjectivePostConeRawAppend_get_left
    {α : Type*} (xs ys : List α) (i : Fin xs.length) :
    (xs ++ ys).get (Fin.cast (by simp) (Fin.castAdd ys.length i)) = xs.get i := by
  simp

/-- The canonical index offset for the right block of a concatenated raw
word. The two maps in the adjacent lemmas have disjoint ranges and together
cover every index of `xs ++ ys`. -/
theorem canonicalProjectivePostConeRawAppend_get_right
    {α : Type*} (xs ys : List α) (i : Fin ys.length) :
    (xs ++ ys).get (Fin.cast (by simp) (Fin.natAdd xs.length i)) = ys.get i := by
  simp

/-- Transport the left-block `get` law across an equality identifying a
recursive word with a concatenation. -/
private theorem canonicalProjectivePostConeRaw_get_eq_append_left
    {α : Type*} {word xs ys : List α} (hword : word = xs ++ ys)
    (i : Fin xs.length) :
    word.get (Fin.cast (congrArg List.length hword.symm)
      (Fin.cast (by simp) (Fin.castAdd ys.length i))) = xs.get i := by
  exact (get_cast_eq_of_eq hword.symm
    (Fin.cast (by simp) (Fin.castAdd ys.length i))).trans
      (canonicalProjectivePostConeRawAppend_get_left xs ys i)

/-- Transport the right-block `get` law across an equality identifying a
recursive word with a concatenation. -/
private theorem canonicalProjectivePostConeRaw_get_eq_append_right
    {α : Type*} {word xs ys : List α} (hword : word = xs ++ ys)
    (i : Fin ys.length) :
    word.get (Fin.cast (congrArg List.length hword.symm)
      (Fin.cast (by simp) (Fin.natAdd xs.length i))) = ys.get i := by
  exact (get_cast_eq_of_eq hword.symm
    (Fin.cast (by simp) (Fin.natAdd xs.length i))).trans
      (canonicalProjectivePostConeRawAppend_get_right xs ys i)

/-- Transport the inverse append-split position itself across an equality
identifying a recursive word with its two blocks. -/
theorem canonicalProjectivePostConeRaw_get_eq_appendSplit_left
    {α : Type*} {word xs ys : List α} (hword : word = xs ++ ys)
    (i : Fin xs.length) :
    word.get (Fin.cast (congrArg List.length hword.symm)
      ((canonicalProjectivePostConeRawAppendPositionSplit xs ys).symm
        (Sum.inl i))) = xs.get i := by
  exact (get_cast_eq_of_eq hword.symm
    ((canonicalProjectivePostConeRawAppendPositionSplit xs ys).symm (Sum.inl i))).trans
      (canonicalProjectivePostConeRawAppendPositionSplit_get_left xs ys i)

/-- Right-block counterpart of `canonicalProjectivePostConeRaw_get_eq_appendSplit_left`. -/
theorem canonicalProjectivePostConeRaw_get_eq_appendSplit_right
    {α : Type*} {word xs ys : List α} (hword : word = xs ++ ys)
    (i : Fin ys.length) :
    word.get (Fin.cast (congrArg List.length hword.symm)
      ((canonicalProjectivePostConeRawAppendPositionSplit xs ys).symm
        (Sum.inr i))) = ys.get i := by
  exact (get_cast_eq_of_eq hword.symm
    ((canonicalProjectivePostConeRawAppendPositionSplit xs ys).symm (Sum.inr i))).trans
      (canonicalProjectivePostConeRawAppendPositionSplit_get_right xs ys i)

/-- Signed multiplicities in a tree-slot side expansion add across its
ordered list of sides. -/
theorem canonicalProjectivePostConeRawContourTerms_signedOccurrenceCount
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool))
    (sides : List ProjectivePolygonSide)
    [DecidableEq (CanonicalProjectivePostConeFinalGenerator hp hp2)]
    (z : CanonicalProjectivePostConeFinalGenerator hp hp2) (positive : Bool) :
    signedOccurrenceCount z positive
        (canonicalProjectivePostConeRawContourTerms hp hp2 slot ih sides) =
      (sides.map fun s => signedOccurrenceCount z positive
        (canonicalProjectivePostConeRawContourTerm hp hp2 slot ih s)).sum := by
  classical
  induction sides with
  | nil => rfl
  | cons side sides ihs =>
      simp only [canonicalProjectivePostConeRawContourTerms,
        List.map_cons, List.sum_cons]
      rw [signedOccurrenceCount_append, ihs]

private theorem canonicalProjectivePostConeRawContourTerms_mem_of_side_mem
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool))
    (sides : List ProjectivePolygonSide) (s : ProjectivePolygonSide)
    (letter : CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool)
    (hs : s ∈ sides)
    (hletter : letter ∈ canonicalProjectivePostConeRawContourTerm hp hp2 slot ih s) :
    letter ∈ canonicalProjectivePostConeRawContourTerms hp hp2 slot ih sides := by
  induction sides with
  | nil => simp at hs
  | cons t ts ihs =>
      simp only [canonicalProjectivePostConeRawContourTerms, List.mem_append]
      rcases List.mem_cons.mp hs with hside | hside
      · subst t
        exact Or.inl hletter
      · exact Or.inr (ihs hside)

private theorem canonicalProjectivePostConeRawContourTerms_eval
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool))
    (sides : List ProjectivePolygonSide)
    (hsides : ∀ s ∈ sides,
      s ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot) :
    FreeGroup.mk (canonicalProjectivePostConeRawContourTerms hp hp2 slot ih sides) =
      (List.map (fun s =>
        canonicalProjectivePostConeDirectTreeSubstitutionHom hp hp2 slot
          (fun other hdeep => FreeGroup.mk (ih other hdeep))
          (canonicalProjectiveConePostConeBoundaryTerm p slot.right.state s)) sides).prod := by
  induction sides with
  | nil => exact FreeGroup.one_eq_mk.symm
  | cons s sides hind =>
      simp only [canonicalProjectivePostConeRawContourTerms, List.map_cons,
        List.prod_cons]
      rw [← FreeGroup.mul_mk,
        canonicalProjectivePostConeRawContourTerm_eval hp hp2 slot ih s
          (hsides s (by simp)),
        hind (fun t ht => hsides t (by simp [ht]))]

/-- The unreduced expansion of the prefix at a tree slot. -/
noncomputable def canonicalProjectivePostConeRawContourPrefix
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool)) :
    List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool) :=
  canonicalProjectivePostConeRawContourTerms hp hp2 slot ih
    (canonicalProjectivePostConeBoundaryPrefixSides
      (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))

/-- The unreduced expansion of the suffix at a tree slot. -/
noncomputable def canonicalProjectivePostConeRawContourSuffix
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool)) :
    List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool) :=
  canonicalProjectivePostConeRawContourTerms hp hp2 slot ih
    (canonicalProjectivePostConeBoundarySuffixSides
      (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))

/- Every raw term on a prefix side occurs in the concatenated raw prefix. -/
theorem canonicalProjectivePostConeRawContourTerm_mem_prefix
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool))
    (s : ProjectivePolygonSide)
    (hs : s ∈ canonicalProjectivePostConeBoundaryPrefixSides
      (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
    (letter : CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool)
    (hletter : letter ∈ canonicalProjectivePostConeRawContourTerm hp hp2 slot ih s) :
    letter ∈ canonicalProjectivePostConeRawContourPrefix hp hp2 slot ih := by
  unfold canonicalProjectivePostConeRawContourPrefix
  exact canonicalProjectivePostConeRawContourTerms_mem_of_side_mem
    hp hp2 slot ih _ s letter hs hletter

/- Every raw term on a suffix side occurs in the concatenated raw suffix. -/
theorem canonicalProjectivePostConeRawContourTerm_mem_suffix
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool))
    (s : ProjectivePolygonSide)
    (hs : s ∈ canonicalProjectivePostConeBoundarySuffixSides
      (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
    (letter : CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool)
    (hletter : letter ∈ canonicalProjectivePostConeRawContourTerm hp hp2 slot ih s) :
    letter ∈ canonicalProjectivePostConeRawContourSuffix hp hp2 slot ih := by
  unfold canonicalProjectivePostConeRawContourSuffix
  exact canonicalProjectivePostConeRawContourTerms_mem_of_side_mem
    hp hp2 slot ih _ s letter hs hletter

private theorem canonicalProjectivePostConeRawContourPrefix_eval
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool)) :
    FreeGroup.mk (canonicalProjectivePostConeRawContourPrefix hp hp2 slot ih) =
      canonicalProjectivePostConeDirectTreeSubstitutionHom hp hp2 slot
        (fun other hdeep => FreeGroup.mk (ih other hdeep))
        (canonicalProjectiveConePostConeBoundaryPrefix p slot.right.state
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) := by
  unfold canonicalProjectivePostConeRawContourPrefix
  rw [canonicalProjectivePostConeRawContourTerms_eval hp hp2 slot ih _
    (fun t ht => canonicalProjectivePostConeBoundaryPrefixSides_ne _ t ht)]
  calc
    _ = canonicalProjectivePostConeDirectTreeSubstitutionHom hp hp2 slot
        (fun other hdeep => FreeGroup.mk (ih other hdeep))
        ((List.map (canonicalProjectiveConePostConeBoundaryTerm p slot.right.state)
          (canonicalProjectivePostConeBoundaryPrefixSides
            (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))).prod) := by
      symm
      simpa [Function.comp_def] using
        map_list_prod
          (canonicalProjectivePostConeDirectTreeSubstitutionHom hp hp2 slot
            (fun other hdeep => FreeGroup.mk (ih other hdeep)))
          (List.map (canonicalProjectiveConePostConeBoundaryTerm p slot.right.state)
            (canonicalProjectivePostConeBoundaryPrefixSides
              (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)))
    _ = _ := by rw [canonicalProjectivePostConeBoundaryPrefixSides_prod]

private theorem canonicalProjectivePostConeRawContourSuffix_eval
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool)) :
    FreeGroup.mk (canonicalProjectivePostConeRawContourSuffix hp hp2 slot ih) =
      canonicalProjectivePostConeDirectTreeSubstitutionHom hp hp2 slot
        (fun other hdeep => FreeGroup.mk (ih other hdeep))
        (canonicalProjectiveConePostConeBoundarySuffix p slot.right.state
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) := by
  unfold canonicalProjectivePostConeRawContourSuffix
  rw [canonicalProjectivePostConeRawContourTerms_eval hp hp2 slot ih _
    (fun t ht => canonicalProjectivePostConeBoundarySuffixSides_ne _ t ht)]
  calc
    _ = canonicalProjectivePostConeDirectTreeSubstitutionHom hp hp2 slot
        (fun other hdeep => FreeGroup.mk (ih other hdeep))
        ((List.map (canonicalProjectiveConePostConeBoundaryTerm p slot.right.state)
          (canonicalProjectivePostConeBoundarySuffixSides
            (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))).prod) := by
      symm
      simpa [Function.comp_def] using
        map_list_prod
          (canonicalProjectivePostConeDirectTreeSubstitutionHom hp hp2 slot
            (fun other hdeep => FreeGroup.mk (ih other hdeep)))
          (List.map (canonicalProjectiveConePostConeBoundaryTerm p slot.right.state)
            (canonicalProjectivePostConeBoundarySuffixSides
              (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)))
    _ = _ := by rw [canonicalProjectivePostConeBoundarySuffixSides_prod]

/-- The unreduced signed word at a tree slot.  It follows the same
reverse-depth recursion as the direct tree word, but uses list concatenation
and `invRev` rather than multiplication and inversion. -/
noncomputable def canonicalProjectivePostConeRawTreeWordBySlot
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    CanonicalProjectivePostConeTreeSlot hp hp2 →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool) :=
  (canonicalProjectivePostConeDirectTreeDependencyWellFounded hp hp2).fix
    (fun slot ih => by
      classical
      exact if hsource : slot.right = projectivePolygonPostConeEdgeSource
          (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)
        then
          FreeGroup.invRev (canonicalProjectivePostConeRawContourPrefix hp hp2 slot ih) ++
            FreeGroup.invRev (canonicalProjectivePostConeRawContourSuffix hp hp2 slot ih)
        else
          canonicalProjectivePostConeRawContourSuffix hp hp2 slot ih ++
          canonicalProjectivePostConeRawContourPrefix hp hp2 slot ih)

/-- In the source-oriented branch, the recursive slot word is the inverse
reversal of the prefix followed by the inverse reversal of the suffix. -/
theorem canonicalProjectivePostConeRawTreeWordBySlot_eq_splice_of_source
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hsource : slot.right = projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)) :
    canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot =
      FreeGroup.invRev (canonicalProjectivePostConeRawContourPrefix hp hp2 slot
        (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)) ++
        FreeGroup.invRev (canonicalProjectivePostConeRawContourSuffix hp hp2 slot
          (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)) := by
  classical
  unfold canonicalProjectivePostConeRawTreeWordBySlot
  rw [WellFounded.fix_eq]
  rw [dif_pos hsource]

/-- In the target-oriented branch, the recursive slot word concatenates the
suffix before the prefix without changing orientation. -/
theorem canonicalProjectivePostConeRawTreeWordBySlot_eq_splice_of_target
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hsource : slot.right ≠ projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)) :
    canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot =
      canonicalProjectivePostConeRawContourSuffix hp hp2 slot
        (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) ++
      canonicalProjectivePostConeRawContourPrefix hp hp2 slot
        (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) := by
  classical
  unfold canonicalProjectivePostConeRawTreeWordBySlot
  rw [WellFounded.fix_eq]
  rw [dif_neg hsource]

/-- Every position in a recursive slot word belongs uniquely to one of its
two ordered boundary blocks. In the source-oriented case these are the
inverse-reversed prefix and suffix; in the target-oriented case they are the
suffix and prefix. This is the exact, disjoint offset split needed to lift
positions through a slot splice. -/
noncomputable def canonicalProjectivePostConeRawTreeWordBySlot_positionSplit_of_source
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hsource : slot.right = projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)) :
    Fin (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot).length ≃
      Fin ((FreeGroup.invRev (canonicalProjectivePostConeRawContourPrefix hp hp2 slot
        (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other))).length) ⊕
    Fin ((FreeGroup.invRev (canonicalProjectivePostConeRawContourSuffix hp hp2 slot
        (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other))).length) := by
  let hsplice := canonicalProjectivePostConeRawTreeWordBySlot_eq_splice_of_source
    hp hp2 slot hsource
  exact (finCongr (congrArg List.length hsplice)).trans
    (canonicalProjectivePostConeRawAppendPositionSplit _ _)

/-- The source split is definitionally the length transport followed by the
canonical finite append split. -/
theorem canonicalProjectivePostConeRawTreeWordBySlot_positionSplit_of_source_eq
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hsource : slot.right = projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)) :
    canonicalProjectivePostConeRawTreeWordBySlot_positionSplit_of_source
        hp hp2 slot hsource =
      (finCongr (congrArg List.length
        (canonicalProjectivePostConeRawTreeWordBySlot_eq_splice_of_source
          hp hp2 slot hsource))).trans
        (canonicalProjectivePostConeRawAppendPositionSplit
          (FreeGroup.invRev (canonicalProjectivePostConeRawContourPrefix hp hp2 slot
            (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)))
          (FreeGroup.invRev (canonicalProjectivePostConeRawContourSuffix hp hp2 slot
            (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)))) := by
  rfl

/-- The inverse source split's left tag is exactly the casted inverse append
position. -/
theorem canonicalProjectivePostConeRawTreeWordBySlot_positionSplit_of_source_symm_inl
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hsource : slot.right = projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot))
    (i : Fin ((FreeGroup.invRev (canonicalProjectivePostConeRawContourPrefix hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other))).length)) :
    (canonicalProjectivePostConeRawTreeWordBySlot_positionSplit_of_source
      hp hp2 slot hsource).symm (Sum.inl i) =
      Fin.cast (congrArg List.length
        (canonicalProjectivePostConeRawTreeWordBySlot_eq_splice_of_source
          hp hp2 slot hsource).symm)
        ((canonicalProjectivePostConeRawAppendPositionSplit
          (FreeGroup.invRev (canonicalProjectivePostConeRawContourPrefix hp hp2 slot
            (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)))
          (FreeGroup.invRev (canonicalProjectivePostConeRawContourSuffix hp hp2 slot
            (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)))).symm
          (Sum.inl i)) := by
  rw [canonicalProjectivePostConeRawTreeWordBySlot_positionSplit_of_source_eq]
  rfl

/-- The source split's left block preserves the exact element selected by its
inverse position map. -/
theorem canonicalProjectivePostConeRawTreeWordBySlot_get_source_prefix
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hsource : slot.right = projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot))
    (i : Fin ((FreeGroup.invRev (canonicalProjectivePostConeRawContourPrefix hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other))).length)) :
    (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot).get
      ((canonicalProjectivePostConeRawTreeWordBySlot_positionSplit_of_source
        hp hp2 slot hsource).symm (Sum.inl i)) =
      (FreeGroup.invRev (canonicalProjectivePostConeRawContourPrefix hp hp2 slot
        (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other))).get i := by
  rw [canonicalProjectivePostConeRawTreeWordBySlot_positionSplit_of_source_symm_inl]
  exact canonicalProjectivePostConeRaw_get_eq_appendSplit_left
    (canonicalProjectivePostConeRawTreeWordBySlot_eq_splice_of_source
      hp hp2 slot hsource) i

/-- In terms of the unreversed prefix index, the source splice reads the
same generator and flips its orientation bit. -/
theorem canonicalProjectivePostConeRawTreeWordBySlot_get_source_prefix_invRevPosition
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hsource : slot.right = projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot))
    (i : Fin (canonicalProjectivePostConeRawContourPrefix hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)).length) :
    (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot).get
      ((canonicalProjectivePostConeRawTreeWordBySlot_positionSplit_of_source
        hp hp2 slot hsource).symm (Sum.inl (invRevPosition i))) =
      (((canonicalProjectivePostConeRawContourPrefix hp hp2 slot
        (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)).get i).1,
        !((canonicalProjectivePostConeRawContourPrefix hp hp2 slot
          (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)).get i).2) := by
  rw [canonicalProjectivePostConeRawTreeWordBySlot_get_source_prefix,
    get_invRevPosition]

/-- Reading the right tag of the source split identifies the exact
inverse-reversed suffix position. -/
theorem canonicalProjectivePostConeRawTreeWordBySlot_positionSplit_of_source_symm_inr
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hsource : slot.right = projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot))
    (i : Fin ((FreeGroup.invRev (canonicalProjectivePostConeRawContourSuffix hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other))).length)) :
    (canonicalProjectivePostConeRawTreeWordBySlot_positionSplit_of_source
      hp hp2 slot hsource).symm (Sum.inr i) =
      Fin.cast (congrArg List.length
        (canonicalProjectivePostConeRawTreeWordBySlot_eq_splice_of_source
          hp hp2 slot hsource).symm)
        ((canonicalProjectivePostConeRawAppendPositionSplit
          (FreeGroup.invRev (canonicalProjectivePostConeRawContourPrefix hp hp2 slot
            (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)))
          (FreeGroup.invRev (canonicalProjectivePostConeRawContourSuffix hp hp2 slot
            (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)))).symm
          (Sum.inr i)) := by
  rw [canonicalProjectivePostConeRawTreeWordBySlot_positionSplit_of_source_eq]
  rfl

/-- The source split's right block reads its exact inverse-reversed suffix
element. -/
theorem canonicalProjectivePostConeRawTreeWordBySlot_get_source_suffix
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hsource : slot.right = projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot))
    (i : Fin ((FreeGroup.invRev (canonicalProjectivePostConeRawContourSuffix hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other))).length)) :
    (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot).get
      ((canonicalProjectivePostConeRawTreeWordBySlot_positionSplit_of_source
        hp hp2 slot hsource).symm (Sum.inr i)) =
      (FreeGroup.invRev (canonicalProjectivePostConeRawContourSuffix hp hp2 slot
        (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other))).get i := by
  rw [canonicalProjectivePostConeRawTreeWordBySlot_positionSplit_of_source_symm_inr]
  exact canonicalProjectivePostConeRaw_get_eq_appendSplit_right
    (canonicalProjectivePostConeRawTreeWordBySlot_eq_splice_of_source
      hp hp2 slot hsource) i

/-- In terms of the unreversed suffix index, the source splice keeps the
generator and flips its orientation bit. -/
theorem canonicalProjectivePostConeRawTreeWordBySlot_get_source_suffix_invRevPosition
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hsource : slot.right = projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot))
    (i : Fin (canonicalProjectivePostConeRawContourSuffix hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)).length) :
    (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot).get
      ((canonicalProjectivePostConeRawTreeWordBySlot_positionSplit_of_source
        hp hp2 slot hsource).symm (Sum.inr (invRevPosition i))) =
      (((canonicalProjectivePostConeRawContourSuffix hp hp2 slot
        (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)).get i).1,
        !((canonicalProjectivePostConeRawContourSuffix hp hp2 slot
          (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)).get i).2) := by
  rw [canonicalProjectivePostConeRawTreeWordBySlot_get_source_suffix,
    get_invRevPosition]

/-- The target-oriented position split: the suffix block precedes the
prefix block and neither block is reversed. -/
noncomputable def canonicalProjectivePostConeRawTreeWordBySlot_positionSplit_of_target
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hsource : slot.right ≠ projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)) :
    Fin (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot).length ≃
      Fin (canonicalProjectivePostConeRawContourSuffix hp hp2 slot
        (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)).length ⊕
    Fin (canonicalProjectivePostConeRawContourPrefix hp hp2 slot
        (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)).length := by
  let hsplice := canonicalProjectivePostConeRawTreeWordBySlot_eq_splice_of_target
    hp hp2 slot hsource
  exact (finCongr (congrArg List.length hsplice)).trans
    (canonicalProjectivePostConeRawAppendPositionSplit _ _)

/-- Inverse reversal does not change the underlying origin type of a
side-list expansion; it transports positions back through
`invRevPosition`. -/
noncomputable def canonicalProjectivePostConeRawContourTerms_invRev_originEquiv
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (sides : List ProjectivePolygonSide) :
    Fin (FreeGroup.invRev
      (canonicalProjectivePostConeRawContourTerms hp hp2 slot
        (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)
        sides)).length ≃
      CanonicalProjectivePostConeRawContourTermsOriginTag hp hp2 slot
        (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)
        sides := by
  let word := canonicalProjectivePostConeRawContourTerms hp hp2 slot
    (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) sides
  exact (Equiv.ofBijective (@invRevPosition _ word) (invRevPosition_bijective word)).symm.trans
    (canonicalProjectivePostConeRawContourTerms_originEquiv hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) sides)

/-- An origin tag for an inverse-reversed side-list word decodes to the
same generator with its sign toggled. -/
theorem canonicalProjectivePostConeRawContourTerms_invRev_originEquiv_get
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (sides : List ProjectivePolygonSide)
    (tag : CanonicalProjectivePostConeRawContourTermsOriginTag hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)
      sides) :
    (FreeGroup.invRev (canonicalProjectivePostConeRawContourTerms hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)
      sides)).get
      ((canonicalProjectivePostConeRawContourTerms_invRev_originEquiv
        hp hp2 slot sides).symm tag) =
      ((canonicalProjectivePostConeRawContourTermsOriginTag_letter hp hp2 slot
        (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)
        sides tag).1,
        !(canonicalProjectivePostConeRawContourTermsOriginTag_letter hp hp2 slot
          (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)
          sides tag).2) := by
  let word := canonicalProjectivePostConeRawContourTerms hp hp2 slot
    (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) sides
  let positionEquiv := canonicalProjectivePostConeRawContourTerms_originEquiv hp hp2 slot
    (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) sides
  let reverseEquiv := Equiv.ofBijective (@invRevPosition _ word)
    (invRevPosition_bijective word)
  change (FreeGroup.invRev word).get
    (invRevPosition (positionEquiv.symm tag)) = _
  rw [get_invRevPosition]
  rw [canonicalProjectivePostConeRawContourTerms_originEquiv_get]

/-- The literal prefix expansion is the side-list expansion of the ordered
prefix sides, with no change to its occurrence order. -/
theorem canonicalProjectivePostConeRawContourPrefix_eq_terms
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    canonicalProjectivePostConeRawContourPrefix hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) =
    canonicalProjectivePostConeRawContourTerms hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)
      (canonicalProjectivePostConeBoundaryPrefixSides
        (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) := rfl

/-- The suffix expansion is likewise the concatenation over the ordered
suffix-side list. -/
theorem canonicalProjectivePostConeRawContourSuffix_eq_terms
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    canonicalProjectivePostConeRawContourSuffix hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) =
    canonicalProjectivePostConeRawContourTerms hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)
      (canonicalProjectivePostConeBoundarySuffixSides
        (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) := rfl

/-- Explicitly transport the inverse-reversed prefix block to its nested
side-list origin type. -/
noncomputable def canonicalProjectivePostConeRawContourPrefix_invRev_originEquiv
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    Fin ((FreeGroup.invRev (canonicalProjectivePostConeRawContourPrefix hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other))).length) ≃
      CanonicalProjectivePostConeRawContourTermsOriginTag hp hp2 slot
        (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)
        (canonicalProjectivePostConeBoundaryPrefixSides
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) := by
  let sides := canonicalProjectivePostConeBoundaryPrefixSides
    (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)
  let hword := congrArg FreeGroup.invRev
    (canonicalProjectivePostConeRawContourPrefix_eq_terms hp hp2 slot)
  exact (finCongr (congrArg List.length hword)).trans
    (canonicalProjectivePostConeRawContourTerms_invRev_originEquiv hp hp2 slot sides)

/-- Explicitly transport the inverse-reversed suffix block to its nested
side-list origin type. -/
noncomputable def canonicalProjectivePostConeRawContourSuffix_invRev_originEquiv
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    Fin ((FreeGroup.invRev (canonicalProjectivePostConeRawContourSuffix hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other))).length) ≃
      CanonicalProjectivePostConeRawContourTermsOriginTag hp hp2 slot
        (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)
        (canonicalProjectivePostConeBoundarySuffixSides
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) := by
  let sides := canonicalProjectivePostConeBoundarySuffixSides
    (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)
  let hword := congrArg FreeGroup.invRev
    (canonicalProjectivePostConeRawContourSuffix_eq_terms hp hp2 slot)
  exact (finCongr (congrArg List.length hword)).trans
    (canonicalProjectivePostConeRawContourTerms_invRev_originEquiv hp hp2 slot sides)

/-- Explicitly transport an unreversed prefix block to its nested
side-list origin type. -/
noncomputable def canonicalProjectivePostConeRawContourPrefix_originEquiv
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    Fin (canonicalProjectivePostConeRawContourPrefix hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)).length ≃
      CanonicalProjectivePostConeRawContourTermsOriginTag hp hp2 slot
        (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)
        (canonicalProjectivePostConeBoundaryPrefixSides
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) := by
  exact (finCongr (congrArg List.length
      (canonicalProjectivePostConeRawContourPrefix_eq_terms hp hp2 slot))).trans
    (canonicalProjectivePostConeRawContourTerms_originEquiv hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)
      (canonicalProjectivePostConeBoundaryPrefixSides
        (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)))

/-- Explicitly transport an unreversed suffix block to its nested
side-list origin type. -/
noncomputable def canonicalProjectivePostConeRawContourSuffix_originEquiv
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    Fin (canonicalProjectivePostConeRawContourSuffix hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)).length ≃
      CanonicalProjectivePostConeRawContourTermsOriginTag hp hp2 slot
        (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)
        (canonicalProjectivePostConeBoundarySuffixSides
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) := by
  exact (finCongr (congrArg List.length
      (canonicalProjectivePostConeRawContourSuffix_eq_terms hp hp2 slot))).trans
    (canonicalProjectivePostConeRawContourTerms_originEquiv hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)
      (canonicalProjectivePostConeBoundarySuffixSides
        (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)))

/-- Origin tags for a complete recursive slot word. Source-oriented slots
carry the inverse-reversed prefix before the inverse-reversed suffix;
target-oriented slots carry the unchanged suffix before the prefix. -/
inductive CanonicalProjectivePostConeRawTreeWordOriginTag
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) : Type where
  | source
      (hsource : slot.right = projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot))
      (tag : CanonicalProjectivePostConeRawContourTermsOriginTag hp hp2 slot
        (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)
        (canonicalProjectivePostConeBoundaryPrefixSides
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) ⊕
        CanonicalProjectivePostConeRawContourTermsOriginTag hp hp2 slot
          (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)
          (canonicalProjectivePostConeBoundarySuffixSides
            (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))) :
      CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 slot
  | target
      (htarget : slot.right ≠ projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot))
      (tag : CanonicalProjectivePostConeRawContourTermsOriginTag hp hp2 slot
        (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)
        (canonicalProjectivePostConeBoundarySuffixSides
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) ⊕
        CanonicalProjectivePostConeRawContourTermsOriginTag hp hp2 slot
          (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)
          (canonicalProjectivePostConeBoundaryPrefixSides
            (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))) :
      CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 slot

/-- Every position of the complete recursive word at a tree slot has an
origin in exactly one of its ordered prefix/suffix side regions. -/
noncomputable def canonicalProjectivePostConeRawTreeWordBySlot_originEquiv
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    Fin (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot).length ≃
      CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 slot := by
  classical
  by_cases hsource : projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) = slot.right
  · let sourceEquiv :=
      (canonicalProjectivePostConeRawTreeWordBySlot_positionSplit_of_source
        hp hp2 slot hsource.symm).trans
        (Equiv.sumCongr
          (canonicalProjectivePostConeRawContourPrefix_invRev_originEquiv hp hp2 slot)
          (canonicalProjectivePostConeRawContourSuffix_invRev_originEquiv hp hp2 slot))
    refine {
      toFun := fun i => .source hsource.symm (sourceEquiv i)
      invFun := fun tag => match tag with
        | .source hs t =>
            (canonicalProjectivePostConeRawTreeWordBySlot_positionSplit_of_source
              hp hp2 slot hs).symm
              ((Equiv.sumCongr
                (canonicalProjectivePostConeRawContourPrefix_invRev_originEquiv hp hp2 slot)
                (canonicalProjectivePostConeRawContourSuffix_invRev_originEquiv hp hp2 slot)).symm t)
        | .target ht _ => False.elim (ht hsource.symm)
      left_inv := by intro i; simp [sourceEquiv]
      right_inv := by
        intro tag
        cases tag with
        | source hs t => simp [sourceEquiv]
        | target ht t => exact False.elim (ht hsource.symm) }
  · have htarget : slot.right ≠ projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) :=
        fun hr => hsource hr.symm
    let targetEquiv :=
      (canonicalProjectivePostConeRawTreeWordBySlot_positionSplit_of_target
        hp hp2 slot htarget).trans
        (Equiv.sumCongr
          (canonicalProjectivePostConeRawContourSuffix_originEquiv hp hp2 slot)
          (canonicalProjectivePostConeRawContourPrefix_originEquiv hp hp2 slot))
    refine {
      toFun := fun i => .target htarget (targetEquiv i)
      invFun := fun tag => match tag with
        | .source hs _ => False.elim (hsource hs.symm)
        | .target ht t =>
            (canonicalProjectivePostConeRawTreeWordBySlot_positionSplit_of_target
              hp hp2 slot ht).symm
              ((Equiv.sumCongr
                (canonicalProjectivePostConeRawContourSuffix_originEquiv hp hp2 slot)
                (canonicalProjectivePostConeRawContourPrefix_originEquiv hp hp2 slot)).symm t)
      left_inv := by intro i; simp [targetEquiv]
      right_inv := by
        intro tag
        cases tag with
        | source hs t => exact False.elim (hsource hs.symm)
        | target ht t => simp [targetEquiv] }

/-- The signed final letter named by a complete-slot origin tag. The source
case toggles the side-list sign because its blocks are inverse-reversed. -/
noncomputable def canonicalProjectivePostConeRawTreeWordOriginTag_letter
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (tag : CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 slot) :
    CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool := by
  cases tag with
  | source _ t =>
      exact Sum.elim
        (fun origin =>
          let letter := canonicalProjectivePostConeRawContourTermsOriginTag_letter
            hp hp2 slot
            (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)
            (canonicalProjectivePostConeBoundaryPrefixSides
              (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) origin
          (letter.1, !letter.2))
        (fun origin =>
          let letter := canonicalProjectivePostConeRawContourTermsOriginTag_letter
            hp hp2 slot
            (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)
            (canonicalProjectivePostConeBoundarySuffixSides
              (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) origin
          (letter.1, !letter.2)) t
  | target _ t =>
      exact Sum.elim
        (canonicalProjectivePostConeRawContourTermsOriginTag_letter hp hp2 slot
          (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)
          (canonicalProjectivePostConeBoundarySuffixSides
            (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)))
        (canonicalProjectivePostConeRawContourTermsOriginTag_letter hp hp2 slot
          (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)
          (canonicalProjectivePostConeBoundaryPrefixSides
            (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))) t

/-- Interpret a classified side-term origin as its terminal physical dart
and the sign accumulated inside that term. A source child preserves its
child sign; a target child contributes one inverse-reversal flip. -/
noncomputable def canonicalProjectivePostConeRawTermOrigin_endpoint
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (rec : ∀ child : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child →
      CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 child →
        Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
          (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool)
    {s : ProjectivePolygonSide}
    (c : CanonicalProjectivePostConeRawContourTermCase hp hp2 slot s)
    (tag : CanonicalProjectivePostConeRawContourTermPositionTag hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
      c) : Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
        (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool := by
  cases c with
  | one hterm => exact tag.elim
  | finalSource z hsource hz => exact (Sum.inl ⟨z, hz⟩, true)
  | finalTarget z htarget hz => exact (Sum.inr ⟨z, hz⟩, false)
  | deeperSource z child hsource hlabel hdeep =>
      exact rec child hdeep
        (canonicalProjectivePostConeRawTreeWordBySlot_originEquiv hp hp2 child tag)
  | deeperTarget z child htarget hlabel hdeep =>
      let endpoint := rec child hdeep
        (canonicalProjectivePostConeRawTreeWordBySlot_originEquiv hp hp2 child tag)
      exact (endpoint.1, !endpoint.2)

/-- In the deeper-source case, the child-position tag decodes through the
parent term to precisely the recursively decoded child occurrence. -/
theorem canonicalProjectivePostConeRawTermOrigin_endpoint_deeperSource_position
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (rec : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 other →
      Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
        (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool)
    (z : CanonicalProjectiveConeKeptSymbol p)
    (s : ProjectivePolygonSide)
    (hsource :
      (⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p) =
        projectivePolygonPostConeEdgeSource z ∧
      s = projectivePolygonPostConeEdgeSide z ∧
      canonicalProjectiveConePostConeBoundaryTerm p slot.right.state s = FreeGroup.of z)
    (hlabel : canonicalProjectivePostConeTreeSlotLabel hp hp2 child = z)
    (hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child)
    (i : Fin (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).length) :
    canonicalProjectivePostConeRawTermOrigin_endpoint hp hp2 slot rec
      (.deeperSource z child hsource hlabel hdeep) i =
        rec child hdeep
          (canonicalProjectivePostConeRawTreeWordBySlot_originEquiv hp hp2 child i) := rfl

/-- In the deeper-target case, inverse-reversal transports child positions
bijectively and flips only the orientation bit, never the physical dart. -/
theorem canonicalProjectivePostConeRawTermOrigin_endpoint_deeperTarget_position
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (rec : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 other →
      Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
        (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool)
    (z : CanonicalProjectiveConeKeptSymbol p)
    (s : ProjectivePolygonSide)
    (htarget :
      (⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p) =
        projectivePolygonPostConeEdgeTarget z ∧
      s = projectivePolygonPostConeEdgeTargetSide z ∧
      canonicalProjectiveConePostConeBoundaryTerm p slot.right.state s =
        (FreeGroup.of z)⁻¹)
    (hlabel : canonicalProjectivePostConeTreeSlotLabel hp hp2 child = z)
    (hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child)
    (i : Fin (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).length) :
    canonicalProjectivePostConeRawTermOrigin_endpoint hp hp2 slot rec
      (.deeperTarget z child htarget hlabel hdeep) i =
        let endpoint := rec child hdeep
          (canonicalProjectivePostConeRawTreeWordBySlot_originEquiv hp hp2 child i)
        (endpoint.1, !endpoint.2) := rfl

/-- Endpoint interpretation is independent of the selected position tag in a
final-source classifier case. This packages the dependent case transport. -/
theorem canonicalProjectivePostConeRawTermOrigin_endpoint_of_finalSource
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (rec : ∀ child : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child →
      CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 child →
      Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
        (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool)
    {s : ProjectivePolygonSide}
    (z : CanonicalProjectiveConeKeptSymbol p)
    (hsource :
      (⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p) =
        projectivePolygonPostConeEdgeSource z ∧
      s = projectivePolygonPostConeEdgeSide z ∧
      canonicalProjectiveConePostConeBoundaryTerm p slot.right.state s = FreeGroup.of z)
    (hz : ¬ isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z)
    {c : CanonicalProjectivePostConeRawContourTermCase hp hp2 slot s}
    (hc : c = .finalSource z hsource hz)
    (tag : CanonicalProjectivePostConeRawContourTermPositionTag hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) c) :
    canonicalProjectivePostConeRawTermOrigin_endpoint hp hp2 slot rec
      c tag = (Sum.inl ⟨z, hz⟩, true) := by
  cases c with
  | one hone => cases hc
  | finalSource z' hsource' hz' => cases hc; rfl
  | finalTarget z' htarget' hz' => cases hc
  | deeperSource z' child hsource' hlabel hdeep => cases hc
  | deeperTarget z' child htarget' hlabel hdeep => cases hc

/-- The target-oriented final case has the analogous constant endpoint. -/
theorem canonicalProjectivePostConeRawTermOrigin_endpoint_of_finalTarget
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (rec : ∀ child : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child →
      CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 child →
      Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
        (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool)
    {s : ProjectivePolygonSide}
    (z : CanonicalProjectiveConeKeptSymbol p)
    (htarget :
      (⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p) =
        projectivePolygonPostConeEdgeTarget z ∧
      s = projectivePolygonPostConeEdgeTargetSide z ∧
      canonicalProjectiveConePostConeBoundaryTerm p slot.right.state s =
        (FreeGroup.of z)⁻¹)
    (hz : ¬ isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z)
    {c : CanonicalProjectivePostConeRawContourTermCase hp hp2 slot s}
    (hc : c = .finalTarget z htarget hz)
    (tag : CanonicalProjectivePostConeRawContourTermPositionTag hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) c) :
    canonicalProjectivePostConeRawTermOrigin_endpoint hp hp2 slot rec
      c tag = (Sum.inr ⟨z, hz⟩, false) := by
  cases c with
  | one hone => cases hc
  | finalSource z' hsource' hz' => cases hc
  | finalTarget z' htarget' hz' => cases hc; rfl
  | deeperSource z' child hsource' hlabel hdeep => cases hc
  | deeperTarget z' child htarget' hlabel hdeep => cases hc

/-- Interpret a side-origin tag. The pivot tag is empty; otherwise the
selected classifier recursively resolves it to a physical endpoint. -/
noncomputable def canonicalProjectivePostConeRawSideOrigin_endpoint
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (rec : ∀ child : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child →
      CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 child →
        Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
          (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool)
    (s : ProjectivePolygonSide)
    (tag : CanonicalProjectivePostConeRawContourSideOriginTag hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) s) :
    Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
      (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool := by
  classical
  by_cases hs : s = canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot
  · have htag : Empty := by
      simpa [CanonicalProjectivePostConeRawContourSideOriginTag, hs] using tag
    exact htag.elim
  · let i := (canonicalProjectivePostConeRawContourSide_positionEquiv hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) s).symm tag
    exact canonicalProjectivePostConeRawTermOrigin_endpoint hp hp2 slot rec
      (canonicalProjectivePostConeRawContourTermCase hp hp2 slot s hs)
      (canonicalProjectivePostConeRawContourTerm_positionEquiv hp hp2 slot
        (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) s hs i)

/-- Transport a term-origin decoder across an identified deeper-source case.
The child position is recovered by transporting the dependent tag along the
classifier equality. -/
theorem canonicalProjectivePostConeRawTermOrigin_endpoint_eq_rec_of_deeperSource
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (rec : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 other →
      Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
        (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool)
    {s : ProjectivePolygonSide}
    (z : CanonicalProjectiveConeKeptSymbol p)
    (hsource :
      (⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p) =
        projectivePolygonPostConeEdgeSource z ∧
      s = projectivePolygonPostConeEdgeSide z ∧
      canonicalProjectiveConePostConeBoundaryTerm p slot.right.state s =
        FreeGroup.of z)
    (hlabel : canonicalProjectivePostConeTreeSlotLabel hp hp2 child = z)
    (hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child)
    (c : CanonicalProjectivePostConeRawContourTermCase hp hp2 slot s)
    (hcase : c = .deeperSource z child hsource hlabel hdeep)
    (tag : CanonicalProjectivePostConeRawContourTermPositionTag hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) c) :
    canonicalProjectivePostConeRawTermOrigin_endpoint hp hp2 slot rec c tag =
      rec child hdeep
        (canonicalProjectivePostConeRawTreeWordBySlot_originEquiv hp hp2 child
          (Eq.mp (congrArg
            (CanonicalProjectivePostConeRawContourTermPositionTag hp hp2 slot
              (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other))
            hcase) tag)) := by
  cases c with
  | one hterm => exact tag.elim
  | finalSource z' hsource' hz' => cases hcase
  | finalTarget z' htarget' hz' => cases hcase
  | deeperSource z' other hsource' hlabel' hdeep' => cases hcase; rfl
  | deeperTarget z' other htarget' hlabel' hdeep' => cases hcase

/-- The deeper-target endpoint equation is the same recursive physical dart
with its orientation bit toggled by inverse-reversal. -/
theorem canonicalProjectivePostConeRawTermOrigin_endpoint_eq_flip_rec_of_deeperTarget
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (rec : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 other →
      Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
        (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool)
    {s : ProjectivePolygonSide}
    (z : CanonicalProjectiveConeKeptSymbol p)
    (htarget :
      (⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p) =
        projectivePolygonPostConeEdgeTarget z ∧
      s = projectivePolygonPostConeEdgeTargetSide z ∧
      canonicalProjectiveConePostConeBoundaryTerm p slot.right.state s =
        (FreeGroup.of z)⁻¹)
    (hlabel : canonicalProjectivePostConeTreeSlotLabel hp hp2 child = z)
    (hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child)
    (c : CanonicalProjectivePostConeRawContourTermCase hp hp2 slot s)
    (hcase : c = .deeperTarget z child htarget hlabel hdeep)
    (tag : CanonicalProjectivePostConeRawContourTermPositionTag hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) c) :
    canonicalProjectivePostConeRawTermOrigin_endpoint hp hp2 slot rec c tag =
      (fun endpoint => (endpoint.1, !endpoint.2))
        (rec child hdeep
          (canonicalProjectivePostConeRawTreeWordBySlot_originEquiv hp hp2 child
            (Eq.mp (congrArg
              (CanonicalProjectivePostConeRawContourTermPositionTag hp hp2 slot
                (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other))
              hcase) tag))) := by
  cases c with
  | one hterm => exact tag.elim
  | finalSource z' hsource' hz' => cases hcase
  | finalTarget z' htarget' hz' => cases hcase
  | deeperSource z' other hsource' hlabel' hdeep' => cases hcase
  | deeperTarget z' other htarget' hlabel' hdeep' => cases hcase; rfl

theorem BoundaryWords.Internal.eq_mp_mpr_cancel {α β : Sort u} (h : α = β) (x : β) :
    Eq.mp h (Eq.mpr h x) = x := by
  cases h
  rfl

/-- Interpret the nested side-list origin tags without changing their
occurrence identity. -/
noncomputable def canonicalProjectivePostConeRawTermsOrigin_endpoint
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (rec : ∀ child : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child →
      CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 child →
        Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
          (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool) :
    (sides : List ProjectivePolygonSide) →
      CanonicalProjectivePostConeRawContourTermsOriginTag hp hp2 slot
        (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
        sides → Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
          (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool
  | [], tag => tag.elim
  | s :: _sides, Sum.inl tag =>
      canonicalProjectivePostConeRawSideOrigin_endpoint hp hp2 slot rec s tag
  | _s :: sides, Sum.inr tag =>
      canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot rec sides tag

/-- Extract the chosen side occurrence from a nested ordered-list origin.
The dependent side tag retains its position inside that side's raw term. -/
noncomputable def canonicalProjectivePostConeRawTermsOrigin_selectedSide
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ child : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool)) :
    (sides : List ProjectivePolygonSide) →
      CanonicalProjectivePostConeRawContourTermsOriginTag hp hp2 slot ih sides →
        Σ s : ProjectivePolygonSide,
          CanonicalProjectivePostConeRawContourSideOriginTag hp hp2 slot ih s
  | [], tag => tag.elim
  | s :: _sides, Sum.inl tag => ⟨s, tag⟩
  | _s :: sides, Sum.inr tag =>
      canonicalProjectivePostConeRawTermsOrigin_selectedSide hp hp2 slot ih sides tag

/-- The selected side of a nested origin tag belongs to the side list. -/
theorem canonicalProjectivePostConeRawTermsOrigin_selectedSide_mem
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ child : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool))
    (sides : List ProjectivePolygonSide)
    (tag : CanonicalProjectivePostConeRawContourTermsOriginTag hp hp2 slot ih sides) :
    (canonicalProjectivePostConeRawTermsOrigin_selectedSide hp hp2 slot ih
      sides tag).1 ∈ sides := by
  induction sides with
  | nil => cases tag
  | cons s sides ihs =>
      cases tag with
      | inl sideTag => simp [canonicalProjectivePostConeRawTermsOrigin_selectedSide]
      | inr tailTag =>
          simp only [canonicalProjectivePostConeRawTermsOrigin_selectedSide]
          exact List.mem_cons_of_mem s (ihs tailTag)

/-- In a duplicate-free side list, the selected side occurrence and its
dependent local tag determine the full nested-list origin. -/
theorem canonicalProjectivePostConeRawTermsOrigin_eq_of_selectedSide_eq
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ child : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool))
    (sides : List ProjectivePolygonSide) (hnodup : sides.Nodup)
    (tag tag' : CanonicalProjectivePostConeRawContourTermsOriginTag hp hp2 slot ih sides)
    (hselected :
      canonicalProjectivePostConeRawTermsOrigin_selectedSide hp hp2 slot ih sides tag =
        canonicalProjectivePostConeRawTermsOrigin_selectedSide hp hp2 slot ih sides tag') :
    tag = tag' := by
  induction sides with
  | nil => cases tag
  | cons s sides ihs =>
      cases tag with
      | inl headTag =>
          cases tag' with
          | inl headTag' =>
              change (⟨s, headTag⟩ : Σ t,
                CanonicalProjectivePostConeRawContourSideOriginTag hp hp2 slot ih t) =
                ⟨s, headTag'⟩ at hselected
              cases hselected
              rfl
          | inr tailTag' =>
              simp only [canonicalProjectivePostConeRawTermsOrigin_selectedSide] at hselected
              have hside := congrArg Sigma.fst hselected
              have hmem : (canonicalProjectivePostConeRawTermsOrigin_selectedSide
                  hp hp2 slot ih sides tailTag').1 ∈ sides :=
                canonicalProjectivePostConeRawTermsOrigin_selectedSide_mem
                  hp hp2 slot ih sides tailTag'
              have hside' : s = (canonicalProjectivePostConeRawTermsOrigin_selectedSide
                  hp hp2 slot ih sides tailTag').1 := by
                simpa using hside
              have hs : s ∈ sides := by
                rw [hside']
                exact hmem
              exact False.elim ((List.nodup_cons.mp hnodup).1 hs)
      | inr tailTag =>
          cases tag' with
          | inl headTag' =>
              simp only [canonicalProjectivePostConeRawTermsOrigin_selectedSide] at hselected
              have hside := congrArg Sigma.fst hselected
              have hmem : (canonicalProjectivePostConeRawTermsOrigin_selectedSide
                  hp hp2 slot ih sides tailTag).1 ∈ sides :=
                canonicalProjectivePostConeRawTermsOrigin_selectedSide_mem
                  hp hp2 slot ih sides tailTag
              have hside' : (canonicalProjectivePostConeRawTermsOrigin_selectedSide
                  hp hp2 slot ih sides tailTag).1 = s := by
                simpa using hside
              have hs : s ∈ sides := by
                rw [hside'] at hmem
                exact hmem
              exact False.elim ((List.nodup_cons.mp hnodup).1 hs)
          | inr tailTag' =>
              apply congrArg Sum.inr
              exact ihs (List.nodup_cons.mp hnodup).2 tailTag tailTag'
                (by simpa [canonicalProjectivePostConeRawTermsOrigin_selectedSide]
                  using hselected)

/-- The nested-list letter decoder is the letter decoder of its selected
side and dependent local origin tag. -/
theorem canonicalProjectivePostConeRawTermsOriginTag_letter_eq_selectedSide
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ child : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool))
    (sides : List ProjectivePolygonSide)
    (tag : CanonicalProjectivePostConeRawContourTermsOriginTag hp hp2 slot ih sides) :
    canonicalProjectivePostConeRawContourTermsOriginTag_letter hp hp2 slot ih sides tag =
      canonicalProjectivePostConeRawContourSideOriginTag_letter hp hp2 slot ih
        (canonicalProjectivePostConeRawTermsOrigin_selectedSide
          hp hp2 slot ih sides tag).1
        (canonicalProjectivePostConeRawTermsOrigin_selectedSide
          hp hp2 slot ih sides tag).2 := by
  induction sides with
  | nil => exact tag.elim
  | cons s sides ihs =>
      cases tag with
      | inl sideTag => rfl
      | inr tailTag => exact ihs tailTag

/-- A valid side-list origin can never select the pivot, whose local origin
type is empty. -/
theorem canonicalProjectivePostConeRawTermsOrigin_selectedSide_ne_pivot
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ child : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool))
    (sides : List ProjectivePolygonSide)
    (tag : CanonicalProjectivePostConeRawContourTermsOriginTag hp hp2 slot ih sides) :
    (canonicalProjectivePostConeRawTermsOrigin_selectedSide hp hp2 slot ih
      sides tag).1 ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot := by
  induction sides with
  | nil => exact tag.elim
  | cons s sides ihs =>
      cases tag with
      | inl sideTag =>
          intro hs
          change s = canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot at hs
          subst s
          have hempty : Empty := by
            simpa [CanonicalProjectivePostConeRawContourSideOriginTag] using sideTag
          exact hempty.elim
      | inr tailTag => exact ihs tailTag

/-- The ordered-list endpoint decoder is exactly the endpoint decoder of
the selected side occurrence; list offsets change provenance, not geometry. -/
theorem canonicalProjectivePostConeRawTermsOrigin_endpoint_eq_selectedSide
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (rec : ∀ child : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child →
      CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 child →
      Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
        (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool)
    (sides : List ProjectivePolygonSide)
    (tag : CanonicalProjectivePostConeRawContourTermsOriginTag hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
      sides) :
    canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot rec sides tag =
      canonicalProjectivePostConeRawSideOrigin_endpoint hp hp2 slot rec
        (canonicalProjectivePostConeRawTermsOrigin_selectedSide hp hp2 slot
          (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
          sides tag).1
        (canonicalProjectivePostConeRawTermsOrigin_selectedSide hp hp2 slot
          (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
          sides tag).2 := by
  induction sides with
  | nil => exact tag.elim
  | cons s sides ih =>
      cases tag with
      | inl sideTag => rfl
      | inr tailTag => exact ih tailTag

/-- Lifting a side origin into an ordered list preserves the exact selected
side occurrence and its dependent local tag, not merely its endpoint. -/
theorem canonicalProjectivePostConeRawTermsOrigin_exists_of_mem_selectedSide
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ child : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool))
    (sides : List ProjectivePolygonSide) (s : ProjectivePolygonSide)
    (hs : s ∈ sides)
    (tag : CanonicalProjectivePostConeRawContourSideOriginTag hp hp2 slot ih s) :
    ∃ listTag : CanonicalProjectivePostConeRawContourTermsOriginTag hp hp2 slot ih sides,
      canonicalProjectivePostConeRawTermsOrigin_selectedSide hp hp2 slot ih sides listTag =
        ⟨s, tag⟩ := by
  induction sides generalizing s tag with
  | nil => cases hs
  | cons head tail ihs =>
      simp only [List.mem_cons] at hs
      rcases hs with hhead | htail
      · subst head
        exact ⟨Sum.inl tag, rfl⟩
      · obtain ⟨tailTag, htailTag⟩ := ihs s htail tag
        refine ⟨Sum.inr tailTag, ?_⟩
        simpa [canonicalProjectivePostConeRawTermsOrigin_selectedSide] using htailTag

/-- A local term position inside a selected side has a corresponding position
in the concatenated side-list word whose nested origin tag retains that exact
side and local origin tag. -/
theorem canonicalProjectivePostConeRawContourTerms_exists_position_origin_of_mem
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ child : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool))
    (sides : List ProjectivePolygonSide) (s : ProjectivePolygonSide)
    (hs : s ∈ sides)
    (i : Fin (canonicalProjectivePostConeRawContourTerm hp hp2 slot ih s).length) :
    ∃ listTag : CanonicalProjectivePostConeRawContourTermsOriginTag hp hp2 slot ih sides,
      canonicalProjectivePostConeRawTermsOrigin_selectedSide hp hp2 slot ih sides
        listTag = ⟨s,
          canonicalProjectivePostConeRawContourSide_positionEquiv hp hp2 slot ih s i⟩ ∧
      (canonicalProjectivePostConeRawContourTerms hp hp2 slot ih sides).get
        ((canonicalProjectivePostConeRawContourTerms_originEquiv
          hp hp2 slot ih sides).symm listTag) =
        (canonicalProjectivePostConeRawContourTerm hp hp2 slot ih s).get i := by
  let sideTag := canonicalProjectivePostConeRawContourSide_positionEquiv
    hp hp2 slot ih s i
  obtain ⟨listTag, hselected⟩ :=
    canonicalProjectivePostConeRawTermsOrigin_exists_of_mem_selectedSide
      hp hp2 slot ih sides s hs sideTag
  refine ⟨listTag, hselected, ?_⟩
  have hget := canonicalProjectivePostConeRawContourTerms_originEquiv_get
    hp hp2 slot ih sides listTag
  have hletter :
      canonicalProjectivePostConeRawContourTermsOriginTag_letter
        hp hp2 slot ih sides listTag =
      canonicalProjectivePostConeRawContourSideOriginTag_letter
        hp hp2 slot ih s sideTag := by
    rw [canonicalProjectivePostConeRawTermsOriginTag_letter_eq_selectedSide,
      hselected]
  have hlocal :
      canonicalProjectivePostConeRawContourSideOriginTag_letter
        hp hp2 slot ih s sideTag =
      (canonicalProjectivePostConeRawContourTerm hp hp2 slot ih s).get i := by
    simp [sideTag, canonicalProjectivePostConeRawContourSideOriginTag_letter]
  rw [hget, hletter, hlocal]

/-- Any side-origin tag occurring in a side list lifts to a tag for the
concatenated list, preserving its decoded physical endpoint occurrence. -/
theorem canonicalProjectivePostConeRawTermsOrigin_endpoint_exists_of_mem
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (rec : ∀ child : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child →
      CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 child →
      Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
        (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool)
    (sides : List ProjectivePolygonSide) (s : ProjectivePolygonSide)
    (hs : s ∈ sides)
    (tag : CanonicalProjectivePostConeRawContourSideOriginTag hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) s) :
    ∃ listTag : CanonicalProjectivePostConeRawContourTermsOriginTag hp hp2 slot
        (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) sides,
      canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot rec sides listTag =
        canonicalProjectivePostConeRawSideOrigin_endpoint hp hp2 slot rec s tag := by
  induction sides generalizing s tag with
  | nil => cases hs
  | cons head tail ih =>
      simp only [List.mem_cons] at hs
      rcases hs with hhead | htail
      · subst head
        exact ⟨Sum.inl tag, rfl⟩
      · obtain ⟨tailTag, htailTag⟩ := ih s htail tag
        exact ⟨Sum.inr tailTag, by
          simpa [canonicalProjectivePostConeRawTermsOrigin_endpoint] using htailTag⟩

/-- Interpret a complete slot-word origin. In the source-oriented splice,
both blocks are inverse-reversed; the target-oriented splice preserves them.
The resulting Boolean must eventually agree with the root-path parity. -/
noncomputable def canonicalProjectivePostConeRawTreeWordOrigin_endpoint_step
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (rec : ∀ child : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child →
      CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 child →
        Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
          (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool)
    (tag : CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 slot) :
    Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
      (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool := by
  cases tag with
  | source hsource blocks =>
    exact Sum.elim
        (fun origin =>
          let endpoint := canonicalProjectivePostConeRawTermsOrigin_endpoint
            hp hp2 slot rec
            (canonicalProjectivePostConeBoundaryPrefixSides
              (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) origin
          (endpoint.1, !endpoint.2))
        (fun origin =>
          let endpoint := canonicalProjectivePostConeRawTermsOrigin_endpoint
            hp hp2 slot rec
            (canonicalProjectivePostConeBoundarySuffixSides
              (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) origin
          (endpoint.1, !endpoint.2)) blocks
  | target htarget blocks =>
      exact Sum.elim
        (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot rec
          (canonicalProjectivePostConeBoundarySuffixSides
            (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)))
        (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot rec
          (canonicalProjectivePostConeBoundaryPrefixSides
            (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))) blocks

/-- Well-founded recursive interpretation of an origin tag as its physical
endpoint occurrence and accumulated sign. -/
noncomputable def canonicalProjectivePostConeRawTreeWordOrigin_endpoint
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (tag : CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 slot) :
    Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
      (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool :=
  (canonicalProjectivePostConeDirectTreeDependencyWellFounded hp hp2).fix
    (fun slot rec tag =>
      canonicalProjectivePostConeRawTreeWordOrigin_endpoint_step hp hp2 slot rec tag)
    slot tag

/-- Any side-origin endpoint can be represented by a complete slot-word
origin: first lift through its ordered prefix/suffix list, then select the
corresponding block of the source- or target-oriented splice. -/
theorem canonicalProjectivePostConeRawTreeWordOrigin_exists_of_sideOrigin
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (s : ProjectivePolygonSide)
    (sideTag : CanonicalProjectivePostConeRawContourSideOriginTag hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) s)
    (endpoint : Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
      (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool)
    (hside : (canonicalProjectivePostConeRawSideOrigin_endpoint hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 child)
      s sideTag).1 = endpoint.1) :
    ∃ tag : CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 slot,
      (canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 slot tag).1 =
        endpoint.1 := by
  classical
  let recEndpoint := fun child
      (_hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child) =>
      canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 child
  have hnotPivot : s ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot := by
    intro hpivot
    have htag : Empty := by
      simpa [CanonicalProjectivePostConeRawContourSideOriginTag, hpivot] using sideTag
    exact htag.elim
  rcases canonicalProjectivePostConeBoundarySide_mem_prefix_or_suffix s
      (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot) hnotPivot
    with hprefix | hsuffix
  · obtain ⟨listTag, hlist⟩ :=
      canonicalProjectivePostConeRawTermsOrigin_endpoint_exists_of_mem
        hp hp2 slot recEndpoint
        (canonicalProjectivePostConeBoundaryPrefixSides
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
        s hprefix sideTag
    by_cases hsource : projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) = slot.right
    · refine ⟨.source hsource.symm (Sum.inl listTag), ?_⟩
      unfold canonicalProjectivePostConeRawTreeWordOrigin_endpoint
      rw [WellFounded.fix_eq]
      change (canonicalProjectivePostConeRawTreeWordOrigin_endpoint_step
        hp hp2 slot recEndpoint (.source hsource.symm (Sum.inl listTag))).1 = endpoint.1
      change (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot
        recEndpoint (canonicalProjectivePostConeBoundaryPrefixSides
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
        listTag).1 = endpoint.1
      exact (congrArg Prod.fst hlist).trans hside
    · refine ⟨.target (by intro h; exact hsource h.symm) (Sum.inr listTag), ?_⟩
      unfold canonicalProjectivePostConeRawTreeWordOrigin_endpoint
      rw [WellFounded.fix_eq]
      change (canonicalProjectivePostConeRawTreeWordOrigin_endpoint_step
        hp hp2 slot recEndpoint
        (.target (by intro h; exact hsource h.symm) (Sum.inr listTag))).1 = endpoint.1
      change (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot
        recEndpoint (canonicalProjectivePostConeBoundaryPrefixSides
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
        listTag).1 = endpoint.1
      exact (congrArg Prod.fst hlist).trans hside
  · obtain ⟨listTag, hlist⟩ :=
      canonicalProjectivePostConeRawTermsOrigin_endpoint_exists_of_mem
        hp hp2 slot recEndpoint
        (canonicalProjectivePostConeBoundarySuffixSides
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
        s hsuffix sideTag
    by_cases hsource : projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) = slot.right
    · refine ⟨.source hsource.symm (Sum.inr listTag), ?_⟩
      unfold canonicalProjectivePostConeRawTreeWordOrigin_endpoint
      rw [WellFounded.fix_eq]
      change (canonicalProjectivePostConeRawTreeWordOrigin_endpoint_step
        hp hp2 slot recEndpoint (.source hsource.symm (Sum.inr listTag))).1 = endpoint.1
      change (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot
        recEndpoint (canonicalProjectivePostConeBoundarySuffixSides
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
        listTag).1 = endpoint.1
      exact (congrArg Prod.fst hlist).trans hside
    · refine ⟨.target (by intro h; exact hsource h.symm) (Sum.inl listTag), ?_⟩
      unfold canonicalProjectivePostConeRawTreeWordOrigin_endpoint
      rw [WellFounded.fix_eq]
      change (canonicalProjectivePostConeRawTreeWordOrigin_endpoint_step
        hp hp2 slot recEndpoint
        (.target (by intro h; exact hsource h.symm) (Sum.inl listTag))).1 = endpoint.1
      change (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot
        recEndpoint (canonicalProjectivePostConeBoundarySuffixSides
          (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
        listTag).1 = endpoint.1
      exact (congrArg Prod.fst hlist).trans hside

/-- Decode every raw slot-word position to a physical endpoint occurrence.
This is the inverse-provenance map whose injectivity is the remaining local
exhaustion lemma. -/
noncomputable def canonicalProjectivePostConeRawTreeWordPosition_endpoint
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (i : Fin (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot).length) :
    Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
      (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool :=
  canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 slot
    ((canonicalProjectivePostConeRawTreeWordBySlot_originEquiv hp hp2 slot) i)

/-- Read the signed letter represented by an endpoint/sign pair. -/
def canonicalProjectivePostConeEndpointSignedLetter
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (x : Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
      (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool) :=
  (x.1.elim id id, x.2)

/-- The target split is the analogous length transport followed by the
suffix/prefix append split. -/
theorem canonicalProjectivePostConeRawTreeWordBySlot_positionSplit_of_target_eq
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hsource : slot.right ≠ projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)) :
    canonicalProjectivePostConeRawTreeWordBySlot_positionSplit_of_target
        hp hp2 slot hsource =
      (finCongr (congrArg List.length
        (canonicalProjectivePostConeRawTreeWordBySlot_eq_splice_of_target
          hp hp2 slot hsource))).trans
        (canonicalProjectivePostConeRawAppendPositionSplit
          (canonicalProjectivePostConeRawContourSuffix hp hp2 slot
            (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other))
          (canonicalProjectivePostConeRawContourPrefix hp hp2 slot
            (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other))) := by
  rfl

/-- The inverse target split's left tag is exactly the casted suffix
position. -/
theorem canonicalProjectivePostConeRawTreeWordBySlot_positionSplit_of_target_symm_inl
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hsource : slot.right ≠ projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot))
    (i : Fin (canonicalProjectivePostConeRawContourSuffix hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)).length) :
    (canonicalProjectivePostConeRawTreeWordBySlot_positionSplit_of_target
      hp hp2 slot hsource).symm (Sum.inl i) =
      Fin.cast (congrArg List.length
        (canonicalProjectivePostConeRawTreeWordBySlot_eq_splice_of_target
          hp hp2 slot hsource).symm)
        ((canonicalProjectivePostConeRawAppendPositionSplit
          (canonicalProjectivePostConeRawContourSuffix hp hp2 slot
            (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other))
          (canonicalProjectivePostConeRawContourPrefix hp hp2 slot
            (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other))).symm
          (Sum.inl i)) := by
  rw [canonicalProjectivePostConeRawTreeWordBySlot_positionSplit_of_target_eq]
  rfl

/-- The target split's first block recovers the exact suffix element. -/
theorem canonicalProjectivePostConeRawTreeWordBySlot_get_target_suffix
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hsource : slot.right ≠ projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot))
    (i : Fin (canonicalProjectivePostConeRawContourSuffix hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)).length) :
    (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot).get
      ((canonicalProjectivePostConeRawTreeWordBySlot_positionSplit_of_target
        hp hp2 slot hsource).symm (Sum.inl i)) =
      (canonicalProjectivePostConeRawContourSuffix hp hp2 slot
        (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)).get i := by
  rw [canonicalProjectivePostConeRawTreeWordBySlot_positionSplit_of_target_symm_inl]
  exact canonicalProjectivePostConeRaw_get_eq_appendSplit_left
    (canonicalProjectivePostConeRawTreeWordBySlot_eq_splice_of_target
      hp hp2 slot hsource) i

/-- The inverse target split's right tag is exactly the casted prefix
position. -/
theorem canonicalProjectivePostConeRawTreeWordBySlot_positionSplit_of_target_symm_inr
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hsource : slot.right ≠ projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot))
    (i : Fin (canonicalProjectivePostConeRawContourPrefix hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)).length) :
    (canonicalProjectivePostConeRawTreeWordBySlot_positionSplit_of_target
      hp hp2 slot hsource).symm (Sum.inr i) =
      Fin.cast (congrArg List.length
        (canonicalProjectivePostConeRawTreeWordBySlot_eq_splice_of_target
          hp hp2 slot hsource).symm)
        ((canonicalProjectivePostConeRawAppendPositionSplit
          (canonicalProjectivePostConeRawContourSuffix hp hp2 slot
            (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other))
          (canonicalProjectivePostConeRawContourPrefix hp hp2 slot
            (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other))).symm
          (Sum.inr i)) := by
  rw [canonicalProjectivePostConeRawTreeWordBySlot_positionSplit_of_target_eq]
  rfl

/-- The target split's second block recovers the exact prefix element. -/
theorem canonicalProjectivePostConeRawTreeWordBySlot_get_target_prefix
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hsource : slot.right ≠ projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot))
    (i : Fin (canonicalProjectivePostConeRawContourPrefix hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)).length) :
    (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot).get
      ((canonicalProjectivePostConeRawTreeWordBySlot_positionSplit_of_target
        hp hp2 slot hsource).symm (Sum.inr i)) =
      (canonicalProjectivePostConeRawContourPrefix hp hp2 slot
        (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)).get i := by
  rw [canonicalProjectivePostConeRawTreeWordBySlot_positionSplit_of_target_symm_inr]
  exact canonicalProjectivePostConeRaw_get_eq_appendSplit_right
    (canonicalProjectivePostConeRawTreeWordBySlot_eq_splice_of_target
      hp hp2 slot hsource) i

/-- Decoding a complete-slot origin tag reads the exact signed generator in
the recursive slot word. -/
theorem canonicalProjectivePostConeRawTreeWordBySlot_originEquiv_get
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (tag : CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 slot) :
    (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot).get
      ((canonicalProjectivePostConeRawTreeWordBySlot_originEquiv
        hp hp2 slot).symm tag) =
      canonicalProjectivePostConeRawTreeWordOriginTag_letter hp hp2 slot tag := by
  classical
  cases tag with
  | source hs t =>
      by_cases horient : projectivePolygonPostConeEdgeSource
          (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) = slot.right
      · cases t with
        | inl prefixTag =>
            simp only [canonicalProjectivePostConeRawTreeWordBySlot_originEquiv]
            dsimp only [Equiv.symm]
            split_ifs; simp_all
            change (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot).get
              ((canonicalProjectivePostConeRawTreeWordBySlot_positionSplit_of_source
                hp hp2 slot hs).symm
                (Sum.inl ((canonicalProjectivePostConeRawContourPrefix_invRev_originEquiv
                  hp hp2 slot).symm prefixTag))) = _
            rw [canonicalProjectivePostConeRawTreeWordBySlot_get_source_prefix]
            simp only [canonicalProjectivePostConeRawTreeWordOriginTag_letter]
            let sides := canonicalProjectivePostConeBoundaryPrefixSides
              (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)
            let hrev := congrArg FreeGroup.invRev
              (canonicalProjectivePostConeRawContourPrefix_eq_terms hp hp2 slot)
            have hpos :
                (canonicalProjectivePostConeRawContourPrefix_invRev_originEquiv
                  hp hp2 slot).symm prefixTag =
                Fin.cast (congrArg List.length hrev.symm)
                  ((canonicalProjectivePostConeRawContourTerms_invRev_originEquiv
                    hp hp2 slot sides).symm prefixTag) := by
              rfl
            rw [hpos]
            exact (get_cast_eq_of_eq hrev.symm _).symm.trans
              (canonicalProjectivePostConeRawContourTerms_invRev_originEquiv_get
                hp hp2 slot sides prefixTag)
        | inr suffixTag =>
            simp only [canonicalProjectivePostConeRawTreeWordBySlot_originEquiv]
            dsimp only [Equiv.symm]
            split_ifs; simp_all
            change (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot).get
              ((canonicalProjectivePostConeRawTreeWordBySlot_positionSplit_of_source
                hp hp2 slot hs).symm
                (Sum.inr ((canonicalProjectivePostConeRawContourSuffix_invRev_originEquiv
                  hp hp2 slot).symm suffixTag))) = _
            rw [canonicalProjectivePostConeRawTreeWordBySlot_get_source_suffix]
            simp only [canonicalProjectivePostConeRawTreeWordOriginTag_letter]
            let sides := canonicalProjectivePostConeBoundarySuffixSides
              (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)
            let hrev := congrArg FreeGroup.invRev
              (canonicalProjectivePostConeRawContourSuffix_eq_terms hp hp2 slot)
            have hpos :
                (canonicalProjectivePostConeRawContourSuffix_invRev_originEquiv
                  hp hp2 slot).symm suffixTag =
                Fin.cast (congrArg List.length hrev.symm)
                  ((canonicalProjectivePostConeRawContourTerms_invRev_originEquiv
                    hp hp2 slot sides).symm suffixTag) := by
              rfl
            rw [hpos]
            exact (get_cast_eq_of_eq hrev.symm _).symm.trans
              (canonicalProjectivePostConeRawContourTerms_invRev_originEquiv_get
                hp hp2 slot sides suffixTag)
      · exact False.elim (horient hs.symm)
  | target ht t =>
      by_cases horient : projectivePolygonPostConeEdgeSource
          (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) = slot.right
      · exact False.elim (ht horient.symm)
      · cases t with
        | inl suffixTag =>
            simp only [canonicalProjectivePostConeRawTreeWordBySlot_originEquiv]
            dsimp only [Equiv.symm]
            split_ifs; simp_all
            change (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot).get
              ((canonicalProjectivePostConeRawTreeWordBySlot_positionSplit_of_target
                hp hp2 slot ht).symm
                (Sum.inl ((canonicalProjectivePostConeRawContourSuffix_originEquiv
                  hp hp2 slot).symm suffixTag))) = _
            rw [canonicalProjectivePostConeRawTreeWordBySlot_get_target_suffix]
            simp only [canonicalProjectivePostConeRawTreeWordOriginTag_letter]
            let sides := canonicalProjectivePostConeBoundarySuffixSides
              (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)
            have hword := canonicalProjectivePostConeRawContourSuffix_eq_terms hp hp2 slot
            have hpos :
                (canonicalProjectivePostConeRawContourSuffix_originEquiv
                  hp hp2 slot).symm suffixTag =
                Fin.cast (congrArg List.length hword.symm)
                  ((canonicalProjectivePostConeRawContourTerms_originEquiv
                    hp hp2 slot
                    (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)
                    sides).symm suffixTag) := by
              rfl
            rw [hpos]
            exact (get_cast_eq_of_eq hword.symm _).symm.trans
              (canonicalProjectivePostConeRawContourTerms_originEquiv_get
                hp hp2 slot
                (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)
                sides suffixTag)
        | inr prefixTag =>
            simp only [canonicalProjectivePostConeRawTreeWordBySlot_originEquiv]
            dsimp only [Equiv.symm]
            split_ifs; simp_all
            change (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot).get
              ((canonicalProjectivePostConeRawTreeWordBySlot_positionSplit_of_target
                hp hp2 slot ht).symm
                (Sum.inr ((canonicalProjectivePostConeRawContourPrefix_originEquiv
                  hp hp2 slot).symm prefixTag))) = _
            rw [canonicalProjectivePostConeRawTreeWordBySlot_get_target_prefix]
            simp only [canonicalProjectivePostConeRawTreeWordOriginTag_letter]
            let sides := canonicalProjectivePostConeBoundaryPrefixSides
              (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)
            have hword := canonicalProjectivePostConeRawContourPrefix_eq_terms hp hp2 slot
            have hpos :
                (canonicalProjectivePostConeRawContourPrefix_originEquiv
                  hp hp2 slot).symm prefixTag =
                Fin.cast (congrArg List.length hword.symm)
                  ((canonicalProjectivePostConeRawContourTerms_originEquiv
                    hp hp2 slot
                    (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)
                    sides).symm prefixTag) := by
              rfl
            rw [hpos]
            exact (get_cast_eq_of_eq hword.symm _).symm.trans
              (canonicalProjectivePostConeRawContourTerms_originEquiv_get
                hp hp2 slot
                (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)
                sides prefixTag)

/-- At a classified side term, recursive origin decoding preserves the exact
letter; only deeper-target substitution toggles the sign. -/
theorem canonicalProjectivePostConeRawTermOrigin_endpoint_letter
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (rec : ∀ child : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child →
      CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 child →
        Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
          (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool)
    (hrec : ∀ child hdeep tag,
      canonicalProjectivePostConeRawTreeWordOriginTag_letter hp hp2 child tag =
        canonicalProjectivePostConeEndpointSignedLetter hp hp2
          (rec child hdeep tag))
    {s : ProjectivePolygonSide}
    (c : CanonicalProjectivePostConeRawContourTermCase hp hp2 slot s)
    (tag : CanonicalProjectivePostConeRawContourTermPositionTag hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
      c) :
    canonicalProjectivePostConeRawContourTermPositionTag_letter hp hp2 slot
        (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) c tag =
      canonicalProjectivePostConeEndpointSignedLetter hp hp2
        (canonicalProjectivePostConeRawTermOrigin_endpoint hp hp2 slot rec c tag) := by
  cases c with
  | one hterm => exact tag.elim
  | finalSource z hsource hz => rfl
  | finalTarget z htarget hz => rfl
  | deeperSource z child hsource hlabel hdeep =>
      have hget := canonicalProjectivePostConeRawTreeWordBySlot_originEquiv_get
        hp hp2 child (canonicalProjectivePostConeRawTreeWordBySlot_originEquiv
          hp hp2 child tag)
      have hi : (canonicalProjectivePostConeRawTreeWordBySlot_originEquiv
          hp hp2 child).symm
          (canonicalProjectivePostConeRawTreeWordBySlot_originEquiv hp hp2 child tag) = tag :=
        Equiv.symm_apply_apply _ _
      rw [hi] at hget
      have hget' : (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get tag =
          canonicalProjectivePostConeRawTreeWordOriginTag_letter hp hp2 child
            (canonicalProjectivePostConeRawTreeWordBySlot_originEquiv hp hp2 child tag) := by
        exact hget
      change (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get tag =
        canonicalProjectivePostConeEndpointSignedLetter hp hp2
          (rec child hdeep
            (canonicalProjectivePostConeRawTreeWordBySlot_originEquiv hp hp2 child tag))
      rw [hget', hrec child hdeep]
  | deeperTarget z child htarget hlabel hdeep =>
      have hget := canonicalProjectivePostConeRawTreeWordBySlot_originEquiv_get
        hp hp2 child (canonicalProjectivePostConeRawTreeWordBySlot_originEquiv
          hp hp2 child tag)
      have hi : (canonicalProjectivePostConeRawTreeWordBySlot_originEquiv
          hp hp2 child).symm
          (canonicalProjectivePostConeRawTreeWordBySlot_originEquiv hp hp2 child tag) = tag :=
        Equiv.symm_apply_apply _ _
      rw [hi] at hget
      have hget' : (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get tag =
          canonicalProjectivePostConeRawTreeWordOriginTag_letter hp hp2 child
            (canonicalProjectivePostConeRawTreeWordBySlot_originEquiv hp hp2 child tag) := by
        exact hget
      change (((canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get tag).1,
          !((canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get tag).2) =
        canonicalProjectivePostConeEndpointSignedLetter hp hp2
          ((rec child hdeep
            (canonicalProjectivePostConeRawTreeWordBySlot_originEquiv hp hp2 child tag)).1,
           !(rec child hdeep
            (canonicalProjectivePostConeRawTreeWordBySlot_originEquiv hp hp2 child tag)).2)
      rw [hget', hrec child hdeep]
      rfl

/-- The pivot-aware side decoder agrees with the selected classified-term
decoder, including the position casts in the side-origin equivalence. -/
theorem canonicalProjectivePostConeRawSideOrigin_endpoint_letter
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (rec : ∀ child : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child →
      CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 child →
        Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
          (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool)
    (hrec : ∀ child hdeep tag,
      canonicalProjectivePostConeRawTreeWordOriginTag_letter hp hp2 child tag =
        canonicalProjectivePostConeEndpointSignedLetter hp hp2
          (rec child hdeep tag))
    (s : ProjectivePolygonSide)
    (tag : CanonicalProjectivePostConeRawContourSideOriginTag hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) s) :
    canonicalProjectivePostConeRawContourSideOriginTag_letter hp hp2 slot
        (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) s tag =
      canonicalProjectivePostConeEndpointSignedLetter hp hp2
        (canonicalProjectivePostConeRawSideOrigin_endpoint hp hp2 slot rec s tag) := by
  classical
  by_cases hs : s = canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot
  · have htag : Empty := by
      simpa [CanonicalProjectivePostConeRawContourSideOriginTag, hs] using tag
    exact htag.elim
  · let i := (canonicalProjectivePostConeRawContourSide_positionEquiv hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) s).symm tag
    let c := canonicalProjectivePostConeRawContourTermCase hp hp2 slot s hs
    let ctag := canonicalProjectivePostConeRawContourTerm_positionEquiv
      hp hp2 slot (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
      s hs i
    have hget := canonicalProjectivePostConeRawContourTerm_positionEquiv_get
      hp hp2 slot (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
      s hs i
    have hterm := canonicalProjectivePostConeRawTermOrigin_endpoint_letter
      hp hp2 slot rec hrec c ctag
    simp only [canonicalProjectivePostConeRawContourSideOriginTag_letter,
      canonicalProjectivePostConeRawSideOrigin_endpoint, dif_neg hs]
    change (canonicalProjectivePostConeRawContourTerm hp hp2 slot
        (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) s).get i =
      canonicalProjectivePostConeEndpointSignedLetter hp hp2
        (canonicalProjectivePostConeRawTermOrigin_endpoint hp hp2 slot rec c ctag)
    rw [hget, hterm]

/-- The nested ordered-side-list decoder preserves each side occurrence's
literal signed letter, using induction only over the finite side list. -/
theorem canonicalProjectivePostConeRawTermsOrigin_endpoint_letter
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (rec : ∀ child : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child →
      CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 child →
        Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
          (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool)
    (hrec : ∀ child hdeep tag,
      canonicalProjectivePostConeRawTreeWordOriginTag_letter hp hp2 child tag =
        canonicalProjectivePostConeEndpointSignedLetter hp hp2
          (rec child hdeep tag))
    (sides : List ProjectivePolygonSide)
    (tag : CanonicalProjectivePostConeRawContourTermsOriginTag hp hp2 slot
      (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) sides) :
    canonicalProjectivePostConeRawContourTermsOriginTag_letter hp hp2 slot
        (fun child _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) sides tag =
      canonicalProjectivePostConeEndpointSignedLetter hp hp2
        (canonicalProjectivePostConeRawTermsOrigin_endpoint hp hp2 slot rec sides tag) := by
  induction sides with
  | nil => exact tag.elim
  | cons s sides ih =>
      cases tag with
      | inl sideTag =>
          simpa [canonicalProjectivePostConeRawContourTermsOriginTag_letter,
            canonicalProjectivePostConeRawTermsOrigin_endpoint] using
            (canonicalProjectivePostConeRawSideOrigin_endpoint_letter
              hp hp2 slot rec hrec s sideTag)
      | inr tailTag =>
          simpa [canonicalProjectivePostConeRawContourTermsOriginTag_letter,
            canonicalProjectivePostConeRawTermsOrigin_endpoint] using ih tailTag

/-- One complete slot splice preserves the endpoint decoded by its nested
origin, while the source-oriented splice applies its recorded global flip. -/
theorem canonicalProjectivePostConeRawTreeWordOrigin_endpoint_step_letter
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (rec : ∀ child : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child →
      CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 child →
        Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
          (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool)
    (hrec : ∀ child hdeep tag,
      canonicalProjectivePostConeRawTreeWordOriginTag_letter hp hp2 child tag =
        canonicalProjectivePostConeEndpointSignedLetter hp hp2
          (rec child hdeep tag))
    (tag : CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 slot) :
    canonicalProjectivePostConeRawTreeWordOriginTag_letter hp hp2 slot tag =
      canonicalProjectivePostConeEndpointSignedLetter hp hp2
        (canonicalProjectivePostConeRawTreeWordOrigin_endpoint_step hp hp2 slot rec tag) := by
  cases tag with
  | source hsource blocks =>
      cases blocks with
      | inl origin =>
          have hterms := canonicalProjectivePostConeRawTermsOrigin_endpoint_letter
            hp hp2 slot rec hrec
            (canonicalProjectivePostConeBoundaryPrefixSides
              (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) origin
          have hflip := congrArg (fun x : CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool =>
            (x.1, !x.2)) hterms
          simpa [canonicalProjectivePostConeRawTreeWordOriginTag_letter,
            canonicalProjectivePostConeRawTreeWordOrigin_endpoint_step,
            canonicalProjectivePostConeEndpointSignedLetter] using hflip
      | inr origin =>
          have hterms := canonicalProjectivePostConeRawTermsOrigin_endpoint_letter
            hp hp2 slot rec hrec
            (canonicalProjectivePostConeBoundarySuffixSides
              (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) origin
          have hflip := congrArg (fun x : CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool =>
            (x.1, !x.2)) hterms
          simpa [canonicalProjectivePostConeRawTreeWordOriginTag_letter,
            canonicalProjectivePostConeRawTreeWordOrigin_endpoint_step,
            canonicalProjectivePostConeEndpointSignedLetter] using hflip
  | target htarget blocks =>
      cases blocks with
      | inl origin =>
          have hterms := canonicalProjectivePostConeRawTermsOrigin_endpoint_letter
            hp hp2 slot rec hrec
            (canonicalProjectivePostConeBoundarySuffixSides
              (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) origin
          simpa [canonicalProjectivePostConeRawTreeWordOriginTag_letter,
            canonicalProjectivePostConeRawTreeWordOrigin_endpoint_step,
            canonicalProjectivePostConeEndpointSignedLetter] using hterms
      | inr origin =>
          have hterms := canonicalProjectivePostConeRawTermsOrigin_endpoint_letter
            hp hp2 slot rec hrec
            (canonicalProjectivePostConeBoundaryPrefixSides
              (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) origin
          simpa [canonicalProjectivePostConeRawTreeWordOriginTag_letter,
            canonicalProjectivePostConeRawTreeWordOrigin_endpoint_step,
            canonicalProjectivePostConeEndpointSignedLetter] using hterms

/-- The well-founded recursive endpoint decoder agrees with the exact
signed letter named by every complete-slot origin tag. -/
theorem canonicalProjectivePostConeRawTreeWordOrigin_endpoint_letter
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (tag : CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 slot) :
    canonicalProjectivePostConeRawTreeWordOriginTag_letter hp hp2 slot tag =
      canonicalProjectivePostConeEndpointSignedLetter hp hp2
        (canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 slot tag) := by
  classical
  refine ((canonicalProjectivePostConeDirectTreeDependencyWellFounded hp hp2).induction
    (C := fun slot => ∀ tag : CanonicalProjectivePostConeRawTreeWordOriginTag hp hp2 slot,
      canonicalProjectivePostConeRawTreeWordOriginTag_letter hp hp2 slot tag =
        canonicalProjectivePostConeEndpointSignedLetter hp hp2
          (canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 slot tag))
    slot ?_) tag
  intro slot ih tag
  unfold canonicalProjectivePostConeRawTreeWordOrigin_endpoint
  rw [WellFounded.fix_eq]
  exact canonicalProjectivePostConeRawTreeWordOrigin_endpoint_step_letter
    hp hp2 slot
    (fun child _ => canonicalProjectivePostConeRawTreeWordOrigin_endpoint hp hp2 child)
    (fun child hdeep tag => ih child hdeep tag) tag

/-- A slot-word position decodes to exactly its literal signed letter, with
the origin interpreter additionally retaining the terminal endpoint dart. -/
theorem canonicalProjectivePostConeRawTreeWordPosition_endpoint_get
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (i : Fin (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot).length) :
    (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot).get i =
      canonicalProjectivePostConeEndpointSignedLetter hp hp2
        (canonicalProjectivePostConeRawTreeWordPosition_endpoint hp hp2 slot i) := by
  let e := canonicalProjectivePostConeRawTreeWordBySlot_originEquiv hp hp2 slot
  let tag := e i
  have hword := canonicalProjectivePostConeRawTreeWordBySlot_originEquiv_get
    hp hp2 slot tag
  have hi : e.symm tag = i := Equiv.symm_apply_apply e i
  rw [hi] at hword
  rw [hword]
  exact canonicalProjectivePostConeRawTreeWordOrigin_endpoint_letter hp hp2 slot tag

/-- Signed occurrence count follows the literal slot splice. The source
orientation reverses both boundary blocks and hence swaps the requested sign;
the target orientation concatenates suffix then prefix without changing sign.
-/
theorem canonicalProjectivePostConeRawTreeWordBySlot_signedOccurrenceCount
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    [DecidableEq (CanonicalProjectivePostConeFinalGenerator hp hp2)]
    (z : CanonicalProjectivePostConeFinalGenerator hp hp2) (positive : Bool) :
    (slot.right = projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) →
      signedOccurrenceCount z positive
        (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot) =
      signedOccurrenceCount z (!positive)
            (canonicalProjectivePostConeRawContourPrefix hp hp2 slot
              (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)) +
          signedOccurrenceCount z (!positive)
            (canonicalProjectivePostConeRawContourSuffix hp hp2 slot
              (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other))) ∧
    (slot.right ≠ projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) →
      signedOccurrenceCount z positive
        (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot) =
          signedOccurrenceCount z positive
            (canonicalProjectivePostConeRawContourSuffix hp hp2 slot
              (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)) +
          signedOccurrenceCount z positive
            (canonicalProjectivePostConeRawContourPrefix hp hp2 slot
              (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other))) := by
  classical
  constructor
  · intro hsource
    rw [canonicalProjectivePostConeRawTreeWordBySlot_eq_splice_of_source
      hp hp2 slot hsource]
    simp only [signedOccurrenceCount_append, signedOccurrenceCount_invRev]
  · intro hsource
    rw [canonicalProjectivePostConeRawTreeWordBySlot_eq_splice_of_target
      hp hp2 slot hsource]
    simp only [signedOccurrenceCount_append]

private theorem canonicalProjectivePostConeRawContourTerm_mem_invRev
    {X : Type*} (w : List (X × Bool)) {x : X} {b : Bool}
    (h : (x, b) ∈ w) : (x, !b) ∈ FreeGroup.invRev w := by
  change (x, !b) ∈ (List.map (fun g : X × Bool => (g.1, !g.2)) w).reverse
  apply List.mem_reverse.mpr
  apply List.mem_map.mpr
  refine ⟨(x, b), h, ?_⟩
  cases b <;> rfl

/-- Every occurrence in an off-pivot parent term enters its prefix or suffix,
and then the slot splice carries it into the recursive slot word. The
source-oriented splice flips the sign by inverse reversal. -/
theorem canonicalProjectivePostConeRawTreeWordBySlot_mem_boundaryTerm
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (s : ProjectivePolygonSide)
    (hsides : s ∈ canonicalProjectivePostConeBoundaryPrefixSides
        (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot) ∨
      s ∈ canonicalProjectivePostConeBoundarySuffixSides
        (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot))
    (letter : CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool)
    (hletter : letter ∈ canonicalProjectivePostConeRawContourTerm hp hp2
      slot (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) s) :
    ((slot.right = projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)) →
      (letter.1, !letter.2) ∈ canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot) ∧
    ((slot.right ≠ projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)) →
      letter ∈ canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot) := by
  classical
  let ih := fun other
      (_hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other) =>
      canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other
  have hword : canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot =
      if hsource : slot.right = projectivePolygonPostConeEdgeSource
          (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) then
        FreeGroup.invRev (canonicalProjectivePostConeRawContourPrefix hp hp2 slot ih) ++
          FreeGroup.invRev (canonicalProjectivePostConeRawContourSuffix hp hp2 slot ih)
      else
        canonicalProjectivePostConeRawContourSuffix hp hp2 slot ih ++
          canonicalProjectivePostConeRawContourPrefix hp hp2 slot ih := by
    unfold canonicalProjectivePostConeRawTreeWordBySlot
    rw [WellFounded.fix_eq]
    change (if hsource : slot.right = projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) then
        FreeGroup.invRev (canonicalProjectivePostConeRawContourPrefix hp hp2 slot
          (fun other _hdeep => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)) ++
          FreeGroup.invRev (canonicalProjectivePostConeRawContourSuffix hp hp2 slot
            (fun other _hdeep => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other))
      else
        canonicalProjectivePostConeRawContourSuffix hp hp2 slot
          (fun other _hdeep => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) ++
          canonicalProjectivePostConeRawContourPrefix hp hp2 slot
            (fun other _hdeep => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)) = _
    rfl
  constructor
  · intro hsource
    rw [hword]
    split_ifs
    · simp only [List.mem_append]
      rcases hsides with hpref | hsuff
      · exact Or.inl (canonicalProjectivePostConeRawContourTerm_mem_invRev _
          (canonicalProjectivePostConeRawContourTerm_mem_prefix hp hp2 slot ih s
            hpref letter hletter))
      · exact Or.inr (canonicalProjectivePostConeRawContourTerm_mem_invRev _
          (canonicalProjectivePostConeRawContourTerm_mem_suffix hp hp2 slot ih s
            hsuff letter hletter))
  · intro hsource
    rw [hword]
    split_ifs with heq
    · exact (hsource heq).elim
    simp only [List.mem_append]
    rcases hsides with hpref | hsuff
    · exact Or.inr (canonicalProjectivePostConeRawContourTerm_mem_prefix hp hp2 slot ih s
        hpref letter hletter)
    · exact Or.inl (canonicalProjectivePostConeRawContourTerm_mem_suffix hp hp2 slot ih s
        hsuff letter hletter)

private theorem canonicalProjectivePostConeRawContourSubstitutionHom_eq
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (raw : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool))
    (words : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      FreeGroup (CanonicalProjectivePostConeFinalGenerator hp hp2))
    (hraw : ∀ other hdeep, FreeGroup.mk (raw other hdeep) = words other hdeep) :
    canonicalProjectivePostConeDirectTreeSubstitutionHom hp hp2 slot
      (fun other hdeep => FreeGroup.mk (raw other hdeep)) =
      canonicalProjectivePostConeDirectTreeSubstitutionHom hp hp2 slot words := by
  apply FreeGroup.ext_hom
  intro z
  simp only [canonicalProjectivePostConeDirectTreeSubstitutionHom_of]
  unfold canonicalProjectivePostConeDirectTreeSubstitution
  by_cases hz : isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z
  · rw [dif_pos hz, dif_pos hz]
    dsimp only
    split
    · rename_i hdeep
      exact hraw _ hdeep
    · rfl
  · rw [dif_neg hz, dif_neg hz]

/-- Evaluating the recursive signed list at any tree slot recovers the
existing direct defining word exactly. -/
theorem canonicalProjectivePostConeRawTreeWordBySlot_eval
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2) :
    FreeGroup.mk (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot) =
      canonicalProjectivePostConeDirectTreeEliminationWordBySlot hp hp2 slot := by
  classical
  refine (canonicalProjectivePostConeDirectTreeDependencyWellFounded hp hp2).induction
    (C := fun slot =>
      FreeGroup.mk (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot) =
        canonicalProjectivePostConeDirectTreeEliminationWordBySlot hp hp2 slot) slot ?_
  intro slot hind
  unfold canonicalProjectivePostConeRawTreeWordBySlot
  rw [WellFounded.fix_eq]
  change FreeGroup.mk
      (if hsource : slot.right = projectivePolygonPostConeEdgeSource
          (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)
        then
          FreeGroup.invRev (canonicalProjectivePostConeRawContourPrefix hp hp2 slot
            (fun other _hdeep => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)) ++
            FreeGroup.invRev (canonicalProjectivePostConeRawContourSuffix hp hp2 slot
              (fun other _hdeep => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other))
        else
          canonicalProjectivePostConeRawContourSuffix hp hp2 slot
            (fun other _hdeep => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) ++
            canonicalProjectivePostConeRawContourPrefix hp hp2 slot
              (fun other _hdeep => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)) =
      canonicalProjectivePostConeDirectTreeEliminationWordBySlot hp hp2 slot
  have hsub :
      canonicalProjectivePostConeDirectTreeSubstitutionHom hp hp2 slot
        (fun other _hdeep =>
          FreeGroup.mk (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)) =
        canonicalProjectivePostConeDirectTreeSubstitutionHom hp hp2 slot
          (fun other _hdeep =>
            canonicalProjectivePostConeDirectTreeEliminationWordBySlot hp hp2 other) := by
    apply canonicalProjectivePostConeRawContourSubstitutionHom_eq hp hp2 slot
    intro other hdeep
    exact hind other hdeep
  by_cases hsource : slot.right = projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)
  · rw [dif_pos hsource, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk,
      ← FreeGroup.inv_mk,
      canonicalProjectivePostConeRawContourPrefix_eval,
      canonicalProjectivePostConeRawContourSuffix_eval, hsub]
    exact (canonicalProjectivePostConeDirectTreeEliminationWordBySlot_of_source
      hp hp2 slot hsource).symm
  · rw [dif_neg hsource, ← FreeGroup.mul_mk,
      canonicalProjectivePostConeRawContourSuffix_eval,
      canonicalProjectivePostConeRawContourPrefix_eval, hsub]
    exact (canonicalProjectivePostConeDirectTreeEliminationWordBySlot_of_target
      hp hp2 slot hsource).symm

/-- Every off-pivot raw slot expansion retains its exact source/target
origin: it is empty, a final signed letter, a deeper source word, or the
inverse reversal of a deeper target word. -/
theorem canonicalProjectivePostConeRawContourTerm_expansion
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool))
    (s : ProjectivePolygonSide)
    (hs : s ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot) :
    (canonicalProjectivePostConeRawContourTerm hp hp2 slot ih s = [] ∧
      canonicalProjectiveConePostConeBoundaryTerm p slot.right.state s = 1) ∨
    (∃ (z : CanonicalProjectiveConeKeptSymbol p)
        (hz : ¬ isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z),
        ((⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p) =
            projectivePolygonPostConeEdgeSource z ∧
          s = projectivePolygonPostConeEdgeSide z ∧
          canonicalProjectiveConePostConeBoundaryTerm p slot.right.state s = FreeGroup.of z) ∧
        canonicalProjectivePostConeRawContourTerm hp hp2 slot ih s = [(⟨z, hz⟩, true)]) ∨
    (∃ (z : CanonicalProjectiveConeKeptSymbol p)
        (hz : ¬ isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z),
        ((⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p) =
            projectivePolygonPostConeEdgeTarget z ∧
          s = projectivePolygonPostConeEdgeTargetSide z ∧
          canonicalProjectiveConePostConeBoundaryTerm p slot.right.state s = (FreeGroup.of z)⁻¹) ∧
        canonicalProjectivePostConeRawContourTerm hp hp2 slot ih s = [(⟨z, hz⟩, false)]) ∨
    (∃ (z : CanonicalProjectiveConeKeptSymbol p)
        (other : CanonicalProjectivePostConeTreeSlot hp hp2)
        (hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
          canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other),
        ((⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p) =
            projectivePolygonPostConeEdgeSource z ∧
          s = projectivePolygonPostConeEdgeSide z ∧
          canonicalProjectiveConePostConeBoundaryTerm p slot.right.state s = FreeGroup.of z) ∧
        canonicalProjectivePostConeTreeSlotLabel hp hp2 other = z ∧
        canonicalProjectivePostConeRawContourTerm hp hp2 slot ih s = ih other hdeep) ∨
    ∃ (z : CanonicalProjectiveConeKeptSymbol p)
      (other : CanonicalProjectivePostConeTreeSlot hp hp2)
      (hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other),
      ((⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p) =
          projectivePolygonPostConeEdgeTarget z ∧
        s = projectivePolygonPostConeEdgeTargetSide z ∧
        canonicalProjectiveConePostConeBoundaryTerm p slot.right.state s = (FreeGroup.of z)⁻¹) ∧
      canonicalProjectivePostConeTreeSlotLabel hp hp2 other = z ∧
      canonicalProjectivePostConeRawContourTerm hp hp2 slot ih s =
        FreeGroup.invRev (ih other hdeep) := by
  classical
  cases hcase : canonicalProjectivePostConeRawContourTermCase hp hp2 slot s hs with
  | one hterm =>
      left
      refine ⟨?_, hterm⟩
      simp only [canonicalProjectivePostConeRawContourTerm, dif_neg hs,
        canonicalProjectivePostConeRawContourTermOfCase, hcase]
  | finalSource z hsource hz =>
      exact Or.inr (Or.inl ⟨z, hz, hsource, by
        simp only [canonicalProjectivePostConeRawContourTerm, dif_neg hs,
          canonicalProjectivePostConeRawContourTermOfCase, hcase]⟩)
  | finalTarget z htarget hz =>
      exact Or.inr (Or.inr (Or.inl ⟨z, hz, htarget, by
        simp only [canonicalProjectivePostConeRawContourTerm, dif_neg hs,
          canonicalProjectivePostConeRawContourTermOfCase, hcase]⟩))
  | deeperSource z other hsource hlabel hdeep =>
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨z, other, hdeep, hsource, hlabel, by
        simp only [canonicalProjectivePostConeRawContourTerm, dif_neg hs,
          canonicalProjectivePostConeRawContourTermOfCase, hcase]⟩)))
  | deeperTarget z other htarget hlabel hdeep =>
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨z, other, hdeep, htarget, hlabel, by
        simp only [canonicalProjectivePostConeRawContourTerm, dif_neg hs,
          canonicalProjectivePostConeRawContourTermOfCase, hcase]⟩)))

/-- At a non-pivot source dart, the local tree-slot expansion retains the
positive literal of every final physical edge. -/
theorem canonicalProjectivePostConeRawContourTerm_eq_source_letter
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool))
    (z : CanonicalProjectiveConeKeptSymbol p)
    (hz : ¬ isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z)
    (hface : (⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p) =
      projectivePolygonPostConeEdgeSource z)
    (hs : projectivePolygonPostConeEdgeSide z ≠
      canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot) :
    canonicalProjectivePostConeRawContourTerm hp hp2 slot ih
      (projectivePolygonPostConeEdgeSide z) = [(⟨z, hz⟩, true)] := by
  classical
  have hstate : slot.right.state = (projectivePolygonPostConeEdgeSource z).state :=
    congrArg ProjectivePolygonPostConeFace.state hface
  have hterm : canonicalProjectiveConePostConeBoundaryTerm p slot.right.state
      (projectivePolygonPostConeEdgeSide z) = FreeGroup.of z := by
    rw [hstate]
    exact canonicalProjectiveConePostConeBoundaryTerm_edgeSource_eq z
  rcases canonicalProjectivePostConeRawContourTerm_expansion hp hp2 slot ih
      (projectivePolygonPostConeEdgeSide z) hs with hOne | hSource | hTarget |
      hDeepSource | hDeepTarget
  · exact False.elim ((FreeGroup.of_ne_one z) (hterm.symm.trans hOne.2))
  · rcases hSource with ⟨z', hz', hcarrier, hlist⟩
    have hzz : z' = z := FreeGroup.of_injective (hcarrier.2.2.symm.trans hterm)
    subst z'
    simpa using hlist
  · rcases hTarget with ⟨z', hz', hcarrier, hlist⟩
    have hword : FreeGroup.of z = (FreeGroup.of z')⁻¹ :=
      hterm.symm.trans hcarrier.2.2
    exact False.elim (BoundaryWords.Internal.freeGroup_of_ne_inv z z' hword)

  · rcases hDeepSource with ⟨z', other, hdeep, hcarrier, hlabel, hlist⟩
    have hzz : z' = z := FreeGroup.of_injective (hcarrier.2.2.symm.trans hterm)
    have htree : canonicalProjectivePostConeTreeSlotLabel hp hp2 other = z :=
      hlabel.trans hzz
    subst z'
    exact (hz ⟨other, htree⟩).elim
  · rcases hDeepTarget with ⟨z', other, hdeep, hcarrier, hlabel, hlist⟩
    have hword : FreeGroup.of z = (FreeGroup.of z')⁻¹ :=
      hterm.symm.trans hcarrier.2.2
    exact False.elim (BoundaryWords.Internal.freeGroup_of_ne_inv z z' hword)

/-- A source-oriented deeper tree label inserts the child's entire raw word
as the parent's unreduced boundary term. This is one composable parent-step
for lifting occurrence positions toward the root. -/
theorem canonicalProjectivePostConeRawContourTerm_eq_deeper_source_word
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (parent child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (_hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 parent <
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child)
    (s : ProjectivePolygonSide)
    (hs : s ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 parent)
    (hcarrier :
      (⟨parent.right.state⟩ : ProjectivePolygonPostConeFace p) =
          projectivePolygonPostConeEdgeSource
            (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) ∧
        s = projectivePolygonPostConeEdgeSide
          (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) ∧
        canonicalProjectiveConePostConeBoundaryTerm p parent.right.state s =
          FreeGroup.of (canonicalProjectivePostConeTreeSlotLabel hp hp2 child)) :
    canonicalProjectivePostConeRawContourTerm hp hp2 parent
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) s =
        canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child := by
  classical
  let label := canonicalProjectivePostConeTreeSlotLabel hp hp2 child
  let ih := fun other
      (_hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 parent <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other) =>
      canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other
  rcases canonicalProjectivePostConeRawContourTerm_expansion hp hp2 parent ih s hs with
    hOne | hFinalSource | hFinalTarget | hDeepSource | hDeepTarget
  · exact False.elim (FreeGroup.of_ne_one label (hcarrier.2.2.symm.trans hOne.2))
  · rcases hFinalSource with ⟨z, hz, hsource, _⟩
    have hlabel : z = label := FreeGroup.of_injective (hsource.2.2.symm.trans hcarrier.2.2)
    exact (hz ⟨child, hlabel.symm⟩).elim
  · rcases hFinalTarget with ⟨z, hz, htarget, _⟩
    have hword : FreeGroup.of label = (FreeGroup.of z)⁻¹ :=
      hcarrier.2.2.symm.trans htarget.2.2
    have hletters := congrArg FreeGroup.toWord hword
    simp only [FreeGroup.toWord_of, FreeGroup.toWord_inv] at hletters
    simp [FreeGroup.invRev] at hletters

  · rcases hDeepSource with ⟨z, other, hdepth, hsource, hlabel, hlist⟩
    have hz : z = label := FreeGroup.of_injective (hsource.2.2.symm.trans hcarrier.2.2)
    have hother : other = child :=
      canonicalProjectivePostConeTreeSlotLabel_injective hp hp2 (hlabel.trans hz)
    subst other
    simpa [ih] using hlist
  · rcases hDeepTarget with ⟨z, other, hdepth, htarget, hlabel, _⟩
    have hword : FreeGroup.of label = (FreeGroup.of z)⁻¹ :=
      hcarrier.2.2.symm.trans htarget.2.2
    have hletters := congrArg FreeGroup.toWord hword
    simp only [FreeGroup.toWord_of, FreeGroup.toWord_inv] at hletters
    simp [FreeGroup.invRev] at hletters

/-- A target-oriented deeper tree label inserts the inverse reversal of the
child's complete raw word at its parent's boundary term. -/
theorem canonicalProjectivePostConeRawContourTerm_eq_deeper_target_word
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (parent child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (_hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 parent <
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child)
    (s : ProjectivePolygonSide)
    (hs : s ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 parent)
    (hcarrier :
      (⟨parent.right.state⟩ : ProjectivePolygonPostConeFace p) =
          projectivePolygonPostConeEdgeTarget
            (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) ∧
        s = projectivePolygonPostConeEdgeTargetSide
          (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) ∧
        canonicalProjectiveConePostConeBoundaryTerm p parent.right.state s =
          (FreeGroup.of (canonicalProjectivePostConeTreeSlotLabel hp hp2 child))⁻¹) :
    canonicalProjectivePostConeRawContourTerm hp hp2 parent
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) s =
        FreeGroup.invRev (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) := by
  classical
  let label := canonicalProjectivePostConeTreeSlotLabel hp hp2 child
  let ih := fun other
      (_hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 parent <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other) =>
      canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other
  rcases canonicalProjectivePostConeRawContourTerm_expansion hp hp2 parent ih s hs with
    hOne | hFinalSource | hFinalTarget | hDeepSource | hDeepTarget
  · have hone : FreeGroup.of label = 1 := by
      have h := hcarrier.2.2
      rw [hOne.2] at h
      exact inv_eq_one.mp h.symm
    exact False.elim (FreeGroup.of_ne_one label hone)
  · rcases hFinalSource with ⟨z, hz, hsource, _⟩
    have hword : FreeGroup.of z = (FreeGroup.of label)⁻¹ :=
      hsource.2.2.symm.trans hcarrier.2.2
    have hletters := congrArg FreeGroup.toWord hword
    simp only [FreeGroup.toWord_of, FreeGroup.toWord_inv] at hletters
    simp [FreeGroup.invRev] at hletters
  · rcases hFinalTarget with ⟨z, hz, htarget, _⟩
    have hword : FreeGroup.of z = FreeGroup.of label := by
      apply inv_injective
      exact htarget.2.2.symm.trans hcarrier.2.2
    have hlabel : z = label := FreeGroup.of_injective hword
    exact (hz ⟨child, hlabel.symm⟩).elim
  · rcases hDeepSource with ⟨z, other, hdepth, hsource, hlabel, _⟩
    have hword : FreeGroup.of z = (FreeGroup.of label)⁻¹ :=
      hsource.2.2.symm.trans hcarrier.2.2
    have hletters := congrArg FreeGroup.toWord hword
    simp only [FreeGroup.toWord_of, FreeGroup.toWord_inv] at hletters
    simp [FreeGroup.invRev] at hletters
  · rcases hDeepTarget with ⟨z, other, hdepth, htarget, hlabel, hlist⟩
    have hword : FreeGroup.of z = FreeGroup.of label := by
      apply inv_injective
      exact htarget.2.2.symm.trans hcarrier.2.2
    have hz : z = label := FreeGroup.of_injective hword
    have hother : other = child :=
      canonicalProjectivePostConeTreeSlotLabel_injective hp hp2 (hlabel.trans hz)
    subst other
    simpa [ih] using hlist

/-- Inverse reversal carries each child's occurrence position to the parent
term and flips exactly its orientation bit. -/
theorem canonicalProjectivePostConeRawContourTerm_get_deeper_target_word
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (parent child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 parent <
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child)
    (s : ProjectivePolygonSide)
    (hs : s ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 parent)
    (hcarrier :
      (⟨parent.right.state⟩ : ProjectivePolygonPostConeFace p) =
          projectivePolygonPostConeEdgeTarget
            (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) ∧
        s = projectivePolygonPostConeEdgeTargetSide
          (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) ∧
        canonicalProjectiveConePostConeBoundaryTerm p parent.right.state s =
          (FreeGroup.of (canonicalProjectivePostConeTreeSlotLabel hp hp2 child))⁻¹)
    (i : Fin (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).length) :
    ∃ j : Fin (canonicalProjectivePostConeRawContourTerm hp hp2 parent
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) s).length,
      (canonicalProjectivePostConeRawContourTerm hp hp2 parent
        (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) s).get j =
        (((canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get i).1,
          !((canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get i).2) := by
  rw [canonicalProjectivePostConeRawContourTerm_eq_deeper_target_word
    hp hp2 parent child hdeep s hs hcarrier]
  exact ⟨invRevPosition i, get_invRevPosition _ i⟩

/-- Every signed occurrence in a child's raw slot word is therefore present
in the source-oriented parent boundary term. -/
theorem canonicalProjectivePostConeRawContourTerm_mem_deeper_source_word
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (parent child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 parent <
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child)
    (s : ProjectivePolygonSide)
    (hs : s ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 parent)
    (hcarrier :
      (⟨parent.right.state⟩ : ProjectivePolygonPostConeFace p) =
          projectivePolygonPostConeEdgeSource
            (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) ∧
        s = projectivePolygonPostConeEdgeSide
          (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) ∧
        canonicalProjectiveConePostConeBoundaryTerm p parent.right.state s =
          FreeGroup.of (canonicalProjectivePostConeTreeSlotLabel hp hp2 child))
    (letter : CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool)
    (hletter : letter ∈ canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) :
    letter ∈ canonicalProjectivePostConeRawContourTerm hp hp2 parent
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) s := by
  rw [canonicalProjectivePostConeRawContourTerm_eq_deeper_source_word
    hp hp2 parent child hdeep s hs hcarrier]
  exact hletter

/-- The source-carrier premise of the parent-step lemma follows directly
when adjacent tree slots meet with the child label positively oriented out
of the shared face. -/
theorem canonicalProjectivePostConeRawContourTerm_mem_child_of_source_incidence
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (parent child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 parent <
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child)
    (hjoin : parent.right = child.left)
    (hchildSource : child.left = projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 child))
    (s : ProjectivePolygonSide)
    (hs : s ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 parent)
    (hsChild : s = projectivePolygonPostConeEdgeSide
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 child))
    (letter : CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool)
    (hletter : letter ∈ canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) :
    letter ∈ canonicalProjectivePostConeRawContourTerm hp hp2 parent
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) s := by
  have hface : (⟨parent.right.state⟩ : ProjectivePolygonPostConeFace p) =
      projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) := by
    apply ProjectivePolygonPostConeFace.stateEquiv.injective
    exact congrArg ProjectivePolygonPostConeFace.state (hjoin.trans hchildSource)
  have hterm : canonicalProjectiveConePostConeBoundaryTerm p parent.right.state s =
      FreeGroup.of (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) := by
    rw [hsChild, congrArg ProjectivePolygonPostConeFace.state
      (hjoin.trans hchildSource)]
    exact canonicalProjectiveConePostConeBoundaryTerm_edgeSource_eq
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 child)
  exact canonicalProjectivePostConeRawContourTerm_mem_deeper_source_word
    hp hp2 parent child hdeep s hs ⟨hface, hsChild, hterm⟩ letter hletter

/-- Target-oriented child incidence places its inverse-reversed occurrence
at a concrete position in the parent boundary term. -/
theorem canonicalProjectivePostConeRawContourTerm_get_child_of_target_incidence
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (parent child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 parent <
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child)
    (hjoin : parent.right = child.left)
    (hchildTarget : child.left = projectivePolygonPostConeEdgeTarget
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 child))
    (s : ProjectivePolygonSide)
    (hs : s ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 parent)
    (hsChild : s = projectivePolygonPostConeEdgeTargetSide
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 child))
    (i : Fin (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).length) :
    ∃ j : Fin (canonicalProjectivePostConeRawContourTerm hp hp2 parent
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) s).length,
      (canonicalProjectivePostConeRawContourTerm hp hp2 parent
        (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) s).get j =
        (((canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get i).1,
          !((canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get i).2) := by
  have hface : (⟨parent.right.state⟩ : ProjectivePolygonPostConeFace p) =
      projectivePolygonPostConeEdgeTarget
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) := by
    apply ProjectivePolygonPostConeFace.stateEquiv.injective
    exact congrArg ProjectivePolygonPostConeFace.state (hjoin.trans hchildTarget)
  have hterm : canonicalProjectiveConePostConeBoundaryTerm p parent.right.state s =
      (FreeGroup.of (canonicalProjectivePostConeTreeSlotLabel hp hp2 child))⁻¹ := by
    rw [hsChild, congrArg ProjectivePolygonPostConeFace.state
      (hjoin.trans hchildTarget)]
    exact canonicalProjectiveConePostConeBoundaryTerm_edgeTarget_eq_inv hp hp2
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 child)
  rcases canonicalProjectivePostConeRawContourTerm_get_deeper_target_word
      hp hp2 parent child hdeep s hs ⟨hface, hsChild, hterm⟩ i with ⟨j, hj⟩
  exact ⟨j, hj⟩

/-- A concrete child occurrence with target orientation is carried through
the parent's contracted boundary and slot splice.  The parent splice
determines whether the inverse-reversal introduced at the child boundary is
cancelled or retained. -/
theorem canonicalProjectivePostConeRawTreeWordBySlot_get_child_of_target_incidence
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (parent child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 parent <
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child)
    (hjoin : parent.right = child.left)
    (hchildTarget : child.left = projectivePolygonPostConeEdgeTarget
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 child))
    (s : ProjectivePolygonSide)
    (hs : s ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 parent)
    (hsChild : s = projectivePolygonPostConeEdgeTargetSide
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 child))
    (i : Fin (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).length) :
    ((parent.right = projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 parent)) →
      (((canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get i).1,
        ((canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get i).2) ∈
          canonicalProjectivePostConeRawTreeWordBySlot hp hp2 parent) ∧
    ((parent.right ≠ projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 parent)) →
      (((canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get i).1,
        !((canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get i).2) ∈
          canonicalProjectivePostConeRawTreeWordBySlot hp hp2 parent) := by
  have hsides := canonicalProjectivePostConeBoundarySide_mem_prefix_or_suffix
    s (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 parent) hs
  rcases canonicalProjectivePostConeRawContourTerm_get_child_of_target_incidence
      hp hp2 parent child hdeep hjoin hchildTarget s hs hsChild i with ⟨j, hj⟩
  have hletter :
      (((canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get i).1,
        !((canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get i).2) ∈
      canonicalProjectivePostConeRawContourTerm hp hp2 parent
        (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) s := by
    exact List.mem_iff_getElem.mpr ⟨j.val, j.isLt, hj⟩
  simpa using canonicalProjectivePostConeRawTreeWordBySlot_mem_boundaryTerm
    hp hp2 parent s hsides _ hletter

/-- The same source-oriented child occurrence is present in the parent's
contracted prefix whenever its side lies before the pivot. -/
theorem canonicalProjectivePostConeRawContourPrefix_mem_child_of_source_incidence
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (parent child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 parent <
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child)
    (hjoin : parent.right = child.left)
    (hchildSource : child.left = projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 child))
    (s : ProjectivePolygonSide)
    (hs : s ∈ canonicalProjectivePostConeBoundaryPrefixSides
      (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 parent))
    (hsChild : s = projectivePolygonPostConeEdgeSide
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 child))
    (letter : CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool)
    (hletter : letter ∈ canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) :
    letter ∈ canonicalProjectivePostConeRawContourPrefix hp hp2 parent
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) := by
  have hsne : s ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 parent := by
    intro h
    exact (canonicalProjectivePostConeBoundaryPrefixSides_ne
      (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 parent) s hs) h
  exact canonicalProjectivePostConeRawContourTerm_mem_prefix hp hp2 parent
    (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)
    s hs letter
    (canonicalProjectivePostConeRawContourTerm_mem_child_of_source_incidence
      hp hp2 parent child hdeep hjoin hchildSource s hsne hsChild letter hletter)

/-- The source-oriented child occurrence is likewise present in the parent's
contracted suffix whenever its side lies after the pivot. -/
theorem canonicalProjectivePostConeRawContourSuffix_mem_child_of_source_incidence
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (parent child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 parent <
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child)
    (hjoin : parent.right = child.left)
    (hchildSource : child.left = projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 child))
    (s : ProjectivePolygonSide)
    (hs : s ∈ canonicalProjectivePostConeBoundarySuffixSides
      (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 parent))
    (hsChild : s = projectivePolygonPostConeEdgeSide
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 child))
    (letter : CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool)
    (hletter : letter ∈ canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) :
    letter ∈ canonicalProjectivePostConeRawContourSuffix hp hp2 parent
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) := by
  have hsne : s ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 parent := by
    intro h
    exact (canonicalProjectivePostConeBoundarySuffixSides_ne
      (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 parent) s hs) h
  exact canonicalProjectivePostConeRawContourTerm_mem_suffix hp hp2 parent
    (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)
    s hs letter
    (canonicalProjectivePostConeRawContourTerm_mem_child_of_source_incidence
      hp hp2 parent child hdeep hjoin hchildSource s hsne hsChild letter hletter)

/-- A positive retained source letter on a slot's prefix sides is carried
through that slot's recursive splice.  If the distinguished tree edge is
sourced from the right face, the splice uses inverse reversal and the letter
appears with negative sign; otherwise it remains positive. -/
theorem canonicalProjectivePostConeRawTreeWordBySlot_mem_source_prefix
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (z : CanonicalProjectivePostConeFinalGenerator hp hp2)
    (hface : (projectivePolygonPostConeEdgeSource z.1).state = slot.right.state)
    (hs : projectivePolygonPostConeEdgeSide z.1 ∈
      canonicalProjectivePostConeBoundaryPrefixSides
        (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) :
    ((slot.right = projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)) →
      (z, false) ∈ canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot) ∧
    ((slot.right ≠ projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)) →
      (z, true) ∈ canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot) := by
  classical
  have hsne : projectivePolygonPostConeEdgeSide z.1 ≠
      canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot :=
    canonicalProjectivePostConeBoundaryPrefixSides_ne _ _ hs
  let ih := fun other
      (_hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other) =>
      canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other
  have hface' : (⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p) =
      projectivePolygonPostConeEdgeSource z.1 := by
    apply ProjectivePolygonPostConeFace.stateEquiv.injective
    exact hface.symm
  have hlocal := canonicalProjectivePostConeRawContourTerm_eq_source_letter
    hp hp2 slot ih z.1 z.2 hface' hsne
  have hprefix : (z, true) ∈ canonicalProjectivePostConeRawContourPrefix hp hp2 slot ih := by
    unfold canonicalProjectivePostConeRawContourPrefix ih
    have hmem : ∀ sides : List ProjectivePolygonSide,
        projectivePolygonPostConeEdgeSide z.1 ∈ sides →
          (z, true) ∈ canonicalProjectivePostConeRawContourTerms hp hp2 slot
            (fun other hdeep => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) sides := by
      intro sides
      induction sides with
      | nil => intro hx; simp at hx
      | cons s ss ihs =>
          intro hx
          simp only [canonicalProjectivePostConeRawContourTerms, List.mem_append]
          rcases List.mem_cons.mp hx with hside | hside
          · subst s
            left
            rw [hlocal]
            simp only [List.mem_singleton]
            exact Prod.ext (Subtype.ext rfl) rfl
          · exact Or.inr (ihs hside)
    exact hmem _ hs
  have hword : canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot =
      if hsource : slot.right = projectivePolygonPostConeEdgeSource
          (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) then
        FreeGroup.invRev (canonicalProjectivePostConeRawContourPrefix hp hp2 slot ih) ++
          FreeGroup.invRev (canonicalProjectivePostConeRawContourSuffix hp hp2 slot ih)
      else
        canonicalProjectivePostConeRawContourSuffix hp hp2 slot ih ++
          canonicalProjectivePostConeRawContourPrefix hp hp2 slot ih := by
    unfold canonicalProjectivePostConeRawTreeWordBySlot
    rw [WellFounded.fix_eq]
    change (if hsource : slot.right = projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) then
        FreeGroup.invRev (canonicalProjectivePostConeRawContourPrefix hp hp2 slot
          (fun other _hdeep => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)) ++
          FreeGroup.invRev (canonicalProjectivePostConeRawContourSuffix hp hp2 slot
            (fun other _hdeep => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other))
      else
        canonicalProjectivePostConeRawContourSuffix hp hp2 slot
          (fun other _hdeep => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) ++
          canonicalProjectivePostConeRawContourPrefix hp hp2 slot
            (fun other _hdeep => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)) = _
    rfl
  constructor
  · intro hcontract
    rw [hword]
    split_ifs
    · simp only [List.mem_append]
      left
      have hinv : (z, false) ∈ FreeGroup.invRev
          (canonicalProjectivePostConeRawContourPrefix hp hp2 slot ih) := by
        simpa [FreeGroup.invRev] using hprefix
      exact hinv
  · intro hcontract
    rw [hword]
    split_ifs with hsource
    · exact (hcontract hsource).elim
    · simp only [List.mem_append]
      exact Or.inr hprefix

/-- A retained source dart in the suffix is carried through the slot splice,
with sign flipped precisely when that splice uses inverse reversal. -/
theorem canonicalProjectivePostConeRawTreeWordBySlot_mem_source_suffix
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (z : CanonicalProjectivePostConeFinalGenerator hp hp2)
    (hface : (projectivePolygonPostConeEdgeSource z.1).state = slot.right.state)
    (hs : projectivePolygonPostConeEdgeSide z.1 ∈
      canonicalProjectivePostConeBoundarySuffixSides
        (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot)) :
    ((slot.right = projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)) →
      (z, false) ∈ canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot) ∧
    ((slot.right ≠ projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)) →
      (z, true) ∈ canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot) := by
  classical
  have hsne : projectivePolygonPostConeEdgeSide z.1 ≠
      canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot :=
    canonicalProjectivePostConeBoundarySuffixSides_ne _ _ hs
  let ih := fun other
      (_hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other) =>
      canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other
  have hface' : (⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p) =
      projectivePolygonPostConeEdgeSource z.1 := by
    apply ProjectivePolygonPostConeFace.stateEquiv.injective
    exact hface.symm
  have hlocal := canonicalProjectivePostConeRawContourTerm_eq_source_letter
    hp hp2 slot ih z.1 z.2 hface' hsne
  have hsuffix : (z, true) ∈ canonicalProjectivePostConeRawContourSuffix hp hp2 slot ih := by
    unfold canonicalProjectivePostConeRawContourSuffix ih
    have hmem : ∀ sides : List ProjectivePolygonSide,
        projectivePolygonPostConeEdgeSide z.1 ∈ sides →
          (z, true) ∈ canonicalProjectivePostConeRawContourTerms hp hp2 slot
            (fun other hdeep => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) sides := by
      intro sides
      induction sides with
      | nil => intro hx; simp at hx
      | cons s ss ihs =>
          intro hx
          simp only [canonicalProjectivePostConeRawContourTerms, List.mem_append]
          rcases List.mem_cons.mp hx with hside | hside
          · subst s
            left
            rw [hlocal]
            simp only [List.mem_singleton]
            exact Prod.ext (Subtype.ext rfl) rfl
          · exact Or.inr (ihs hside)
    exact hmem _ hs
  have hword : canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot =
      if hsource : slot.right = projectivePolygonPostConeEdgeSource
          (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) then
        FreeGroup.invRev (canonicalProjectivePostConeRawContourPrefix hp hp2 slot ih) ++
          FreeGroup.invRev (canonicalProjectivePostConeRawContourSuffix hp hp2 slot ih)
      else
        canonicalProjectivePostConeRawContourSuffix hp hp2 slot ih ++
          canonicalProjectivePostConeRawContourPrefix hp hp2 slot ih := by
    unfold canonicalProjectivePostConeRawTreeWordBySlot
    rw [WellFounded.fix_eq]
    change (if hsource : slot.right = projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) then
        FreeGroup.invRev (canonicalProjectivePostConeRawContourPrefix hp hp2 slot
          (fun other _hdeep => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)) ++
          FreeGroup.invRev (canonicalProjectivePostConeRawContourSuffix hp hp2 slot
            (fun other _hdeep => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other))
      else
        canonicalProjectivePostConeRawContourSuffix hp hp2 slot
          (fun other _hdeep => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) ++
          canonicalProjectivePostConeRawContourPrefix hp hp2 slot
            (fun other _hdeep => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other)) = _
    rfl
  constructor
  · intro hcontract
    rw [hword]
    split_ifs
    · simp only [List.mem_append]
      right
      simpa [FreeGroup.invRev] using hsuffix
  · intro hcontract
    rw [hword]
    split_ifs with hsource
    · exact (hcontract hsource).elim
    · simp only [List.mem_append]
      exact Or.inl hsuffix

/-- A retained physical source dart cannot coincide with the pivot side of
the incoming tree slot: that side is carried by the slot's deleted label. -/
theorem canonicalProjectivePostConeRawIncomingSlot_source_ne_pivot
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : projectivePolygonPostConeCanonicalSpanningTree hp hp2)
    (hq : q ≠ canonicalProjectivePostConeTreeRoot hp hp2)
    (z : CanonicalProjectivePostConeFinalGenerator hp hp2)
    (hsource : projectivePolygonPostConeEdgeSource z.1 = q) :
    projectivePolygonPostConeEdgeSide z.1 ≠
      canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2
        (canonicalProjectivePostConeTreeIncomingSlot hp hp2 q hq) := by
  classical
  let slot := canonicalProjectivePostConeTreeIncomingSlot hp hp2 q hq
  let y := canonicalProjectivePostConeTreeSlotLabel hp hp2 slot
  have hright : slot.right = q :=
    canonicalProjectivePostConeTreeIncomingSlot_right hp hp2 q hq
  have hface : slot.right = projectivePolygonPostConeEdgeSource z.1 :=
    hright.trans hsource.symm
  intro hs
  by_cases hslotSource : slot.right = projectivePolygonPostConeEdgeSource y
  · have hside : projectivePolygonPostConeEdgeSide z.1 =
        projectivePolygonPostConeEdgeSide y := by
      unfold canonicalProjectivePostConeTreeSlotRightFactorSide at hs
      rw [if_pos hslotSource] at hs
      exact hs
    have hzterm : canonicalProjectiveConePostConeBoundaryTerm p slot.right.state
        (projectivePolygonPostConeEdgeSide z.1) = FreeGroup.of z.1 := by
      rw [congrArg ProjectivePolygonPostConeFace.state hface]
      exact canonicalProjectiveConePostConeBoundaryTerm_edgeSource_eq z.1
    have hyterm : canonicalProjectiveConePostConeBoundaryTerm p slot.right.state
        (projectivePolygonPostConeEdgeSide y) = FreeGroup.of y := by
      rw [congrArg ProjectivePolygonPostConeFace.state hslotSource]
      exact canonicalProjectiveConePostConeBoundaryTerm_edgeSource_eq y
    have hword : FreeGroup.of z.1 = FreeGroup.of y := by
      calc
        FreeGroup.of z.1 = canonicalProjectiveConePostConeBoundaryTerm p
            slot.right.state (projectivePolygonPostConeEdgeSide z.1) := hzterm.symm
        _ = canonicalProjectiveConePostConeBoundaryTerm p slot.right.state
              (projectivePolygonPostConeEdgeSide y) := by rw [hside]
        _ = FreeGroup.of y := hyterm
    have hzy : z.1 = y := FreeGroup.of_injective hword
    exact z.2 ⟨slot, hzy.symm⟩
  · have hslotTarget : slot.right = projectivePolygonPostConeEdgeTarget y := by
      rcases canonicalProjectivePostConeTreeSlot_right_eq_physicalSource_or_target
          hp hp2 slot with hsource' | htarget'
      · exact (hslotSource hsource').elim
      · exact htarget'
    have hside : projectivePolygonPostConeEdgeSide z.1 =
        projectivePolygonPostConeEdgeTargetSide y := by
      unfold canonicalProjectivePostConeTreeSlotRightFactorSide at hs
      rw [if_neg hslotSource] at hs
      exact hs
    have hzterm : canonicalProjectiveConePostConeBoundaryTerm p slot.right.state
        (projectivePolygonPostConeEdgeSide z.1) = FreeGroup.of z.1 := by
      rw [congrArg ProjectivePolygonPostConeFace.state hface]
      exact canonicalProjectiveConePostConeBoundaryTerm_edgeSource_eq z.1
    have hyterm : canonicalProjectiveConePostConeBoundaryTerm p slot.right.state
        (projectivePolygonPostConeEdgeTargetSide y) = (FreeGroup.of y)⁻¹ := by
      rw [congrArg ProjectivePolygonPostConeFace.state hslotTarget]
      exact canonicalProjectiveConePostConeBoundaryTerm_edgeTarget_eq_inv hp hp2 y
    have hword : FreeGroup.of z.1 = (FreeGroup.of y)⁻¹ := by
      calc
        FreeGroup.of z.1 = canonicalProjectiveConePostConeBoundaryTerm p
            slot.right.state (projectivePolygonPostConeEdgeSide z.1) := hzterm.symm
        _ = canonicalProjectiveConePostConeBoundaryTerm p slot.right.state
              (projectivePolygonPostConeEdgeTargetSide y) := by rw [hside]
        _ = (FreeGroup.of y)⁻¹ := hyterm
    have hletters := congrArg FreeGroup.toWord hword
    simp only [FreeGroup.toWord_of, FreeGroup.toWord_inv] at hletters
    simp [FreeGroup.invRev] at hletters

/-- At a non-root face, the unique incoming tree slot captures a retained
source dart in its recursive word whenever the dart is not the slot pivot.
This is the composable one-edge step from a physical face to its parent
slot; the remaining root theorem must iterate these steps along the root
path. -/
theorem canonicalProjectivePostConeRawIncomingSlot_mem_source
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : projectivePolygonPostConeCanonicalSpanningTree hp hp2)
    (hq : q ≠ canonicalProjectivePostConeTreeRoot hp hp2)
    (z : CanonicalProjectivePostConeFinalGenerator hp hp2)
    (hsource : projectivePolygonPostConeEdgeSource z.1 = q) :
    ((canonicalProjectivePostConeTreeIncomingSlot hp hp2 q hq).right =
        projectivePolygonPostConeEdgeSource
          (canonicalProjectivePostConeTreeSlotLabel hp hp2
            (canonicalProjectivePostConeTreeIncomingSlot hp hp2 q hq)) →
      (z, false) ∈ canonicalProjectivePostConeRawTreeWordBySlot hp hp2
        (canonicalProjectivePostConeTreeIncomingSlot hp hp2 q hq)) ∧
    ((canonicalProjectivePostConeTreeIncomingSlot hp hp2 q hq).right ≠
        projectivePolygonPostConeEdgeSource
          (canonicalProjectivePostConeTreeSlotLabel hp hp2
            (canonicalProjectivePostConeTreeIncomingSlot hp hp2 q hq)) →
      (z, true) ∈ canonicalProjectivePostConeRawTreeWordBySlot hp hp2
        (canonicalProjectivePostConeTreeIncomingSlot hp hp2 q hq)) := by
  classical
  let slot := canonicalProjectivePostConeTreeIncomingSlot hp hp2 q hq
  have hright : slot.right = q :=
    canonicalProjectivePostConeTreeIncomingSlot_right hp hp2 q hq
  have hnonpivot := canonicalProjectivePostConeRawIncomingSlot_source_ne_pivot
    hp hp2 q hq z hsource
  have hface : (projectivePolygonPostConeEdgeSource z.1).state = slot.right.state := by
    exact (congrArg ProjectivePolygonPostConeFace.state hsource).trans
      (congrArg ProjectivePolygonPostConeFace.state hright).symm
  have hsides := canonicalProjectivePostConeBoundarySide_mem_prefix_or_suffix
    (projectivePolygonPostConeEdgeSide z.1)
    (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot) hnonpivot
  rcases hsides with hprefix | hsuffix
  · exact canonicalProjectivePostConeRawTreeWordBySlot_mem_source_prefix
      hp hp2 slot z hface hprefix
  · exact canonicalProjectivePostConeRawTreeWordBySlot_mem_source_suffix
      hp hp2 slot z hface hsuffix

/-- A complete source/target classification for one root-boundary term.  In
the tree cases the selected label points to the recursive raw slot word. -/
inductive CanonicalProjectivePostConeRawRootContourTermCase
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide) : Type where
  | one : canonicalProjectiveConePostConeBoundaryTerm p q s = 1 →
      CanonicalProjectivePostConeRawRootContourTermCase hp hp2 q s
  | finalSource (z : CanonicalProjectiveConeKeptSymbol p)
      (hsource :
        (⟨q⟩ : ProjectivePolygonPostConeFace p) = projectivePolygonPostConeEdgeSource z ∧
          s = projectivePolygonPostConeEdgeSide z ∧
          canonicalProjectiveConePostConeBoundaryTerm p q s = FreeGroup.of z)
      (hz : ¬ isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z) :
      CanonicalProjectivePostConeRawRootContourTermCase hp hp2 q s
  | finalTarget (z : CanonicalProjectiveConeKeptSymbol p)
      (htarget :
        (⟨q⟩ : ProjectivePolygonPostConeFace p) = projectivePolygonPostConeEdgeTarget z ∧
          s = projectivePolygonPostConeEdgeTargetSide z ∧
          canonicalProjectiveConePostConeBoundaryTerm p q s = (FreeGroup.of z)⁻¹)
      (hz : ¬ isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z) :
      CanonicalProjectivePostConeRawRootContourTermCase hp hp2 q s
  | treeSource (z : CanonicalProjectiveConeKeptSymbol p)
      (hsource :
        (⟨q⟩ : ProjectivePolygonPostConeFace p) = projectivePolygonPostConeEdgeSource z ∧
          s = projectivePolygonPostConeEdgeSide z ∧
          canonicalProjectiveConePostConeBoundaryTerm p q s = FreeGroup.of z)
      (hz : isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z) :
      CanonicalProjectivePostConeRawRootContourTermCase hp hp2 q s
  | treeTarget (z : CanonicalProjectiveConeKeptSymbol p)
      (htarget :
        (⟨q⟩ : ProjectivePolygonPostConeFace p) = projectivePolygonPostConeEdgeTarget z ∧
          s = projectivePolygonPostConeEdgeTargetSide z ∧
          canonicalProjectiveConePostConeBoundaryTerm p q s = (FreeGroup.of z)⁻¹)
      (hz : isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z) :
      CanonicalProjectivePostConeRawRootContourTermCase hp hp2 q s

/-- A root-side term has a unique source/target and tree/final
classification. This makes the root-side origin selected by classical choice
independent of the chosen existence witness. -/
theorem canonicalProjectivePostConeRawRootContourTermCase_unique
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide)
    (a b : CanonicalProjectivePostConeRawRootContourTermCase hp hp2 q s) :
    a = b := by
  classical
  cases a with
  | one hone =>
    cases b with
    | one hone' => rfl
    | finalSource z hsource hz =>
        exact False.elim ((FreeGroup.of_ne_one z) (hsource.2.2.symm.trans hone))
    | finalTarget z htarget hz =>
        have hz1 : FreeGroup.of z = 1 := inv_eq_one.mp (htarget.2.2.symm.trans hone)
        exact False.elim ((FreeGroup.of_ne_one z) hz1)
    | treeSource z hsource hz =>
        exact False.elim ((FreeGroup.of_ne_one z) (hsource.2.2.symm.trans hone))
    | treeTarget z htarget hz =>
        have hz1 : FreeGroup.of z = 1 := inv_eq_one.mp (htarget.2.2.symm.trans hone)
        exact False.elim ((FreeGroup.of_ne_one z) hz1)
  | finalSource z₁ hsource₁ hz₁ =>
    cases b with
    | one hone =>
        exact False.elim ((FreeGroup.of_ne_one z₁) (hsource₁.2.2.symm.trans hone))
    | finalSource z₂ hsource₂ hz₂ =>
        have hz : z₁ = z₂ := FreeGroup.of_injective (hsource₁.2.2.symm.trans hsource₂.2.2)
        subst z₂
        rfl
    | finalTarget z₂ htarget₂ hz₂ =>
        exact False.elim (BoundaryWords.Internal.freeGroup_of_ne_inv z₁ z₂ (hsource₁.2.2.symm.trans htarget₂.2.2))
    | treeSource z₂ hsource₂ hz₂ =>
        have hz : z₁ = z₂ := FreeGroup.of_injective (hsource₁.2.2.symm.trans hsource₂.2.2)
        exact False.elim (hz₁ (hz.symm ▸ hz₂))
    | treeTarget z₂ htarget₂ hz₂ =>
        exact False.elim (BoundaryWords.Internal.freeGroup_of_ne_inv z₁ z₂ (hsource₁.2.2.symm.trans htarget₂.2.2))
  | finalTarget z₁ htarget₁ hz₁ =>
    cases b with
    | one hone =>
        have hz1 : FreeGroup.of z₁ = 1 := inv_eq_one.mp (htarget₁.2.2.symm.trans hone)
        exact False.elim ((FreeGroup.of_ne_one z₁) hz1)
    | finalSource z₂ hsource₂ hz₂ =>
        exact False.elim (BoundaryWords.Internal.freeGroup_of_ne_inv z₂ z₁ (hsource₂.2.2.symm.trans htarget₁.2.2))
    | finalTarget z₂ htarget₂ hz₂ =>
        have hz : z₁ = z₂ := FreeGroup.of_injective <| by
          apply inv_injective
          exact htarget₁.2.2.symm.trans htarget₂.2.2
        subst z₂
        rfl
    | treeSource z₂ hsource₂ hz₂ =>
        exact False.elim (BoundaryWords.Internal.freeGroup_of_ne_inv z₂ z₁ (hsource₂.2.2.symm.trans htarget₁.2.2))
    | treeTarget z₂ htarget₂ hz₂ =>
        have hz : z₁ = z₂ := FreeGroup.of_injective <| by
          apply inv_injective
          exact htarget₁.2.2.symm.trans htarget₂.2.2
        exact False.elim (hz₁ (hz.symm ▸ hz₂))
  | treeSource z₁ hsource₁ hz₁ =>
    cases b with
    | one hone =>
        exact False.elim ((FreeGroup.of_ne_one z₁) (hsource₁.2.2.symm.trans hone))
    | finalSource z₂ hsource₂ hz₂ =>
        have hz : z₁ = z₂ := FreeGroup.of_injective (hsource₁.2.2.symm.trans hsource₂.2.2)
        exact False.elim (hz₂ (hz ▸ hz₁))
    | finalTarget z₂ htarget₂ hz₂ =>
        exact False.elim (BoundaryWords.Internal.freeGroup_of_ne_inv z₁ z₂ (hsource₁.2.2.symm.trans htarget₂.2.2))
    | treeSource z₂ hsource₂ hz₂ =>
        have hz : z₁ = z₂ := FreeGroup.of_injective (hsource₁.2.2.symm.trans hsource₂.2.2)
        subst z₂
        rfl
    | treeTarget z₂ htarget₂ hz₂ =>
        exact False.elim (BoundaryWords.Internal.freeGroup_of_ne_inv z₁ z₂ (hsource₁.2.2.symm.trans htarget₂.2.2))
  | treeTarget z₁ htarget₁ hz₁ =>
    cases b with
    | one hone =>
        have hz1 : FreeGroup.of z₁ = 1 := inv_eq_one.mp (htarget₁.2.2.symm.trans hone)
        exact False.elim ((FreeGroup.of_ne_one z₁) hz1)
    | finalSource z₂ hsource₂ hz₂ =>
        exact False.elim (BoundaryWords.Internal.freeGroup_of_ne_inv z₂ z₁ (hsource₂.2.2.symm.trans htarget₁.2.2))
    | finalTarget z₂ htarget₂ hz₂ =>
        have hz : z₁ = z₂ := FreeGroup.of_injective <| by
          apply inv_injective
          exact htarget₁.2.2.symm.trans htarget₂.2.2
        exact False.elim (hz₂ (hz ▸ hz₁))
    | treeSource z₂ hsource₂ hz₂ =>
        exact False.elim (BoundaryWords.Internal.freeGroup_of_ne_inv z₂ z₁ (hsource₂.2.2.symm.trans htarget₁.2.2))
    | treeTarget z₂ htarget₂ hz₂ =>
        have hz : z₁ = z₂ := FreeGroup.of_injective <| by
          apply inv_injective
          exact htarget₁.2.2.symm.trans htarget₂.2.2
        subst z₂
        rfl

theorem BoundaryWords.Internal.canonicalProjectivePostConeRawRootContourTermCase_nonempty
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide) :
    Nonempty (CanonicalProjectivePostConeRawRootContourTermCase hp hp2 q s) := by
  rcases canonicalProjectiveConePostConeBoundaryTerm_eq_one_or_physicalCarrier hp hp2 q s with
    hterm | ⟨z, hsource | htarget⟩
  · exact ⟨.one hterm⟩
  · by_cases hz : isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z
    · exact ⟨.treeSource z hsource hz⟩
    · exact ⟨.finalSource z hsource hz⟩
  · by_cases hz : isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z
    · exact ⟨.treeTarget z htarget hz⟩
    · exact ⟨.finalTarget z htarget hz⟩

/-- Choose the literal source/target classification of a root-boundary term. -/
noncomputable def canonicalProjectivePostConeRawRootContourTermCase
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide) :
    CanonicalProjectivePostConeRawRootContourTermCase hp hp2 q s :=
  Classical.choice
    (BoundaryWords.Internal.canonicalProjectivePostConeRawRootContourTermCase_nonempty hp hp2 q s)

/-- Turn a classified root-boundary term into its unreduced signed list. -/
noncomputable def canonicalProjectivePostConeRawRootContourTermOfCase
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide)
    (c : CanonicalProjectivePostConeRawRootContourTermCase hp hp2 q s) :
    List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool) :=
  match c with
  | .one _ => []
  | .finalSource z _ hz => [(⟨z, hz⟩, true)]
  | .finalTarget z _ hz => [(⟨z, hz⟩, false)]
  | .treeSource z _ hz =>
      canonicalProjectivePostConeRawTreeWordBySlot hp hp2
        (canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz)
  | .treeTarget z _ hz => FreeGroup.invRev
      (canonicalProjectivePostConeRawTreeWordBySlot hp hp2
        (canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz))

private theorem canonicalProjectivePostConeRawRoot_source_eq_one_false
    {α : Type*} (x : α) (h : FreeGroup.of x = 1) : False :=
  (FreeGroup.of_ne_one x) h

private theorem canonicalProjectivePostConeRawRoot_target_eq_one_false
    {α : Type*} (x : α) (h : (FreeGroup.of x)⁻¹ = 1) : False :=
  canonicalProjectivePostConeRawRoot_source_eq_one_false x (inv_eq_one.mp h)

private theorem canonicalProjectivePostConeRawRoot_source_eq_target_false
    {α : Type*} (x y : α)
    (h : FreeGroup.of x = (FreeGroup.of y)⁻¹) : False := by
  classical
  have hword := congrArg FreeGroup.toWord h
  simp only [FreeGroup.toWord_of, FreeGroup.toWord_inv] at hword
  simp [FreeGroup.invRev] at hword

private theorem canonicalProjectivePostConeRawRoot_target_eq_source_false
    {α : Type*} (x y : α)
    (h : (FreeGroup.of x)⁻¹ = FreeGroup.of y) : False :=
  canonicalProjectivePostConeRawRoot_source_eq_target_false y x h.symm

private theorem canonicalProjectivePostConeRawRoot_target_eq_target_injective
    {α : Type*} (x y : α)
    (h : (FreeGroup.of x)⁻¹ = (FreeGroup.of y)⁻¹) : x = y := by
  apply FreeGroup.of_injective
  exact congrArg Inv.inv h

/-- A non-pivot target dart retains the negative literal of its final
physical edge in the local tree-slot expansion. -/
theorem canonicalProjectivePostConeRawContourTerm_eq_target_letter
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (ih : ∀ other : CanonicalProjectivePostConeTreeSlot hp hp2,
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool))
    (z : CanonicalProjectiveConeKeptSymbol p)
    (hz : ¬ isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z)
    (hface : (⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p) =
      projectivePolygonPostConeEdgeTarget z)
    (hs : projectivePolygonPostConeEdgeTargetSide z ≠
      canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot) :
    canonicalProjectivePostConeRawContourTerm hp hp2 slot ih
      (projectivePolygonPostConeEdgeTargetSide z) = [(⟨z, hz⟩, false)] := by
  classical
  have hstate : slot.right.state = (projectivePolygonPostConeEdgeTarget z).state :=
    congrArg ProjectivePolygonPostConeFace.state hface
  have hterm : canonicalProjectiveConePostConeBoundaryTerm p slot.right.state
      (projectivePolygonPostConeEdgeTargetSide z) = (FreeGroup.of z)⁻¹ := by
    rw [hstate]
    exact canonicalProjectiveConePostConeBoundaryTerm_edgeTarget_eq_inv hp hp2 z
  rcases canonicalProjectivePostConeRawContourTerm_expansion hp hp2 slot ih
      (projectivePolygonPostConeEdgeTargetSide z) hs with hOne | hSource | hTarget |
      hDeepSource | hDeepTarget
  · exact False.elim (canonicalProjectivePostConeRawRoot_target_eq_one_false z
      (hterm.symm.trans hOne.2))
  · rcases hSource with ⟨z', hz', hcarrier, _⟩
    exact False.elim (canonicalProjectivePostConeRawRoot_target_eq_source_false z z'
      (hterm.symm.trans hcarrier.2.2))
  · rcases hTarget with ⟨z', hz', hcarrier, hlist⟩
    have hzz : z' = z := canonicalProjectivePostConeRawRoot_target_eq_target_injective
      z' z (hcarrier.2.2.symm.trans hterm)
    subst z'
    simpa using hlist
  · rcases hDeepSource with ⟨z', other, hdeep, hcarrier, hlabel, _⟩
    exact False.elim (canonicalProjectivePostConeRawRoot_target_eq_source_false z z'
      (hterm.symm.trans hcarrier.2.2))
  · rcases hDeepTarget with ⟨z', other, hdeep, hcarrier, hlabel, _⟩
    have hzz : z' = z := canonicalProjectivePostConeRawRoot_target_eq_target_injective
      z' z (hcarrier.2.2.symm.trans hterm)
    exact (hz ⟨other, hlabel.trans hzz⟩).elim

/-- Any two certified root-term classifications at paired darts produce
literally inverse-reversed lists.  Thus the use of `Classical.choice` in the
public raw expansion is harmless: physical-carrier and orientation data force
the chosen branch at the partner dart. -/
private theorem canonicalProjectivePostConeRawRootContourTermOfCase_partner_eq_invRev
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide)
    (c : CanonicalProjectivePostConeRawRootContourTermCase hp hp2 q s)
    (c' : CanonicalProjectivePostConeRawRootContourTermCase hp hp2
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).1
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).2) :
    canonicalProjectivePostConeRawRootContourTermOfCase hp hp2
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).1
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).2 c' =
      FreeGroup.invRev (canonicalProjectivePostConeRawRootContourTermOfCase hp hp2 q s c) := by
  classical
  have hpair := canonicalProjectiveConePostConeBoundaryTerm_partner_eq_inv hp hp2 q s
  cases c with
  | one hone =>
    have hP : canonicalProjectiveConePostConeBoundaryTerm p
        ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).1
        ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).2 = 1 := by
      rw [hpair, hone]
      simp
    cases c' with
    | one hone' => rfl
    | finalSource z hsource hz =>
      exact (canonicalProjectivePostConeRawRoot_source_eq_one_false z
        (hsource.2.2.symm.trans hP)).elim
    | finalTarget z htarget hz =>
      exact (canonicalProjectivePostConeRawRoot_target_eq_one_false z
        (htarget.2.2.symm.trans hP)).elim
    | treeSource z hsource hz =>
      exact (canonicalProjectivePostConeRawRoot_source_eq_one_false z
        (hsource.2.2.symm.trans hP)).elim
    | treeTarget z htarget hz =>
      exact (canonicalProjectivePostConeRawRoot_target_eq_one_false z
        (htarget.2.2.symm.trans hP)).elim
  | finalSource z hsource hz =>
    have hP : canonicalProjectiveConePostConeBoundaryTerm p
        ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).1
        ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).2 =
        (FreeGroup.of z)⁻¹ := by
      rw [hpair, hsource.2.2]
    cases c' with
    | one hone' =>
      exact (canonicalProjectivePostConeRawRoot_target_eq_one_false z
        (hP.symm.trans hone')).elim
    | finalSource z' hsource' hz' =>
      exact (canonicalProjectivePostConeRawRoot_source_eq_target_false z' z
        (hsource'.2.2.symm.trans hP)).elim
    | finalTarget z' htarget' hz' =>
      have hzz : z' = z := canonicalProjectivePostConeRawRoot_target_eq_target_injective z' z
        (htarget'.2.2.symm.trans hP)
      subst z'
      rfl
    | treeSource z' hsource' hz' =>
      exact (canonicalProjectivePostConeRawRoot_source_eq_target_false z' z
        (hsource'.2.2.symm.trans hP)).elim
    | treeTarget z' htarget' hz' =>
      have hzz : z' = z := canonicalProjectivePostConeRawRoot_target_eq_target_injective z' z
        (htarget'.2.2.symm.trans hP)
      subst z'
      exact (hz hz').elim
  | finalTarget z htarget hz =>
    have hP : canonicalProjectiveConePostConeBoundaryTerm p
        ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).1
        ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).2 =
        FreeGroup.of z := by
      rw [hpair, htarget.2.2]
      simp
    cases c' with
    | one hone' =>
      exact (canonicalProjectivePostConeRawRoot_source_eq_one_false z
        (hP.symm.trans hone')).elim
    | finalSource z' hsource' hz' =>
      have hzz : z' = z := FreeGroup.of_injective (hsource'.2.2.symm.trans hP)
      subst z'
      rfl
    | finalTarget z' htarget' hz' =>
      exact (canonicalProjectivePostConeRawRoot_target_eq_source_false z' z
        (htarget'.2.2.symm.trans hP)).elim
    | treeSource z' hsource' hz' =>
      have hzz : z' = z := FreeGroup.of_injective (hsource'.2.2.symm.trans hP)
      subst z'
      exact (hz hz').elim
    | treeTarget z' htarget' hz' =>
      exact (canonicalProjectivePostConeRawRoot_target_eq_source_false z' z
        (htarget'.2.2.symm.trans hP)).elim
  | treeSource z hsource hz =>
    have hP : canonicalProjectiveConePostConeBoundaryTerm p
        ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).1
        ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).2 =
        (FreeGroup.of z)⁻¹ := by
      rw [hpair, hsource.2.2]
    cases c' with
    | one hone' =>
      exact (canonicalProjectivePostConeRawRoot_target_eq_one_false z
        (hP.symm.trans hone')).elim
    | finalSource z' hsource' hz' =>
      exact (canonicalProjectivePostConeRawRoot_source_eq_target_false z' z
        (hsource'.2.2.symm.trans hP)).elim
    | finalTarget z' htarget' hz' =>
      have hzz : z' = z := canonicalProjectivePostConeRawRoot_target_eq_target_injective z' z
        (htarget'.2.2.symm.trans hP)
      subst z'
      exact (hz' hz).elim
    | treeSource z' hsource' hz' =>
      exact (canonicalProjectivePostConeRawRoot_source_eq_target_false z' z
        (hsource'.2.2.symm.trans hP)).elim
    | treeTarget z' htarget' hz' =>
      have hzz : z' = z := canonicalProjectivePostConeRawRoot_target_eq_target_injective z' z
        (htarget'.2.2.symm.trans hP)
      subst z'
      rfl
  | treeTarget z htarget hz =>
    have hP : canonicalProjectiveConePostConeBoundaryTerm p
        ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).1
        ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).2 =
        FreeGroup.of z := by
      rw [hpair, htarget.2.2]
      simp
    cases c' with
    | one hone' =>
      exact (canonicalProjectivePostConeRawRoot_source_eq_one_false z
        (hP.symm.trans hone')).elim
    | finalSource z' hsource' hz' =>
      have hzz : z' = z := FreeGroup.of_injective (hsource'.2.2.symm.trans hP)
      subst z'
      exact (hz' hz).elim
    | finalTarget z' htarget' hz' =>
      exact (canonicalProjectivePostConeRawRoot_target_eq_source_false z' z
        (htarget'.2.2.symm.trans hP)).elim
    | treeSource z' hsource' hz' =>
      have hzz : z' = z := FreeGroup.of_injective (hsource'.2.2.symm.trans hP)
      subst z'
      simp only [canonicalProjectivePostConeRawRootContourTermOfCase]
      exact FreeGroup.invRev_invRev.symm
    | treeTarget z' htarget' hz' =>
      exact (canonicalProjectivePostConeRawRoot_target_eq_source_false z' z
        (htarget'.2.2.symm.trans hP)).elim

/-- The literal unreduced expansion of one root-boundary term. -/
noncomputable def canonicalProjectivePostConeRawRootContourTerm
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide) :
    List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool) :=
  canonicalProjectivePostConeRawRootContourTermOfCase hp hp2 q s
    (canonicalProjectivePostConeRawRootContourTermCase hp hp2 q s)

/-- The raw root-term expansion evaluates to direct final substitution. -/
theorem canonicalProjectivePostConeRawRootContourTerm_eval
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide) :
    FreeGroup.mk (canonicalProjectivePostConeRawRootContourTerm hp hp2 q s) =
      canonicalProjectivePostConeDirectFinalSubstitution hp hp2
        (canonicalProjectiveConePostConeBoundaryTerm p q s) := by
  classical
  cases hcase : canonicalProjectivePostConeRawRootContourTermCase hp hp2 q s with
  | one hterm =>
      simp only [canonicalProjectivePostConeRawRootContourTerm,
        canonicalProjectivePostConeRawRootContourTermOfCase, hcase]
      rw [hterm]
      simpa only [map_one] using (FreeGroup.one_eq_mk.symm :
        FreeGroup.mk ([] : List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool)) = 1)
  | finalSource z hsource hz =>
      simp only [canonicalProjectivePostConeRawRootContourTerm,
        canonicalProjectivePostConeRawRootContourTermOfCase, hcase]
      rw [hsource.2.2,
        canonicalProjectivePostConeDirectFinalSubstitution_of_kept hp hp2 ⟨z, hz⟩]
      rfl
  | finalTarget z htarget hz =>
      simp only [canonicalProjectivePostConeRawRootContourTerm,
        canonicalProjectivePostConeRawRootContourTermOfCase, hcase]
      rw [htarget.2.2, map_inv,
        canonicalProjectivePostConeDirectFinalSubstitution_of_kept hp hp2 ⟨z, hz⟩]
      rfl
  | treeSource z hsource hz =>
      simp only [canonicalProjectivePostConeRawRootContourTerm,
        canonicalProjectivePostConeRawRootContourTermOfCase, hcase]
      rw [hsource.2.2,
        canonicalProjectivePostConeDirectFinalSubstitution_of_deleted hp hp2 z hz]
      unfold canonicalProjectivePostConeDirectTreeEliminationWord
      exact canonicalProjectivePostConeRawTreeWordBySlot_eval hp hp2 _
  | treeTarget z htarget hz =>
      simp only [canonicalProjectivePostConeRawRootContourTerm,
        canonicalProjectivePostConeRawRootContourTermOfCase, hcase]
      rw [htarget.2.2, map_inv,
        canonicalProjectivePostConeDirectFinalSubstitution_of_deleted hp hp2 z hz,
        ← FreeGroup.inv_mk]
      unfold canonicalProjectivePostConeDirectTreeEliminationWord
      exact congrArg (fun w => w⁻¹)
        (canonicalProjectivePostConeRawTreeWordBySlot_eval hp hp2 _)

/-- Each root-term list preserves the classifier's literal source or target
occurrence, including the orientation used for a recursive tree splice. -/
theorem canonicalProjectivePostConeRawRootContourTerm_expansion
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide) :
    (canonicalProjectivePostConeRawRootContourTerm hp hp2 q s = [] ∧
      canonicalProjectiveConePostConeBoundaryTerm p q s = 1) ∨
    (∃ (z : CanonicalProjectiveConeKeptSymbol p)
        (hz : ¬ isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z),
        ((⟨q⟩ : ProjectivePolygonPostConeFace p) =
            projectivePolygonPostConeEdgeSource z ∧
          s = projectivePolygonPostConeEdgeSide z ∧
          canonicalProjectiveConePostConeBoundaryTerm p q s = FreeGroup.of z) ∧
        canonicalProjectivePostConeRawRootContourTerm hp hp2 q s = [(⟨z, hz⟩, true)]) ∨
    (∃ (z : CanonicalProjectiveConeKeptSymbol p)
        (hz : ¬ isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z),
        ((⟨q⟩ : ProjectivePolygonPostConeFace p) =
            projectivePolygonPostConeEdgeTarget z ∧
          s = projectivePolygonPostConeEdgeTargetSide z ∧
          canonicalProjectiveConePostConeBoundaryTerm p q s = (FreeGroup.of z)⁻¹) ∧
        canonicalProjectivePostConeRawRootContourTerm hp hp2 q s = [(⟨z, hz⟩, false)]) ∨
    (∃ (z : CanonicalProjectiveConeKeptSymbol p)
        (hz : isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z),
        ((⟨q⟩ : ProjectivePolygonPostConeFace p) =
            projectivePolygonPostConeEdgeSource z ∧
          s = projectivePolygonPostConeEdgeSide z ∧
          canonicalProjectiveConePostConeBoundaryTerm p q s = FreeGroup.of z) ∧
        canonicalProjectivePostConeRawRootContourTerm hp hp2 q s =
          canonicalProjectivePostConeRawTreeWordBySlot hp hp2
            (canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz)) ∨
    ∃ (z : CanonicalProjectiveConeKeptSymbol p)
      (hz : isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z),
      ((⟨q⟩ : ProjectivePolygonPostConeFace p) =
          projectivePolygonPostConeEdgeTarget z ∧
        s = projectivePolygonPostConeEdgeTargetSide z ∧
        canonicalProjectiveConePostConeBoundaryTerm p q s = (FreeGroup.of z)⁻¹) ∧
      canonicalProjectivePostConeRawRootContourTerm hp hp2 q s = FreeGroup.invRev
        (canonicalProjectivePostConeRawTreeWordBySlot hp hp2
          (canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz)) := by
  classical
  cases hcase : canonicalProjectivePostConeRawRootContourTermCase hp hp2 q s with
  | one hterm =>
      left
      refine ⟨?_, hterm⟩
      simp only [canonicalProjectivePostConeRawRootContourTerm,
        canonicalProjectivePostConeRawRootContourTermOfCase, hcase]
  | finalSource z hsource hz =>
      exact Or.inr (Or.inl ⟨z, hz, hsource, by
        simp only [canonicalProjectivePostConeRawRootContourTerm,
          canonicalProjectivePostConeRawRootContourTermOfCase, hcase]⟩)
  | finalTarget z htarget hz =>
      exact Or.inr (Or.inr (Or.inl ⟨z, hz, htarget, by
        simp only [canonicalProjectivePostConeRawRootContourTerm,
          canonicalProjectivePostConeRawRootContourTermOfCase, hcase]⟩))
  | treeSource z hsource hz =>
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨z, hz, hsource, by
        simp only [canonicalProjectivePostConeRawRootContourTerm,
          canonicalProjectivePostConeRawRootContourTermOfCase, hcase]⟩)))
  | treeTarget z htarget hz =>
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨z, hz, htarget, by
        simp only [canonicalProjectivePostConeRawRootContourTerm,
          canonicalProjectivePostConeRawRootContourTermOfCase, hcase]⟩)))

/-- A root-side term position records either its singleton final dart or the
exact position in the recursive child word. -/
def CanonicalProjectivePostConeRawRootContourTermPositionTag
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide)
    (c : CanonicalProjectivePostConeRawRootContourTermCase hp hp2 q s) : Type :=
  match c with
  | .one _ => Empty
  | .finalSource _ _ _ => Fin 1
  | .finalTarget _ _ _ => Fin 1
  | .treeSource z _ hz =>
      Fin (canonicalProjectivePostConeRawTreeWordBySlot hp hp2
        (canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz)).length
  | .treeTarget z _ hz =>
      Fin (canonicalProjectivePostConeRawTreeWordBySlot hp hp2
        (canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz)).length

/-- Positions in the classified root-side list are equivalent to their
singleton or child-word provenance tags. The target case inverts the position
transport for `invRev`, retaining the child word's original order. -/
noncomputable def canonicalProjectivePostConeRawRootContourTermOfCase_positionEquiv
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide)
    (c : CanonicalProjectivePostConeRawRootContourTermCase hp hp2 q s) :
    Fin (canonicalProjectivePostConeRawRootContourTermOfCase hp hp2 q s c).length ≃
      CanonicalProjectivePostConeRawRootContourTermPositionTag hp hp2 q s c := by
  cases c with
  | one hterm => exact finZeroEquiv
  | finalSource z hsource hz => exact Equiv.refl _
  | finalTarget z htarget hz => exact Equiv.refl _
  | treeSource z hsource hz => exact Equiv.refl _
  | treeTarget z htarget hz =>
      exact (Equiv.ofBijective
        (@invRevPosition _ (canonicalProjectivePostConeRawTreeWordBySlot hp hp2
          (canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz)))
        (invRevPosition_bijective _)).symm

/-- Reindex a position of the chosen root-side term by its provenance tag. -/
noncomputable def canonicalProjectivePostConeRawRootContourTerm_positionEquiv
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide) :
    Fin (canonicalProjectivePostConeRawRootContourTerm hp hp2 q s).length ≃
      CanonicalProjectivePostConeRawRootContourTermPositionTag hp hp2 q s
        (canonicalProjectivePostConeRawRootContourTermCase hp hp2 q s) := by
  change Fin (canonicalProjectivePostConeRawRootContourTermOfCase hp hp2 q s
      (canonicalProjectivePostConeRawRootContourTermCase hp hp2 q s)).length ≃ _
  exact canonicalProjectivePostConeRawRootContourTermOfCase_positionEquiv
    hp hp2 q s (canonicalProjectivePostConeRawRootContourTermCase hp hp2 q s)

/-- Interpret a root-side provenance tag as the physical endpoint dart and
orientation represented by that literal letter. -/
def canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    {q : BuserSarnakProjectiveReductionRange p} {s : ProjectivePolygonSide}
    (c : CanonicalProjectivePostConeRawRootContourTermCase hp hp2 q s) :
    CanonicalProjectivePostConeRawRootContourTermPositionTag hp hp2 q s c →
      Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
        (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool := by
  cases c with
  | one hterm => exact fun i => i.elim
  | finalSource z hsource hz => exact fun _ => (Sum.inl ⟨z, hz⟩, true)
  | finalTarget z htarget hz => exact fun _ => (Sum.inr ⟨z, hz⟩, false)
  | treeSource z hsource hz =>
      exact canonicalProjectivePostConeRawTreeWordPosition_endpoint hp hp2
        (canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz)
  | treeTarget z htarget hz =>
      let slot := canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz
      intro i
      exact
        let x := canonicalProjectivePostConeRawTreeWordPosition_endpoint hp hp2 slot i
        (x.1, !x.2)

/-- Reading a classified root-term position agrees exactly with the endpoint
and orientation decoded by its provenance tag. -/
theorem canonicalProjectivePostConeRawRootContourTermOfCase_positionEquiv_get
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    {q : BuserSarnakProjectiveReductionRange p} {s : ProjectivePolygonSide}
    (c : CanonicalProjectivePostConeRawRootContourTermCase hp hp2 q s)
    (i : Fin (canonicalProjectivePostConeRawRootContourTermOfCase hp hp2 q s c).length) :
    (canonicalProjectivePostConeRawRootContourTermOfCase hp hp2 q s c).get i =
      canonicalProjectivePostConeEndpointSignedLetter hp hp2
        (canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint
          hp hp2 c
          (canonicalProjectivePostConeRawRootContourTermOfCase_positionEquiv
            hp hp2 q s c i)) := by
  cases c with
  | one hterm => exact Fin.elim0 i
  | finalSource z hsource hz =>
      change Fin 1 at i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      rfl
  | finalTarget z htarget hz =>
      change Fin 1 at i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      rfl
  | treeSource z hsource hz =>
      exact canonicalProjectivePostConeRawTreeWordPosition_endpoint_get hp hp2
        (canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz) i
  | treeTarget z htarget hz =>
      let slot := canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz
      let word := canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot
      let e := Equiv.ofBijective (@invRevPosition _ word) (invRevPosition_bijective word)
      simp only [canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint,
        canonicalProjectivePostConeRawRootContourTermOfCase_positionEquiv,
        canonicalProjectivePostConeRawRootContourTermOfCase]
      have hi : invRevPosition (e.symm i) = i := e.apply_symm_apply i
      change (FreeGroup.invRev word).get i =
        canonicalProjectivePostConeEndpointSignedLetter hp hp2
          (let x := canonicalProjectivePostConeRawTreeWordPosition_endpoint
            hp hp2 slot (e.symm i)
          (x.1, !x.2))
      calc
        (FreeGroup.invRev word).get i =
            (FreeGroup.invRev word).get (invRevPosition (e.symm i)) :=
          congrArg (FreeGroup.invRev word).get hi.symm
        _ = ((word.get (e.symm i)).1, !(word.get (e.symm i)).2) :=
          get_invRevPosition word (e.symm i)
        _ = canonicalProjectivePostConeEndpointSignedLetter hp hp2
            (let x := canonicalProjectivePostConeRawTreeWordPosition_endpoint
              hp hp2 slot (e.symm i); (x.1, !x.2)) := by
          simpa [canonicalProjectivePostConeEndpointSignedLetter] using
            congrArg (fun x : CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool =>
              (x.1, !x.2))
                (canonicalProjectivePostConeRawTreeWordPosition_endpoint_get
                  hp hp2 slot (e.symm i))

/-- The chosen root-side term has the same exact position decoder as its
classified list. -/
theorem canonicalProjectivePostConeRawRootContourTerm_positionEquiv_get
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide)
    (i : Fin (canonicalProjectivePostConeRawRootContourTerm hp hp2 q s).length) :
    (canonicalProjectivePostConeRawRootContourTerm hp hp2 q s).get i =
      canonicalProjectivePostConeEndpointSignedLetter hp hp2
        (canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint
          hp hp2 (canonicalProjectivePostConeRawRootContourTermCase hp hp2 q s)
          (canonicalProjectivePostConeRawRootContourTerm_positionEquiv
            hp hp2 q s i)) := by
  change (canonicalProjectivePostConeRawRootContourTermOfCase hp hp2 q s
    (canonicalProjectivePostConeRawRootContourTermCase hp hp2 q s)).get i = _
  exact canonicalProjectivePostConeRawRootContourTermOfCase_positionEquiv_get
    hp hp2 (canonicalProjectivePostConeRawRootContourTermCase hp hp2 q s) i

/-- Concatenate literal root-term expansions without free reduction. -/
noncomputable def canonicalProjectivePostConeRawRootContourTerms
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) :
    List ProjectivePolygonSide →
      List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool)
  | [] => []
  | s :: ss => canonicalProjectivePostConeRawRootContourTerm hp hp2 q s ++
      canonicalProjectivePostConeRawRootContourTerms hp hp2 q ss

/-- A nested tag records which side occurrence in a root-side list owns a
raw position, together with its position within that side's term. -/
def CanonicalProjectivePostConeRawRootContourTermsPositionTag
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) : List ProjectivePolygonSide → Type
  | [] => Empty
  | s :: ss =>
      Fin (canonicalProjectivePostConeRawRootContourTerm hp hp2 q s).length ⊕
        CanonicalProjectivePostConeRawRootContourTermsPositionTag hp hp2 q ss

/-- Every position in a root-side list expansion is equivalent to its
side-occurrence and within-term position tag. -/
noncomputable def canonicalProjectivePostConeRawRootContourTerms_positionEquiv
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) :
    (sides : List ProjectivePolygonSide) →
      Fin (canonicalProjectivePostConeRawRootContourTerms hp hp2 q sides).length ≃
        CanonicalProjectivePostConeRawRootContourTermsPositionTag hp hp2 q sides
  | [] => finZeroEquiv
  | s :: ss =>
      (canonicalProjectivePostConeRawAppendPositionSplit
        (canonicalProjectivePostConeRawRootContourTerm hp hp2 q s)
        (canonicalProjectivePostConeRawRootContourTerms hp hp2 q ss)).trans
        (Equiv.sumCongr (Equiv.refl _)
          (canonicalProjectivePostConeRawRootContourTerms_positionEquiv hp hp2 q ss))

/-- Splitting the root-side list at its head recovers a position in either
the head term or the remaining side-list expansion. -/
theorem canonicalProjectivePostConeRawRootContourTerms_get_cons_left
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide) (ss : List ProjectivePolygonSide)
    (i : Fin (canonicalProjectivePostConeRawRootContourTerm hp hp2 q s).length) :
    (canonicalProjectivePostConeRawRootContourTerms hp hp2 q (s :: ss)).get
      ((canonicalProjectivePostConeRawAppendPositionSplit
        (canonicalProjectivePostConeRawRootContourTerm hp hp2 q s)
        (canonicalProjectivePostConeRawRootContourTerms hp hp2 q ss)).symm
        (Sum.inl i)) =
      (canonicalProjectivePostConeRawRootContourTerm hp hp2 q s).get i := by
  change (canonicalProjectivePostConeRawRootContourTerm hp hp2 q s ++
    canonicalProjectivePostConeRawRootContourTerms hp hp2 q ss).get _ = _
  exact canonicalProjectivePostConeRawAppendPositionSplit_get_left _ _ i

theorem canonicalProjectivePostConeRawRootContourTerms_get_cons_right
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide) (ss : List ProjectivePolygonSide)
    (i : Fin (canonicalProjectivePostConeRawRootContourTerms hp hp2 q ss).length) :
    (canonicalProjectivePostConeRawRootContourTerms hp hp2 q (s :: ss)).get
      ((canonicalProjectivePostConeRawAppendPositionSplit
        (canonicalProjectivePostConeRawRootContourTerm hp hp2 q s)
        (canonicalProjectivePostConeRawRootContourTerms hp hp2 q ss)).symm
        (Sum.inr i)) =
      (canonicalProjectivePostConeRawRootContourTerms hp hp2 q ss).get i := by
  change (canonicalProjectivePostConeRawRootContourTerm hp hp2 q s ++
    canonicalProjectivePostConeRawRootContourTerms hp hp2 q ss).get _ = _
  exact canonicalProjectivePostConeRawAppendPositionSplit_get_right _ _ i

/-- Decode a root-side-list tag to the physical endpoint and orientation of
its represented literal occurrence. -/
noncomputable def canonicalProjectivePostConeRawRootContourTermsPositionTag_endpoint
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) :
    (sides : List ProjectivePolygonSide) →
      CanonicalProjectivePostConeRawRootContourTermsPositionTag hp hp2 q sides →
        Sum (CanonicalProjectivePostConeFinalGenerator hp hp2)
          (CanonicalProjectivePostConeFinalGenerator hp hp2) × Bool
  | [] => fun tag => tag.elim
  | s :: ss => fun tag =>
      Sum.elim
        (fun i =>
          canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint hp hp2
            (canonicalProjectivePostConeRawRootContourTermCase hp hp2 q s)
            ((canonicalProjectivePostConeRawRootContourTerm_positionEquiv hp hp2 q s) i))
        (canonicalProjectivePostConeRawRootContourTermsPositionTag_endpoint hp hp2 q ss)
        tag

/-- Select the directed root-side occurrence recorded by a nested position
tag. Repeated side values in a general list remain distinguished by the tag's
sum path. -/
def canonicalProjectivePostConeRawRootContourTermsPositionTag_side
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) :
    (sides : List ProjectivePolygonSide) →
      CanonicalProjectivePostConeRawRootContourTermsPositionTag hp hp2 q sides →
        ProjectivePolygonSide
  | [], tag => tag.elim
  | s :: ss, tag =>
      Sum.elim (fun _ => s)
        (canonicalProjectivePostConeRawRootContourTermsPositionTag_side hp hp2 q ss)
        tag

/-- The side projection of a nested root-side tag always belongs to the
ordered list from which that tag was built. -/
theorem canonicalProjectivePostConeRawRootContourTermsPositionTag_side_mem
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p)
    (sides : List ProjectivePolygonSide)
    (tag : CanonicalProjectivePostConeRawRootContourTermsPositionTag hp hp2 q sides) :
    canonicalProjectivePostConeRawRootContourTermsPositionTag_side hp hp2 q sides tag ∈
      sides := by
  induction sides with
  | nil => cases tag
  | cons s ss ih =>
      cases tag with
      | inl head => simp [canonicalProjectivePostConeRawRootContourTermsPositionTag_side]
      | inr tail =>
          change canonicalProjectivePostConeRawRootContourTermsPositionTag_side
            hp hp2 q ss tail ∈ s :: ss
          simp only [List.mem_cons]
          exact Or.inr (ih tail)

/-- Any side occurrence in a root-side list can be retained as a nested tag
without losing its local term position. -/
theorem canonicalProjectivePostConeRawRootContourTermsPositionTag_exists_of_mem
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p)
    (sides : List ProjectivePolygonSide) (s : ProjectivePolygonSide)
    (hs : s ∈ sides)
    (i : Fin (canonicalProjectivePostConeRawRootContourTerm hp hp2 q s).length) :
    ∃ tag : CanonicalProjectivePostConeRawRootContourTermsPositionTag hp hp2 q sides,
      canonicalProjectivePostConeRawRootContourTermsPositionTag_endpoint hp hp2 q
        sides tag =
        canonicalProjectivePostConeRawRootContourTermPositionTag_endpoint hp hp2
          (canonicalProjectivePostConeRawRootContourTermCase hp hp2 q s)
          ((canonicalProjectivePostConeRawRootContourTerm_positionEquiv hp hp2 q s) i) := by
  induction sides generalizing s i with
  | nil => cases hs
  | cons t ts ih =>
      rcases List.mem_cons.mp hs with hst | htail
      · subst t
        exact ⟨Sum.inl i, rfl⟩
      · obtain ⟨tag, htag⟩ := ih s htail i
        exact ⟨Sum.inr tag, htag⟩

/-- Every root-side-list occurrence decodes to its exact physical dart and
orientation in the concatenated unreduced root expansion. -/
theorem canonicalProjectivePostConeRawRootContourTerms_positionEquiv_get
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p)
    (sides : List ProjectivePolygonSide)
    (tag : CanonicalProjectivePostConeRawRootContourTermsPositionTag hp hp2 q sides) :
    (canonicalProjectivePostConeRawRootContourTerms hp hp2 q sides).get
      ((canonicalProjectivePostConeRawRootContourTerms_positionEquiv
        hp hp2 q sides).symm tag) =
      canonicalProjectivePostConeEndpointSignedLetter hp hp2
        (canonicalProjectivePostConeRawRootContourTermsPositionTag_endpoint
          hp hp2 q sides tag) := by
  induction sides with
  | nil => cases tag
  | cons s ss ihs =>
      cases tag with
      | inl head =>
          have hindex :
              (canonicalProjectivePostConeRawRootContourTerms_positionEquiv
                hp hp2 q (s :: ss)).symm (Sum.inl head) =
                (canonicalProjectivePostConeRawAppendPositionSplit
                  (canonicalProjectivePostConeRawRootContourTerm hp hp2 q s)
                  (canonicalProjectivePostConeRawRootContourTerms hp hp2 q ss)).symm
                  (Sum.inl head) := by
            change (canonicalProjectivePostConeRawAppendPositionSplit
                (canonicalProjectivePostConeRawRootContourTerm hp hp2 q s)
                (canonicalProjectivePostConeRawRootContourTerms hp hp2 q ss)).symm
                ((Equiv.sumCongr (Equiv.refl _)
                  (canonicalProjectivePostConeRawRootContourTerms_positionEquiv
                    hp hp2 q ss)).symm (Sum.inl head)) = _
            congr 1
          rw [hindex, canonicalProjectivePostConeRawRootContourTerms_get_cons_left]
          exact canonicalProjectivePostConeRawRootContourTerm_positionEquiv_get
            hp hp2 q s head
      | inr tail =>
          have hindex :
              (canonicalProjectivePostConeRawRootContourTerms_positionEquiv
                hp hp2 q (s :: ss)).symm (Sum.inr tail) =
                (canonicalProjectivePostConeRawAppendPositionSplit
                  (canonicalProjectivePostConeRawRootContourTerm hp hp2 q s)
                  (canonicalProjectivePostConeRawRootContourTerms hp hp2 q ss)).symm
                  (Sum.inr ((canonicalProjectivePostConeRawRootContourTerms_positionEquiv
                    hp hp2 q ss).symm tail)) := by
            change (canonicalProjectivePostConeRawAppendPositionSplit
                (canonicalProjectivePostConeRawRootContourTerm hp hp2 q s)
                (canonicalProjectivePostConeRawRootContourTerms hp hp2 q ss)).symm
                ((Equiv.sumCongr (Equiv.refl _)
                  (canonicalProjectivePostConeRawRootContourTerms_positionEquiv
                    hp hp2 q ss)).symm (Sum.inr tail)) = _
            congr 1
          rw [hindex, canonicalProjectivePostConeRawRootContourTerms_get_cons_right]
          exact ihs tail

/-- At the root's physical source side, the deterministic root classifier
selects the matching final-source case. -/
theorem canonicalProjectivePostConeRawRootContourTermCase_eq_finalSource_of_root_source
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : CanonicalProjectiveConeKeptSymbol p)
    (hz : ¬ isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z)
    (hroot : projectivePolygonPostConeEdgeSource z =
      canonicalProjectivePostConeTreeRoot hp hp2) :
    canonicalProjectivePostConeRawRootContourTermCase hp hp2
      (canonicalProjectivePostConeTreeRoot hp hp2).state
      (projectivePolygonPostConeEdgeSide z) =
      .finalSource z ⟨by
        let root := canonicalProjectivePostConeTreeRoot hp hp2
        have hrootState : (⟨root.state⟩ : ProjectivePolygonPostConeFace p) = root :=
          ProjectivePolygonPostConeFace.stateEquiv.symm_apply_apply root
        exact hrootState.trans hroot.symm,
        rfl, by
          have hstate := congrArg ProjectivePolygonPostConeFace.state hroot
          rw [← hstate]
          exact canonicalProjectiveConePostConeBoundaryTerm_edgeSource_eq z⟩ hz := by
  apply canonicalProjectivePostConeRawRootContourTermCase_unique hp hp2

/-- Target-oriented root incidence selects the matching final-target case. -/
theorem canonicalProjectivePostConeRawRootContourTermCase_eq_finalTarget_of_root_target
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : CanonicalProjectiveConeKeptSymbol p)
    (hz : ¬ isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z)
    (hroot : projectivePolygonPostConeEdgeTarget z =
      canonicalProjectivePostConeTreeRoot hp hp2) :
    canonicalProjectivePostConeRawRootContourTermCase hp hp2
      (canonicalProjectivePostConeTreeRoot hp hp2).state
      (projectivePolygonPostConeEdgeTargetSide z) =
      .finalTarget z ⟨by
        let root := canonicalProjectivePostConeTreeRoot hp hp2
        have hrootState : (⟨root.state⟩ : ProjectivePolygonPostConeFace p) = root :=
          ProjectivePolygonPostConeFace.stateEquiv.symm_apply_apply root
        exact hrootState.trans hroot.symm,
        rfl, by
          have hstate := congrArg ProjectivePolygonPostConeFace.state hroot
          rw [← hstate]
          exact canonicalProjectiveConePostConeBoundaryTerm_edgeTarget_eq_inv hp hp2 z⟩ hz := by
  apply canonicalProjectivePostConeRawRootContourTermCase_unique hp hp2

/-- At the root face, a deleted tree edge on its source side selects the
root classifier's tree-source case. -/
theorem canonicalProjectivePostConeRawRootContourTermCase_eq_treeSource_of_root_source
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : CanonicalProjectiveConeKeptSymbol p)
    (hz : isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z)
    (hroot : projectivePolygonPostConeEdgeSource z =
      canonicalProjectivePostConeTreeRoot hp hp2) :
    canonicalProjectivePostConeRawRootContourTermCase hp hp2
      (canonicalProjectivePostConeTreeRoot hp hp2).state
      (projectivePolygonPostConeEdgeSide z) =
      .treeSource z ⟨by
        let root := canonicalProjectivePostConeTreeRoot hp hp2
        have hrootState : (⟨root.state⟩ : ProjectivePolygonPostConeFace p) = root :=
          ProjectivePolygonPostConeFace.stateEquiv.symm_apply_apply root
        exact hrootState.trans hroot.symm,
        rfl, by
          have hstate := congrArg ProjectivePolygonPostConeFace.state hroot
          rw [← hstate]
          exact canonicalProjectiveConePostConeBoundaryTerm_edgeSource_eq z⟩ hz := by
  apply canonicalProjectivePostConeRawRootContourTermCase_unique hp hp2

/-- Target-oriented root incidence selects the root classifier's
tree-target case. -/
theorem canonicalProjectivePostConeRawRootContourTermCase_eq_treeTarget_of_root_target
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : CanonicalProjectiveConeKeptSymbol p)
    (hz : isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z)
    (hroot : projectivePolygonPostConeEdgeTarget z =
      canonicalProjectivePostConeTreeRoot hp hp2) :
    canonicalProjectivePostConeRawRootContourTermCase hp hp2
      (canonicalProjectivePostConeTreeRoot hp hp2).state
      (projectivePolygonPostConeEdgeTargetSide z) =
      .treeTarget z ⟨by
        let root := canonicalProjectivePostConeTreeRoot hp hp2
        have hrootState : (⟨root.state⟩ : ProjectivePolygonPostConeFace p) = root :=
          ProjectivePolygonPostConeFace.stateEquiv.symm_apply_apply root
        exact hrootState.trans hroot.symm,
        rfl, by
          have hstate := congrArg ProjectivePolygonPostConeFace.state hroot
          rw [← hstate]
          exact canonicalProjectiveConePostConeBoundaryTerm_edgeTarget_eq_inv hp hp2 z⟩ hz := by
  apply canonicalProjectivePostConeRawRootContourTermCase_unique hp hp2

/-- Every retained physical edge contributes its positive letter literally
at its source dart, before the face terms are concatenated. -/
theorem canonicalProjectivePostConeRawRootContourTerm_eq_source_letter
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : CanonicalProjectiveConeKeptSymbol p)
    (hz : ¬ isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z) :
    canonicalProjectivePostConeRawRootContourTerm hp hp2
      (projectivePolygonPostConeEdgeSource z).state
      (projectivePolygonPostConeEdgeSide z) = [(⟨z, hz⟩, true)] := by
  have hterm := canonicalProjectiveConePostConeBoundaryTerm_edgeSource_eq z
  cases hcase : canonicalProjectivePostConeRawRootContourTermCase hp hp2
      (projectivePolygonPostConeEdgeSource z).state
      (projectivePolygonPostConeEdgeSide z) with
  | one hone =>
      exact (canonicalProjectivePostConeRawRoot_source_eq_one_false z
        (hterm.symm.trans hone)).elim
  | finalSource z' hsource hz' =>
      have hzz : z' = z := FreeGroup.of_injective (hsource.2.2.symm.trans hterm)
      subst z'
      simp [canonicalProjectivePostConeRawRootContourTerm,
        canonicalProjectivePostConeRawRootContourTermOfCase, hcase]
  | finalTarget z' htarget hz' =>
      exact (canonicalProjectivePostConeRawRoot_source_eq_target_false z z'
        (hterm.symm.trans htarget.2.2)).elim
  | treeSource z' hsource hz' =>
      have hzz : z' = z := FreeGroup.of_injective (hsource.2.2.symm.trans hterm)
      subst z'
      exact (hz hz').elim
  | treeTarget z' htarget hz' =>
      exact (canonicalProjectivePostConeRawRoot_source_eq_target_false z z'
        (hterm.symm.trans htarget.2.2)).elim

/-- Every retained physical edge contributes its negative literal at the
paired target dart, before face terms are concatenated. -/
theorem canonicalProjectivePostConeRawRootContourTerm_eq_target_letter
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : CanonicalProjectiveConeKeptSymbol p)
    (hz : ¬ isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z) :
    canonicalProjectivePostConeRawRootContourTerm hp hp2
      (projectivePolygonPostConeEdgeTarget z).state
      (projectivePolygonPostConeEdgeTargetSide z) = [(⟨z, hz⟩, false)] := by
  have hterm := canonicalProjectiveConePostConeBoundaryTerm_edgeTarget_eq_inv hp hp2 z
  cases hcase : canonicalProjectivePostConeRawRootContourTermCase hp hp2
      (projectivePolygonPostConeEdgeTarget z).state
      (projectivePolygonPostConeEdgeTargetSide z) with
  | one hone =>
      exact (canonicalProjectivePostConeRawRoot_target_eq_one_false z
        (hterm.symm.trans hone)).elim
  | finalSource z' hsource hz' =>
      exact (canonicalProjectivePostConeRawRoot_target_eq_source_false z z'
        (hterm.symm.trans hsource.2.2)).elim
  | finalTarget z' htarget hz' =>
      have hzz : z' = z := canonicalProjectivePostConeRawRoot_target_eq_target_injective
        z' z (htarget.2.2.symm.trans hterm)
      subst z'
      simp [canonicalProjectivePostConeRawRootContourTerm,
        canonicalProjectivePostConeRawRootContourTermOfCase, hcase]
  | treeSource z' hsource hz' =>
      exact (canonicalProjectivePostConeRawRoot_target_eq_source_false z z'
        (hterm.symm.trans hsource.2.2)).elim
  | treeTarget z' htarget hz' =>
      have hzz : z' = z := canonicalProjectivePostConeRawRoot_target_eq_target_injective
        z' z (htarget.2.2.symm.trans hterm)
      subst z'
      exact (hz hz').elim

/-- The signed multiplicity of a generator in a root-boundary expansion is
the sum of its multiplicities in the individual side expansions. -/
theorem canonicalProjectivePostConeRawRootContourTerms_signedOccurrenceCount
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p)
    (sides : List ProjectivePolygonSide)
    [DecidableEq (CanonicalProjectivePostConeFinalGenerator hp hp2)]
    (z : CanonicalProjectivePostConeFinalGenerator hp hp2) (positive : Bool) :
    signedOccurrenceCount z positive
        (canonicalProjectivePostConeRawRootContourTerms hp hp2 q sides) =
      (sides.map fun s => signedOccurrenceCount z positive
        (canonicalProjectivePostConeRawRootContourTerm hp hp2 q s)).sum := by
  classical
  induction sides with
  | nil => rfl
  | cons side sides ih =>
      simp only [canonicalProjectivePostConeRawRootContourTerms,
        List.map_cons, List.sum_cons]
      rw [signedOccurrenceCount_append, ih]

private theorem canonicalProjectivePostConeRawRootContourTerms_eval
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (sides : List ProjectivePolygonSide) :
    FreeGroup.mk (canonicalProjectivePostConeRawRootContourTerms hp hp2 q sides) =
      (List.map (fun s => canonicalProjectivePostConeDirectFinalSubstitution hp hp2
        (canonicalProjectiveConePostConeBoundaryTerm p q s)) sides).prod := by
  induction sides with
  | nil => exact FreeGroup.one_eq_mk.symm
  | cons s sides hind =>
      simp only [canonicalProjectivePostConeRawRootContourTerms, List.map_cons,
        List.prod_cons]
      rw [← FreeGroup.mul_mk,
        canonicalProjectivePostConeRawRootContourTerm_eval hp hp2 q s, hind]

/-- The global root boundary contour after recursively splicing tree slots,
stored as an unreduced signed list on the final alphabet. -/
noncomputable def canonicalProjectivePostConeRawRootContour
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool) :=
  canonicalProjectivePostConeRawRootContourTerms hp hp2
    (canonicalProjectivePostConeTreeRoot hp hp2).state
    canonicalProjectivePostConeBoundarySideCycle

/-- Every literal position in the global root contour has a nested origin
tag recording its root-face side and the physical dart at the end of its
recursive splice. This is the position decoder for the eight-side assembly;
proving its endpoint map is bijective is the remaining global exhaustion
step. -/
noncomputable def canonicalProjectivePostConeRawRootContour_positionEquiv
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    Fin (canonicalProjectivePostConeRawRootContour hp hp2).length ≃
      CanonicalProjectivePostConeRawRootContourTermsPositionTag hp hp2
        (canonicalProjectivePostConeTreeRoot hp hp2).state
        canonicalProjectivePostConeBoundarySideCycle := by
  exact canonicalProjectivePostConeRawRootContourTerms_positionEquiv hp hp2
    (canonicalProjectivePostConeTreeRoot hp hp2).state
    canonicalProjectivePostConeBoundarySideCycle

/-- The root-contour position decoder reads the same signed letter as its
physical endpoint origin. -/
theorem canonicalProjectivePostConeRawRootContour_positionEquiv_get
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (tag : CanonicalProjectivePostConeRawRootContourTermsPositionTag hp hp2
      (canonicalProjectivePostConeTreeRoot hp hp2).state
      canonicalProjectivePostConeBoundarySideCycle) :
    (canonicalProjectivePostConeRawRootContour hp hp2).get
      ((canonicalProjectivePostConeRawRootContour_positionEquiv hp hp2).symm tag) =
      canonicalProjectivePostConeEndpointSignedLetter hp hp2
        (canonicalProjectivePostConeRawRootContourTermsPositionTag_endpoint hp hp2
          (canonicalProjectivePostConeTreeRoot hp hp2).state
          canonicalProjectivePostConeBoundarySideCycle tag) := by
  exact canonicalProjectivePostConeRawRootContourTerms_positionEquiv_get hp hp2
    (canonicalProjectivePostConeTreeRoot hp hp2).state
    canonicalProjectivePostConeBoundarySideCycle tag

/-- The root-contour multiplicity is the sum of the eight explicit
root-boundary side-term multiplicities. -/
theorem canonicalProjectivePostConeRawRootContour_signedOccurrenceCount
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    [DecidableEq (CanonicalProjectivePostConeFinalGenerator hp hp2)]
    (z : CanonicalProjectivePostConeFinalGenerator hp hp2) (positive : Bool) :
    signedOccurrenceCount z positive
        (canonicalProjectivePostConeRawRootContour hp hp2) =
      (canonicalProjectivePostConeBoundarySideCycle.map fun s =>
        signedOccurrenceCount z positive
          (canonicalProjectivePostConeRawRootContourTerm hp hp2
            (canonicalProjectivePostConeTreeRoot hp hp2).state s)).sum := by
  unfold canonicalProjectivePostConeRawRootContour
  exact canonicalProjectivePostConeRawRootContourTerms_signedOccurrenceCount
    hp hp2 (canonicalProjectivePostConeTreeRoot hp hp2).state
    canonicalProjectivePostConeBoundarySideCycle z positive

/-- Literal concatenation of the raw polygon boundary words over every
quotient face. This is an occurrence inventory before the dual-tree
contraction; it is not the final single-face relator. -/
noncomputable def canonicalProjectivePostConeRawAllFacesContour
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool) := by
  classical
  exact List.flatten ((Finset.univ : Finset (BuserSarnakProjectiveReductionRange p)).toList.map
    fun q => canonicalProjectivePostConeRawRootContourTerms hp hp2 q
      canonicalProjectivePostConeBoundarySideCycle)

private theorem canonicalProjectivePostConeRawRootContourTerms_mem_of_side_mem
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p)
    (sides : List ProjectivePolygonSide) (s : ProjectivePolygonSide)
    (letter : CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool)
    (hs : s ∈ sides)
    (hletter : letter ∈ canonicalProjectivePostConeRawRootContourTerm hp hp2 q s) :
    letter ∈ canonicalProjectivePostConeRawRootContourTerms hp hp2 q sides := by
  induction sides with
  | nil => simp at hs
  | cons t ts ih =>
      simp only [canonicalProjectivePostConeRawRootContourTerms, List.mem_append]
      rcases List.mem_cons.mp hs with hst | hst
      · subst t
        exact Or.inl hletter
      · exact Or.inr (ih hst)

/-- A retained generator whose physical source dart lies on the selected
root face remains a literal positive occurrence in the contracted root
contour.  The witness is obtained from its actual boundary side, rather
than from the all-face inventory. -/
theorem canonicalProjectivePostConeRawRootContour_exists_positive_occurrence_of_root_source
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : CanonicalProjectivePostConeFinalGenerator hp hp2)
    (hroot : (projectivePolygonPostConeEdgeSource z.1).state =
      (canonicalProjectivePostConeTreeRoot hp hp2).state) :
    ∃ i : Fin (canonicalProjectivePostConeRawRootContour hp hp2).length,
      (canonicalProjectivePostConeRawRootContour hp hp2).get i = (z, true) := by
  classical
  let q := (canonicalProjectivePostConeTreeRoot hp hp2).state
  let s := projectivePolygonPostConeEdgeSide z.1
  have hs : s ∈ canonicalProjectivePostConeBoundarySideCycle := by
    cases hgen : z.1.1.1.2 <;>
      simp [s, projectivePolygonPostConeEdgeSide,
        ProjectiveOctagonGenerator.positivePolygonSide,
        canonicalProjectivePostConeBoundarySideCycle, hgen]
  have hletter : (z, true) ∈ canonicalProjectivePostConeRawRootContourTerm hp hp2 q s := by
    rw [show q = (projectivePolygonPostConeEdgeSource z.1).state from hroot.symm]
    rw [canonicalProjectivePostConeRawRootContourTerm_eq_source_letter hp hp2 z.1 z.2]
    simp only [List.mem_singleton]
    apply Prod.ext
    · exact Subtype.ext rfl
    · rfl
  have hmem : (z, true) ∈ canonicalProjectivePostConeRawRootContourTerms hp hp2 q
      canonicalProjectivePostConeBoundarySideCycle :=
    canonicalProjectivePostConeRawRootContourTerms_mem_of_side_mem hp hp2 q
      canonicalProjectivePostConeBoundarySideCycle s (z, true) hs hletter
  rcases List.mem_iff_getElem.mp (by
      simpa [canonicalProjectivePostConeRawRootContour, q] using hmem) with
    ⟨i, hi, hget⟩
  exact ⟨⟨i, hi⟩, by simpa [canonicalProjectivePostConeRawRootContour] using hget⟩

/-- A retained generator whose physical target dart lies on the root face
contributes its literal negative occurrence to the contracted contour. -/
theorem canonicalProjectivePostConeRawRootContour_exists_negative_occurrence_of_root_target
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : CanonicalProjectivePostConeFinalGenerator hp hp2)
    (hroot : (projectivePolygonPostConeEdgeTarget z.1).state =
      (canonicalProjectivePostConeTreeRoot hp hp2).state) :
    ∃ i : Fin (canonicalProjectivePostConeRawRootContour hp hp2).length,
      (canonicalProjectivePostConeRawRootContour hp hp2).get i = (z, false) := by
  classical
  let q := (canonicalProjectivePostConeTreeRoot hp hp2).state
  let s := projectivePolygonPostConeEdgeTargetSide z.1
  have hs : s ∈ canonicalProjectivePostConeBoundarySideCycle := by
    cases s <;> simp [canonicalProjectivePostConeBoundarySideCycle]
  have hletter : (z, false) ∈ canonicalProjectivePostConeRawRootContourTerm hp hp2 q s := by
    rw [show q = (projectivePolygonPostConeEdgeTarget z.1).state from hroot.symm]
    rw [canonicalProjectivePostConeRawRootContourTerm_eq_target_letter hp hp2 z.1 z.2]
    simp only [List.mem_singleton]
    apply Prod.ext
    · exact Subtype.ext rfl
    · rfl
  have hmem : (z, false) ∈ canonicalProjectivePostConeRawRootContourTerms hp hp2 q
      canonicalProjectivePostConeBoundarySideCycle :=
    canonicalProjectivePostConeRawRootContourTerms_mem_of_side_mem hp hp2 q
      canonicalProjectivePostConeBoundarySideCycle s (z, false) hs hletter
  rcases List.mem_iff_getElem.mp (by
      simpa [canonicalProjectivePostConeRawRootContour, q] using hmem) with
    ⟨i, hi, hget⟩
  exact ⟨⟨i, hi⟩, by simpa [canonicalProjectivePostConeRawRootContour] using hget⟩

/-- Every surviving final generator occurs positively somewhere in the
literal all-face boundary inventory, at the source dart of its physical
edge. -/
theorem canonicalProjectivePostConeRawAllFacesContour_mem_source_letter
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : CanonicalProjectivePostConeFinalGenerator hp hp2) :
    (z, true) ∈ canonicalProjectivePostConeRawAllFacesContour hp hp2 := by
  classical
  let q := (projectivePolygonPostConeEdgeSource z.1).state
  let s := projectivePolygonPostConeEdgeSide z.1
  have hs : s ∈ canonicalProjectivePostConeBoundarySideCycle := by
    cases hgen : z.1.1.1.2 <;>
      simp [s, projectivePolygonPostConeEdgeSide,
        ProjectiveOctagonGenerator.positivePolygonSide,
        canonicalProjectivePostConeBoundarySideCycle, hgen]
  have hletter : (z, true) ∈ canonicalProjectivePostConeRawRootContourTerm hp hp2 q s := by
    rw [canonicalProjectivePostConeRawRootContourTerm_eq_source_letter hp hp2 z.1 z.2]
    simp only [List.mem_singleton]
    apply Prod.ext
    · exact Subtype.ext rfl
    · rfl
  have hface : q ∈ (Finset.univ : Finset (BuserSarnakProjectiveReductionRange p)).toList := by
    simp [q]
  apply List.mem_flatten.mpr
  refine ⟨canonicalProjectivePostConeRawRootContourTerms hp hp2 q
    canonicalProjectivePostConeBoundarySideCycle, ?_, ?_⟩
  · apply List.mem_map.mpr
    exact ⟨q, hface, rfl⟩
  · exact canonicalProjectivePostConeRawRootContourTerms_mem_of_side_mem hp hp2 q
      canonicalProjectivePostConeBoundarySideCycle s (z, true) hs hletter

/-- Convert the source-letter membership into an actual Fin-indexed
occurrence in the concatenated all-face word. -/
theorem canonicalProjectivePostConeRawAllFacesContour_exists_positive_occurrence
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : CanonicalProjectivePostConeFinalGenerator hp hp2) :
    ∃ i : Fin (canonicalProjectivePostConeRawAllFacesContour hp hp2).length,
      (canonicalProjectivePostConeRawAllFacesContour hp hp2).get i = (z, true) := by
  rcases List.mem_iff_getElem.mp
      (canonicalProjectivePostConeRawAllFacesContour_mem_source_letter hp hp2 z) with
    ⟨i, hi, hget⟩
  exact ⟨⟨i, hi⟩, by simpa using hget⟩

/-- A chosen positive occurrence of every surviving generator in the
all-face contour. -/
noncomputable def canonicalProjectivePostConeRawAllFacesPositiveOccurrence
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : CanonicalProjectivePostConeFinalGenerator hp hp2) :
    Fin (canonicalProjectivePostConeRawAllFacesContour hp hp2).length :=
  Classical.choose
    (canonicalProjectivePostConeRawAllFacesContour_exists_positive_occurrence hp hp2 z)

theorem canonicalProjectivePostConeRawAllFacesPositiveOccurrence_spec
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : CanonicalProjectivePostConeFinalGenerator hp hp2) :
    (canonicalProjectivePostConeRawAllFacesContour hp hp2).get
      (canonicalProjectivePostConeRawAllFacesPositiveOccurrence hp hp2 z) =
        (z, true) :=
  Classical.choose_spec
    (canonicalProjectivePostConeRawAllFacesContour_exists_positive_occurrence hp hp2 z)

theorem canonicalProjectivePostConeRawAllFacesPositiveOccurrence_injective
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    Function.Injective
      (canonicalProjectivePostConeRawAllFacesPositiveOccurrence hp hp2) := by
  intro z z' h
  have hget := congrArg (canonicalProjectivePostConeRawAllFacesContour hp hp2).get h
  rw [canonicalProjectivePostConeRawAllFacesPositiveOccurrence_spec,
    canonicalProjectivePostConeRawAllFacesPositiveOccurrence_spec] at hget
  exact congrArg Prod.fst hget

/-- Evaluation of the literal global raw contour is the named direct root
word. No cancellation or word normalization is used in the construction. -/
theorem canonicalProjectivePostConeRawRootContour_eval
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    FreeGroup.mk (canonicalProjectivePostConeRawRootContour hp hp2) =
      canonicalProjectivePostConeDirectRootWord hp hp2 := by
  unfold canonicalProjectivePostConeRawRootContour
  rw [canonicalProjectivePostConeRawRootContourTerms_eval]
  change (List.map (canonicalProjectivePostConeDirectFinalSubstitution hp hp2)
    (canonicalProjectiveConePostConeBoundaryTermContour p
      (canonicalProjectivePostConeTreeRoot hp hp2).state)).prod = _
  unfold canonicalProjectivePostConeDirectRootWord
  rw [← map_list_prod,
    canonicalProjectiveConePostConeBoundaryTermContour_prod]

/- The literal raw expansion respects reversal across every paired polygon
side.  This is stated at the free-group value level so it does not hide the
unreduced list behind a cancellation or a chosen normal form. -/
theorem canonicalProjectivePostConeRawRootContourTerm_partner_eq_inv
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide) :
    FreeGroup.mk (canonicalProjectivePostConeRawRootContourTerm hp hp2
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).1
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).2) =
      (FreeGroup.mk (canonicalProjectivePostConeRawRootContourTerm hp hp2 q s))⁻¹ := by
  rw [canonicalProjectivePostConeRawRootContourTerm_eval,
    canonicalProjectivePostConeRawRootContourTerm_eval,
    canonicalProjectivePostConeDirectFinalSubstitution_boundaryTerm_partner_eq_inv]

/-- Pairing a root boundary term literally reverses its signed raw list.  The
classifier proof above shows that this is independent of the two local
`Classical.choice` calls: a paired physical carrier must have the opposite
orientation and the same final or deleted label. -/
theorem canonicalProjectivePostConeRawRootContourTerm_partner_eq_invRev
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide) :
    canonicalProjectivePostConeRawRootContourTerm hp hp2
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).1
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).2 =
      FreeGroup.invRev (canonicalProjectivePostConeRawRootContourTerm hp hp2 q s) := by
  unfold canonicalProjectivePostConeRawRootContourTerm
  exact canonicalProjectivePostConeRawRootContourTermOfCase_partner_eq_invRev hp hp2 q s _ _

/-- The literal inverse-reversal law induces a bijection of occurrence
positions between paired raw contour terms. This keeps occurrence indices
available for constructing the concrete Wicks pairing. -/
theorem canonicalProjectivePostConeRawRootContourTerm_partner_occurrence_bijective
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide) :
    Function.Bijective (fun i : Fin
        (canonicalProjectivePostConeRawRootContourTerm hp hp2 q s).length =>
      Fin.cast ((congrArg List.length
        (canonicalProjectivePostConeRawRootContourTerm_partner_eq_invRev hp hp2 q s)).symm)
        (invRevPosition i)) := by
  let w := canonicalProjectivePostConeRawRootContourTerm hp hp2 q s
  let paired := canonicalProjectivePostConeRawRootContourTerm hp hp2
    ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).1
    ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).2
  have hraw : paired = FreeGroup.invRev w :=
    canonicalProjectivePostConeRawRootContourTerm_partner_eq_invRev hp hp2 q s
  let hlen : (FreeGroup.invRev w).length = paired.length :=
    (congrArg List.length hraw).symm
  change Function.Bijective (fun i => Fin.cast hlen (invRevPosition i))
  constructor
  · intro i j hij
    apply (invRevPosition_bijective w).1
    exact Fin.cast_injective hlen hij
  · intro j
    obtain ⟨i, hi⟩ := (invRevPosition_bijective w).2 (Fin.cast hlen.symm j)
    refine ⟨i, ?_⟩
    calc
      Fin.cast hlen (invRevPosition i) = Fin.cast hlen (Fin.cast hlen.symm j) :=
        congrArg (Fin.cast hlen) hi
      _ = j := by simp

/-- The occurrence-position bijection carries each literal final generator
to the same generator with opposite orientation. -/
theorem canonicalProjectivePostConeRawRootContourTerm_partner_occurrence_letter
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide)
    (i : Fin (canonicalProjectivePostConeRawRootContourTerm hp hp2 q s).length) :
    (canonicalProjectivePostConeRawRootContourTerm hp hp2
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).1
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).2).get
        (Fin.cast ((congrArg List.length
          (canonicalProjectivePostConeRawRootContourTerm_partner_eq_invRev hp hp2 q s)).symm)
          (invRevPosition i)) =
      (((canonicalProjectivePostConeRawRootContourTerm hp hp2 q s).get i).1,
        !((canonicalProjectivePostConeRawRootContourTerm hp hp2 q s).get i).2) := by
  let w := canonicalProjectivePostConeRawRootContourTerm hp hp2 q s
  let paired := canonicalProjectivePostConeRawRootContourTerm hp hp2
    ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).1
    ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).2
  have hraw : paired = FreeGroup.invRev w :=
    canonicalProjectivePostConeRawRootContourTerm_partner_eq_invRev hp hp2 q s
  let hlen : (FreeGroup.invRev w).length = paired.length :=
    (congrArg List.length hraw).symm
  change paired.get (Fin.cast hlen (invRevPosition i)) =
    ((w.get i).1, !(w.get i).2)
  exact (get_cast_eq_of_eq hraw.symm (invRevPosition i)).trans
    (get_invRevPosition w i)

/-- Applying free reduction to the literal partner law gives the canonical
reduced-word counterpart. -/
theorem canonicalProjectivePostConeRawRootContourTerm_partner_reduce_eq_invRev_reduce
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide) :
    @FreeGroup.reduce _ (Classical.decEq _)
      (canonicalProjectivePostConeRawRootContourTerm hp hp2
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).1
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).2) =
      FreeGroup.invRev (@FreeGroup.reduce _ (Classical.decEq _)
        (canonicalProjectivePostConeRawRootContourTerm hp hp2 q s)) := by
  classical
  rw [canonicalProjectivePostConeRawRootContourTerm_partner_eq_invRev hp hp2 q s,
    FreeGroup.reduce_invRev]

/-- At the source dart of a deleted tree edge, the literal root-boundary
term is its entire recursively expanded slot word, with no reduction. -/
theorem canonicalProjectivePostConeRawRootContourTerm_eq_treeSource_word
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : CanonicalProjectiveConeKeptSymbol p)
    (hz : isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z) :
    canonicalProjectivePostConeRawRootContourTerm hp hp2
      (projectivePolygonPostConeEdgeSource z).state
      (projectivePolygonPostConeEdgeSide z) =
        canonicalProjectivePostConeRawTreeWordBySlot hp hp2
          (canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz) := by
  have hterm := canonicalProjectiveConePostConeBoundaryTerm_edgeSource_eq z
  cases hcase : canonicalProjectivePostConeRawRootContourTermCase hp hp2
      (projectivePolygonPostConeEdgeSource z).state
      (projectivePolygonPostConeEdgeSide z) with
  | one hone =>
      exact (canonicalProjectivePostConeRawRoot_source_eq_one_false z
        (hterm.symm.trans hone)).elim
  | finalSource z' hsource hz' =>
      have hzz : z' = z := FreeGroup.of_injective (hsource.2.2.symm.trans hterm)
      subst z'
      exact (hz' hz).elim
  | finalTarget z' htarget hz' =>
      exact (canonicalProjectivePostConeRawRoot_source_eq_target_false z z'
        (hterm.symm.trans htarget.2.2)).elim
  | treeSource z' hsource hz' =>
      have hzz : z' = z := FreeGroup.of_injective (hsource.2.2.symm.trans hterm)
      subst z'
      simp [canonicalProjectivePostConeRawRootContourTerm,
        canonicalProjectivePostConeRawRootContourTermOfCase, hcase]
  | treeTarget z' htarget hz' =>
      exact (canonicalProjectivePostConeRawRoot_source_eq_target_false z z'
        (hterm.symm.trans htarget.2.2)).elim

/-- The target dart of a deleted tree edge inserts the inverse reversal of
the same complete slot word into the literal root contour. -/
theorem canonicalProjectivePostConeRawRootContourTerm_eq_treeTarget_word
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : CanonicalProjectiveConeKeptSymbol p)
    (hz : isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z) :
    canonicalProjectivePostConeRawRootContourTerm hp hp2
      (projectivePolygonPostConeEdgeTarget z).state
      (projectivePolygonPostConeEdgeTargetSide z) =
        FreeGroup.invRev (canonicalProjectivePostConeRawTreeWordBySlot hp hp2
          (canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz)) := by
  have hpair := canonicalProjectivePostConeRawRootContourTerm_partner_eq_invRev hp hp2
    (projectivePolygonPostConeEdgeSource z).state
    (projectivePolygonPostConeEdgeSide z)
  change canonicalProjectivePostConeRawRootContourTerm hp hp2
      (projectivePolygonPostConeEdgeTarget z).state
      (projectivePolygonPostConeEdgeTargetSide z) =
        FreeGroup.invRev (canonicalProjectivePostConeRawRootContourTerm hp hp2
          (projectivePolygonPostConeEdgeSource z).state
          (projectivePolygonPostConeEdgeSide z)) at hpair
  rw [canonicalProjectivePostConeRawRootContourTerm_eq_treeSource_word hp hp2 z hz]
    at hpair
  exact hpair

/-- One root-side expansion is a literal sublist of the concatenated root
contour. The sublist proof retains order and therefore distinguishes all
positions even when the same signed letter appears more than once. -/
theorem canonicalProjectivePostConeRawRootContourTerm_sublist_rootContour
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (s : ProjectivePolygonSide) :
    List.Sublist (canonicalProjectivePostConeRawRootContourTerm hp hp2
      (canonicalProjectivePostConeTreeRoot hp hp2).state s)
        (canonicalProjectivePostConeRawRootContour hp hp2) := by
  have hsub : ∀ (q : BuserSarnakProjectiveReductionRange p)
      (sides : List ProjectivePolygonSide) (t : ProjectivePolygonSide),
      t ∈ sides →
      List.Sublist (canonicalProjectivePostConeRawRootContourTerm hp hp2 q t)
        (canonicalProjectivePostConeRawRootContourTerms hp hp2 q sides) := by
    intro q sides
    induction sides with
    | nil => intro t ht; simp at ht
    | cons u us ih =>
        intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · exact List.sublist_append_left _ _
        · exact (ih t ht).trans (List.sublist_append_right _ _)
  have hs : s ∈ canonicalProjectivePostConeBoundarySideCycle := by
    cases s <;> simp [canonicalProjectivePostConeBoundarySideCycle]
  exact hsub _ _ s hs

/-- The literal inclusion of a root side supplies an injective,
order-preserving map on its occurrence indices. -/
theorem canonicalProjectivePostConeRawRootContourTerm_indexEmbedding
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (s : ProjectivePolygonSide) :
    ∃ f : Fin (canonicalProjectivePostConeRawRootContourTerm hp hp2
      (canonicalProjectivePostConeTreeRoot hp hp2).state s).length ↪o
        Fin (canonicalProjectivePostConeRawRootContour hp hp2).length,
      ∀ i, (canonicalProjectivePostConeRawRootContour hp hp2).get (f i) =
        (canonicalProjectivePostConeRawRootContourTerm hp hp2
          (canonicalProjectivePostConeTreeRoot hp hp2).state s).get i := by
  obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp
    (canonicalProjectivePostConeRawRootContourTerm_sublist_rootContour hp hp2 s)
  exact ⟨f, fun i => (hf i).symm⟩

/-- An occurrence in one side's literal term has a genuine index in the
single root-face contour. This is the final index handoff after following a
tree path toward the root. -/
theorem canonicalProjectivePostConeRawRootContour_exists_occurrence_of_term
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (s : ProjectivePolygonSide)
    (i : Fin (canonicalProjectivePostConeRawRootContourTerm hp hp2
      (canonicalProjectivePostConeTreeRoot hp hp2).state s).length) :
    ∃ j : Fin (canonicalProjectivePostConeRawRootContour hp hp2).length,
      (canonicalProjectivePostConeRawRootContour hp hp2).get j =
        (canonicalProjectivePostConeRawRootContourTerm hp hp2
          (canonicalProjectivePostConeTreeRoot hp hp2).state s).get i := by
  have hs : s ∈ canonicalProjectivePostConeBoundarySideCycle := by
    cases s <;> simp [canonicalProjectivePostConeBoundarySideCycle]
  have hmem := canonicalProjectivePostConeRawRootContourTerms_mem_of_side_mem
    hp hp2 (canonicalProjectivePostConeTreeRoot hp hp2).state
    canonicalProjectivePostConeBoundarySideCycle s _ hs (List.get_mem _ i)
  rcases List.mem_iff_getElem.mp (by
      simpa [canonicalProjectivePostConeRawRootContour] using hmem) with
    ⟨j, hj, hget⟩
  exact ⟨⟨j, hj⟩, by simpa [canonicalProjectivePostConeRawRootContour] using hget⟩

/-- When a tree slot leaves the root through the physical source of its
label, each child-word position survives at an actual root-contour index
with the same signed letter. -/
theorem canonicalProjectivePostConeRawRootContour_get_child_of_source_incidence
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hroot : child.left = canonicalProjectivePostConeTreeRoot hp hp2)
    (hsource : child.left = projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 child))
    (i : Fin (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).length) :
    ∃ j : Fin (canonicalProjectivePostConeRawRootContour hp hp2).length,
      (canonicalProjectivePostConeRawRootContour hp hp2).get j =
        (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get i := by
  let z := canonicalProjectivePostConeTreeSlotLabel hp hp2 child
  have hz : isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z := ⟨child, rfl⟩
  have hslot : canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz = child :=
    canonicalProjectivePostConeDirectTreeSlotOfDeleted_eq_of_label hp hp2 z hz child rfl
  let s := projectivePolygonPostConeEdgeSide z
  have hstate : (canonicalProjectivePostConeTreeRoot hp hp2).state =
      (projectivePolygonPostConeEdgeSource z).state :=
    congrArg ProjectivePolygonPostConeFace.state (hroot.symm.trans hsource)
  have hterm : canonicalProjectivePostConeRawRootContourTerm hp hp2
      (canonicalProjectivePostConeTreeRoot hp hp2).state s =
        canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child := by
    rw [hstate, canonicalProjectivePostConeRawRootContourTerm_eq_treeSource_word
      hp hp2 z hz, hslot]
  let k : Fin (canonicalProjectivePostConeRawRootContourTerm hp hp2
      (canonicalProjectivePostConeTreeRoot hp hp2).state s).length :=
    Fin.cast (congrArg List.length hterm).symm i
  obtain ⟨j, hj⟩ :=
    canonicalProjectivePostConeRawRootContour_exists_occurrence_of_term hp hp2 s k
  exact ⟨j, hj.trans (get_cast_eq_of_eq hterm.symm i)⟩

/-- If the root sees the target dart of a tree slot, inverse reversal
transports a child position to the same final generator with opposite sign. -/
theorem canonicalProjectivePostConeRawRootContour_get_child_of_target_incidence
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hroot : child.left = canonicalProjectivePostConeTreeRoot hp hp2)
    (htarget : child.left = projectivePolygonPostConeEdgeTarget
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 child))
    (i : Fin (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).length) :
    ∃ j : Fin (canonicalProjectivePostConeRawRootContour hp hp2).length,
      (canonicalProjectivePostConeRawRootContour hp hp2).get j =
        (((canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get i).1,
          !((canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get i).2) := by
  let z := canonicalProjectivePostConeTreeSlotLabel hp hp2 child
  have hz : isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z := ⟨child, rfl⟩
  have hslot : canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz = child :=
    canonicalProjectivePostConeDirectTreeSlotOfDeleted_eq_of_label hp hp2 z hz child rfl
  let s := projectivePolygonPostConeEdgeTargetSide z
  have hstate : (canonicalProjectivePostConeTreeRoot hp hp2).state =
      (projectivePolygonPostConeEdgeTarget z).state :=
    congrArg ProjectivePolygonPostConeFace.state (hroot.symm.trans htarget)
  have hterm : canonicalProjectivePostConeRawRootContourTerm hp hp2
      (canonicalProjectivePostConeTreeRoot hp hp2).state s =
        FreeGroup.invRev (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) := by
    rw [hstate, canonicalProjectivePostConeRawRootContourTerm_eq_treeTarget_word
      hp hp2 z hz, hslot]
  let k : Fin (canonicalProjectivePostConeRawRootContourTerm hp hp2
      (canonicalProjectivePostConeTreeRoot hp hp2).state s).length :=
    Fin.cast (congrArg List.length hterm).symm (invRevPosition i)
  obtain ⟨j, hj⟩ :=
    canonicalProjectivePostConeRawRootContour_exists_occurrence_of_term hp hp2 s k
  exact ⟨j, hj.trans ((get_cast_eq_of_eq hterm.symm (invRevPosition i)).trans
    (get_invRevPosition _ i))⟩

/-- At a source-oriented root child, the complete child word embeds into
the root contour with distinct positions retained. -/
theorem canonicalProjectivePostConeRawRootContour_child_source_indexEmbedding
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hroot : child.left = canonicalProjectivePostConeTreeRoot hp hp2)
    (hsource : child.left = projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 child)) :
    ∃ f : Fin (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).length →
        Fin (canonicalProjectivePostConeRawRootContour hp hp2).length,
      Function.Injective f ∧ ∀ i,
        (canonicalProjectivePostConeRawRootContour hp hp2).get (f i) =
          (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get i := by
  let z := canonicalProjectivePostConeTreeSlotLabel hp hp2 child
  have hz : isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z := ⟨child, rfl⟩
  have hslot : canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz = child :=
    canonicalProjectivePostConeDirectTreeSlotOfDeleted_eq_of_label hp hp2 z hz child rfl
  let s := projectivePolygonPostConeEdgeSide z
  have hstate : (canonicalProjectivePostConeTreeRoot hp hp2).state =
      (projectivePolygonPostConeEdgeSource z).state :=
    congrArg ProjectivePolygonPostConeFace.state (hroot.symm.trans hsource)
  have hterm : canonicalProjectivePostConeRawRootContourTerm hp hp2
      (canonicalProjectivePostConeTreeRoot hp hp2).state s =
        canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child := by
    rw [hstate, canonicalProjectivePostConeRawRootContourTerm_eq_treeSource_word
      hp hp2 z hz, hslot]
  obtain ⟨e, he⟩ :=
    canonicalProjectivePostConeRawRootContourTerm_indexEmbedding hp hp2 s
  refine ⟨fun i => e (Fin.cast (congrArg List.length hterm).symm i), ?_, ?_⟩
  · intro i j hij
    exact Fin.cast_injective _ (e.injective hij)
  · intro i
    exact (he _).trans (get_cast_eq_of_eq hterm.symm i)

/-- At a target-oriented root child, positions still embed injectively;
the inverse reversal changes their order and flips their signs. -/
theorem canonicalProjectivePostConeRawRootContour_child_target_indexEmbedding
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hroot : child.left = canonicalProjectivePostConeTreeRoot hp hp2)
    (htarget : child.left = projectivePolygonPostConeEdgeTarget
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 child)) :
    ∃ f : Fin (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).length →
        Fin (canonicalProjectivePostConeRawRootContour hp hp2).length,
      Function.Injective f ∧ ∀ i,
        (canonicalProjectivePostConeRawRootContour hp hp2).get (f i) =
          (((canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get i).1,
            !((canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get i).2) := by
  let z := canonicalProjectivePostConeTreeSlotLabel hp hp2 child
  have hz : isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z := ⟨child, rfl⟩
  have hslot : canonicalProjectivePostConeDirectTreeSlotOfDeleted hp hp2 z hz = child :=
    canonicalProjectivePostConeDirectTreeSlotOfDeleted_eq_of_label hp hp2 z hz child rfl
  let s := projectivePolygonPostConeEdgeTargetSide z
  have hstate : (canonicalProjectivePostConeTreeRoot hp hp2).state =
      (projectivePolygonPostConeEdgeTarget z).state :=
    congrArg ProjectivePolygonPostConeFace.state (hroot.symm.trans htarget)
  have hterm : canonicalProjectivePostConeRawRootContourTerm hp hp2
      (canonicalProjectivePostConeTreeRoot hp hp2).state s =
        FreeGroup.invRev (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child) := by
    rw [hstate, canonicalProjectivePostConeRawRootContourTerm_eq_treeTarget_word
      hp hp2 z hz, hslot]
  obtain ⟨e, he⟩ :=
    canonicalProjectivePostConeRawRootContourTerm_indexEmbedding hp hp2 s
  refine ⟨fun i => e (Fin.cast (congrArg List.length hterm).symm (invRevPosition i)),
    ?_, ?_⟩
  · intro i j hij
    apply (invRevPosition_bijective _).1
    exact Fin.cast_injective _ (e.injective hij)
  · intro i
    exact (he _).trans ((get_cast_eq_of_eq hterm.symm (invRevPosition i)).trans
      (get_invRevPosition _ i))

/-- Every position in a tree word one edge below the root has a literal
position in the root contour. The physical orientation determines which of
the two signed forms appears; it is derived from the actual tree edge. -/
theorem canonicalProjectivePostConeRawRootContour_get_child_of_root
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hroot : child.left = canonicalProjectivePostConeTreeRoot hp hp2)
    (i : Fin (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).length) :
    ∃ j : Fin (canonicalProjectivePostConeRawRootContour hp hp2).length,
      (canonicalProjectivePostConeRawRootContour hp hp2).get j =
          (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get i ∨
        (canonicalProjectivePostConeRawRootContour hp hp2).get j =
          (((canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get i).1,
            !((canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get i).2) := by
  rcases canonicalProjectivePostConeTreeSlot_left_eq_physicalSource_or_target
      hp hp2 child with hsource | htarget
  · obtain ⟨j, hj⟩ :=
      canonicalProjectivePostConeRawRootContour_get_child_of_source_incidence
        hp hp2 child hroot hsource i
    exact ⟨j, Or.inl hj⟩
  · obtain ⟨j, hj⟩ :=
      canonicalProjectivePostConeRawRootContour_get_child_of_target_incidence
        hp hp2 child hroot htarget i
    exact ⟨j, Or.inr hj⟩

/-- A selected off-pivot term occupies distinct positions in the appropriate
prefix or suffix of a recursive tree-slot word. -/
private theorem canonicalProjectivePostConeRawContourTerm_sublist_terms_of_side_mem
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (sides : List ProjectivePolygonSide) (s : ProjectivePolygonSide)
    (hs : s ∈ sides) :
    List.Sublist (canonicalProjectivePostConeRawContourTerm hp hp2 slot
      (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) s)
      (canonicalProjectivePostConeRawContourTerms hp hp2 slot
        (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) sides) := by
  induction sides with
  | nil => simp at hs
  | cons t ts ih =>
      rcases List.mem_cons.mp hs with rfl | hst
      · exact List.sublist_append_left _ _
      · exact (ih hst).trans (List.sublist_append_right _ _)

/-- A selected off-pivot raw term embeds into the whole recursive slot word.
When the slot is physically source-oriented, the embedding uses inverse
reversal; otherwise it preserves the literal term. -/
theorem canonicalProjectivePostConeRawContourTerm_sublist_slotWord
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (s : ProjectivePolygonSide)
    (hs : s ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot) :
    (slot.right = projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) →
      List.Sublist (FreeGroup.invRev (canonicalProjectivePostConeRawContourTerm hp hp2
        slot (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) s))
          (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot)) ∧
    (slot.right ≠ projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) →
      List.Sublist (canonicalProjectivePostConeRawContourTerm hp hp2
        slot (fun other _ => canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other) s)
          (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot)) := by
  classical
  let ih := fun other
      (_hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other) =>
      canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other
  have hword : canonicalProjectivePostConeRawTreeWordBySlot hp hp2 slot =
      if hsource : slot.right = projectivePolygonPostConeEdgeSource
          (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) then
        FreeGroup.invRev (canonicalProjectivePostConeRawContourPrefix hp hp2 slot ih) ++
          FreeGroup.invRev (canonicalProjectivePostConeRawContourSuffix hp hp2 slot ih)
      else
        canonicalProjectivePostConeRawContourSuffix hp hp2 slot ih ++
          canonicalProjectivePostConeRawContourPrefix hp hp2 slot ih := by
    unfold canonicalProjectivePostConeRawTreeWordBySlot
    rw [WellFounded.fix_eq]
    rfl
  rcases canonicalProjectivePostConeBoundarySide_mem_prefix_or_suffix
    s (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot) hs with
    hprefix | hsuffix
  · have hsub : List.Sublist
        (canonicalProjectivePostConeRawContourTerm hp hp2 slot ih s)
        (canonicalProjectivePostConeRawContourPrefix hp hp2 slot ih) := by
      exact canonicalProjectivePostConeRawContourTerm_sublist_terms_of_side_mem
        hp hp2 slot _ s hprefix
    constructor
    · intro hsource
      rw [hword, dif_pos hsource]
      have hinv : List.Sublist
          (FreeGroup.invRev (canonicalProjectivePostConeRawContourTerm hp hp2 slot ih s))
          (FreeGroup.invRev (canonicalProjectivePostConeRawContourPrefix hp hp2 slot ih)) := by
        exact (hsub.map (fun g => (g.1, !g.2))).reverse
      exact hinv.trans (List.sublist_append_left _ _)
    · intro hsource
      rw [hword, dif_neg hsource]
      exact hsub.trans (List.sublist_append_right _ _)
  · have hsub : List.Sublist
        (canonicalProjectivePostConeRawContourTerm hp hp2 slot ih s)
        (canonicalProjectivePostConeRawContourSuffix hp hp2 slot ih) := by
      exact canonicalProjectivePostConeRawContourTerm_sublist_terms_of_side_mem
        hp hp2 slot _ s hsuffix
    constructor
    · intro hsource
      rw [hword, dif_pos hsource]
      have hinv : List.Sublist
          (FreeGroup.invRev (canonicalProjectivePostConeRawContourTerm hp hp2 slot ih s))
          (FreeGroup.invRev (canonicalProjectivePostConeRawContourSuffix hp hp2 slot ih)) := by
        exact (hsub.map (fun g => (g.1, !g.2))).reverse
      exact hinv.trans (List.sublist_append_right _ _)
    · intro hsource
      rw [hword, dif_neg hsource]
      exact hsub.trans (List.sublist_append_left _ _)

/-- A source dart carried by a physical edge other than the slot's own
deleted edge cannot be the slot's pivot side. -/
theorem canonicalProjectivePostConeRawTreeWord_source_ne_pivot_of_label_ne
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (z : CanonicalProjectiveConeKeptSymbol p)
    (hz : z ≠ canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)
    (hsource : slot.right = projectivePolygonPostConeEdgeSource z) :
    projectivePolygonPostConeEdgeSide z ≠
      canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot := by
  classical
  let y := canonicalProjectivePostConeTreeSlotLabel hp hp2 slot
  intro hs
  by_cases hslotSource : slot.right = projectivePolygonPostConeEdgeSource y
  · have hside : projectivePolygonPostConeEdgeSide z =
        projectivePolygonPostConeEdgeSide y := by
      unfold canonicalProjectivePostConeTreeSlotRightFactorSide at hs
      rw [if_pos hslotSource] at hs
      exact hs
    have hzterm : canonicalProjectiveConePostConeBoundaryTerm p slot.right.state
        (projectivePolygonPostConeEdgeSide z) = FreeGroup.of z := by
      rw [congrArg ProjectivePolygonPostConeFace.state hsource]
      exact canonicalProjectiveConePostConeBoundaryTerm_edgeSource_eq z
    have hyterm : canonicalProjectiveConePostConeBoundaryTerm p slot.right.state
        (projectivePolygonPostConeEdgeSide y) = FreeGroup.of y := by
      rw [congrArg ProjectivePolygonPostConeFace.state hslotSource]
      exact canonicalProjectiveConePostConeBoundaryTerm_edgeSource_eq y
    apply hz
    apply FreeGroup.of_injective
    calc
      FreeGroup.of z = canonicalProjectiveConePostConeBoundaryTerm p slot.right.state
          (projectivePolygonPostConeEdgeSide z) := hzterm.symm
      _ = canonicalProjectiveConePostConeBoundaryTerm p slot.right.state
          (projectivePolygonPostConeEdgeSide y) := by rw [hside]
      _ = FreeGroup.of y := hyterm
  · have hslotTarget : slot.right = projectivePolygonPostConeEdgeTarget y := by
      rcases canonicalProjectivePostConeTreeSlot_right_eq_physicalSource_or_target
          hp hp2 slot with hsource' | htarget'
      · exact (hslotSource hsource').elim
      · exact htarget'
    have hside : projectivePolygonPostConeEdgeSide z =
        projectivePolygonPostConeEdgeTargetSide y := by
      unfold canonicalProjectivePostConeTreeSlotRightFactorSide at hs
      rw [if_neg hslotSource] at hs
      exact hs
    have hzterm : canonicalProjectiveConePostConeBoundaryTerm p slot.right.state
        (projectivePolygonPostConeEdgeSide z) = FreeGroup.of z := by
      rw [congrArg ProjectivePolygonPostConeFace.state hsource]
      exact canonicalProjectiveConePostConeBoundaryTerm_edgeSource_eq z
    have hyterm : canonicalProjectiveConePostConeBoundaryTerm p slot.right.state
        (projectivePolygonPostConeEdgeTargetSide y) = (FreeGroup.of y)⁻¹ := by
      rw [congrArg ProjectivePolygonPostConeFace.state hslotTarget]
      exact canonicalProjectiveConePostConeBoundaryTerm_edgeTarget_eq_inv hp hp2 y
    apply canonicalProjectivePostConeRawRoot_source_eq_target_false z y
    calc
      FreeGroup.of z = canonicalProjectiveConePostConeBoundaryTerm p slot.right.state
          (projectivePolygonPostConeEdgeSide z) := hzterm.symm
      _ = canonicalProjectiveConePostConeBoundaryTerm p slot.right.state
          (projectivePolygonPostConeEdgeTargetSide y) := by rw [hside]
      _ = (FreeGroup.of y)⁻¹ := hyterm

/-- The analogous target dart of another physical edge cannot be the
distinguished pivot side of a slot. -/
theorem canonicalProjectivePostConeRawTreeWord_target_ne_pivot_of_label_ne
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (slot : CanonicalProjectivePostConeTreeSlot hp hp2)
    (z : CanonicalProjectiveConeKeptSymbol p)
    (hz : z ≠ canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)
    (htarget : slot.right = projectivePolygonPostConeEdgeTarget z) :
    projectivePolygonPostConeEdgeTargetSide z ≠
      canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot := by
  classical
  let y := canonicalProjectivePostConeTreeSlotLabel hp hp2 slot
  intro hs
  by_cases hslotSource : slot.right = projectivePolygonPostConeEdgeSource y
  · have hside : projectivePolygonPostConeEdgeTargetSide z =
        projectivePolygonPostConeEdgeSide y := by
      unfold canonicalProjectivePostConeTreeSlotRightFactorSide at hs
      rw [if_pos hslotSource] at hs
      exact hs
    have hzterm : canonicalProjectiveConePostConeBoundaryTerm p slot.right.state
        (projectivePolygonPostConeEdgeTargetSide z) = (FreeGroup.of z)⁻¹ := by
      rw [congrArg ProjectivePolygonPostConeFace.state htarget]
      exact canonicalProjectiveConePostConeBoundaryTerm_edgeTarget_eq_inv hp hp2 z
    have hyterm : canonicalProjectiveConePostConeBoundaryTerm p slot.right.state
        (projectivePolygonPostConeEdgeSide y) = FreeGroup.of y := by
      rw [congrArg ProjectivePolygonPostConeFace.state hslotSource]
      exact canonicalProjectiveConePostConeBoundaryTerm_edgeSource_eq y
    apply canonicalProjectivePostConeRawRoot_target_eq_source_false z y
    calc
      (FreeGroup.of z)⁻¹ = canonicalProjectiveConePostConeBoundaryTerm p slot.right.state
          (projectivePolygonPostConeEdgeTargetSide z) := hzterm.symm
      _ = canonicalProjectiveConePostConeBoundaryTerm p slot.right.state
          (projectivePolygonPostConeEdgeSide y) := by rw [hside]
      _ = FreeGroup.of y := hyterm
  · have hslotTarget : slot.right = projectivePolygonPostConeEdgeTarget y := by
      rcases canonicalProjectivePostConeTreeSlot_right_eq_physicalSource_or_target
          hp hp2 slot with hsource' | htarget'
      · exact (hslotSource hsource').elim
      · exact htarget'
    have hside : projectivePolygonPostConeEdgeTargetSide z =
        projectivePolygonPostConeEdgeTargetSide y := by
      unfold canonicalProjectivePostConeTreeSlotRightFactorSide at hs
      rw [if_neg hslotSource] at hs
      exact hs
    have hzterm : canonicalProjectiveConePostConeBoundaryTerm p slot.right.state
        (projectivePolygonPostConeEdgeTargetSide z) = (FreeGroup.of z)⁻¹ := by
      rw [congrArg ProjectivePolygonPostConeFace.state htarget]
      exact canonicalProjectiveConePostConeBoundaryTerm_edgeTarget_eq_inv hp hp2 z
    have hyterm : canonicalProjectiveConePostConeBoundaryTerm p slot.right.state
        (projectivePolygonPostConeEdgeTargetSide y) = (FreeGroup.of y)⁻¹ := by
      rw [congrArg ProjectivePolygonPostConeFace.state hslotTarget]
      exact canonicalProjectiveConePostConeBoundaryTerm_edgeTarget_eq_inv hp hp2 y
    apply hz
    apply canonicalProjectivePostConeRawRoot_target_eq_target_injective z y
    calc
      (FreeGroup.of z)⁻¹ = canonicalProjectiveConePostConeBoundaryTerm p slot.right.state
          (projectivePolygonPostConeEdgeTargetSide z) := hzterm.symm
      _ = canonicalProjectiveConePostConeBoundaryTerm p slot.right.state
          (projectivePolygonPostConeEdgeTargetSide y) := by rw [hside]
      _ = (FreeGroup.of y)⁻¹ := hyterm

/-- At a non-root face, its unique incoming slot captures the negative
occurrence at the target dart of any retained physical edge. The slot's
orientation records whether the later path splice flips that sign. -/
theorem canonicalProjectivePostConeRawIncomingSlot_mem_target
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : projectivePolygonPostConeCanonicalSpanningTree hp hp2)
    (hq : q ≠ canonicalProjectivePostConeTreeRoot hp hp2)
    (z : CanonicalProjectivePostConeFinalGenerator hp hp2)
    (htarget : projectivePolygonPostConeEdgeTarget z.1 = q) :
    ((canonicalProjectivePostConeTreeIncomingSlot hp hp2 q hq).right =
        projectivePolygonPostConeEdgeSource
          (canonicalProjectivePostConeTreeSlotLabel hp hp2
            (canonicalProjectivePostConeTreeIncomingSlot hp hp2 q hq)) →
      (z, true) ∈ canonicalProjectivePostConeRawTreeWordBySlot hp hp2
        (canonicalProjectivePostConeTreeIncomingSlot hp hp2 q hq)) ∧
    ((canonicalProjectivePostConeTreeIncomingSlot hp hp2 q hq).right ≠
        projectivePolygonPostConeEdgeSource
          (canonicalProjectivePostConeTreeSlotLabel hp hp2
            (canonicalProjectivePostConeTreeIncomingSlot hp hp2 q hq)) →
      (z, false) ∈ canonicalProjectivePostConeRawTreeWordBySlot hp hp2
        (canonicalProjectivePostConeTreeIncomingSlot hp hp2 q hq)) := by
  classical
  let slot := canonicalProjectivePostConeTreeIncomingSlot hp hp2 q hq
  have hright : slot.right = q :=
    canonicalProjectivePostConeTreeIncomingSlot_right hp hp2 q hq
  have hslotTarget : slot.right = projectivePolygonPostConeEdgeTarget z.1 :=
    hright.trans htarget.symm
  have hzne : z.1 ≠ canonicalProjectivePostConeTreeSlotLabel hp hp2 slot := by
    intro h
    exact z.2 ⟨slot, h.symm⟩
  have hnotPivot := canonicalProjectivePostConeRawTreeWord_target_ne_pivot_of_label_ne
    hp hp2 slot z.1 hzne hslotTarget
  have hface : (⟨slot.right.state⟩ : ProjectivePolygonPostConeFace p) =
      projectivePolygonPostConeEdgeTarget z.1 := by
    apply ProjectivePolygonPostConeFace.stateEquiv.injective
    exact congrArg ProjectivePolygonPostConeFace.state hslotTarget
  let ih := fun other
      (_hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 slot <
        canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 other) =>
      canonicalProjectivePostConeRawTreeWordBySlot hp hp2 other
  have hlocal := canonicalProjectivePostConeRawContourTerm_eq_target_letter
    hp hp2 slot ih z.1 z.2 hface hnotPivot
  have hzval : (⟨z.1, z.2⟩ : CanonicalProjectivePostConeFinalGenerator hp hp2) = z :=
    Subtype.ext rfl
  have hsides := canonicalProjectivePostConeBoundarySide_mem_prefix_or_suffix
    (projectivePolygonPostConeEdgeTargetSide z.1)
    (canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 slot) hnotPivot
  have hterm : (z, false) ∈ canonicalProjectivePostConeRawContourTerm hp hp2 slot ih
      (projectivePolygonPostConeEdgeTargetSide z.1) := by
    rw [hlocal, hzval]
    simp
  have hcarry := canonicalProjectivePostConeRawTreeWordBySlot_mem_boundaryTerm
    hp hp2 slot (projectivePolygonPostConeEdgeTargetSide z.1) hsides (z, false) hterm
  exact ⟨hcarry.1, hcarry.2⟩

/-- A deeper child inserted positively in a parent side is an actual
sublist of the parent slot word, with one inverse reversal exactly when the
parent's own distinguished edge is physically source-oriented. -/
theorem canonicalProjectivePostConeRawTreeWordBySlot_child_source_sublist_parent
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (parent child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 parent <
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child)
    (s : ProjectivePolygonSide)
    (hs : s ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 parent)
    (hcarrier :
      (⟨parent.right.state⟩ : ProjectivePolygonPostConeFace p) =
          projectivePolygonPostConeEdgeSource
            (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) ∧
        s = projectivePolygonPostConeEdgeSide
          (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) ∧
        canonicalProjectiveConePostConeBoundaryTerm p parent.right.state s =
          FreeGroup.of (canonicalProjectivePostConeTreeSlotLabel hp hp2 child)) :
    (parent.right = projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 parent) →
      List.Sublist (FreeGroup.invRev
        (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child))
          (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 parent)) ∧
    (parent.right ≠ projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 parent) →
      List.Sublist (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
        (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 parent)) := by
  have hterm := canonicalProjectivePostConeRawContourTerm_eq_deeper_source_word
    hp hp2 parent child hdeep s hs hcarrier
  simpa only [hterm] using
    canonicalProjectivePostConeRawContourTerm_sublist_slotWord hp hp2 parent s hs

/-- A deeper child inserted negatively in a parent side has its sign
flipped there; the parent's inverse reversal flips it back when its own
distinguished edge is physically source-oriented. -/
theorem canonicalProjectivePostConeRawTreeWordBySlot_child_target_sublist_parent
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (parent child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hdeep : canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 parent <
      canonicalProjectivePostConeTreeSlotTargetDepth hp hp2 child)
    (s : ProjectivePolygonSide)
    (hs : s ≠ canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 parent)
    (hcarrier :
      (⟨parent.right.state⟩ : ProjectivePolygonPostConeFace p) =
          projectivePolygonPostConeEdgeTarget
            (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) ∧
        s = projectivePolygonPostConeEdgeTargetSide
          (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) ∧
        canonicalProjectiveConePostConeBoundaryTerm p parent.right.state s =
          (FreeGroup.of (canonicalProjectivePostConeTreeSlotLabel hp hp2 child))⁻¹) :
    (parent.right = projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 parent) →
      List.Sublist (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
        (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 parent)) ∧
    (parent.right ≠ projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 parent) →
      List.Sublist (FreeGroup.invRev
        (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child))
          (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 parent)) := by
  have hterm := canonicalProjectivePostConeRawContourTerm_eq_deeper_target_word
    hp hp2 parent child hdeep s hs hcarrier
  have hsub :=
    canonicalProjectivePostConeRawContourTerm_sublist_slotWord hp hp2 parent s hs
  rw [hterm] at hsub
  simpa only [FreeGroup.invRev_invRev] using hsub

/-- The source-oriented side of a child edge is automatically off the
parent pivot. Hence actual adjacent tree slots inherit the injective
sublist transport, without a separately assumed side inequality. -/
theorem canonicalProjectivePostConeRawTreeWordBySlot_child_source_sublist_of_adjacent
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (parent child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hjoin : parent.right = child.left)
    (hchildSource : child.left = projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 child)) :
    (parent.right = projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 parent) →
      List.Sublist (FreeGroup.invRev
        (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child))
          (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 parent)) ∧
    (parent.right ≠ projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 parent) →
      List.Sublist (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
        (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 parent)) := by
  let z := canonicalProjectivePostConeTreeSlotLabel hp hp2 child
  have hdeep := canonicalProjectivePostConeTreeSlot_targetDepth_lt_of_right_eq_left
    hp hp2 hjoin
  have hlabelNe : z ≠ canonicalProjectivePostConeTreeSlotLabel hp hp2 parent := by
    intro hlabel
    have heq := canonicalProjectivePostConeTreeSlotLabel_injective hp hp2 hlabel
    subst child
    exact (lt_irrefl _) hdeep
  have hface : parent.right = projectivePolygonPostConeEdgeSource z :=
    hjoin.trans hchildSource
  have hs : projectivePolygonPostConeEdgeSide z ≠
      canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 parent :=
    canonicalProjectivePostConeRawTreeWord_source_ne_pivot_of_label_ne
      hp hp2 parent z hlabelNe hface
  have hcarrier :
      (⟨parent.right.state⟩ : ProjectivePolygonPostConeFace p) =
          projectivePolygonPostConeEdgeSource z ∧
        projectivePolygonPostConeEdgeSide z = projectivePolygonPostConeEdgeSide z ∧
        canonicalProjectiveConePostConeBoundaryTerm p parent.right.state
          (projectivePolygonPostConeEdgeSide z) = FreeGroup.of z := by
    refine ⟨?_, rfl, ?_⟩
    · apply ProjectivePolygonPostConeFace.stateEquiv.injective
      exact congrArg ProjectivePolygonPostConeFace.state hface
    · rw [congrArg ProjectivePolygonPostConeFace.state hface]
      exact canonicalProjectiveConePostConeBoundaryTerm_edgeSource_eq z
  exact canonicalProjectivePostConeRawTreeWordBySlot_child_source_sublist_parent
    hp hp2 parent child hdeep (projectivePolygonPostConeEdgeSide z) hs hcarrier

/-- The target-oriented side of an adjacent child edge is likewise off the
parent pivot, and its inverse-reversal transport is a literal sublist. -/
theorem canonicalProjectivePostConeRawTreeWordBySlot_child_target_sublist_of_adjacent
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (parent child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hjoin : parent.right = child.left)
    (hchildTarget : child.left = projectivePolygonPostConeEdgeTarget
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 child)) :
    (parent.right = projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 parent) →
      List.Sublist (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
        (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 parent)) ∧
    (parent.right ≠ projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 parent) →
      List.Sublist (FreeGroup.invRev
        (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child))
          (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 parent)) := by
  let z := canonicalProjectivePostConeTreeSlotLabel hp hp2 child
  have hdeep := canonicalProjectivePostConeTreeSlot_targetDepth_lt_of_right_eq_left
    hp hp2 hjoin
  have hlabelNe : z ≠ canonicalProjectivePostConeTreeSlotLabel hp hp2 parent := by
    intro hlabel
    have heq := canonicalProjectivePostConeTreeSlotLabel_injective hp hp2 hlabel
    subst child
    exact (lt_irrefl _) hdeep
  have hface : parent.right = projectivePolygonPostConeEdgeTarget z :=
    hjoin.trans hchildTarget
  have hs : projectivePolygonPostConeEdgeTargetSide z ≠
      canonicalProjectivePostConeTreeSlotRightFactorSide hp hp2 parent :=
    canonicalProjectivePostConeRawTreeWord_target_ne_pivot_of_label_ne
      hp hp2 parent z hlabelNe hface
  have hcarrier :
      (⟨parent.right.state⟩ : ProjectivePolygonPostConeFace p) =
          projectivePolygonPostConeEdgeTarget z ∧
        projectivePolygonPostConeEdgeTargetSide z = projectivePolygonPostConeEdgeTargetSide z ∧
        canonicalProjectiveConePostConeBoundaryTerm p parent.right.state
          (projectivePolygonPostConeEdgeTargetSide z) = (FreeGroup.of z)⁻¹ := by
    refine ⟨?_, rfl, ?_⟩
    · apply ProjectivePolygonPostConeFace.stateEquiv.injective
      exact congrArg ProjectivePolygonPostConeFace.state hface
    · rw [congrArg ProjectivePolygonPostConeFace.state hface]
      exact canonicalProjectiveConePostConeBoundaryTerm_edgeTarget_eq_inv hp hp2 z
  exact canonicalProjectivePostConeRawTreeWordBySlot_child_target_sublist_parent
    hp hp2 parent child hdeep (projectivePolygonPostConeEdgeTargetSide z) hs hcarrier

/-- Any two adjacent canonical tree slots admit a literal occurrence
embedding from the child word into the parent word, possibly after the
single inverse reversal forced by their physical orientations. -/
theorem canonicalProjectivePostConeRawTreeWordBySlot_child_sublist_of_adjacent
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (parent child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hjoin : parent.right = child.left) :
    List.Sublist (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child)
      (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 parent) ∨
    List.Sublist (FreeGroup.invRev
      (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child))
        (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 parent) := by
  rcases canonicalProjectivePostConeTreeSlot_left_eq_physicalSource_or_target
      hp hp2 child with hsource | htarget
  · have hstep := canonicalProjectivePostConeRawTreeWordBySlot_child_source_sublist_of_adjacent
      hp hp2 parent child hjoin hsource
    by_cases hpSource : parent.right = projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 parent)
    · exact Or.inr (hstep.1 hpSource)
    · exact Or.inl (hstep.2 hpSource)
  · have hstep := canonicalProjectivePostConeRawTreeWordBySlot_child_target_sublist_of_adjacent
      hp hp2 parent child hjoin htarget
    by_cases hpSource : parent.right = projectivePolygonPostConeEdgeSource
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 parent)
    · exact Or.inl (hstep.1 hpSource)
    · exact Or.inr (hstep.2 hpSource)

/-- Concrete one-step transport of every child occurrence index through an
adjacent tree slot. The index map is injective, so distinct occurrences stay
distinct; all signs are either preserved or all flipped according to the
two physical orientations. -/
theorem canonicalProjectivePostConeRawTreeWordBySlot_child_indexEmbedding_of_adjacent
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (parent child : CanonicalProjectivePostConeTreeSlot hp hp2)
    (hjoin : parent.right = child.left) :
    ∃ f : Fin (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).length →
        Fin (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 parent).length,
      Function.Injective f ∧
        ((∀ i, (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 parent).get (f i) =
          (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get i) ∨
        (∀ i, (canonicalProjectivePostConeRawTreeWordBySlot hp hp2 parent).get (f i) =
          (((canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get i).1,
            !((canonicalProjectivePostConeRawTreeWordBySlot hp hp2 child).get i).2))) := by
  rcases canonicalProjectivePostConeRawTreeWordBySlot_child_sublist_of_adjacent
      hp hp2 parent child hjoin with hsub | hsub
  · obtain ⟨e, he⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
    exact ⟨e, e.injective, Or.inl (fun i => (he i).symm)⟩
  · obtain ⟨e, he⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
    refine ⟨fun i => e (invRevPosition i), ?_, Or.inr ?_⟩
    · intro i j hij
      exact (invRevPosition_bijective _).1 (e.injective hij)
    · intro i
      exact (he (invRevPosition i)).symm.trans (get_invRevPosition _ i)

/-- The orientation change in one parent-child transport step. -/
noncomputable def canonicalProjectivePostConeRawSlotStepFlip
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (parent child : CanonicalProjectivePostConeTreeSlot hp hp2) : Bool := by
  classical
  exact if parent.right = projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 parent) then
    if child.left = projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) then true else false
  else
    if child.left = projectivePolygonPostConeEdgeSource
      (canonicalProjectivePostConeTreeSlotLabel hp hp2 child) then false else true

/-! A slot endpoint is a vertex in the symmetrized wide subquiver. Keep that
type explicit here so source/target casts and endpoint equalities line up. -/
abbrev CanonicalProjectivePostConeTreeVertex
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :=
  WideSubquiver.toType (Quiver.Symmetrify (ProjectivePolygonPostConeFace p))
    (projectivePolygonPostConeCanonicalSpanningTree hp hp2)

end

end SystolicGrowth
