module

public import BuserSarnak.BuserSarnakProjectiveLevelMarking

@[expose] public section

/-!
# Height facts for the canonical projective Schreier tree

The canonical positive representatives orient every deleted Schreier symbol
away from the identity.  This module records the elementary height increase
needed for the maximal-height part of the tree--cotree argument.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete

noncomputable local instance buserSarnakProjectiveCanonicalTreeRangeFintype
    (p : ℕ) [NeZero p] : Fintype (BuserSarnakProjectiveReductionRange p) :=
  Fintype.ofFinite _

/-- The finite Schreier data attached to the canonical projective section. -/
abbrev CanonicalProjectiveTreeSchreierData (p : ℕ) [NeZero p] :=
  (canonicalBuserSarnakProjectiveQuotientSectionData p).schreierData
    |>.toFiniteQuotientSchreierData

/-- The length of the canonical positive representative of a projective
quotient state. -/
def canonicalProjectiveWordHeight
    (p : ℕ) [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p) : ℕ :=
  (canonicalPositiveProjectiveWord p q).length

/-- A degenerate canonical Schreier symbol increases representative height by
one along its transition. -/
theorem canonicalProjectiveWordHeight_transition_eq_succ_of_isDegenerate
    {p : ℕ} [NeZero p]
    {q : BuserSarnakProjectiveReductionRange p}
    {x : ProjectiveOctagonGenerator}
    (h : (CanonicalProjectiveTreeSchreierData p).IsDegenerateSchreierSymbol
      (q, x)) :
    canonicalProjectiveWordHeight p
      ((CanonicalProjectiveTreeSchreierData p).transition q x) =
      canonicalProjectiveWordHeight p q + 1 := by
  have hword := canonicalBuserSarnakProjective_isDegenerate_word h
  have hlength := congrArg List.length hword
  simpa only [canonicalProjectiveWordHeight, positiveSignedProjectiveWord,
    List.length_map, List.length_append, List.length_singleton] using hlength

/-- In particular, a degenerate transition never returns to its source. -/
theorem canonicalProjectiveWordHeight_lt_transition_of_isDegenerate
    {p : ℕ} [NeZero p]
    {q : BuserSarnakProjectiveReductionRange p}
    {x : ProjectiveOctagonGenerator}
    (h : (CanonicalProjectiveTreeSchreierData p).IsDegenerateSchreierSymbol
      (q, x)) :
    canonicalProjectiveWordHeight p q <
      canonicalProjectiveWordHeight p
        ((CanonicalProjectiveTreeSchreierData p).transition q x) := by
  rw [canonicalProjectiveWordHeight_transition_eq_succ_of_isDegenerate h]
  omega

/-- The target endpoint of an oriented canonical projective tree edge. -/
def canonicalProjectiveTreeTarget
    (p : ℕ) [NeZero p]
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p) :
    BuserSarnakProjectiveReductionRange p :=
  (canonicalBuserSarnakProjectiveDegenerateTarget p z).1

/-- Every oriented canonical tree edge strictly increases the canonical-word
height from its source to its target. -/
theorem canonicalProjectiveWordHeight_lt_treeTarget
    {p : ℕ} [NeZero p]
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p) :
    canonicalProjectiveWordHeight p z.1.1 <
      canonicalProjectiveWordHeight p (canonicalProjectiveTreeTarget p z) := by
  exact canonicalProjectiveWordHeight_lt_transition_of_isDegenerate z.2

/-- A nonempty finite family of canonical tree edges has an edge with maximal
target height. -/
theorem canonicalProjectiveTree_exists_maxTargetHeight
    {p : ℕ} [NeZero p]
    (B : Finset (CanonicalBuserSarnakProjectiveDegenerateSymbol p))
    (hB : B.Nonempty) :
    ∃ z ∈ B, ∀ w ∈ B,
      canonicalProjectiveWordHeight p (canonicalProjectiveTreeTarget p w) ≤
        canonicalProjectiveWordHeight p (canonicalProjectiveTreeTarget p z) := by
  classical
  exact Finset.exists_max_image B
    (fun z => canonicalProjectiveWordHeight p (canonicalProjectiveTreeTarget p z)) hB

/-- At a maximal target height, no distinct edge in the same finite family
can be incident to that target.  This is the leaf step of the cut argument. -/
theorem canonicalProjectiveTree_maxTarget_incident_eq
    {p : ℕ} [NeZero p]
    {B : Finset (CanonicalBuserSarnakProjectiveDegenerateSymbol p)}
    {z w : CanonicalBuserSarnakProjectiveDegenerateSymbol p}
    (hw : w ∈ B)
    (hmax : ∀ u ∈ B,
      canonicalProjectiveWordHeight p (canonicalProjectiveTreeTarget p u) ≤
        canonicalProjectiveWordHeight p (canonicalProjectiveTreeTarget p z))
    (hincident : w.1.1 = canonicalProjectiveTreeTarget p z ∨
      canonicalProjectiveTreeTarget p w = canonicalProjectiveTreeTarget p z) :
    w = z := by
  rcases hincident with hsource | htarget
  · exfalso
    have hlt := canonicalProjectiveWordHeight_lt_treeTarget w
    have hle := hmax w hw
    rw [hsource] at hlt
    omega
  · apply canonicalBuserSarnakProjectiveDegenerateTarget_injective p
    apply Subtype.ext
    exact htarget

end

end SystolicGrowth
