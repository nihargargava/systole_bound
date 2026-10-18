module

public import BuserSarnak.BuserSarnakProjectivePostConeTietze

@[expose] public section

/-!
# Post-cone polygon-word factors

This module exposes the eight substituted side words of a projective polygon
boundary.  In particular, the retained label of a physical post-cone edge is
an explicit factor of the polygon word at the face from which that edge is
traversed.  Later tree elimination uses this local factorization together with
the depth-descending order of physical-tree slots.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete
open ReidemeisterSchreier.Discrete.Presentations

noncomputable local instance buserSarnakProjectivePostConePolygonFactorsRangeFintype
    (p : ℕ) [NeZero p] : Fintype (BuserSarnakProjectiveReductionRange p) :=
  Fintype.ofFinite _

noncomputable local instance buserSarnakProjectivePostConePolygonFactorsDegenerateDecidable
    {p : ℕ} [NeZero p] :
    DecidablePred
      (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol :=
  Classical.decPred _

/-- The first-cone-stage image of the cleaned Schreier word attached to one
oriented polygon side. -/
noncomputable def canonicalProjectiveConePostConeSideWord
    (p : ℕ) [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide) :
    FreeGroup (CanonicalProjectiveConeKeptSymbol p) :=
  canonicalProjectiveConeFirstStageSubstitution p
    ((CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol q s))

/-- The post-cone polygon word is the ordered product of its eight substituted
side words, with the two inverse boundary occurrences inverted. -/
theorem canonicalProjectiveConePostConePolygonWord_eq_sideWords
    {p : ℕ} [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p) :
    canonicalProjectiveConePostConePolygonWord p q =
      canonicalProjectiveConePostConeSideWord p q .a *
      canonicalProjectiveConePostConeSideWord p q .e1 *
      (canonicalProjectiveConePostConeSideWord p q .cInv)⁻¹ *
      canonicalProjectiveConePostConeSideWord p q .e2 *
      (canonicalProjectiveConePostConeSideWord p q .aInv)⁻¹ *
      canonicalProjectiveConePostConeSideWord p q .e3 *
      canonicalProjectiveConePostConeSideWord p q .c *
      canonicalProjectiveConePostConeSideWord p q .e4 := by
  simp [canonicalProjectiveConePostConePolygonWord,
    canonicalProjectiveConePostConeSideWord,
    BuserSarnakProjectiveQuotientSectionData.polygonCleanedWord,
    BuserSarnakProjectiveQuotientSectionData.polygonSideRawSymbol]

/-- At the source face of a retained physical edge, its positive side word is
exactly the corresponding retained free generator. -/
theorem canonicalProjectiveConePostConeSideWord_edgeSource_eq
    {p : ℕ} [NeZero p]
    (z : CanonicalProjectiveConeKeptSymbol p) :
    canonicalProjectiveConePostConeSideWord p
      (projectivePolygonPostConeEdgeSource z).state
      (projectivePolygonPostConeEdgeSide z) = FreeGroup.of z := by
  unfold canonicalProjectiveConePostConeSideWord
  rw [projectivePolygonPostConeEdgeSource_rawSymbol]
  rw [(CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord_of_not_degenerate]
  exact canonicalProjectiveConeFirstStageSubstitution_of_kept z

/-- The oriented word contributed by a named side of the polygon boundary. -/
noncomputable def canonicalProjectiveConePostConeBoundaryTerm
    (p : ℕ) [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p) :
    ProjectivePolygonSide → FreeGroup (CanonicalProjectiveConeKeptSymbol p)
  | .a => canonicalProjectiveConePostConeSideWord p q .a
  | .e1 => canonicalProjectiveConePostConeSideWord p q .e1
  | .cInv => (canonicalProjectiveConePostConeSideWord p q .cInv)⁻¹
  | .e2 => canonicalProjectiveConePostConeSideWord p q .e2
  | .aInv => (canonicalProjectiveConePostConeSideWord p q .aInv)⁻¹
  | .e3 => canonicalProjectiveConePostConeSideWord p q .e3
  | .c => canonicalProjectiveConePostConeSideWord p q .c
  | .e4 => canonicalProjectiveConePostConeSideWord p q .e4

/-- The part of the displayed polygon boundary strictly before a side. -/
noncomputable def canonicalProjectiveConePostConeBoundaryPrefix
    (p : ℕ) [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p) :
    ProjectivePolygonSide → FreeGroup (CanonicalProjectiveConeKeptSymbol p)
  | .a => 1
  | .e1 => canonicalProjectiveConePostConeBoundaryTerm p q .a
  | .cInv => canonicalProjectiveConePostConeBoundaryTerm p q .a *
      canonicalProjectiveConePostConeBoundaryTerm p q .e1
  | .e2 => canonicalProjectiveConePostConeBoundaryTerm p q .a *
      canonicalProjectiveConePostConeBoundaryTerm p q .e1 *
      canonicalProjectiveConePostConeBoundaryTerm p q .cInv
  | .aInv => canonicalProjectiveConePostConeBoundaryTerm p q .a *
      canonicalProjectiveConePostConeBoundaryTerm p q .e1 *
      canonicalProjectiveConePostConeBoundaryTerm p q .cInv *
      canonicalProjectiveConePostConeBoundaryTerm p q .e2
  | .e3 => canonicalProjectiveConePostConeBoundaryTerm p q .a *
      canonicalProjectiveConePostConeBoundaryTerm p q .e1 *
      canonicalProjectiveConePostConeBoundaryTerm p q .cInv *
      canonicalProjectiveConePostConeBoundaryTerm p q .e2 *
      canonicalProjectiveConePostConeBoundaryTerm p q .aInv
  | .c => canonicalProjectiveConePostConeBoundaryTerm p q .a *
      canonicalProjectiveConePostConeBoundaryTerm p q .e1 *
      canonicalProjectiveConePostConeBoundaryTerm p q .cInv *
      canonicalProjectiveConePostConeBoundaryTerm p q .e2 *
      canonicalProjectiveConePostConeBoundaryTerm p q .aInv *
      canonicalProjectiveConePostConeBoundaryTerm p q .e3
  | .e4 => canonicalProjectiveConePostConeBoundaryTerm p q .a *
      canonicalProjectiveConePostConeBoundaryTerm p q .e1 *
      canonicalProjectiveConePostConeBoundaryTerm p q .cInv *
      canonicalProjectiveConePostConeBoundaryTerm p q .e2 *
      canonicalProjectiveConePostConeBoundaryTerm p q .aInv *
      canonicalProjectiveConePostConeBoundaryTerm p q .e3 *
      canonicalProjectiveConePostConeBoundaryTerm p q .c

/-- The part of the displayed polygon boundary strictly after a side. -/
noncomputable def canonicalProjectiveConePostConeBoundarySuffix
    (p : ℕ) [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p) :
    ProjectivePolygonSide → FreeGroup (CanonicalProjectiveConeKeptSymbol p)
  | .a => canonicalProjectiveConePostConeBoundaryTerm p q .e1 *
      canonicalProjectiveConePostConeBoundaryTerm p q .cInv *
      canonicalProjectiveConePostConeBoundaryTerm p q .e2 *
      canonicalProjectiveConePostConeBoundaryTerm p q .aInv *
      canonicalProjectiveConePostConeBoundaryTerm p q .e3 *
      canonicalProjectiveConePostConeBoundaryTerm p q .c *
      canonicalProjectiveConePostConeBoundaryTerm p q .e4
  | .e1 => canonicalProjectiveConePostConeBoundaryTerm p q .cInv *
      canonicalProjectiveConePostConeBoundaryTerm p q .e2 *
      canonicalProjectiveConePostConeBoundaryTerm p q .aInv *
      canonicalProjectiveConePostConeBoundaryTerm p q .e3 *
      canonicalProjectiveConePostConeBoundaryTerm p q .c *
      canonicalProjectiveConePostConeBoundaryTerm p q .e4
  | .cInv => canonicalProjectiveConePostConeBoundaryTerm p q .e2 *
      canonicalProjectiveConePostConeBoundaryTerm p q .aInv *
      canonicalProjectiveConePostConeBoundaryTerm p q .e3 *
      canonicalProjectiveConePostConeBoundaryTerm p q .c *
      canonicalProjectiveConePostConeBoundaryTerm p q .e4
  | .e2 => canonicalProjectiveConePostConeBoundaryTerm p q .aInv *
      canonicalProjectiveConePostConeBoundaryTerm p q .e3 *
      canonicalProjectiveConePostConeBoundaryTerm p q .c *
      canonicalProjectiveConePostConeBoundaryTerm p q .e4
  | .aInv => canonicalProjectiveConePostConeBoundaryTerm p q .e3 *
      canonicalProjectiveConePostConeBoundaryTerm p q .c *
      canonicalProjectiveConePostConeBoundaryTerm p q .e4
  | .e3 => canonicalProjectiveConePostConeBoundaryTerm p q .c *
      canonicalProjectiveConePostConeBoundaryTerm p q .e4
  | .c => canonicalProjectiveConePostConeBoundaryTerm p q .e4
  | .e4 => 1

/-- Every displayed polygon boundary is an explicit prefix–side–suffix
factorization at any one of its eight occurrences. -/
theorem canonicalProjectiveConePostConePolygonWord_eq_prefix_term_suffix
    {p : ℕ} [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide) :
    canonicalProjectiveConePostConePolygonWord p q =
      canonicalProjectiveConePostConeBoundaryPrefix p q s *
        canonicalProjectiveConePostConeBoundaryTerm p q s *
          canonicalProjectiveConePostConeBoundarySuffix p q s := by
  cases s <;>
    rw [canonicalProjectiveConePostConePolygonWord_eq_sideWords] <;>
    simp only [canonicalProjectiveConePostConeBoundaryTerm,
      canonicalProjectiveConePostConeBoundaryPrefix,
      canonicalProjectiveConePostConeBoundarySuffix] <;>
    group

/-- At its physical source, the oriented boundary term of a retained edge is
the corresponding retained free generator. -/
theorem canonicalProjectiveConePostConeBoundaryTerm_edgeSource_eq
    {p : ℕ} [NeZero p]
    (z : CanonicalProjectiveConeKeptSymbol p) :
    canonicalProjectiveConePostConeBoundaryTerm p
      (projectivePolygonPostConeEdgeSource z).state
      (projectivePolygonPostConeEdgeSide z) = FreeGroup.of z := by
  cases h : z.1.1.2 <;>
    simpa [canonicalProjectiveConePostConeBoundaryTerm,
      projectivePolygonPostConeEdgeSide,
      ProjectiveOctagonGenerator.positivePolygonSide, h] using
      canonicalProjectiveConePostConeSideWord_edgeSource_eq z

/-- The retained label of a physical post-cone edge is a visible, positively
oriented factor of the polygon word at its source face. -/
theorem canonicalProjectiveConePostConePolygonWord_edgeSource_factor
    {p : ℕ} [NeZero p]
    (z : CanonicalProjectiveConeKeptSymbol p) :
    canonicalProjectiveConePostConePolygonWord p
        (projectivePolygonPostConeEdgeSource z).state =
      canonicalProjectiveConePostConeBoundaryPrefix p
          (projectivePolygonPostConeEdgeSource z).state
          (projectivePolygonPostConeEdgeSide z) *
        FreeGroup.of z *
          canonicalProjectiveConePostConeBoundarySuffix p
            (projectivePolygonPostConeEdgeSource z).state
            (projectivePolygonPostConeEdgeSide z) := by
  rw [canonicalProjectiveConePostConePolygonWord_eq_prefix_term_suffix,
    canonicalProjectiveConePostConeBoundaryTerm_edgeSource_eq]

end

end SystolicGrowth
