module

public import BuserSarnak.BuserSarnakProjectivePostConeContour
public import BuserSarnak.BuserSarnakProjectivePostConeDirectPresentation
public import Mathlib.GroupTheory.FreeGroup.Reduce

@[expose] public section

/-!
# A recursively spliced contour for the direct root word

The direct tree substitution replaces each selected physical-tree letter by
its reverse-depth recursive defining word.  This file exposes the result as
an ordered boundary contour: first as a list of fully substituted factors,
and then as a literal signed list on the final free alphabet.  Its value is
exactly the named direct root word.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete
open ReidemeisterSchreier.Discrete.Presentations

/-- The eight sides of a projective polygon in its displayed oriented
boundary order. -/
def canonicalProjectivePostConeBoundarySideCycle : List ProjectivePolygonSide :=
  [.a, .e1, .cInv, .e2, .aInv, .e3, .c, .e4]

/-- The ordered post-cone boundary terms of one polygon. -/
noncomputable def canonicalProjectiveConePostConeBoundaryTermContour
    (p : ℕ) [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p) :
    List (FreeGroup (CanonicalProjectiveConeKeptSymbol p)) :=
  canonicalProjectivePostConeBoundarySideCycle.map
    (canonicalProjectiveConePostConeBoundaryTerm p q)

/-- Evaluating the ordered boundary-term contour recovers the original
post-cone polygon word. -/
theorem canonicalProjectiveConePostConeBoundaryTermContour_prod
    {p : ℕ} [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p) :
    (canonicalProjectiveConePostConeBoundaryTermContour p q).prod =
      canonicalProjectiveConePostConePolygonWord p q := by
  rw [canonicalProjectiveConePostConePolygonWord_eq_sideWords]
  simp only [canonicalProjectiveConePostConeBoundaryTermContour,
    canonicalProjectivePostConeBoundarySideCycle, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, canonicalProjectiveConePostConeBoundaryTerm]
  group

/-- One fully spliced boundary factor.  On a tree letter this applies the
reverse-depth recursive defining word; on a final edge it leaves the letter
visible. -/
noncomputable def canonicalProjectivePostConeDirectSplicedBoundaryTerm
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide) :
    FreeGroup (CanonicalProjectivePostConeFinalGenerator hp hp2) :=
  canonicalProjectivePostConeDirectFinalSubstitution hp hp2
    (canonicalProjectiveConePostConeBoundaryTerm p q s)

/-- Splice all eight terms of a polygon contour through the direct recursive
tree substitution. -/
noncomputable def canonicalProjectivePostConeDirectSplicedBoundaryContour
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) :
    List (FreeGroup (CanonicalProjectivePostConeFinalGenerator hp hp2)) :=
  canonicalProjectivePostConeBoundarySideCycle.map
    (canonicalProjectivePostConeDirectSplicedBoundaryTerm hp hp2 q)

/-- Splicing respects reversal across every paired contour dart. -/
theorem canonicalProjectivePostConeDirectSplicedBoundaryTerm_partner_eq_inv
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide) :
    canonicalProjectivePostConeDirectSplicedBoundaryTerm hp hp2
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).1
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).2 =
        (canonicalProjectivePostConeDirectSplicedBoundaryTerm hp hp2 q s)⁻¹ := by
  exact canonicalProjectivePostConeDirectFinalSubstitution_boundaryTerm_partner_eq_inv
    hp hp2 q s

/-- A source occurrence of a deleted tree letter is replaced by its explicit
reverse-depth recursive word. -/
theorem canonicalProjectivePostConeDirectSplicedBoundaryTerm_eq_treeWord_of_source
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide)
    (z : CanonicalProjectiveConeKeptSymbol p)
    (hterm : canonicalProjectiveConePostConeBoundaryTerm p q s = FreeGroup.of z)
    (hz : isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z) :
    canonicalProjectivePostConeDirectSplicedBoundaryTerm hp hp2 q s =
      canonicalProjectivePostConeDirectTreeEliminationWord hp hp2 ⟨z, hz⟩ := by
  unfold canonicalProjectivePostConeDirectSplicedBoundaryTerm
  rw [hterm, canonicalProjectivePostConeDirectFinalSubstitution_of_deleted hp hp2 z hz]

/-- A target occurrence of a deleted tree letter is replaced by the inverse
of its explicit reverse-depth recursive word. -/
theorem canonicalProjectivePostConeDirectSplicedBoundaryTerm_eq_inv_treeWord_of_target
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide)
    (z : CanonicalProjectiveConeKeptSymbol p)
    (hterm : canonicalProjectiveConePostConeBoundaryTerm p q s = (FreeGroup.of z)⁻¹)
    (hz : isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z) :
    canonicalProjectivePostConeDirectSplicedBoundaryTerm hp hp2 q s =
      (canonicalProjectivePostConeDirectTreeEliminationWord hp hp2 ⟨z, hz⟩)⁻¹ := by
  unfold canonicalProjectivePostConeDirectSplicedBoundaryTerm
  rw [hterm, map_inv,
    canonicalProjectivePostConeDirectFinalSubstitution_of_deleted hp hp2 z hz]

/-- The product of a fully spliced face contour is the direct substitution of
that face's polygon word. -/
theorem canonicalProjectivePostConeDirectSplicedBoundaryContour_prod
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) :
    (canonicalProjectivePostConeDirectSplicedBoundaryContour hp hp2 q).prod =
      canonicalProjectivePostConeDirectFinalSubstitution hp hp2
        (canonicalProjectiveConePostConePolygonWord p q) := by
  change (List.map (canonicalProjectivePostConeDirectFinalSubstitution hp hp2)
    (canonicalProjectiveConePostConeBoundaryTermContour p q)).prod = _
  rw [← map_list_prod, canonicalProjectiveConePostConeBoundaryTermContour_prod]

/-- The fully spliced global contour based at the canonical dual-tree root. -/
noncomputable def canonicalProjectivePostConeDirectRootSplicedBoundaryContour
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    List (FreeGroup (CanonicalProjectivePostConeFinalGenerator hp hp2)) :=
  canonicalProjectivePostConeDirectSplicedBoundaryContour hp hp2
    (canonicalProjectivePostConeTreeRoot hp hp2).state

/-- The product of the recursively spliced global root contour is precisely
the named direct root word. -/
theorem canonicalProjectivePostConeDirectRootSplicedBoundaryContour_prod
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    (canonicalProjectivePostConeDirectRootSplicedBoundaryContour hp hp2).prod =
      canonicalProjectivePostConeDirectRootWord hp hp2 := by
  unfold canonicalProjectivePostConeDirectRootSplicedBoundaryContour
    canonicalProjectivePostConeDirectRootWord
  exact canonicalProjectivePostConeDirectSplicedBoundaryContour_prod hp hp2 _

private theorem freeGroup_mk_flatten_map_toWord_eq_prod
    {α : Type*} [DecidableEq α] (xs : List (FreeGroup α)) :
    FreeGroup.mk (List.flatten (List.map FreeGroup.toWord xs)) = xs.prod := by
  classical
  induction xs with
  | nil => exact FreeGroup.one_eq_mk.symm
  | cons x xs ih =>
      simp only [List.map_cons, List.flatten_cons, List.prod_cons]
      rw [← FreeGroup.mul_mk, FreeGroup.mk_toWord, ih]

/-- A literal signed final-generator word obtained by flattening the
recursively spliced root contour. -/
noncomputable def canonicalProjectivePostConeDirectRootSplicedLetterWord
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    List (CanonicalProjectivePostConeFinalGenerator hp hp2 × Bool) := by
  classical
  exact List.flatten (List.map FreeGroup.toWord
    (canonicalProjectivePostConeDirectRootSplicedBoundaryContour hp hp2))

/-- Evaluating the explicit signed final-generator list gives the direct root
word without adding a normalization assumption. -/
theorem canonicalProjectivePostConeDirectRootSplicedLetterWord_eval
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    FreeGroup.mk (canonicalProjectivePostConeDirectRootSplicedLetterWord hp hp2) =
      canonicalProjectivePostConeDirectRootWord hp hp2 := by
  classical
  unfold canonicalProjectivePostConeDirectRootSplicedLetterWord
  rw [freeGroup_mk_flatten_map_toWord_eq_prod]
  exact canonicalProjectivePostConeDirectRootSplicedBoundaryContour_prod hp hp2

end

end SystolicGrowth
