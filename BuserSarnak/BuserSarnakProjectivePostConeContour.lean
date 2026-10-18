module

public import BuserSarnak.BuserSarnakProjectivePostConeDirectTreeWords

@[expose] public section

/-!
# Orientation reversal along the post-cone polygon contour

The side-pairing involution reverses every first-stage post-cone boundary
term.  This is the global oriented-contour law behind the two occurrences of
each physical edge in the residual one-face word.  Applying the direct tree
substitution preserves the law on the final survivor alphabet.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete
open ReidemeisterSchreier.Discrete.Presentations

/-- Crossing any paired polygon side reverses its complete post-cone boundary
term.  The non-cone cases use equality of their raw Schreier symbols; the
four cone cases use the cone-pair elimination relation. -/
theorem canonicalProjectiveConePostConeBoundaryTerm_partner_eq_inv
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide) :
    canonicalProjectiveConePostConeBoundaryTerm p
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).1
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).2 =
        (canonicalProjectiveConePostConeBoundaryTerm p q s)⁻¹ := by
  let S := canonicalBuserSarnakProjectiveQuotientSectionData p
  cases s with
  | a =>
      have hraw :
          S.polygonSideRawSymbol (S.polygonSidePartner q .a).1
              (S.polygonSidePartner q .a).2 = S.polygonSideRawSymbol q .a := by
        simpa using S.polygonSideRawSymbol_partner q .a
      simp only [canonicalProjectiveConePostConeBoundaryTerm]
      change (canonicalProjectiveConePostConeSideWord p
        (S.polygonSidePartner q .a).1 (S.polygonSidePartner q .a).2)⁻¹ = _
      unfold canonicalProjectiveConePostConeSideWord
      rw [hraw]
  | e1 =>
      simpa [S, canonicalProjectiveConePostConeBoundaryTerm,
        ProjectiveOctagonConeGenerator.lift,
        ProjectiveOctagonGenerator.positivePolygonSide] using
        canonicalProjectiveConePostConeBoundaryTerm_partnerCone_eq_inv
        hp hp2 q .e1
  | cInv =>
      have hraw :
          S.polygonSideRawSymbol (S.polygonSidePartner q .cInv).1
              (S.polygonSidePartner q .cInv).2 = S.polygonSideRawSymbol q .cInv := by
        simpa using S.polygonSideRawSymbol_partner q .cInv
      simp only [canonicalProjectiveConePostConeBoundaryTerm]
      change canonicalProjectiveConePostConeSideWord p
        (S.polygonSidePartner q .cInv).1 (S.polygonSidePartner q .cInv).2 = _
      unfold canonicalProjectiveConePostConeSideWord
      rw [hraw]
      simp [S]
  | e2 =>
      simpa [S, canonicalProjectiveConePostConeBoundaryTerm,
        ProjectiveOctagonConeGenerator.lift,
        ProjectiveOctagonGenerator.positivePolygonSide] using
        canonicalProjectiveConePostConeBoundaryTerm_partnerCone_eq_inv
        hp hp2 q .e2
  | aInv =>
      have hraw :
          S.polygonSideRawSymbol (S.polygonSidePartner q .aInv).1
              (S.polygonSidePartner q .aInv).2 = S.polygonSideRawSymbol q .aInv := by
        simpa using S.polygonSideRawSymbol_partner q .aInv
      simp only [canonicalProjectiveConePostConeBoundaryTerm]
      change canonicalProjectiveConePostConeSideWord p
        (S.polygonSidePartner q .aInv).1 (S.polygonSidePartner q .aInv).2 = _
      unfold canonicalProjectiveConePostConeSideWord
      rw [hraw]
      simp [S]
  | e3 =>
      simpa [S, canonicalProjectiveConePostConeBoundaryTerm,
        ProjectiveOctagonConeGenerator.lift,
        ProjectiveOctagonGenerator.positivePolygonSide] using
        canonicalProjectiveConePostConeBoundaryTerm_partnerCone_eq_inv
        hp hp2 q .e3
  | c =>
      have hraw :
          S.polygonSideRawSymbol (S.polygonSidePartner q .c).1
              (S.polygonSidePartner q .c).2 = S.polygonSideRawSymbol q .c := by
        simpa using S.polygonSideRawSymbol_partner q .c
      simp only [canonicalProjectiveConePostConeBoundaryTerm]
      change (canonicalProjectiveConePostConeSideWord p
        (S.polygonSidePartner q .c).1 (S.polygonSidePartner q .c).2)⁻¹ = _
      unfold canonicalProjectiveConePostConeSideWord
      rw [hraw]
  | e4 =>
      simpa [S, canonicalProjectiveConePostConeBoundaryTerm,
        ProjectiveOctagonConeGenerator.lift,
        ProjectiveOctagonGenerator.positivePolygonSide] using
        canonicalProjectiveConePostConeBoundaryTerm_partnerCone_eq_inv
        hp hp2 q .e4

/-- Direct tree substitution preserves reversal across the paired contour
dart.  In particular, surviving physical-edge occurrences enter the final
root contour with opposite signs. -/
theorem canonicalProjectivePostConeDirectFinalSubstitution_boundaryTerm_partner_eq_inv
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide) :
    canonicalProjectivePostConeDirectFinalSubstitution hp hp2
      (canonicalProjectiveConePostConeBoundaryTerm p
        ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).1
        ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).2) =
      (canonicalProjectivePostConeDirectFinalSubstitution hp hp2
        (canonicalProjectiveConePostConeBoundaryTerm p q s))⁻¹ := by
  rw [canonicalProjectiveConePostConeBoundaryTerm_partner_eq_inv hp hp2 q s,
    map_inv]

end

end SystolicGrowth
