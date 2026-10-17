module

public import BuserSarnak.BuserSarnakProjectivePostConePolygonFactors

@[expose] public section

/-!
# Target-face factors of post-cone polygon words

This module complements the positive source-face occurrence of each retained
physical edge.  At the paired target occurrence, the same label appears with
inverse orientation.  This supplies the leaf-face relation used when a
rooted physical tree is eliminated from its leaves toward its root.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete
open ReidemeisterSchreier.Discrete.Presentations

noncomputable local instance buserSarnakProjectivePostConePolygonTargetFactorsRangeFintype
    (p : ℕ) [NeZero p] : Fintype (BuserSarnakProjectiveReductionRange p) :=
  Fintype.ofFinite _

noncomputable local instance buserSarnakProjectivePostConePolygonTargetFactorsDegenerateDecidable
    {p : ℕ} [NeZero p] :
    DecidablePred
      (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol :=
  Classical.decPred _

/-- Across a cone edge, the first cone-stage images of the two oriented raw
symbols are inverse words. -/
theorem canonicalProjectiveConeFirstStageSubstitution_conePartner_eq_inv
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p)
    (e : ProjectiveOctagonConeGenerator) :
    canonicalProjectiveConeFirstStageSubstitution p
      ((CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord
        ((CanonicalProjectiveConeSchreierData p).transition q e.lift, e.lift)) =
      (canonicalProjectiveConeFirstStageSubstitution p
        ((CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord
          (q, e.lift)))⁻¹ := by
  have hpair := canonicalProjectiveConeFirstStageSubstitution_conePair_eq_one
    hp hp2 q e
  rw [map_mul] at hpair
  calc
    canonicalProjectiveConeFirstStageSubstitution p
        ((CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord
          ((CanonicalProjectiveConeSchreierData p).transition q e.lift, e.lift)) =
        (canonicalProjectiveConeFirstStageSubstitution p
          ((CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord
            (q, e.lift)))⁻¹ *
          (canonicalProjectiveConeFirstStageSubstitution p
            ((CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord
              (q, e.lift)) *
            canonicalProjectiveConeFirstStageSubstitution p
              ((CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord
                ((CanonicalProjectiveConeSchreierData p).transition q e.lift, e.lift))) := by
            group
    _ = (canonicalProjectiveConeFirstStageSubstitution p
      ((CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord
        (q, e.lift)))⁻¹ * 1 := by rw [hpair]
    _ = _ := by simp

/-- The paired polygon occurrence of a cone side contains its opposite raw
Schreier symbol. -/
theorem projectivePolygonPostConeConePartnerRawSymbol
    {p : ℕ} [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p)
    (e : ProjectiveOctagonConeGenerator) :
    (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner
        q e.lift.positivePolygonSide).1
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner
        q e.lift.positivePolygonSide).2 =
      (((canonicalBuserSarnakProjectiveQuotientSectionData p).schreierData.toFiniteQuotientSchreierData).transition
        ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol
          q e.lift.positivePolygonSide).1
        ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol
          q e.lift.positivePolygonSide).2,
        ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol
          q e.lift.positivePolygonSide).2) := by
  cases e <;>
    simpa [BuserSarnakProjectiveQuotientSectionData.polygonSidePartner,
      ProjectiveOctagonConeGenerator.lift,
      ProjectiveOctagonGenerator.positivePolygonSide,
      ProjectivePolygonSide.reverse] using
      BuserSarnakProjectiveQuotientSectionData.polygonSideRawSymbol_partner
        (canonicalBuserSarnakProjectiveQuotientSectionData p) q _

/-- On a cone side, the target boundary term is the substituted cleaned word
of the paired raw symbol. -/
theorem canonicalProjectiveConePostConeBoundaryTerm_partnerCone_eq_substitution
    {p : ℕ} [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p)
    (e : ProjectiveOctagonConeGenerator) :
    canonicalProjectiveConePostConeBoundaryTerm p
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner
        q e.lift.positivePolygonSide).1
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner
        q e.lift.positivePolygonSide).2 =
      canonicalProjectiveConeFirstStageSubstitution p
        ((CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord
          ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol
            ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner
              q e.lift.positivePolygonSide).1
            ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner
              q e.lift.positivePolygonSide).2)) := by
  cases e <;> rfl

/-- A positive cone-side word is the substituted cleaned word at the source
raw state used by the cone-pair relation. -/
theorem canonicalProjectiveConePostConeConeSourceSideWord_eq_substitution
    {p : ℕ} [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p)
    (e : ProjectiveOctagonConeGenerator) :
    canonicalProjectiveConePostConeSideWord p q e.lift.positivePolygonSide =
      canonicalProjectiveConeFirstStageSubstitution p
        ((CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord
          (((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol
            q e.lift.positivePolygonSide).1, e.lift)) := by
  cases e <;> rfl

/-- Crossing a cone side in a polygon reverses its post-cone boundary word. -/
theorem canonicalProjectiveConePostConeBoundaryTerm_partnerCone_eq_inv
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p)
    (e : ProjectiveOctagonConeGenerator) :
    canonicalProjectiveConePostConeBoundaryTerm p
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner
        q e.lift.positivePolygonSide).1
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner
        q e.lift.positivePolygonSide).2 =
      (canonicalProjectiveConePostConeSideWord p q e.lift.positivePolygonSide)⁻¹ := by
  rw [canonicalProjectiveConePostConeBoundaryTerm_partnerCone_eq_substitution]
  rw [projectivePolygonPostConeConePartnerRawSymbol]
  have hsource := canonicalProjectiveConePostConeConeSourceSideWord_eq_substitution q e
  rw [hsource]
  have hgenerator :
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol
        q e.lift.positivePolygonSide).2 = e.lift := by
    cases e <;> rfl
  rw [hgenerator]
  exact canonicalProjectiveConeFirstStageSubstitution_conePartner_eq_inv hp hp2
    ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol
      q e.lift.positivePolygonSide).1 e

/-- If the preferred physical orientation is a cone side, its target polygon
occurrence is the inverse of the retained label. -/
theorem canonicalProjectiveConePostConeBoundaryTerm_edgeTarget_eq_inv_of_cone
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : CanonicalProjectiveConeKeptSymbol p)
    (e : ProjectiveOctagonConeGenerator)
    (h : z.1.1.2 = e.lift) :
    canonicalProjectiveConePostConeBoundaryTerm p
      (projectivePolygonPostConeEdgeTarget z).state
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner
        (projectivePolygonPostConeEdgeSource z).state
        (projectivePolygonPostConeEdgeSide z)).2 = (FreeGroup.of z)⁻¹ := by
  have hedge : projectivePolygonPostConeEdgeSide z = e.lift.positivePolygonSide := by
    unfold projectivePolygonPostConeEdgeSide
    rw [h]
  change canonicalProjectiveConePostConeBoundaryTerm p
    ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner
      (projectivePolygonPostConeEdgeSource z).state
      (projectivePolygonPostConeEdgeSide z)).1
    ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner
      (projectivePolygonPostConeEdgeSource z).state
      (projectivePolygonPostConeEdgeSide z)).2 = _
  rw [hedge]
  rw [canonicalProjectiveConePostConeBoundaryTerm_partnerCone_eq_inv hp hp2]
  have hsource := canonicalProjectiveConePostConeSideWord_edgeSource_eq z
  rw [hedge] at hsource
  rw [hsource]

/-- An `a`-label appears inversely at its paired target occurrence. -/
theorem canonicalProjectiveConePostConeBoundaryTerm_edgeTarget_eq_inv_of_generator_a
    {p : ℕ} [NeZero p]
    (z : CanonicalProjectiveConeKeptSymbol p)
    (h : z.1.1.2 = .a) :
    canonicalProjectiveConePostConeBoundaryTerm p
      (projectivePolygonPostConeEdgeTarget z).state
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner
        (projectivePolygonPostConeEdgeSource z).state
        (projectivePolygonPostConeEdgeSide z)).2 = (FreeGroup.of z)⁻¹ := by
  cases hx : z.1.1.2 <;> simp [hx] at h
  simp only [projectivePolygonPostConeEdgeTarget,
    projectivePolygonPostConeEdgeSide,
    ProjectiveOctagonGenerator.positivePolygonSide, hx]
  change canonicalProjectiveConePostConeBoundaryTerm p
    ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner
      (projectivePolygonPostConeEdgeSource z).state .a).1 .aInv = _
  simp only [canonicalProjectiveConePostConeBoundaryTerm]
  unfold canonicalProjectiveConePostConeSideWord
  have hraw :
      (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol
        ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner
          (projectivePolygonPostConeEdgeSource z).state .a).1 .aInv =
      (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol
        (projectivePolygonPostConeEdgeSource z).state .a := by
    simpa [BuserSarnakProjectiveQuotientSectionData.polygonSidePartner,
      ProjectivePolygonSide.reverse] using
      BuserSarnakProjectiveQuotientSectionData.polygonSideRawSymbol_partner
        (canonicalBuserSarnakProjectiveQuotientSectionData p)
        (projectivePolygonPostConeEdgeSource z).state .a
  rw [hraw]
  have hsource := canonicalProjectiveConePostConeSideWord_edgeSource_eq z
  simp only [projectivePolygonPostConeEdgeSide,
    ProjectiveOctagonGenerator.positivePolygonSide, hx] at hsource
  exact congrArg Inv.inv hsource

/-- A `c`-label appears inversely at its paired target occurrence. -/
theorem canonicalProjectiveConePostConeBoundaryTerm_edgeTarget_eq_inv_of_generator_c
    {p : ℕ} [NeZero p]
    (z : CanonicalProjectiveConeKeptSymbol p)
    (h : z.1.1.2 = .c) :
    canonicalProjectiveConePostConeBoundaryTerm p
      (projectivePolygonPostConeEdgeTarget z).state
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner
        (projectivePolygonPostConeEdgeSource z).state
        (projectivePolygonPostConeEdgeSide z)).2 = (FreeGroup.of z)⁻¹ := by
  cases hx : z.1.1.2 <;> simp [hx] at h
  simp only [projectivePolygonPostConeEdgeTarget,
    projectivePolygonPostConeEdgeSide,
    ProjectiveOctagonGenerator.positivePolygonSide, hx]
  change canonicalProjectiveConePostConeBoundaryTerm p
    ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner
      (projectivePolygonPostConeEdgeSource z).state .c).1 .cInv = _
  simp only [canonicalProjectiveConePostConeBoundaryTerm]
  unfold canonicalProjectiveConePostConeSideWord
  have hraw :
      (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol
        ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner
          (projectivePolygonPostConeEdgeSource z).state .c).1 .cInv =
      (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol
        (projectivePolygonPostConeEdgeSource z).state .c := by
    simpa [BuserSarnakProjectiveQuotientSectionData.polygonSidePartner,
      ProjectivePolygonSide.reverse] using
      BuserSarnakProjectiveQuotientSectionData.polygonSideRawSymbol_partner
        (canonicalBuserSarnakProjectiveQuotientSectionData p)
        (projectivePolygonPostConeEdgeSource z).state .c
  rw [hraw]
  have hsource := canonicalProjectiveConePostConeSideWord_edgeSource_eq z
  simp only [projectivePolygonPostConeEdgeSide,
    ProjectiveOctagonGenerator.positivePolygonSide, hx] at hsource
  exact congrArg Inv.inv hsource

/-- At the target face of every retained physical edge, its paired boundary
term is the inverse of the retained free generator. -/
theorem canonicalProjectiveConePostConeBoundaryTerm_edgeTarget_eq_inv
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : CanonicalProjectiveConeKeptSymbol p) :
    canonicalProjectiveConePostConeBoundaryTerm p
      (projectivePolygonPostConeEdgeTarget z).state
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner
        (projectivePolygonPostConeEdgeSource z).state
        (projectivePolygonPostConeEdgeSide z)).2 = (FreeGroup.of z)⁻¹ := by
  cases h : z.1.1.2 with
  | a => exact canonicalProjectiveConePostConeBoundaryTerm_edgeTarget_eq_inv_of_generator_a z h
  | c => exact canonicalProjectiveConePostConeBoundaryTerm_edgeTarget_eq_inv_of_generator_c z h
  | e1 =>
      apply canonicalProjectiveConePostConeBoundaryTerm_edgeTarget_eq_inv_of_cone hp hp2 z .e1
      simpa [ProjectiveOctagonConeGenerator.lift] using h
  | e2 =>
      apply canonicalProjectiveConePostConeBoundaryTerm_edgeTarget_eq_inv_of_cone hp hp2 z .e2
      simpa [ProjectiveOctagonConeGenerator.lift] using h
  | e3 =>
      apply canonicalProjectiveConePostConeBoundaryTerm_edgeTarget_eq_inv_of_cone hp hp2 z .e3
      simpa [ProjectiveOctagonConeGenerator.lift] using h
  | e4 =>
      apply canonicalProjectiveConePostConeBoundaryTerm_edgeTarget_eq_inv_of_cone hp hp2 z .e4
      simpa [ProjectiveOctagonConeGenerator.lift] using h

/-- The named side occurrence at the target face of a retained physical edge. -/
noncomputable def projectivePolygonPostConeEdgeTargetSide
    {p : ℕ} [NeZero p]
    (z : CanonicalProjectiveConeKeptSymbol p) : ProjectivePolygonSide :=
  ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner
    (projectivePolygonPostConeEdgeSource z).state
    (projectivePolygonPostConeEdgeSide z)).2

/-- A retained label is an explicit inverse factor in the polygon word at the
other endpoint of its physical post-cone edge. -/
theorem canonicalProjectiveConePostConePolygonWord_edgeTarget_factor
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : CanonicalProjectiveConeKeptSymbol p) :
    canonicalProjectiveConePostConePolygonWord p
        (projectivePolygonPostConeEdgeTarget z).state =
      canonicalProjectiveConePostConeBoundaryPrefix p
          (projectivePolygonPostConeEdgeTarget z).state
          (projectivePolygonPostConeEdgeTargetSide z) *
        (FreeGroup.of z)⁻¹ *
          canonicalProjectiveConePostConeBoundarySuffix p
            (projectivePolygonPostConeEdgeTarget z).state
            (projectivePolygonPostConeEdgeTargetSide z) := by
  unfold projectivePolygonPostConeEdgeTargetSide
  rw [canonicalProjectiveConePostConePolygonWord_eq_prefix_term_suffix,
    canonicalProjectiveConePostConeBoundaryTerm_edgeTarget_eq_inv hp hp2]

end

end SystolicGrowth
