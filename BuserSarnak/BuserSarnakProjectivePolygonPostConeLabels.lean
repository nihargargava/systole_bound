module

public import BuserSarnak.BuserSarnakProjectivePolygonArborescence
public import BuserSarnak.BuserSarnakProjectiveConeTietze

@[expose] public section

/-!
# Post-cone labels for projective polygon sides

This module separates the raw Schreier symbol associated with each oriented
polygon side from the subsequent cone-pivot elimination.  The normalization
under side pairing is the local input for the eligible dual quiver used in the
second Tietze stage.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete
open ReidemeisterSchreier.Discrete.Presentations

noncomputable local instance buserSarnakProjectivePolygonPostConeLabelsRangeFintype
    (p : ℕ) [NeZero p] : Fintype (BuserSarnakProjectiveReductionRange p) :=
  Fintype.ofFinite _

namespace BuserSarnakProjectiveQuotientSectionData

/-- The raw Schreier symbol occurring at an oriented side of the polygon
boundary.  Inverse `a` and `c` sides use their endpoint, matching the cleaned
Schreier boundary word. -/
def polygonSideRawSymbol
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p) :
    ProjectivePolygonSide →
      FiniteQuotientSchreierData.FiniteSchreierSymbol
        ProjectiveOctagonGenerator (BuserSarnakProjectiveReductionRange p)
  | .a => (q, .a)
  | .e1 => (S.polygonAfterA q, .e1)
  | .cInv => (S.polygonAfterCInv q, .c)
  | .e2 => (S.polygonAfterCInv q, .e2)
  | .aInv => (S.polygonAfterAInv q, .a)
  | .e3 => (S.polygonAfterAInv q, .e3)
  | .c => (S.polygonAfterE3 q, .c)
  | .e4 => (S.polygonAfterC q, .e4)

/-- The raw symbol retains the projective-generator label of its side. -/
@[simp] theorem polygonSideRawSymbol_generator
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide) :
    (S.polygonSideRawSymbol q s).2 = s.generator := by
  cases s <;> rfl

/-- Paired non-cone sides carry exactly the same raw Schreier symbol; a cone
side carries the symbol at the opposite endpoint of its cone orbit. -/
theorem polygonSideRawSymbol_partner
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide) :
    S.polygonSideRawSymbol (S.polygonSidePartner q s).1
        (S.polygonSidePartner q s).2 =
      match s with
      | .a | .cInv | .aInv | .c => S.polygonSideRawSymbol q s
      | .e1 | .e2 | .e3 | .e4 =>
          (S.schreierData.toFiniteQuotientSchreierData.transition
            (S.polygonSideRawSymbol q s).1
            (S.polygonSideRawSymbol q s).2,
            (S.polygonSideRawSymbol q s).2) := by
  cases s
  · change
      (S.polygonSideEnd (S.polygonSidePartner q .a).1
        (S.polygonSidePartner q .a).2, ProjectiveOctagonGenerator.a) =
        (S.polygonSideStart q .a, ProjectiveOctagonGenerator.a)
    rw [S.polygonSidePartner_end q .a]
  · change
      (S.polygonSideStart (S.polygonSidePartner q .e1).1
        (S.polygonSidePartner q .e1).2, ProjectiveOctagonGenerator.e1) =
        (S.polygonSideEnd q .e1, ProjectiveOctagonGenerator.e1)
    rw [S.polygonSidePartner_start q .e1]
  · change
      (S.polygonSideStart (S.polygonSidePartner q .cInv).1
        (S.polygonSidePartner q .cInv).2, ProjectiveOctagonGenerator.c) =
        (S.polygonSideEnd q .cInv, ProjectiveOctagonGenerator.c)
    rw [S.polygonSidePartner_start q .cInv]
  · change
      (S.polygonSideStart (S.polygonSidePartner q .e2).1
        (S.polygonSidePartner q .e2).2, ProjectiveOctagonGenerator.e2) =
        (S.polygonSideEnd q .e2, ProjectiveOctagonGenerator.e2)
    rw [S.polygonSidePartner_start q .e2]
  · change
      (S.polygonSideStart (S.polygonSidePartner q .aInv).1
        (S.polygonSidePartner q .aInv).2, ProjectiveOctagonGenerator.a) =
        (S.polygonSideEnd q .aInv, ProjectiveOctagonGenerator.a)
    rw [S.polygonSidePartner_start q .aInv]
  · change
      (S.polygonSideStart (S.polygonSidePartner q .e3).1
        (S.polygonSidePartner q .e3).2, ProjectiveOctagonGenerator.e3) =
        (S.polygonSideEnd q .e3, ProjectiveOctagonGenerator.e3)
    rw [S.polygonSidePartner_start q .e3]
  · change
      (S.polygonSideEnd (S.polygonSidePartner q .c).1
        (S.polygonSidePartner q .c).2, ProjectiveOctagonGenerator.c) =
        (S.polygonSideStart q .c, ProjectiveOctagonGenerator.c)
    rw [S.polygonSidePartner_end q .c]
  · change
      (S.polygonSideStart (S.polygonSidePartner q .e4).1
        (S.polygonSidePartner q .e4).2, ProjectiveOctagonGenerator.e4) =
        (S.polygonSideEnd q .e4, ProjectiveOctagonGenerator.e4)
    rw [S.polygonSidePartner_start q .e4]

/-- On an `a`- or `c`-side, side pairing preserves the raw symbol exactly. -/
theorem polygonSideRawSymbol_partner_of_noncone
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide)
    (hs : s.generator = .a ∨ s.generator = .c) :
    S.polygonSideRawSymbol (S.polygonSidePartner q s).1
        (S.polygonSidePartner q s).2 = S.polygonSideRawSymbol q s := by
  rw [S.polygonSideRawSymbol_partner q s]
  cases s <;> simp [ProjectivePolygonSide.generator] at hs ⊢

end BuserSarnakProjectiveQuotientSectionData

/-- A nondegenerate `a`- or `c`-labelled Schreier symbol cannot be a cone
pivot, because every cone pivot has one of the four cone-generator labels. -/
theorem canonicalProjectiveConeNoncone_not_eliminated
    {p : ℕ} [NeZero p]
    (z : CanonicalProjectiveConeNondegenerateSymbol p)
    (hz : z.1.2 = .a ∨ z.1.2 = .c) :
    ¬ isCanonicalProjectiveConeEliminationSymbol z := by
  rintro ⟨i, hi⟩
  have hgenerator : z.1.2 = i.1.lift := by
    rw [← hi]
    exact canonicalProjectiveConeEliminationSymbol_generator i
  rcases hz with ha | hc
  · rw [ha] at hgenerator
    rcases i with ⟨e, r⟩
    cases e <;> simp [ProjectiveOctagonConeGenerator.lift] at hgenerator
  · rw [hc] at hgenerator
    rcases i with ⟨e, r⟩
    cases e <;> simp [ProjectiveOctagonConeGenerator.lift] at hgenerator

/-- View any surviving non-cone symbol as a generator retained by the first
cone Tietze stage. -/
def canonicalProjectiveConeKeptOfNoncone
    {p : ℕ} [NeZero p]
    (z : CanonicalProjectiveConeNondegenerateSymbol p)
    (hz : z.1.2 = .a ∨ z.1.2 = .c) :
    CanonicalProjectiveConeKeptSymbol p :=
  ⟨z, canonicalProjectiveConeNoncone_not_eliminated z hz⟩

/-- A nondegenerate non-cone polygon side determines a generator retained by
the first cone Tietze stage. -/
def canonicalProjectiveConeKeptPolygonNonconeSide
    {p : ℕ} [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide)
    (hraw : ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol q s))
    (hs : s.generator = .a ∨ s.generator = .c) :
    CanonicalProjectiveConeKeptSymbol p :=
  canonicalProjectiveConeKeptOfNoncone
    ⟨(canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol q s,
      hraw⟩
    (by
      rw [(canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol_generator q s]
      exact hs)

/-- The kept label of a non-cone side is invariant under its paired polygon
occurrence, whenever the shared raw symbol is nondegenerate. -/
theorem canonicalProjectiveConeKeptPolygonNonconeSide_partner
    {p : ℕ} [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide)
    (hs : s.generator = .a ∨ s.generator = .c)
    (q' : BuserSarnakProjectiveReductionRange p)
    (s' : ProjectivePolygonSide)
    (hpair : (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s =
      (q', s'))
    (hraw : ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol q s))
    (hpartner : ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol
        q' s'))
    (hs' : s'.generator = .a ∨ s'.generator = .c) :
    canonicalProjectiveConeKeptPolygonNonconeSide
      q' s' hpartner hs' =
      canonicalProjectiveConeKeptPolygonNonconeSide q s hraw hs := by
  apply Subtype.ext
  change
    (⟨(canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol q' s',
        hpartner⟩ : CanonicalProjectiveConeNondegenerateSymbol p) =
      ⟨(canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol q s,
        hraw⟩
  apply Subtype.ext
  have h := BuserSarnakProjectiveQuotientSectionData.polygonSideRawSymbol_partner_of_noncone
    (canonicalBuserSarnakProjectiveQuotientSectionData p) q s hs
  rw [hpair] at h
  exact h

end

end SystolicGrowth
