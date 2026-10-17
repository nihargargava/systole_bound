module

public import BuserSarnak.BuserSarnakProjectiveConeRelators

@[expose] public section

/-!
# Polygon relators in the projective Schreier presentation

This module exposes each lift of the octagon polygon relation as an explicit
eight-letter cleaned Schreier word.  These closed boundary words are the input
for the remaining dual-graph/polygon-elimination stage.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete
open ReidemeisterSchreier.Discrete.Presentations

noncomputable local instance buserSarnakProjectivePolygonRangeFintype
    (p : ℕ) [NeZero p] : Fintype (BuserSarnakProjectiveReductionRange p) :=
  Fintype.ofFinite _

noncomputable local instance buserSarnakProjectivePolygonDegenerateDecidable
    {p : ℕ} [NeZero p]
    {S : BuserSarnakProjectiveQuotientSectionData p} :
    DecidablePred
      S.schreierData.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol :=
  Classical.decPred _

namespace BuserSarnakProjectiveQuotientSectionData

/-- State after the first `a` side of a lifted polygon boundary. -/
def polygonAfterA
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p) :
    BuserSarnakProjectiveReductionRange p :=
  S.schreierData.toFiniteQuotientSchreierData.transition q .a

/-- State after the `a e₁` prefix of a lifted polygon boundary. -/
def polygonAfterE1
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p) :
    BuserSarnakProjectiveReductionRange p :=
  S.schreierData.toFiniteQuotientSchreierData.transition (S.polygonAfterA q) .e1

/-- State after the `a e₁ c⁻¹` prefix of a lifted polygon boundary. -/
def polygonAfterCInv
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p) :
    BuserSarnakProjectiveReductionRange p :=
  S.schreierData.toFiniteQuotientSchreierData.inverseTransition (S.polygonAfterE1 q) .c

/-- State after the `a e₁ c⁻¹ e₂` prefix of a lifted polygon boundary. -/
def polygonAfterE2
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p) :
    BuserSarnakProjectiveReductionRange p :=
  S.schreierData.toFiniteQuotientSchreierData.transition (S.polygonAfterCInv q) .e2

/-- State after the `a e₁ c⁻¹ e₂ a⁻¹` prefix of a lifted polygon boundary. -/
def polygonAfterAInv
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p) :
    BuserSarnakProjectiveReductionRange p :=
  S.schreierData.toFiniteQuotientSchreierData.inverseTransition (S.polygonAfterE2 q) .a

/-- State after the `a e₁ c⁻¹ e₂ a⁻¹ e₃` prefix. -/
def polygonAfterE3
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p) :
    BuserSarnakProjectiveReductionRange p :=
  S.schreierData.toFiniteQuotientSchreierData.transition (S.polygonAfterAInv q) .e3

/-- State after the first seven sides of a lifted polygon boundary. -/
def polygonAfterC
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p) :
    BuserSarnakProjectiveReductionRange p :=
  S.schreierData.toFiniteQuotientSchreierData.transition (S.polygonAfterE3 q) .c

/-- The cleaned boundary word of the polygon based at `q`. -/
def polygonCleanedWord
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p) :
    FreeGroup S.schreierData.toFiniteQuotientSchreierData.NondegenerateSchreierSymbol :=
  S.schreierData.toFiniteQuotientSchreierData.cleanedSchreierSymbolWord (q, .a) *
    S.schreierData.toFiniteQuotientSchreierData.cleanedSchreierSymbolWord
      (S.polygonAfterA q, .e1) *
    (S.schreierData.toFiniteQuotientSchreierData.cleanedSchreierSymbolWord
      (S.polygonAfterCInv q, .c))⁻¹ *
    S.schreierData.toFiniteQuotientSchreierData.cleanedSchreierSymbolWord
      (S.polygonAfterCInv q, .e2) *
    (S.schreierData.toFiniteQuotientSchreierData.cleanedSchreierSymbolWord
      (S.polygonAfterAInv q, .a))⁻¹ *
    S.schreierData.toFiniteQuotientSchreierData.cleanedSchreierSymbolWord
      (S.polygonAfterAInv q, .e3) *
    S.schreierData.toFiniteQuotientSchreierData.cleanedSchreierSymbolWord
      (S.polygonAfterE3 q, .c) *
    S.schreierData.toFiniteQuotientSchreierData.cleanedSchreierSymbolWord
      (S.polygonAfterC q, .e4)

/-- Rewriting the polygon relation gives its displayed eight-side boundary
word after degenerate symbols are erased. -/
theorem cleanedTau_polygon
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p) :
    S.schreierData.cleanedTau q (projectiveOctagonRelator .polygon) =
      S.polygonCleanedWord q := by
  change S.schreierData.toFiniteQuotientSchreierData.cleanedTau q
    (FreeGroup.mk [(.a, true), (.e1, true), (.c, false), (.e2, true),
      (.a, false), (.e3, true), (.c, true), (.e4, true)]) = _
  rw [FiniteQuotientSchreierData.cleanedTau_mk,
    FiniteQuotientSchreierData.cleanedTauList_cons_true,
    FiniteQuotientSchreierData.cleanedTauList_cons_true,
    FiniteQuotientSchreierData.cleanedTauList_cons_false,
    FiniteQuotientSchreierData.cleanedTauList_cons_true,
    FiniteQuotientSchreierData.cleanedTauList_cons_false,
    FiniteQuotientSchreierData.cleanedTauList_cons_true,
    FiniteQuotientSchreierData.cleanedTauList_cons_true,
    FiniteQuotientSchreierData.cleanedTauList_cons_true,
    FiniteQuotientSchreierData.cleanedTauList_nil]
  simp [polygonCleanedWord, polygonAfterA, polygonAfterE1,
    polygonAfterCInv, polygonAfterE2, polygonAfterAInv, polygonAfterE3,
    polygonAfterC]
  group

/-- Each displayed polygon boundary word is trivial modulo the canonical
cleaned projective relators. -/
theorem polygonCleanedWord_relatorEquivalent
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p) :
    RelatorEquivalent
      (S.schreierData.cleanedSchreierRelators projectiveOctagonRelators)
      (S.polygonCleanedWord q) 1 := by
  rw [← S.cleanedTau_polygon q]
  exact RelatorEquivalent.of_mem
    ⟨q, projectiveOctagonRelator .polygon, ⟨.polygon, rfl⟩, rfl⟩

/-- The eighth polygon side returns a boundary traversal to its starting
quotient state. -/
theorem polygonAfterE4_eq
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p) :
    S.schreierData.toFiniteQuotientSchreierData.transition
      (S.polygonAfterC q) .e4 = q := by
  rw [FiniteQuotientSchreierData.transition_eq,
    S.schreierData_quotientMap]
  simp only [polygonAfterC, polygonAfterE3, polygonAfterAInv, polygonAfterE2,
    polygonAfterCInv, polygonAfterE1, polygonAfterA,
    FiniteQuotientSchreierData.transition_eq,
    FiniteQuotientSchreierData.inverseTransition_eq,
    S.schreierData_quotientMap]
  simp only [buserSarnakProjectiveReductionMap, FreeGroup.lift_apply_of]
  have hpolygon := buserSarnakProjectiveReductionImage_relations p
    (projectiveOctagonRelator .polygon)
    (⟨.polygon, rfl⟩ : projectiveOctagonRelator .polygon ∈ projectiveOctagonRelators)
  simp only [projectiveOctagonRelator, map_mul, map_inv,
    FreeGroup.lift_apply_of] at hpolygon
  calc
    q * buserSarnakProjectiveReductionImage p .a *
          buserSarnakProjectiveReductionImage p .e1 *
        (buserSarnakProjectiveReductionImage p .c)⁻¹ *
      buserSarnakProjectiveReductionImage p .e2 *
    (buserSarnakProjectiveReductionImage p .a)⁻¹ *
      buserSarnakProjectiveReductionImage p .e3 *
        buserSarnakProjectiveReductionImage p .c *
          buserSarnakProjectiveReductionImage p .e4 =
      q * (buserSarnakProjectiveReductionImage p .a *
        buserSarnakProjectiveReductionImage p .e1 *
        (buserSarnakProjectiveReductionImage p .c)⁻¹ *
        buserSarnakProjectiveReductionImage p .e2 *
        (buserSarnakProjectiveReductionImage p .a)⁻¹ *
        buserSarnakProjectiveReductionImage p .e3 *
        buserSarnakProjectiveReductionImage p .c *
        buserSarnakProjectiveReductionImage p .e4) := by group
    _ = q := by rw [hpolygon, mul_one]

end BuserSarnakProjectiveQuotientSectionData

end

end SystolicGrowth
