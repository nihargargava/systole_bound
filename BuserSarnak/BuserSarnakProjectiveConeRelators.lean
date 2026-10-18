module

public import BuserSarnak.BuserSarnakProjectiveLevelMarking

@[expose] public section

/-!
# Cone-square relators in the projective Schreier presentation

The four order-two orbifold generators rewrite to two-symbol relators.  At an
odd prime their finite-quotient actions are fixed-point-free involutions, so
these relators provide the first stage of the eventual uniform Tietze
certificate.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete
open ReidemeisterSchreier.Discrete.Presentations

noncomputable local instance buserSarnakProjectiveConeRangeFintype
    (p : ℕ) [NeZero p] : Fintype (BuserSarnakProjectiveReductionRange p) :=
  Fintype.ofFinite _

noncomputable local instance buserSarnakProjectiveConeDegenerateDecidable
    {p : ℕ} [NeZero p]
    {S : BuserSarnakProjectiveQuotientSectionData p} :
    DecidablePred
      S.schreierData.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol :=
  Classical.decPred _

/-- The four projective generators with order-two defining relators. -/
inductive ProjectiveOctagonConeGenerator where
  | e1 | e2 | e3 | e4
  deriving DecidableEq

/-- Exhaustive finite enumeration of the four cone generators. -/
instance instFintypeProjectiveOctagonConeGenerator :
    Fintype ProjectiveOctagonConeGenerator :=
  Fintype.ofList [.e1, .e2, .e3, .e4] (by
    intro e
    cases e <;> simp)

@[simp] theorem card_projectiveOctagonConeGenerator :
    Fintype.card ProjectiveOctagonConeGenerator = 4 := by
  decide

/-- View a cone generator as one of the six projective octagon generators. -/
def ProjectiveOctagonConeGenerator.lift :
    ProjectiveOctagonConeGenerator → ProjectiveOctagonGenerator
  | .e1 => .e1
  | .e2 => .e2
  | .e3 => .e3
  | .e4 => .e4

/-- The embedding of cone generators into projective generators is injective. -/
theorem ProjectiveOctagonConeGenerator.lift_injective :
    Function.Injective ProjectiveOctagonConeGenerator.lift := by
  intro e f h
  cases e <;> cases f <;> simp [ProjectiveOctagonConeGenerator.lift] at h ⊢

/-- The defining projective relator associated with a cone generator. -/
def ProjectiveOctagonConeGenerator.relator :
    ProjectiveOctagonConeGenerator → ProjectiveOctagonRelator
  | .e1 => .e1_sq
  | .e2 => .e2_sq
  | .e3 => .e3_sq
  | .e4 => .e4_sq

@[simp] lemma ProjectiveOctagonConeGenerator.relator_eq_sq
    (e : ProjectiveOctagonConeGenerator) :
    projectiveOctagonRelator e.relator = FreeGroup.of e.lift ^ 2 := by
  cases e <;> rfl

@[simp] lemma ProjectiveOctagonConeGenerator.lift_isCone
    (e : ProjectiveOctagonConeGenerator) :
    e.lift = .e1 ∨ e.lift = .e2 ∨ e.lift = .e3 ∨ e.lift = .e4 := by
  cases e <;> simp [ProjectiveOctagonConeGenerator.lift]

namespace BuserSarnakProjectiveQuotientSectionData

/-- Rewriting the square of any projective generator yields its two consecutive
cleaned Schreier symbols. -/
theorem cleanedTau_sq
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p)
    (x : ProjectiveOctagonGenerator) :
    S.schreierData.cleanedTau q (FreeGroup.of x ^ 2) =
      S.schreierData.toFiniteQuotientSchreierData.cleanedSchreierSymbolWord (q, x) *
        S.schreierData.toFiniteQuotientSchreierData.cleanedSchreierSymbolWord
          (S.schreierData.toFiniteQuotientSchreierData.transition q x, x) := by
  change S.schreierData.toFiniteQuotientSchreierData.cleanedTau q
      (FreeGroup.mk [(x, true), (x, true)]) = _
  rw [FiniteQuotientSchreierData.cleanedTau_mk,
    FiniteQuotientSchreierData.cleanedTauList_cons_true,
    FiniteQuotientSchreierData.cleanedTauList_cons_true,
    FiniteQuotientSchreierData.cleanedTauList_nil]
  simp

/-- If a projective-generator image squares to one in the quotient, following
its Schreier transition twice returns to the original quotient state. -/
theorem transition_twice_eq_of_reductionImage_sq
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p)
    (x : ProjectiveOctagonGenerator)
    (hx : buserSarnakProjectiveReductionImage p x ^ 2 = 1) :
    S.schreierData.toFiniteQuotientSchreierData.transition
        (S.schreierData.toFiniteQuotientSchreierData.transition q x) x = q := by
  rw [FiniteQuotientSchreierData.transition_eq,
    FiniteQuotientSchreierData.transition_eq,
    S.schreierData_quotientMap]
  rw [show buserSarnakProjectiveReductionMap p (FreeGroup.of x) =
      buserSarnakProjectiveReductionImage p x by
    exact FreeGroup.lift_apply_of]
  calc
    (q * buserSarnakProjectiveReductionImage p x) *
        buserSarnakProjectiveReductionImage p x =
      q * (buserSarnakProjectiveReductionImage p x ^ 2) := by
        rw [pow_two, mul_assoc]
    _ = q := by rw [hx, mul_one]

/-- Each cone generator acts as an involution on projective Schreier states. -/
theorem cone_transition_twice
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p)
    (e : ProjectiveOctagonConeGenerator) :
    S.schreierData.toFiniteQuotientSchreierData.transition
        (S.schreierData.toFiniteQuotientSchreierData.transition q e.lift) e.lift = q :=
  S.transition_twice_eq_of_reductionImage_sq q e.lift
    (buserSarnakProjectiveReductionImage_cone_sq p e.lift e.lift_isCone)

/-- The canonical finite Schreier data, exposed for the cone-elimination
stage of the projective Tietze certificate. -/
abbrev canonicalBuserSarnakProjectiveConeSchreierData
    (p : ℕ) [NeZero p] :=
  (canonicalBuserSarnakProjectiveQuotientSectionData p).schreierData.toFiniteQuotientSchreierData

/-- In the canonical tree, a cone edge and its reverse cannot both be
degenerate.  Thus every cone orbit supplies a nondegenerate symbol to remove. -/
theorem canonical_cone_not_both_degenerate
    {p : ℕ} [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p)
    (e : ProjectiveOctagonConeGenerator) :
    ¬ ((canonicalBuserSarnakProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
          (q, e.lift) ∧
      (canonicalBuserSarnakProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
        ((canonicalBuserSarnakProjectiveConeSchreierData p).transition q e.lift, e.lift)) := by
  exact canonicalBuserSarnakProjective_cone_not_both_isDegenerate
    q e.lift e.lift_isCone

/-- The two cleaned symbols across a cone edge multiply to one modulo the
cleaned projective relators. -/
theorem conePair_relatorEquivalent
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p)
    (e : ProjectiveOctagonConeGenerator) :
    RelatorEquivalent
      (S.schreierData.cleanedSchreierRelators projectiveOctagonRelators)
      (S.schreierData.toFiniteQuotientSchreierData.cleanedSchreierSymbolWord (q, e.lift) *
        S.schreierData.toFiniteQuotientSchreierData.cleanedSchreierSymbolWord
          (S.schreierData.toFiniteQuotientSchreierData.transition q e.lift, e.lift)) 1 := by
  rw [← S.cleanedTau_sq q e.lift,
    ← e.relator_eq_sq]
  exact RelatorEquivalent.of_mem
    ⟨q, projectiveOctagonRelator e.relator, ⟨e.relator, rfl⟩, rfl⟩

/-- If the first cone-edge symbol is a tree symbol, its cone relation makes
the second cleaned symbol trivial. -/
theorem conePair_right_eq_one_of_left_degenerate
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p)
    (e : ProjectiveOctagonConeGenerator)
    (hleft : S.schreierData.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol
      (q, e.lift)) :
    RelatorEquivalent
      (S.schreierData.cleanedSchreierRelators projectiveOctagonRelators)
      (S.schreierData.toFiniteQuotientSchreierData.cleanedSchreierSymbolWord
        (S.schreierData.toFiniteQuotientSchreierData.transition q e.lift, e.lift)) 1 := by
  exact RelatorEquivalent.eq_one_of_mul_eq_one_left
    (u := S.schreierData.toFiniteQuotientSchreierData.cleanedSchreierSymbolWord
      (q, e.lift))
    (v := S.schreierData.toFiniteQuotientSchreierData.cleanedSchreierSymbolWord
      (S.schreierData.toFiniteQuotientSchreierData.transition q e.lift, e.lift))
    (by
      rw [S.schreierData.toFiniteQuotientSchreierData.cleanedSchreierSymbolWord_of_degenerate hleft])
    (S.conePair_relatorEquivalent q e)

/-- If the second cone-edge symbol is a tree symbol, its cone relation makes
the first cleaned symbol trivial. -/
theorem conePair_left_eq_one_of_right_degenerate
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p)
    (e : ProjectiveOctagonConeGenerator)
    (hright : S.schreierData.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol
      (S.schreierData.toFiniteQuotientSchreierData.transition q e.lift, e.lift)) :
    RelatorEquivalent
      (S.schreierData.cleanedSchreierRelators projectiveOctagonRelators)
      (S.schreierData.toFiniteQuotientSchreierData.cleanedSchreierSymbolWord
        (q, e.lift)) 1 := by
  apply RelatorEquivalent.eq_one_of_mul_eq_one_right
  · exact S.conePair_relatorEquivalent q e
  · rw [S.schreierData.toFiniteQuotientSchreierData.cleanedSchreierSymbolWord_of_degenerate hright]

end BuserSarnakProjectiveQuotientSectionData

end

end SystolicGrowth
