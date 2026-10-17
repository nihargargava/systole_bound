module

public import BuserSarnak.BuserSarnakProjectiveConePairing

@[expose] public section

/-!
# First-stage projective cone eliminations

This module turns the four fixed-point-free cone involutions into an explicit
family of distinct nondegenerate Schreier-generator pivots.  Each pivot is
either killed by a cone relator or defined as the inverse of its companion,
and the family has the required cardinality `2h`.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete
open ReidemeisterSchreier.Discrete.Presentations

noncomputable local instance buserSarnakProjectiveConeEliminationRangeFintype
    (p : ℕ) [NeZero p] : Fintype (BuserSarnakProjectiveReductionRange p) :=
  Fintype.ofFinite _

/-- The canonical finite Schreier data used by the projective cone stage. -/
abbrev CanonicalProjectiveConeSchreierData (p : ℕ) [NeZero p] :=
  (canonicalBuserSarnakProjectiveQuotientSectionData p).schreierData.toFiniteQuotientSchreierData

noncomputable local instance buserSarnakProjectiveConeEliminationDegenerateDecidable
    {p : ℕ} [NeZero p] :
    DecidablePred
      (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol :=
  Classical.decPred _

/-- A non-tree Schreier generator in the canonical projective presentation. -/
abbrev CanonicalProjectiveConeNondegenerateSymbol (p : ℕ) [NeZero p] :=
  (CanonicalProjectiveConeSchreierData p).NondegenerateSchreierSymbol

noncomputable local instance buserSarnakProjectiveConeEliminationPairRepresentativeFintype
    (p : ℕ) [NeZero p] (e : ProjectiveOctagonConeGenerator) :
    Fintype (BuserSarnakProjectiveConePairRepresentative p e) :=
  Fintype.subtype
    (Finset.univ.filter fun q : BuserSarnakProjectiveReductionRange p =>
      buserSarnakProjectiveConeRank p q <
        buserSarnakProjectiveConeRank p (buserSarnakProjectiveConePartner p e q))
    (by simp)

noncomputable local instance canonicalProjectiveConeNondegenerateSymbolFintype
    (p : ℕ) [NeZero p] : Fintype (CanonicalProjectiveConeNondegenerateSymbol p) :=
  Fintype.subtype
    (Finset.univ.filter fun z =>
      ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol z)
    (by simp)

/-- The lower-ranked raw symbol of a selected cone-edge orbit. -/
def canonicalProjectiveConePairSource
    {p : ℕ} [NeZero p]
    (i : BuserSarnakProjectiveConePairIndex p) :
    FiniteQuotientSchreierData.FiniteSchreierSymbol
      ProjectiveOctagonGenerator (BuserSarnakProjectiveReductionRange p) :=
  (i.2.1, i.1.lift)

/-- The opposite raw symbol in a selected cone-edge orbit. -/
def canonicalProjectiveConePairTarget
    {p : ℕ} [NeZero p]
    (i : BuserSarnakProjectiveConePairIndex p) :
    FiniteQuotientSchreierData.FiniteSchreierSymbol
      ProjectiveOctagonGenerator (BuserSarnakProjectiveReductionRange p) :=
  (buserSarnakProjectiveConePartner p i.1 i.2.1, i.1.lift)

/-- If a chosen cone source is a tree symbol, the opposite endpoint is not. -/
theorem canonicalProjectiveConePairTarget_not_degenerate_of_source_degenerate
    {p : ℕ} [NeZero p]
    (i : BuserSarnakProjectiveConePairIndex p)
    (hsource : (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      (canonicalProjectiveConePairSource i)) :
    ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      (canonicalProjectiveConePairTarget i) := by
  intro htarget
  exact BuserSarnakProjectiveQuotientSectionData.canonical_cone_not_both_degenerate
    i.2.1 i.1 ⟨hsource, htarget⟩

/-- The nondegenerate pivot selected from each unordered cone-edge pair. -/
noncomputable def canonicalProjectiveConeEliminationSymbol
    {p : ℕ} [NeZero p]
    (i : BuserSarnakProjectiveConePairIndex p) :
    CanonicalProjectiveConeNondegenerateSymbol p :=
  if hsource : (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      (canonicalProjectiveConePairSource i) then
    ⟨canonicalProjectiveConePairTarget i,
      canonicalProjectiveConePairTarget_not_degenerate_of_source_degenerate i hsource⟩
  else
    ⟨canonicalProjectiveConePairSource i, hsource⟩

/-- The selected pivot retains the cone generator labelling its orbit. -/
theorem canonicalProjectiveConeEliminationSymbol_generator
    {p : ℕ} [NeZero p]
    (i : BuserSarnakProjectiveConePairIndex p) :
    (canonicalProjectiveConeEliminationSymbol i).1.2 = i.1.lift := by
  by_cases hsource : (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      (i.2.1, i.1.lift)
  · simp [canonicalProjectiveConeEliminationSymbol, hsource,
      canonicalProjectiveConePairSource, canonicalProjectiveConePairTarget]
  · simp [canonicalProjectiveConeEliminationSymbol, hsource,
      canonicalProjectiveConePairSource]

/-- The state of a pivot determines the lower endpoint of its cone orbit. -/
theorem canonicalProjectiveConeEliminationSymbol_state
    {p : ℕ} [NeZero p]
    (i : BuserSarnakProjectiveConePairIndex p) :
    (canonicalProjectiveConeEliminationSymbol i).1.1 =
      if (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
          (i.2.1, i.1.lift) then
        buserSarnakProjectiveConePartner p i.1 i.2.1
      else i.2.1 := by
  by_cases hsource : (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      (i.2.1, i.1.lift)
  · simp [canonicalProjectiveConeEliminationSymbol, hsource,
      canonicalProjectiveConePairSource, canonicalProjectiveConePairTarget]
  · simp [canonicalProjectiveConeEliminationSymbol, hsource,
      canonicalProjectiveConePairSource]

theorem buserSarnakProjectiveConeLower_of_representative
    {p : ℕ} [NeZero p]
    (e : ProjectiveOctagonConeGenerator)
    (q : BuserSarnakProjectiveConePairRepresentative p e) :
    buserSarnakProjectiveConeLower p e q.1 = q.1 := by
  simp [buserSarnakProjectiveConeLower, q.2]

theorem buserSarnakProjectiveConeLower_partner_of_representative
    {p : ℕ} [NeZero p]
    (e : ProjectiveOctagonConeGenerator)
    (q : BuserSarnakProjectiveConePairRepresentative p e) :
    buserSarnakProjectiveConeLower p e
      (buserSarnakProjectiveConePartner p e q.1) = q.1 := by
  rw [buserSarnakProjectiveConeLower]
  have hnot : ¬buserSarnakProjectiveConeRank p
      (buserSarnakProjectiveConePartner p e q.1) <
        buserSarnakProjectiveConeRank p q.1 :=
    Nat.not_lt_of_ge q.2.le
  simp [hnot, buserSarnakProjectiveConePartner_partner]

theorem canonicalProjectiveConeEliminationSymbol_lower
    {p : ℕ} [NeZero p]
    (i : BuserSarnakProjectiveConePairIndex p) :
    buserSarnakProjectiveConeLower p i.1
      (canonicalProjectiveConeEliminationSymbol i).1.1 = i.2.1 := by
  rw [canonicalProjectiveConeEliminationSymbol_state]
  split_ifs
  · exact buserSarnakProjectiveConeLower_partner_of_representative i.1 i.2
  · exact buserSarnakProjectiveConeLower_of_representative i.1 i.2

/-- Distinct cone-edge orbits select distinct nondegenerate pivots. -/
theorem canonicalProjectiveConeEliminationSymbol_injective
    {p : ℕ} [NeZero p] :
    Function.Injective (@canonicalProjectiveConeEliminationSymbol p _) := by
  intro i j hij
  have hval := congrArg Subtype.val hij
  have hgen := congrArg Prod.snd hval
  have he : i.1 = j.1 := by
    apply ProjectiveOctagonConeGenerator.lift_injective
    calc
      i.1.lift = (canonicalProjectiveConeEliminationSymbol i).1.2 :=
        (canonicalProjectiveConeEliminationSymbol_generator i).symm
      _ = (canonicalProjectiveConeEliminationSymbol j).1.2 := hgen
      _ = j.1.lift := canonicalProjectiveConeEliminationSymbol_generator j
  rcases i with ⟨e, q⟩
  rcases j with ⟨f, r⟩
  simp only at he
  subst f
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Subtype.ext
    have hstate := congrArg Prod.fst hval
    have hq := canonicalProjectiveConeEliminationSymbol_lower
      (i := Sigma.mk e q)
    have hr := canonicalProjectiveConeEliminationSymbol_lower
      (i := Sigma.mk e r)
    calc
      q.1 = buserSarnakProjectiveConeLower p e
          (canonicalProjectiveConeEliminationSymbol (Sigma.mk e q)).1.1 := hq.symm
      _ = buserSarnakProjectiveConeLower p e
          (canonicalProjectiveConeEliminationSymbol (Sigma.mk e r)).1.1 := by
            rw [hstate]
      _ = r.1 := hr

/-- The relators of the canonical projective Schreier presentation. -/
abbrev CanonicalProjectiveConeRelators (p : ℕ) [NeZero p] :=
  (CanonicalProjectiveConeSchreierData p).cleanedSchreierRelators projectiveOctagonRelators

/-- The word to which a cone pivot is defined: `1` at a tree endpoint, and
the inverse of the opposite nondegenerate cone symbol otherwise. -/
noncomputable def canonicalProjectiveConeEliminationCompanion
    {p : ℕ} [NeZero p]
    (i : BuserSarnakProjectiveConePairIndex p) :
    FreeGroup (CanonicalProjectiveConeNondegenerateSymbol p) :=
  if _hsource : (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      (canonicalProjectiveConePairSource i) then
    1
  else if _htarget : (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      (canonicalProjectiveConePairTarget i) then
    1
  else ((CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord
    (canonicalProjectiveConePairTarget i))⁻¹

/-- Every selected cone pivot is equivalent to its defining companion word. -/
theorem canonicalProjectiveConeEliminationSymbol_relatorEquivalent_companion
    {p : ℕ} [NeZero p]
    (i : BuserSarnakProjectiveConePairIndex p) :
    RelatorEquivalent (CanonicalProjectiveConeRelators p)
      (FreeGroup.of (canonicalProjectiveConeEliminationSymbol i))
      (canonicalProjectiveConeEliminationCompanion i) := by
  by_cases hsource : (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      (canonicalProjectiveConePairSource i)
  · have htargetnot :=
      canonicalProjectiveConePairTarget_not_degenerate_of_source_degenerate i hsource
    have hrel := (canonicalBuserSarnakProjectiveQuotientSectionData p).conePair_right_eq_one_of_left_degenerate
      i.2.1 i.1 hsource
    change RelatorEquivalent (CanonicalProjectiveConeRelators p)
      ((CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord
        (canonicalProjectiveConePairTarget i)) 1 at hrel
    rw [(CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord_of_not_degenerate htargetnot] at hrel
    have hsymbol : canonicalProjectiveConeEliminationSymbol i =
        ⟨canonicalProjectiveConePairTarget i, htargetnot⟩ := by
      simp [canonicalProjectiveConeEliminationSymbol, hsource]
      apply Subtype.ext
      rfl
    have hcompanion : canonicalProjectiveConeEliminationCompanion i = 1 := by
      simp [canonicalProjectiveConeEliminationCompanion, hsource]
    rw [hsymbol, hcompanion]
    exact hrel
  · by_cases htarget : (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      (canonicalProjectiveConePairTarget i)
    · have hrel := (canonicalBuserSarnakProjectiveQuotientSectionData p).conePair_left_eq_one_of_right_degenerate
        i.2.1 i.1 htarget
      change RelatorEquivalent (CanonicalProjectiveConeRelators p)
        ((CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord
          (canonicalProjectiveConePairSource i)) 1 at hrel
      rw [(CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord_of_not_degenerate hsource] at hrel
      have hsymbol : canonicalProjectiveConeEliminationSymbol i =
          ⟨canonicalProjectiveConePairSource i, hsource⟩ := by
        simp [canonicalProjectiveConeEliminationSymbol, hsource]
        apply Subtype.ext
        rfl
      have hcompanion : canonicalProjectiveConeEliminationCompanion i = 1 := by
        simp [canonicalProjectiveConeEliminationCompanion, hsource, htarget]
      rw [hsymbol, hcompanion]
      exact hrel
    · have hrel := (canonicalBuserSarnakProjectiveQuotientSectionData p).conePair_relatorEquivalent
        i.2.1 i.1
      change RelatorEquivalent (CanonicalProjectiveConeRelators p)
        ((CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord
          (canonicalProjectiveConePairSource i) *
        (CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord
          (canonicalProjectiveConePairTarget i)) 1 at hrel
      rw [(CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord_of_not_degenerate hsource,
        (CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord_of_not_degenerate htarget] at hrel
      have hsymbol : canonicalProjectiveConeEliminationSymbol i =
          ⟨canonicalProjectiveConePairSource i, hsource⟩ := by
        simp [canonicalProjectiveConeEliminationSymbol, hsource]
        apply Subtype.ext
        rfl
      have hcompanion : canonicalProjectiveConeEliminationCompanion i =
          (FreeGroup.of ⟨canonicalProjectiveConePairTarget i, htarget⟩)⁻¹ := by
        simp [canonicalProjectiveConeEliminationCompanion, hsource, htarget]
        congr 1
      rw [hsymbol, hcompanion]
      exact RelatorEquivalent.eq_inv_of_mul_eq_one hrel

/-- Predicate selecting the actual pivot generators used by the cone stage. -/
def isCanonicalProjectiveConeEliminationSymbol
    {p : ℕ} [NeZero p]
    (z : CanonicalProjectiveConeNondegenerateSymbol p) : Prop :=
  ∃ i : BuserSarnakProjectiveConePairIndex p,
    canonicalProjectiveConeEliminationSymbol i = z

noncomputable local instance isCanonicalProjectiveConeEliminationSymbolDecidable
    {p : ℕ} [NeZero p] :
    DecidablePred (@isCanonicalProjectiveConeEliminationSymbol p _) :=
  Classical.decPred _

/-- The subtype of the `2h` projective cone pivots to be deleted first. -/
abbrev CanonicalProjectiveConeEliminatedSymbol
    (p : ℕ) [NeZero p] :=
  {z : CanonicalProjectiveConeNondegenerateSymbol p //
    isCanonicalProjectiveConeEliminationSymbol z}

noncomputable local instance canonicalProjectiveConeEliminatedSymbolFintype
    (p : ℕ) [NeZero p] : Fintype (CanonicalProjectiveConeEliminatedSymbol p) :=
  Fintype.subtype
    (Finset.univ.filter fun z => isCanonicalProjectiveConeEliminationSymbol z)
    (by simp)

/-- The cone-orbit index set is equivalent to the selected pivot subtype. -/
noncomputable def canonicalProjectiveConeEliminationSymbolEquiv
    (p : ℕ) [NeZero p] :
    BuserSarnakProjectiveConePairIndex p ≃
      CanonicalProjectiveConeEliminatedSymbol p :=
  Equiv.ofBijective
    (fun i => ⟨canonicalProjectiveConeEliminationSymbol i, ⟨i, rfl⟩⟩)
    ⟨by
      intro i j h
      apply canonicalProjectiveConeEliminationSymbol_injective
      exact congrArg Subtype.val h,
      by
        intro z
        rcases z.2 with ⟨i, hi⟩
        exact ⟨i, Subtype.ext hi⟩⟩

/-- At an odd prime, the first cone-elimination stage removes exactly `2h`
nondegenerate projective Schreier generators. -/
theorem card_canonicalProjectiveConeEliminatedSymbol
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : BuserSarnakCorrectionData p) :
    Fintype.card (CanonicalProjectiveConeEliminatedSymbol p) =
      2 * data.halfImageIndex := by
  calc
    Fintype.card (CanonicalProjectiveConeEliminatedSymbol p) =
        Fintype.card (BuserSarnakProjectiveConePairIndex p) :=
      (Fintype.card_congr (canonicalProjectiveConeEliminationSymbolEquiv p)).symm
    _ = 2 * data.halfImageIndex :=
      card_buserSarnakProjectiveConePairIndex hp hp2 data

end

end SystolicGrowth
