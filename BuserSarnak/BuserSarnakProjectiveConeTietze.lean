module

public import BuserSarnak.BuserSarnakProjectiveConeElimination
public import Vendored.ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Tietze.Script

@[expose] public section

/-!
# First Tietze stage for projective cone pairs

The `2h` pivots selected in `BuserSarnakProjectiveConeElimination` can be
deleted simultaneously.  This module proves that their companion words use
only retained generators, adjoins the resulting redundant defining relators,
and applies the vendored predicate-based substitution move.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete
open ReidemeisterSchreier.Discrete.Presentations

noncomputable local instance buserSarnakProjectiveConeTietzeRangeFintype
    (p : ℕ) [NeZero p] : Fintype (BuserSarnakProjectiveReductionRange p) :=
  Fintype.ofFinite _

noncomputable local instance buserSarnakProjectiveConeTietzeDegenerateDecidable
    {p : ℕ} [NeZero p] :
    DecidablePred
      (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol :=
  Classical.decPred _

noncomputable local instance buserSarnakProjectiveConeTietzeDecidable
    {p : ℕ} [NeZero p] :
    DecidablePred (@isCanonicalProjectiveConeEliminationSymbol p _) :=
  Classical.decPred _

/-- When both endpoints are nondegenerate, the opposite cone symbol is not a
selected pivot.  Thus it can occur in a defining word for the selected one. -/
theorem canonicalProjectiveConePairTarget_not_eliminated
    {p : ℕ} [NeZero p]
    (i : BuserSarnakProjectiveConePairIndex p)
    (hsource : ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      (canonicalProjectiveConePairSource i))
    (htarget : ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      (canonicalProjectiveConePairTarget i)) :
    ¬ isCanonicalProjectiveConeEliminationSymbol
      (⟨canonicalProjectiveConePairTarget i, htarget⟩ :
        CanonicalProjectiveConeNondegenerateSymbol p) := by
  intro hmember
  rcases hmember with ⟨j, hj⟩
  have hval := congrArg Subtype.val hj
  have hgen : j.1.lift = i.1.lift := by
    calc
      j.1.lift = (canonicalProjectiveConeEliminationSymbol j).1.2 :=
        (canonicalProjectiveConeEliminationSymbol_generator j).symm
      _ = (⟨canonicalProjectiveConePairTarget i, htarget⟩ :
          CanonicalProjectiveConeNondegenerateSymbol p).1.2 :=
        congrArg Prod.snd hval
      _ = i.1.lift := by
        simp [canonicalProjectiveConePairTarget]
  have he : j.1 = i.1 :=
    ProjectiveOctagonConeGenerator.lift_injective hgen
  rcases i with ⟨e, q⟩
  rcases j with ⟨f, r⟩
  simp only at he
  subst f
  have hstate := congrArg Prod.fst hval
  change (canonicalProjectiveConeEliminationSymbol (Sigma.mk e r)).1.1 =
    buserSarnakProjectiveConePartner p e q.1 at hstate
  have hrq : r.1 = q.1 := by
    calc
      r.1 = buserSarnakProjectiveConeLower p e
          (canonicalProjectiveConeEliminationSymbol (Sigma.mk e r)).1.1 :=
        (canonicalProjectiveConeEliminationSymbol_lower (Sigma.mk e r)).symm
      _ = buserSarnakProjectiveConeLower p e
          (buserSarnakProjectiveConePartner p e q.1) := by rw [hstate]
      _ = q.1 := buserSarnakProjectiveConeLower_partner_of_representative e q
  have hrq' : r = q := Subtype.ext hrq
  subst r
  change ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
    (q.1, e.lift) at hsource
  have hsource' : ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      (q.1, e.lift) := hsource
  have hselectedState := canonicalProjectiveConeEliminationSymbol_state
    (Sigma.mk e q)
  have hselectedState' :
      (canonicalProjectiveConeEliminationSymbol (Sigma.mk e q)).1.1 = q.1 := by
    rw [if_neg hsource'] at hselectedState
    exact hselectedState
  have hfixed : buserSarnakProjectiveConePartner p e q.1 = q.1 := by
    calc
      buserSarnakProjectiveConePartner p e q.1 =
          (canonicalProjectiveConeEliminationSymbol (Sigma.mk e q)).1.1 := hstate.symm
      _ = q.1 := hselectedState'
  have hlt := q.2
  rw [hfixed] at hlt
  exact (Nat.lt_irrefl _) hlt

/-- Nondegenerate Schreier generators retained after the cone Tietze move. -/
abbrev CanonicalProjectiveConeKeptSymbol (p : ℕ) [NeZero p] :=
  Presented.GeneratorPartition.Kept
    (@isCanonicalProjectiveConeEliminationSymbol p _)

/-- The selected cone pivots to be removed by the first Tietze move. -/
abbrev CanonicalProjectiveConeDeletedSymbol (p : ℕ) [NeZero p] :=
  Presented.GeneratorPartition.Deleted
    (@isCanonicalProjectiveConeEliminationSymbol p _)

/-- Choose the unique cone-pair index witnessing that a deleted symbol is a
selected pivot.  Uniqueness is not required computationally here. -/
noncomputable def canonicalProjectiveConeEliminationIndex
    {p : ℕ} [NeZero p]
    (z : CanonicalProjectiveConeDeletedSymbol p) :
    BuserSarnakProjectiveConePairIndex p :=
  Classical.choose z.2

/-- The chosen cone-pair index produces the deleted pivot. -/
theorem canonicalProjectiveConeEliminationIndex_spec
    {p : ℕ} [NeZero p]
    (z : CanonicalProjectiveConeDeletedSymbol p) :
    canonicalProjectiveConeEliminationSymbol
      (canonicalProjectiveConeEliminationIndex z) = z.1 :=
  Classical.choose_spec z.2

/-- The retained target symbol used by a nontrivial cone defining word. -/
noncomputable def canonicalProjectiveConeKeptTarget
    {p : ℕ} [NeZero p]
    (i : BuserSarnakProjectiveConePairIndex p)
    (hsource : ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      (canonicalProjectiveConePairSource i))
    (htarget : ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      (canonicalProjectiveConePairTarget i)) :
    CanonicalProjectiveConeKeptSymbol p :=
  ⟨⟨canonicalProjectiveConePairTarget i, htarget⟩,
    canonicalProjectiveConePairTarget_not_eliminated i hsource htarget⟩

/-- The word over retained generators that defines a deleted cone pivot. -/
noncomputable def canonicalProjectiveConeEliminationKeptWord
    {p : ℕ} [NeZero p]
    (z : CanonicalProjectiveConeDeletedSymbol p) :
    FreeGroup (CanonicalProjectiveConeKeptSymbol p) :=
  if hsource : (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      (canonicalProjectiveConePairSource (canonicalProjectiveConeEliminationIndex z)) then
    1
  else if htarget : (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      (canonicalProjectiveConePairTarget (canonicalProjectiveConeEliminationIndex z)) then
    1
  else (FreeGroup.of (canonicalProjectiveConeKeptTarget
    (canonicalProjectiveConeEliminationIndex z) hsource htarget))⁻¹

/-- Include words on retained generators into words on all nondegenerate
projective Schreier generators. -/
noncomputable def canonicalProjectiveConeKeptInclusion
    (p : ℕ) [NeZero p] :
    FreeGroup (CanonicalProjectiveConeKeptSymbol p) →*
      FreeGroup (CanonicalProjectiveConeNondegenerateSymbol p) :=
  FreeGroup.lift (fun z => FreeGroup.of z.1)

@[simp] theorem canonicalProjectiveConeKeptInclusion_of
    {p : ℕ} [NeZero p]
    (z : CanonicalProjectiveConeKeptSymbol p) :
    canonicalProjectiveConeKeptInclusion p (FreeGroup.of z) = FreeGroup.of z.1 := by
  simp [canonicalProjectiveConeKeptInclusion]

/-- Including a pivot's retained defining word recovers its previously proved
cone companion word. -/
theorem canonicalProjectiveConeEliminationKeptWord_inclusion
    {p : ℕ} [NeZero p]
    (z : CanonicalProjectiveConeDeletedSymbol p) :
    canonicalProjectiveConeKeptInclusion p
      (canonicalProjectiveConeEliminationKeptWord z) =
      canonicalProjectiveConeEliminationCompanion
        (canonicalProjectiveConeEliminationIndex z) := by
  by_cases hsource : (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      (canonicalProjectiveConePairSource (canonicalProjectiveConeEliminationIndex z))
  · simp [canonicalProjectiveConeEliminationKeptWord,
      canonicalProjectiveConeEliminationCompanion, hsource]
  · by_cases htarget : (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      (canonicalProjectiveConePairTarget (canonicalProjectiveConeEliminationIndex z))
    · simp [canonicalProjectiveConeEliminationKeptWord,
        canonicalProjectiveConeEliminationCompanion, hsource, htarget]
    · simp [canonicalProjectiveConeEliminationKeptWord,
        canonicalProjectiveConeEliminationCompanion,
        canonicalProjectiveConeKeptInclusion,
        canonicalProjectiveConeKeptTarget, hsource, htarget]
      congr 1

/-- The defining relation for every deleted cone pivot is already a consequence
of the canonical projective cleaned relators. -/
theorem canonicalProjectiveConeEliminationDefinedRelator
    {p : ℕ} [NeZero p]
    (z : CanonicalProjectiveConeDeletedSymbol p) :
    RelatorEquivalent (CanonicalProjectiveConeRelators p)
      (FreeGroup.of z.1 *
        (canonicalProjectiveConeKeptInclusion p
          (canonicalProjectiveConeEliminationKeptWord z))⁻¹) 1 := by
  have h := canonicalProjectiveConeEliminationSymbol_relatorEquivalent_companion
    (canonicalProjectiveConeEliminationIndex z)
  rw [canonicalProjectiveConeEliminationIndex_spec z] at h
  rw [← canonicalProjectiveConeEliminationKeptWord_inclusion z] at h
  exact RelatorEquivalent.mul_inv_eq_one h

/-- The predicate-based Tietze API pulls each cone defining relation back to
the direct relation proved above. -/
theorem canonicalProjectiveConePulledBackDefinedRelator
    {p : ℕ} [NeZero p]
    (z : CanonicalProjectiveConeDeletedSymbol p) :
    (FreeGroup.freeGroupCongr
      (Presented.GeneratorPartition.equiv
        (@isCanonicalProjectiveConeEliminationSymbol p _))).symm
      (FreeGroup.of (Sum.inr z) *
        (Presented.includeAdjoinedGenerators
          (CanonicalProjectiveConeKeptSymbol p)
          (CanonicalProjectiveConeDeletedSymbol p)
          (canonicalProjectiveConeEliminationKeptWord z))⁻¹) =
      FreeGroup.of z.1 *
        (canonicalProjectiveConeKeptInclusion p
          (canonicalProjectiveConeEliminationKeptWord z))⁻¹ := by
  simp [FreeGroup.freeGroupCongr, Presented.GeneratorPartition.equiv,
    Presented.includeAdjoinedGenerators, canonicalProjectiveConeKeptInclusion]
  rw [← MonoidHom.comp_apply]
  congr 1
  ext x
  simp

/-- All predicate-based cone defining relators are redundant consequences of
the canonical cleaned presentation. -/
theorem canonicalProjectiveConeDefinedGeneratorRelators_subset_normalClosure
    {p : ℕ} [NeZero p] :
    Presented.definedGeneratorRelatorsOfPredicate
      (@isCanonicalProjectiveConeEliminationSymbol p _)
      (@canonicalProjectiveConeEliminationKeptWord p _) ⊆
      Subgroup.normalClosure (CanonicalProjectiveConeRelators p) := by
  intro r hr
  change r ∈ (FreeGroup.freeGroupCongr
    (Presented.GeneratorPartition.equiv
      (@isCanonicalProjectiveConeEliminationSymbol p _))).symm ''
      Presented.definedGeneratorRelators
        (@canonicalProjectiveConeEliminationKeptWord p _) at hr
  rcases hr with ⟨q, ⟨z, rfl⟩, rfl⟩
  rw [canonicalProjectiveConePulledBackDefinedRelator z]
  exact RelatorEquivalent.mem_normalClosure_of_eq_one
    (canonicalProjectiveConeEliminationDefinedRelator z)

/-- The first semantic Tietze stage removes precisely the selected `2h` cone
pivots, leaving a presentation over `CanonicalProjectiveConeKeptSymbol`. -/
noncomputable def canonicalProjectiveConeFirstStageTietzeEquiv
    (p : ℕ) [NeZero p] :
    TietzeEquiv (CanonicalProjectiveConeRelators p)
      (Presented.relatorsAfterSubstitutingDefinedGeneratorsOfPredicate
        (CanonicalProjectiveConeRelators p)
        (@isCanonicalProjectiveConeEliminationSymbol p _)
        (@canonicalProjectiveConeEliminationKeptWord p _)) :=
  (Presented.addRedundantRelatorsTietzeEquiv
    (R := CanonicalProjectiveConeRelators p)
    (S := Presented.definedGeneratorRelatorsOfPredicate
      (@isCanonicalProjectiveConeEliminationSymbol p _)
      (@canonicalProjectiveConeEliminationKeptWord p _))
    canonicalProjectiveConeDefinedGeneratorRelators_subset_normalClosure).symm.trans
    (Presented.substituteDefinedGeneratorsOfPredicateTietzeEquiv
      (CanonicalProjectiveConeRelators p)
      (@isCanonicalProjectiveConeEliminationSymbol p _)
      (@canonicalProjectiveConeEliminationKeptWord p _))

/-- An inspectable two-move certificate for the first cone-elimination stage:
first adjoin the already redundant defining relators, then substitute the
selected pivots. -/
noncomputable def canonicalProjectiveConeFirstStageVerifiedTietzeScript
    (p : ℕ) [NeZero p] :
    VerifiedTietzeScript
      (Presentation.ofRelators (CanonicalProjectiveConeRelators p))
      (Presentation.ofRelators
        (Presented.relatorsAfterSubstitutingDefinedGeneratorsOfPredicate
          (CanonicalProjectiveConeRelators p)
          (@isCanonicalProjectiveConeEliminationSymbol p _)
          (@canonicalProjectiveConeEliminationKeptWord p _))) :=
  (VerifiedTietzeScript.replaceRelators
    (R := CanonicalProjectiveConeRelators p)
    (S := CanonicalProjectiveConeRelators p ∪
      Presented.definedGeneratorRelatorsOfPredicate
        (@isCanonicalProjectiveConeEliminationSymbol p _)
        (@canonicalProjectiveConeEliminationKeptWord p _))
    (by
      intro r hr
      exact RelatorEquivalent.of_mem (Or.inl hr))
    (by
      intro r hr
      rcases hr with hr | hr
      · exact RelatorEquivalent.of_mem hr
      · exact RelatorEquivalent.of_mem_normalClosure
          (canonicalProjectiveConeDefinedGeneratorRelators_subset_normalClosure hr))).trans
    (VerifiedTietzeScript.substituteDefinedGeneratorsAlongEquiv
      (CanonicalProjectiveConeRelators p)
      (Presented.GeneratorPartition.equiv
        (@isCanonicalProjectiveConeEliminationSymbol p _))
      (@canonicalProjectiveConeEliminationKeptWord p _))

/-- The cone certificate has one relator-adjunction move and one substitution
move. -/
@[simp] theorem canonicalProjectiveConeFirstStageVerifiedTietzeScript_trace
    (p : ℕ) [NeZero p] :
    (canonicalProjectiveConeFirstStageVerifiedTietzeScript p).trace =
      [.replaceRelators, .substituteDefinedGenerators] :=
  rfl

/-- The first cone stage is an explicit two-move Tietze script. -/
@[simp] theorem canonicalProjectiveConeFirstStageVerifiedTietzeScript_moveCount
    (p : ℕ) [NeZero p] :
    (canonicalProjectiveConeFirstStageVerifiedTietzeScript p).moveCount = 2 :=
  rfl

noncomputable local instance canonicalProjectiveConeTietzeNondegenerateFintype
    (p : ℕ) [NeZero p] : Fintype (CanonicalProjectiveConeNondegenerateSymbol p) :=
  Fintype.subtype
    (Finset.univ.filter fun z =>
      ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol z)
    (by simp)

noncomputable local instance canonicalProjectiveConeTietzeDeletedFintype
    (p : ℕ) [NeZero p] : Fintype (CanonicalProjectiveConeDeletedSymbol p) :=
  Fintype.subtype
    (Finset.univ.filter fun z =>
      isCanonicalProjectiveConeEliminationSymbol z)
    (by simp)

noncomputable local instance canonicalProjectiveConeTietzeKeptFintype
    (p : ℕ) [NeZero p] : Fintype (CanonicalProjectiveConeKeptSymbol p) :=
  Fintype.subtype
    (Finset.univ.filter fun z =>
      ¬ isCanonicalProjectiveConeEliminationSymbol z)
    (by simp)

/-- The first cone Tietze stage leaves exactly `3h + 1` nondegenerate
generators.  Thus the remaining route to the genus-`h + 1` surface
presentation needs exactly `h - 1` further eliminations. -/
theorem card_canonicalProjectiveConeKeptSymbol
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : BuserSarnakCorrectionData p) :
    Fintype.card (CanonicalProjectiveConeKeptSymbol p) =
      3 * data.halfImageIndex + 1 := by
  have hsplit : Fintype.card (CanonicalProjectiveConeKeptSymbol p) =
      Fintype.card (CanonicalProjectiveConeNondegenerateSymbol p) -
        Fintype.card (CanonicalProjectiveConeDeletedSymbol p) := by
    exact Fintype.card_subtype_compl
      (@isCanonicalProjectiveConeEliminationSymbol p _)
  have hdeleted : Fintype.card (CanonicalProjectiveConeDeletedSymbol p) =
      2 * data.halfImageIndex := by
    simpa [CanonicalProjectiveConeDeletedSymbol,
      Presented.GeneratorPartition.Deleted] using
      card_canonicalProjectiveConeEliminatedSymbol hp hp2 data
  have hnondeg : Fintype.card (CanonicalProjectiveConeNondegenerateSymbol p) =
      5 * data.halfImageIndex + 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact natCard_canonicalBuserSarnakProjectiveConeSchreierData_nondegenerateSymbol
      hp hp2 data
  rw [hsplit, hdeleted, hnondeg]
  omega

end

end SystolicGrowth
