module

public import BuserSarnak.BuserSarnakProjectivePolygonPostConeRootedConnectivity
public import BuserSarnak.BuserSarnakProjectivePolygonRelators

@[expose] public section

/-!
# Post-cone Tietze interface for the projective polygon presentation

This module makes the first cone-stage substitution explicit and transports
the polygon relators through it.  It also packages the canonical physical
dual tree as the exact family of `h - 1` distinct future elimination slots.
The remaining work is to orient those slots by a leaf order and extract a
defining polygon word for each slot.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete
open ReidemeisterSchreier.Discrete.Presentations

noncomputable local instance buserSarnakProjectivePostConeTietzeRangeFintype
    (p : ℕ) [NeZero p] : Fintype (BuserSarnakProjectiveReductionRange p) :=
  Fintype.ofFinite _

noncomputable local instance buserSarnakProjectivePostConeTietzeDegenerateDecidable
    {p : ℕ} [NeZero p] :
    DecidablePred
      (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol :=
  Classical.decPred _

noncomputable local instance buserSarnakProjectivePostConeTietzeEliminationDecidable
    {p : ℕ} [NeZero p] :
    DecidablePred (@isCanonicalProjectiveConeEliminationSymbol p _) :=
  Classical.decPred _

/-- The relators after the verified first cone substitution. -/
abbrev CanonicalProjectiveConeFirstStageRelators (p : ℕ) [NeZero p] :=
  Presented.relatorsAfterSubstitutingDefinedGeneratorsOfPredicate
    (CanonicalProjectiveConeRelators p)
    (@isCanonicalProjectiveConeEliminationSymbol p _)
    (@canonicalProjectiveConeEliminationKeptWord p _)

/-- The homomorphism used by the first cone substitution, written directly on
the original nondegenerate projective Schreier generators. -/
noncomputable def canonicalProjectiveConeFirstStageSubstitution
    (p : ℕ) [NeZero p] :
    FreeGroup (CanonicalProjectiveConeNondegenerateSymbol p) →*
      FreeGroup (CanonicalProjectiveConeKeptSymbol p) :=
  (Presented.eliminateAdjoinedGeneratorsHom
    (@canonicalProjectiveConeEliminationKeptWord p _)).comp
    (FreeGroup.freeGroupCongr
      (Presented.GeneratorPartition.equiv
        (@isCanonicalProjectiveConeEliminationSymbol p _)))

/-- A selected cone pivot maps to its proved defining word. -/
@[simp] theorem canonicalProjectiveConeFirstStageSubstitution_of_deleted
    {p : ℕ} [NeZero p]
    (z : CanonicalProjectiveConeNondegenerateSymbol p)
    (hz : isCanonicalProjectiveConeEliminationSymbol z) :
    canonicalProjectiveConeFirstStageSubstitution p (FreeGroup.of z) =
      canonicalProjectiveConeEliminationKeptWord ⟨z, hz⟩ := by
  simp only [canonicalProjectiveConeFirstStageSubstitution,
    MonoidHom.coe_comp, MonoidHom.coe_coe, Function.comp_apply,
    FreeGroup.freeGroupCongr_apply, FreeGroup.map.of,
    Presented.GeneratorPartition.equiv_apply_of_delete
      (@isCanonicalProjectiveConeEliminationSymbol p _) hz]
  exact Presented.eliminateAdjoinedGeneratorsHom_inr
    (X := CanonicalProjectiveConeKeptSymbol p)
    (Y := CanonicalProjectiveConeDeletedSymbol p)
    (@canonicalProjectiveConeEliminationKeptWord p _) ⟨z, hz⟩

/-- A retained post-cone generator maps to itself. -/
@[simp] theorem canonicalProjectiveConeFirstStageSubstitution_of_kept
    {p : ℕ} [NeZero p]
    (z : CanonicalProjectiveConeKeptSymbol p) :
    canonicalProjectiveConeFirstStageSubstitution p (FreeGroup.of z.1) =
      FreeGroup.of z := by
  simp only [canonicalProjectiveConeFirstStageSubstitution,
    MonoidHom.coe_comp, MonoidHom.coe_coe, Function.comp_apply,
    FreeGroup.freeGroupCongr_apply, FreeGroup.map.of,
    Presented.GeneratorPartition.equiv_apply_of_not_delete
      (@isCanonicalProjectiveConeEliminationSymbol p _) z.2]
  exact Presented.eliminateAdjoinedGeneratorsHom_inl
    (X := CanonicalProjectiveConeKeptSymbol p)
    (Y := CanonicalProjectiveConeDeletedSymbol p)
    (@canonicalProjectiveConeEliminationKeptWord p _) z

/-- The explicit post-cone image of the polygon boundary based at `q`. -/
noncomputable def canonicalProjectiveConePostConePolygonWord
    (p : ℕ) [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p) :
    FreeGroup (CanonicalProjectiveConeKeptSymbol p) :=
  canonicalProjectiveConeFirstStageSubstitution p
    ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonCleanedWord q)

/-- The polygon-only relator family in the post-cone generator alphabet. -/
def CanonicalProjectiveConePostConePolygonRelators
    (p : ℕ) [NeZero p] :
    Set (FreeGroup (CanonicalProjectiveConeKeptSymbol p)) :=
  Set.range (canonicalProjectiveConePostConePolygonWord p)

/-- Every post-cone polygon word is literally a relator of the first-stage
target presentation. -/
theorem canonicalProjectiveConePostConePolygonWord_mem_firstStageRelators
    {p : ℕ} [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p) :
    canonicalProjectiveConePostConePolygonWord p q ∈
      CanonicalProjectiveConeFirstStageRelators p := by
  change canonicalProjectiveConeFirstStageSubstitution p
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonCleanedWord q) ∈
    (Presented.eliminateAdjoinedGeneratorsHom
      (@canonicalProjectiveConeEliminationKeptWord p _)) ''
      (FreeGroup.freeGroupCongr
        (Presented.GeneratorPartition.equiv
          (@isCanonicalProjectiveConeEliminationSymbol p _)) ''
        CanonicalProjectiveConeRelators p)
  refine ⟨FreeGroup.freeGroupCongr
      (Presented.GeneratorPartition.equiv
        (@isCanonicalProjectiveConeEliminationSymbol p _))
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonCleanedWord q), ?_, rfl⟩
  refine ⟨(canonicalBuserSarnakProjectiveQuotientSectionData p).polygonCleanedWord q, ?_, rfl⟩
  rw [← (canonicalBuserSarnakProjectiveQuotientSectionData p).cleanedTau_polygon q]
  exact (CanonicalProjectiveConeSchreierData p).mem_cleanedSchreierRelators
    projectiveOctagonRelators q ⟨.polygon, rfl⟩

/-- A selected cone-pair relator becomes the empty word after the first-stage
substitution.  The three branches correspond to a tree source, a tree target,
and two surviving endpoints. -/
theorem canonicalProjectiveConeFirstStageSubstitution_pair_eq_one
    {p : ℕ} [NeZero p]
    (i : BuserSarnakProjectiveConePairIndex p) :
    canonicalProjectiveConeFirstStageSubstitution p
      ((CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord
          (canonicalProjectiveConePairSource i) *
        (CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord
          (canonicalProjectiveConePairTarget i)) = 1 := by
  rw [map_mul]
  by_cases hsource : (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      (canonicalProjectiveConePairSource i)
  · have htarget : ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
        (canonicalProjectiveConePairTarget i) :=
      canonicalProjectiveConePairTarget_not_degenerate_of_source_degenerate i hsource
    let z : CanonicalProjectiveConeNondegenerateSymbol p :=
      ⟨canonicalProjectiveConePairTarget i, htarget⟩
    have hselected : canonicalProjectiveConeEliminationSymbol i = z := by
      simp [z, canonicalProjectiveConeEliminationSymbol, hsource]
      apply Subtype.ext
      rfl
    have hdeleted : isCanonicalProjectiveConeEliminationSymbol z := ⟨i, hselected⟩
    let zd : CanonicalProjectiveConeDeletedSymbol p := ⟨z, hdeleted⟩
    have hindex : canonicalProjectiveConeEliminationIndex zd = i := by
      apply canonicalProjectiveConeEliminationSymbol_injective
      rw [canonicalProjectiveConeEliminationIndex_spec]
      exact hselected.symm
    rw [(CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord_of_degenerate hsource,
      map_one, one_mul,
      (CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord_of_not_degenerate htarget]
    change canonicalProjectiveConeFirstStageSubstitution p (FreeGroup.of z) = 1
    rw [canonicalProjectiveConeFirstStageSubstitution_of_deleted z hdeleted]
    change canonicalProjectiveConeEliminationKeptWord zd = 1
    simp only [canonicalProjectiveConeEliminationKeptWord]
    rw [hindex]
    simp [hsource]
  · by_cases htarget : (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
        (canonicalProjectiveConePairTarget i)
    · let z : CanonicalProjectiveConeNondegenerateSymbol p :=
        ⟨canonicalProjectiveConePairSource i, hsource⟩
      have hselected : canonicalProjectiveConeEliminationSymbol i = z := by
        simp [z, canonicalProjectiveConeEliminationSymbol, hsource]
        apply Subtype.ext
        rfl
      have hdeleted : isCanonicalProjectiveConeEliminationSymbol z := ⟨i, hselected⟩
      let zd : CanonicalProjectiveConeDeletedSymbol p := ⟨z, hdeleted⟩
      have hindex : canonicalProjectiveConeEliminationIndex zd = i := by
        apply canonicalProjectiveConeEliminationSymbol_injective
        rw [canonicalProjectiveConeEliminationIndex_spec]
        exact hselected.symm
      rw [(CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord_of_not_degenerate hsource,
        (CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord_of_degenerate htarget,
        map_one, mul_one]
      change canonicalProjectiveConeFirstStageSubstitution p (FreeGroup.of z) = 1
      rw [canonicalProjectiveConeFirstStageSubstitution_of_deleted z hdeleted]
      change canonicalProjectiveConeEliminationKeptWord zd = 1
      simp only [canonicalProjectiveConeEliminationKeptWord]
      rw [hindex]
      simp [hsource, htarget]
    · let z : CanonicalProjectiveConeNondegenerateSymbol p :=
        ⟨canonicalProjectiveConePairSource i, hsource⟩
      have hselected : canonicalProjectiveConeEliminationSymbol i = z := by
        simp [z, canonicalProjectiveConeEliminationSymbol, hsource]
        apply Subtype.ext
        rfl
      have hdeleted : isCanonicalProjectiveConeEliminationSymbol z := ⟨i, hselected⟩
      let zd : CanonicalProjectiveConeDeletedSymbol p := ⟨z, hdeleted⟩
      have hindex : canonicalProjectiveConeEliminationIndex zd = i := by
        apply canonicalProjectiveConeEliminationSymbol_injective
        rw [canonicalProjectiveConeEliminationIndex_spec]
        exact hselected.symm
      let w : CanonicalProjectiveConeKeptSymbol p :=
        canonicalProjectiveConeKeptTarget i hsource htarget
      rw [(CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord_of_not_degenerate hsource,
        (CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord_of_not_degenerate htarget]
      have htarget_eq :
          (⟨canonicalProjectiveConePairTarget i, htarget⟩ :
            CanonicalProjectiveConeNondegenerateSymbol p) = w.1 := by
        apply Subtype.ext
        rfl
      change canonicalProjectiveConeFirstStageSubstitution p (FreeGroup.of z) *
          canonicalProjectiveConeFirstStageSubstitution p
            (FreeGroup.of (⟨canonicalProjectiveConePairTarget i, htarget⟩ :
              CanonicalProjectiveConeNondegenerateSymbol p)) = 1
      rw [htarget_eq, canonicalProjectiveConeFirstStageSubstitution_of_deleted z hdeleted,
        canonicalProjectiveConeFirstStageSubstitution_of_kept w]
      change canonicalProjectiveConeEliminationKeptWord zd * FreeGroup.of w = 1
      simp only [canonicalProjectiveConeEliminationKeptWord]
      rw [hindex]
      simp [hsource, htarget, w]

/-- The image of the cone-square boundary at either endpoint of a cone orbit
is trivial after substitution. -/
theorem canonicalProjectiveConeFirstStageSubstitution_conePair_eq_one
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p)
    (e : ProjectiveOctagonConeGenerator) :
    canonicalProjectiveConeFirstStageSubstitution p
      ((CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord (q, e.lift) *
        (CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord
          ((CanonicalProjectiveConeSchreierData p).transition q e.lift, e.lift)) = 1 := by
  let r := buserSarnakProjectiveConeLower p e q
  let i : BuserSarnakProjectiveConePairIndex p :=
    ⟨e, ⟨r, buserSarnakProjectiveConeLower_lt_partner p hp hp2 e q⟩⟩
  have hpair := canonicalProjectiveConeFirstStageSubstitution_pair_eq_one i
  have hpair' :
      canonicalProjectiveConeFirstStageSubstitution p
        ((CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord
            (r, e.lift) *
          (CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord
            (buserSarnakProjectiveConePartner p e r, e.lift)) = 1 := by
    simpa [i, canonicalProjectiveConePairSource,
      canonicalProjectiveConePairTarget] using hpair
  have htransition :
      (CanonicalProjectiveConeSchreierData p).transition q e.lift =
        buserSarnakProjectiveConePartner p e q :=
    rfl
  by_cases hlt : buserSarnakProjectiveConeRank p q <
      buserSarnakProjectiveConeRank p (buserSarnakProjectiveConePartner p e q)
  · have hr : r = q := by
      simp [r, buserSarnakProjectiveConeLower, hlt]
    calc
      canonicalProjectiveConeFirstStageSubstitution p
          ((CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord (q, e.lift) *
            (CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord
              ((CanonicalProjectiveConeSchreierData p).transition q e.lift, e.lift)) =
          canonicalProjectiveConeFirstStageSubstitution p
            ((CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord (q, e.lift) *
              (CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord
                (buserSarnakProjectiveConePartner p e q, e.lift)) := by
              rw [htransition]
      _ = 1 := by simpa [hr] using hpair'
  · have hr : r = buserSarnakProjectiveConePartner p e q := by
      simp [r, buserSarnakProjectiveConeLower, hlt]
    have hpair_reverse :
        canonicalProjectiveConeFirstStageSubstitution p
          ((CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord
              (buserSarnakProjectiveConePartner p e q, e.lift) *
            (CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord
              (q, e.lift)) = 1 := by
      simpa [hr, buserSarnakProjectiveConePartner_partner] using hpair'
    let A := canonicalProjectiveConeFirstStageSubstitution p
      ((CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord (q, e.lift))
    let B := canonicalProjectiveConeFirstStageSubstitution p
      ((CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord
        (buserSarnakProjectiveConePartner p e q, e.lift))
    have hBA : B * A = 1 := by
      simpa only [A, B, map_mul] using hpair_reverse
    calc
      canonicalProjectiveConeFirstStageSubstitution p
          ((CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord (q, e.lift) *
            (CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord
              ((CanonicalProjectiveConeSchreierData p).transition q e.lift, e.lift)) = A * B := by
          rw [map_mul, htransition]
      _ = A * (B * A) * A⁻¹ := by group
      _ = 1 := by rw [hBA]; simp

/-- Each substituted projective cone-square relator is literally the empty
word.  Thus the cone part of the first-stage target relator family contributes
no nontrivial post-cone relation. -/
theorem canonicalProjectiveConeFirstStageSubstitution_coneSquare_eq_one
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p)
    (e : ProjectiveOctagonConeGenerator) :
    canonicalProjectiveConeFirstStageSubstitution p
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).schreierData.cleanedTau q
        (FreeGroup.of e.lift ^ 2)) = 1 := by
  rw [(canonicalBuserSarnakProjectiveQuotientSectionData p).cleanedTau_sq q e.lift]
  exact canonicalProjectiveConeFirstStageSubstitution_conePair_eq_one hp hp2 q e

/-- Every first-stage relator is a consequence of the post-cone polygon
relators: the four cone-square cases collapse literally, while the remaining
case is a polygon boundary word. -/
theorem canonicalProjectiveConeFirstStageRelators_subset_normalClosure_postConePolygon
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    CanonicalProjectiveConeFirstStageRelators p ⊆
      Subgroup.normalClosure (CanonicalProjectiveConePostConePolygonRelators p) := by
  rintro r ⟨u, ⟨v, hv, rfl⟩, rfl⟩
  rcases hv with ⟨q, w, hw, rfl⟩
  rcases hw with ⟨kind, rfl⟩
  cases kind with
  | e1_sq =>
      change canonicalProjectiveConeFirstStageSubstitution p
          ((canonicalBuserSarnakProjectiveQuotientSectionData p).schreierData.cleanedTau q
            (FreeGroup.of ProjectiveOctagonGenerator.e1 ^ 2)) ∈
          Subgroup.normalClosure (CanonicalProjectiveConePostConePolygonRelators p)
      have hcollapse : canonicalProjectiveConeFirstStageSubstitution p
          ((canonicalBuserSarnakProjectiveQuotientSectionData p).schreierData.cleanedTau q
            (FreeGroup.of ProjectiveOctagonGenerator.e1 ^ 2)) = 1 := by
        simpa [ProjectiveOctagonConeGenerator.lift] using
          (canonicalProjectiveConeFirstStageSubstitution_coneSquare_eq_one hp hp2 q .e1)
      rw [hcollapse]
      exact Subgroup.one_mem _
  | e2_sq =>
      change canonicalProjectiveConeFirstStageSubstitution p
          ((canonicalBuserSarnakProjectiveQuotientSectionData p).schreierData.cleanedTau q
            (FreeGroup.of ProjectiveOctagonGenerator.e2 ^ 2)) ∈
          Subgroup.normalClosure (CanonicalProjectiveConePostConePolygonRelators p)
      have hcollapse : canonicalProjectiveConeFirstStageSubstitution p
          ((canonicalBuserSarnakProjectiveQuotientSectionData p).schreierData.cleanedTau q
            (FreeGroup.of ProjectiveOctagonGenerator.e2 ^ 2)) = 1 := by
        simpa [ProjectiveOctagonConeGenerator.lift] using
          (canonicalProjectiveConeFirstStageSubstitution_coneSquare_eq_one hp hp2 q .e2)
      rw [hcollapse]
      exact Subgroup.one_mem _
  | e3_sq =>
      change canonicalProjectiveConeFirstStageSubstitution p
          ((canonicalBuserSarnakProjectiveQuotientSectionData p).schreierData.cleanedTau q
            (FreeGroup.of ProjectiveOctagonGenerator.e3 ^ 2)) ∈
          Subgroup.normalClosure (CanonicalProjectiveConePostConePolygonRelators p)
      have hcollapse : canonicalProjectiveConeFirstStageSubstitution p
          ((canonicalBuserSarnakProjectiveQuotientSectionData p).schreierData.cleanedTau q
            (FreeGroup.of ProjectiveOctagonGenerator.e3 ^ 2)) = 1 := by
        simpa [ProjectiveOctagonConeGenerator.lift] using
          (canonicalProjectiveConeFirstStageSubstitution_coneSquare_eq_one hp hp2 q .e3)
      rw [hcollapse]
      exact Subgroup.one_mem _
  | e4_sq =>
      change canonicalProjectiveConeFirstStageSubstitution p
          ((canonicalBuserSarnakProjectiveQuotientSectionData p).schreierData.cleanedTau q
            (FreeGroup.of ProjectiveOctagonGenerator.e4 ^ 2)) ∈
          Subgroup.normalClosure (CanonicalProjectiveConePostConePolygonRelators p)
      have hcollapse : canonicalProjectiveConeFirstStageSubstitution p
          ((canonicalBuserSarnakProjectiveQuotientSectionData p).schreierData.cleanedTau q
            (FreeGroup.of ProjectiveOctagonGenerator.e4 ^ 2)) = 1 := by
        simpa [ProjectiveOctagonConeGenerator.lift] using
          (canonicalProjectiveConeFirstStageSubstitution_coneSquare_eq_one hp hp2 q .e4)
      rw [hcollapse]
      exact Subgroup.one_mem _
  | polygon =>
      change canonicalProjectiveConeFirstStageSubstitution p
          ((canonicalBuserSarnakProjectiveQuotientSectionData p).schreierData.cleanedTau q
            (projectiveOctagonRelator .polygon)) ∈
          Subgroup.normalClosure (CanonicalProjectiveConePostConePolygonRelators p)
      rw [(canonicalBuserSarnakProjectiveQuotientSectionData p).cleanedTau_polygon q]
      exact Subgroup.subset_normalClosure ⟨q, rfl⟩

/-- Each displayed post-cone polygon word is already a first-stage target
relator. -/
theorem canonicalProjectiveConePostConePolygonRelators_subset_normalClosure_firstStage
    {p : ℕ} [NeZero p] :
    CanonicalProjectiveConePostConePolygonRelators p ⊆
      Subgroup.normalClosure (CanonicalProjectiveConeFirstStageRelators p) := by
  rintro r ⟨q, rfl⟩
  exact Subgroup.subset_normalClosure
    (canonicalProjectiveConePostConePolygonWord_mem_firstStageRelators q)

/-- At odd projective levels, the first cone-stage target and the polygon-only
post-cone presentation have the same relator normal closure. -/
theorem canonicalProjectiveConeFirstStage_normalClosure_eq_postConePolygon
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    Subgroup.normalClosure (CanonicalProjectiveConeFirstStageRelators p) =
      Subgroup.normalClosure (CanonicalProjectiveConePostConePolygonRelators p) := by
  exact normalClosure_eq_of_subset_normalClosure
    (canonicalProjectiveConeFirstStageRelators_subset_normalClosure_postConePolygon hp hp2)
    canonicalProjectiveConePostConePolygonRelators_subset_normalClosure_firstStage

/-- The first cone-stage target is Tietze equivalent to its polygon-only
post-cone relator presentation. -/
noncomputable def canonicalProjectiveConeFirstStagePostConePolygonTietzeEquiv
    (p : ℕ) [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    TietzeEquiv (CanonicalProjectiveConeFirstStageRelators p)
      (CanonicalProjectiveConePostConePolygonRelators p) :=
  TietzeEquiv.ofNormalClosureEq
    (canonicalProjectiveConeFirstStage_normalClosure_eq_postConePolygon hp hp2)

/-- The arrows of the canonical post-cone physical tree.  These are the
concrete slots for the second, polygon-based Tietze elimination. -/
abbrev CanonicalProjectivePostConeTreeSlot
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :=
  Quiver.Total (projectivePolygonPostConeCanonicalSpanningTree hp hp2)

/-- The retained generator carried by a canonical physical-tree arrow. -/
noncomputable def canonicalProjectivePostConeTreeSlotLabel
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    CanonicalProjectivePostConeTreeSlot hp hp2 →
      CanonicalProjectiveConeKeptSymbol p := by
  letI := projectivePolygonPostConeCanonicalSpanningTreeArborescence hp hp2
  exact projectivePolygonPostConeTreeArrowLabel
    (projectivePolygonPostConeCanonicalSpanningTree hp hp2)

/-- Canonical physical-tree slots carry pairwise distinct retained generators. -/
theorem canonicalProjectivePostConeTreeSlotLabel_injective
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    Function.Injective (canonicalProjectivePostConeTreeSlotLabel hp hp2) := by
  letI := projectivePolygonPostConeCanonicalSpanningTreeArborescence hp hp2
  exact projectivePolygonPostConeTreeArrowLabel_injective
    (projectivePolygonPostConeCanonicalSpanningTree hp hp2)

/-- The canonical dual tree supplies exactly the remaining `h - 1` distinct
generator-elimination slots. -/
theorem natCard_canonicalProjectivePostConeTreeSlot
    {p : ℕ} [NeZero p]
    (data : BuserSarnakCorrectionData p)
    (hp : p.Prime) (hp2 : p ≠ 2) :
    Nat.card (CanonicalProjectivePostConeTreeSlot hp hp2) =
      data.halfImageIndex - 1 := by
  letI := projectivePolygonPostConeCanonicalSpanningTreeArborescence hp hp2
  exact natCard_projectivePolygonPostConeTree_total_eq_halfImageIndex_sub_one
    data hp hp2 (projectivePolygonPostConeCanonicalSpanningTree hp hp2)

end

end SystolicGrowth
