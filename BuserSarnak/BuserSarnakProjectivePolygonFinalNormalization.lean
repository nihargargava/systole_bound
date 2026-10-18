module

public import BuserSarnak.BuserSarnakProjectivePolygonTreeEliminationPlan

@[expose] public section

/-!
# Final normalization interface for the post-cone projective polygon

After the cone and physical-tree eliminations, the remaining alphabet has the
cardinality of the standard genus-`h + 1` surface alphabet.  This module makes
that generator renaming explicit and isolates the sole remaining algebraic
obligation: proving that the renamed post-tree relators have the normal
closure of the standard surface relator.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete.Presentations

noncomputable local instance buserSarnakProjectiveFinalNormalizationRangeFintype
    (p : ℕ) [NeZero p] : Fintype (BuserSarnakProjectiveReductionRange p) :=
  Fintype.ofFinite _

noncomputable local instance buserSarnakProjectiveFinalNormalizationDegenerateDecidable
    {p : ℕ} [NeZero p] :
    DecidablePred (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol :=
  Classical.decPred _

noncomputable local instance buserSarnakProjectiveFinalNormalizationConeEliminationDecidable
    {p : ℕ} [NeZero p] :
    DecidablePred (@isCanonicalProjectiveConeEliminationSymbol p _) :=
  Classical.decPred _

noncomputable local instance buserSarnakProjectiveFinalNormalizationTreeEliminationDecidable
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    DecidablePred (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2) :=
  Classical.decPred _

noncomputable local instance buserSarnakProjectiveFinalNormalizationNondegenerateFintype
    (p : ℕ) [NeZero p] : Fintype (CanonicalProjectiveConeNondegenerateSymbol p) :=
  Fintype.subtype
    (Finset.univ.filter fun z =>
      ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol z)
    (by simp)

noncomputable local instance buserSarnakProjectiveFinalNormalizationKeptFintype
    (p : ℕ) [NeZero p] : Fintype (CanonicalProjectiveConeKeptSymbol p) :=
  Fintype.subtype
    (Finset.univ.filter fun z =>
      ¬ isCanonicalProjectiveConeEliminationSymbol z)
    (by simp)

noncomputable local instance buserSarnakProjectiveFinalNormalizationDeletedFintype
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    Fintype (Presented.GeneratorPartition.Deleted
      (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)) :=
  Fintype.subtype
    (Finset.univ.filter fun z =>
      isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z)
    (by simp)

noncomputable local instance buserSarnakProjectiveFinalNormalizationFinalKeptFintype
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    Fintype (Presented.GeneratorPartition.Kept
      (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)) :=
  Fintype.subtype
    (Finset.univ.filter fun z =>
      ¬ isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z)
    (by simp)

noncomputable local instance buserSarnakProjectiveFinalNormalizationTreeSlotFintype
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    Fintype (CanonicalProjectivePostConeTreeSlot hp hp2) :=
  Fintype.ofEquiv _ (canonicalProjectivePostConeTreeSlotEquivDeleted hp hp2).symm

/-- Generators remaining after all canonical post-cone tree slots are
eliminated. -/
abbrev CanonicalProjectivePostConeFinalGenerator
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :=
  Presented.GeneratorPartition.Kept
    (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)

/-- The relator set after a supplied complete tree-elimination plan. -/
abbrev CanonicalProjectivePostConeFinalRelators
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (D : CanonicalProjectivePostConeTreeEliminationData hp hp2) :=
  @Presented.relatorsAfterSubstitutingDefinedGeneratorsOfPredicate
    (CanonicalProjectiveConeKeptSymbol p)
    (CanonicalProjectiveConeFirstStageRelators p)
    (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)
    (canonicalProjectivePostConeTreeEliminationDecidable hp hp2) D.word

/-- The final post-tree alphabet has two generators for each of the `h + 1`
standard handles. -/
theorem natCard_canonicalProjectivePostConeFinalGenerator
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : BuserSarnakCorrectionData p) :
    Nat.card (CanonicalProjectivePostConeFinalGenerator hp hp2) =
      2 * (data.halfImageIndex + 1) := by
  rw [Nat.card_eq_fintype_card]
  have hsplit := Fintype.card_subtype_compl
    (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)
  have hdeleted : Fintype.card (Presented.GeneratorPartition.Deleted
      (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)) =
      data.halfImageIndex - 1 := by
    rw [← Fintype.card_congr (canonicalProjectivePostConeTreeSlotEquivDeleted hp hp2)]
    rw [← Nat.card_eq_fintype_card]
    exact natCard_canonicalProjectivePostConeTreeSlot data hp hp2
  have hdeleted' : Fintype.card {z : CanonicalProjectiveConeKeptSymbol p //
      isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z} =
      data.halfImageIndex - 1 := by
    change Fintype.card {z : CanonicalProjectiveConeKeptSymbol p //
      isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z} = _ at hdeleted
    exact hdeleted
  have hkept : Fintype.card (CanonicalProjectiveConeKeptSymbol p) =
      3 * data.halfImageIndex + 1 := by
    rw [← Nat.card_eq_fintype_card]
    rw [Nat.card_eq_fintype_card]
    exact card_canonicalProjectiveConeKeptSymbol hp hp2 data
  have hhalf_pos : 0 < data.halfImageIndex := by
    have hrange_pos : 0 < Nat.card (BuserSarnakProjectiveReductionRange p) :=
      Nat.card_pos
    rw [natCard_buserSarnakProjectiveReductionRange hp hp2 data] at hrange_pos
    omega
  change Fintype.card {z : CanonicalProjectiveConeKeptSymbol p //
    ¬ isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z} = _
  rw [hsplit, hdeleted', hkept]
  omega

/-- Choose a finite renaming of the final post-tree alphabet to the standard
surface-generator alphabet.  The later relator-normalization proof is
responsible for choosing a combinatorially meaningful description of this
otherwise cardinality-based equivalence. -/
noncomputable def canonicalProjectivePostConeFinalGeneratorEquivSurface
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : BuserSarnakCorrectionData p) :
    CanonicalProjectivePostConeFinalGenerator hp hp2 ≃
      SurfaceGenerator (data.halfImageIndex + 1) := by
  apply Fintype.equivOfCardEq
  rw [← Nat.card_eq_fintype_card,
    natCard_canonicalProjectivePostConeFinalGenerator hp hp2 data]
  simp only [SurfaceGenerator, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool]
  omega

/-- Exact remaining data for the algebraic surface normalization.  The first
field proves every renamed post-tree relator redundant under the standard
surface relation; the second proves the standard relation follows from them.
Together they permit one relator-replacement move after the generator rename. -/
structure CanonicalProjectivePostConeSurfaceNormalizationData
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : BuserSarnakCorrectionData p)
    (D : CanonicalProjectivePostConeTreeEliminationData hp hp2) where
  generatorEquiv :
    CanonicalProjectivePostConeFinalGenerator hp hp2 ≃
      SurfaceGenerator (data.halfImageIndex + 1)
  relators_map_to_surface :
    ∀ r ∈ CanonicalProjectivePostConeFinalRelators hp hp2 D,
      RelatorEquivalent
        ({surfaceRelator (data.halfImageIndex + 1)} :
          Set (FreeGroup (SurfaceGenerator (data.halfImageIndex + 1))))
        (FreeGroup.freeGroupCongr generatorEquiv r) 1
  surfaceRelator_maps_from :
    RelatorEquivalent
      (FreeGroup.freeGroupCongr generatorEquiv ''
        CanonicalProjectivePostConeFinalRelators hp hp2 D)
      (surfaceRelator (data.halfImageIndex + 1)) 1

namespace CanonicalProjectivePostConeSurfaceNormalizationData

/-- Rename the final alphabet and replace its relator family by the standard
surface relation, using the supplied two-way normal-closure certificate. -/
noncomputable def verifiedTietzeScript
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : BuserSarnakCorrectionData p)
    (D : CanonicalProjectivePostConeTreeEliminationData hp hp2)
    (N : CanonicalProjectivePostConeSurfaceNormalizationData hp hp2 data D) :
    VerifiedTietzeScript
      (Presentation.ofRelators (CanonicalProjectivePostConeFinalRelators hp hp2 D))
      (Presentation.ofRelators
        ({surfaceRelator (data.halfImageIndex + 1)} :
          Set (FreeGroup (SurfaceGenerator (data.halfImageIndex + 1))))) :=
  (VerifiedTietzeScript.renameGenerators
    (CanonicalProjectivePostConeFinalRelators hp hp2 D)
    N.generatorEquiv).trans
    (VerifiedTietzeScript.replaceRelators
      (by
        rintro r ⟨s, hs, rfl⟩
        exact N.relators_map_to_surface s hs)
      (by
        intro r hr
        rw [Set.mem_singleton_iff.mp hr]
        exact N.surfaceRelator_maps_from))

/-- Compose the completed physical-tree elimination with the final surface
normalization.  Thus the remaining mathematics is precisely the construction
of the two fields of `CanonicalProjectivePostConeSurfaceNormalizationData`. -/
noncomputable def completeVerifiedTietzeScript
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : BuserSarnakCorrectionData p)
    (D : CanonicalProjectivePostConeTreeEliminationData hp hp2)
    (N : CanonicalProjectivePostConeSurfaceNormalizationData hp hp2 data D) :
    VerifiedTietzeScript
      (Presentation.ofRelators (CanonicalProjectiveConeFirstStageRelators p))
      (Presentation.ofRelators
        ({surfaceRelator (data.halfImageIndex + 1)} :
          Set (FreeGroup (SurfaceGenerator (data.halfImageIndex + 1))))) :=
  (CanonicalProjectivePostConeTreeEliminationData.verifiedTietzeScript hp hp2 D).trans
    (N.verifiedTietzeScript hp hp2 data D)

@[simp] theorem completeVerifiedTietzeScript_moveCount
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : BuserSarnakCorrectionData p)
    (D : CanonicalProjectivePostConeTreeEliminationData hp hp2)
    (N : CanonicalProjectivePostConeSurfaceNormalizationData hp hp2 data D) :
    (N.completeVerifiedTietzeScript hp hp2 data D).moveCount = 4 := by
  unfold completeVerifiedTietzeScript
  rw [VerifiedTietzeScript.moveCount_trans,
    CanonicalProjectivePostConeTreeEliminationData.verifiedTietzeScript_moveCount]
  rfl

/-- The final normalization has exactly a generator rename and a relator
replacement once its two normal-closure directions are proved. -/
@[simp] theorem verifiedTietzeScript_trace
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : BuserSarnakCorrectionData p)
    (D : CanonicalProjectivePostConeTreeEliminationData hp hp2)
    (N : CanonicalProjectivePostConeSurfaceNormalizationData hp hp2 data D) :
    (N.verifiedTietzeScript hp hp2 data D).trace =
      [.renameGenerators, .replaceRelators] :=
  rfl

@[simp] theorem verifiedTietzeScript_moveCount
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : BuserSarnakCorrectionData p)
    (D : CanonicalProjectivePostConeTreeEliminationData hp hp2)
    (N : CanonicalProjectivePostConeSurfaceNormalizationData hp hp2 data D) :
    (N.verifiedTietzeScript hp hp2 data D).moveCount = 2 :=
  rfl

end CanonicalProjectivePostConeSurfaceNormalizationData

end

end SystolicGrowth
