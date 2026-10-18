module

public import BuserSarnak.BuserSarnakProjectivePostConeDirectTreeWords
public import BuserSarnak.BuserSarnakProjectivePolygonFinalNormalization

@[expose] public section

/-!
# Direct post-cone presentation collapse

The boundary-explicit tree words make the second Tietze substitution concrete.
This module transports the literal non-root-face collapse through the complete
first-stage relator presentation.  Consequently the resulting post-tree
presentation has exactly one remaining relator normal-closure generator: the
direct image of the physical root-face polygon word.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete
open ReidemeisterSchreier.Discrete.Presentations

/-- For the direct boundary-explicit tree data, the generic final relator
family is precisely the image of the first-stage relators under the explicit
simultaneous substitution. -/
theorem canonicalProjectivePostConeDirectFinalRelators_eq_image_firstStage
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    CanonicalProjectivePostConeFinalRelators hp hp2
      (canonicalProjectivePostConeDirectTreeEliminationData hp hp2) =
      canonicalProjectivePostConeDirectFinalSubstitution hp hp2 ''
        CanonicalProjectiveConeFirstStageRelators p := by
  let : DecidablePred
      (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2) :=
    canonicalProjectivePostConeTreeEliminationDecidable hp hp2
  ext r
  change r ∈ Presented.eliminateAdjoinedGeneratorsHom
      (canonicalProjectivePostConeDirectTreeEliminationWord hp hp2) ''
      (FreeGroup.freeGroupCongr
        (Presented.GeneratorPartition.equiv
          (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)) ''
        CanonicalProjectiveConeFirstStageRelators p) ↔
    r ∈ ((Presented.eliminateAdjoinedGeneratorsHom
      (canonicalProjectivePostConeDirectTreeEliminationWord hp hp2)).comp
      (FreeGroup.freeGroupCongr (Presented.GeneratorPartition.equiv
        (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)))) ''
      CanonicalProjectiveConeFirstStageRelators p
  constructor
  · rintro ⟨u, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨FreeGroup.freeGroupCongr
      (Presented.GeneratorPartition.equiv
        (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2)) v,
      ⟨v, hv, rfl⟩, rfl⟩

/-- The concrete post-tree relators have the normal closure of the sole
surviving root-face polygon word.  This is the complete algebraic collapse of
the post-cone relator family. Subsequent Nielsen modules normalize the
root word to the standard surface word. -/
theorem canonicalProjectivePostConeDirectFinalRelators_normalClosure_eq_singleton_root
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    Subgroup.normalClosure
      (CanonicalProjectivePostConeFinalRelators hp hp2
        (canonicalProjectivePostConeDirectTreeEliminationData hp hp2)) =
      Subgroup.normalClosure
        ({(canonicalProjectivePostConeDirectFinalSubstitution hp hp2
          (canonicalProjectiveConePostConePolygonWord p
            (canonicalProjectivePostConeTreeRoot hp hp2).state))} :
          Set (FreeGroup (CanonicalProjectivePostConeFinalGenerator hp hp2))) := by
  rw [canonicalProjectivePostConeDirectFinalRelators_eq_image_firstStage hp hp2]
  apply normalClosure_eq_of_subset_normalClosure
  · rintro r ⟨s, hs, rfl⟩
    apply map_mem_normalClosure_of_relators
      (R := CanonicalProjectiveConePostConePolygonRelators p)
      (canonicalProjectivePostConeDirectFinalSubstitution hp hp2)
    · intro x hx
      rw [← canonicalProjectivePostConeDirectFinalSubstitution_polygonRelators_normalClosure_eq_singleton_root
        hp hp2]
      exact Subgroup.subset_normalClosure ⟨x, hx, rfl⟩
    · exact canonicalProjectiveConeFirstStageRelators_subset_normalClosure_postConePolygon
        hp hp2 hs
  · intro r hr
    rw [Set.mem_singleton_iff.mp hr]
    exact Subgroup.subset_normalClosure
      ⟨_, canonicalProjectiveConePostConePolygonWord_mem_firstStageRelators _, rfl⟩

/-- The one relator left after direct tree elimination, written as a named
word on the surviving physical-edge alphabet. -/
noncomputable def canonicalProjectivePostConeDirectRootWord
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    FreeGroup (CanonicalProjectivePostConeFinalGenerator hp hp2) :=
  canonicalProjectivePostConeDirectFinalSubstitution hp hp2
    (canonicalProjectiveConePostConePolygonWord p
      (canonicalProjectivePostConeTreeRoot hp hp2).state)

/-- Convenience form of the direct final-relator collapse using the named
root word. -/
theorem canonicalProjectivePostConeDirectFinalRelators_normalClosure_eq_singleton_rootWord
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    Subgroup.normalClosure
      (CanonicalProjectivePostConeFinalRelators hp hp2
        (canonicalProjectivePostConeDirectTreeEliminationData hp hp2)) =
      Subgroup.normalClosure ({canonicalProjectivePostConeDirectRootWord hp hp2} :
        Set (FreeGroup (CanonicalProjectivePostConeFinalGenerator hp hp2))) := by
  simpa [canonicalProjectivePostConeDirectRootWord] using
    canonicalProjectivePostConeDirectFinalRelators_normalClosure_eq_singleton_root hp hp2

/-- Replace the concrete direct final-relator family by its singleton root
word presentation. -/
noncomputable def canonicalProjectivePostConeDirectFinalRelatorsTietzeEquivSingletonRoot
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    TietzeEquiv
      (CanonicalProjectivePostConeFinalRelators hp hp2
        (canonicalProjectivePostConeDirectTreeEliminationData hp hp2))
      ({canonicalProjectivePostConeDirectRootWord hp hp2} :
        Set (FreeGroup (CanonicalProjectivePostConeFinalGenerator hp hp2))) :=
  TietzeEquiv.ofNormalClosureEq
    (canonicalProjectivePostConeDirectFinalRelators_normalClosure_eq_singleton_rootWord hp hp2)

/-- The complete second-stage direct tree elimination, followed by removal of
all redundant face relators, yields the singleton root-word presentation. -/
noncomputable def canonicalProjectivePostConeDirectFirstStageTietzeEquivSingletonRoot
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    TietzeEquiv (CanonicalProjectiveConeFirstStageRelators p)
      ({canonicalProjectivePostConeDirectRootWord hp hp2} :
        Set (FreeGroup (CanonicalProjectivePostConeFinalGenerator hp hp2))) :=
  ((CanonicalProjectivePostConeTreeEliminationData.verifiedTietzeScript hp hp2
    (canonicalProjectivePostConeDirectTreeEliminationData hp hp2)).toCertificate.toTietzeEquiv).trans
    (canonicalProjectivePostConeDirectFinalRelatorsTietzeEquivSingletonRoot hp hp2)

/-- Starting with the cleaned projective cone presentation, the verified cone
and direct tree eliminations leave precisely the singleton root-word
presentation. -/
noncomputable def canonicalProjectiveConeTietzeEquivSingletonRoot
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    TietzeEquiv (CanonicalProjectiveConeRelators p)
      ({canonicalProjectivePostConeDirectRootWord hp hp2} :
        Set (FreeGroup (CanonicalProjectivePostConeFinalGenerator hp hp2))) :=
  ((canonicalProjectiveConeFirstStageVerifiedTietzeScript p).toCertificate.toTietzeEquiv).trans
    (canonicalProjectivePostConeDirectFirstStageTietzeEquivSingletonRoot hp hp2)

end

end SystolicGrowth
