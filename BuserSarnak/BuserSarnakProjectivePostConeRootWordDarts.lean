module

public import BuserSarnak.BuserSarnakProjectivePostConeDirectTreeWords

@[expose] public section

/-!
# Oriented survivor darts for the direct root word

Each retained physical edge supplies two distinct oriented polygon-boundary
occurrences.  For a final (non-tree) edge, direct substitution carries those
occurrences to a surviving generator and its inverse.  These are the local
pairing data required by the remaining global chord/Nielsen normalization.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete
open ReidemeisterSchreier.Discrete.Presentations

/-- A directed occurrence in a post-cone polygon boundary. -/
abbrev ProjectivePolygonPostConeBoundaryDart
    (p : ℕ) [NeZero p] :=
  BuserSarnakProjectiveReductionRange p × ProjectivePolygonSide

/-- The positively oriented boundary occurrence of a retained physical edge. -/
noncomputable def projectivePolygonPostConeEdgeSourceDart
    {p : ℕ} [NeZero p]
    (z : CanonicalProjectiveConeKeptSymbol p) :
    ProjectivePolygonPostConeBoundaryDart p :=
  ((projectivePolygonPostConeEdgeSource z).state,
    projectivePolygonPostConeEdgeSide z)

/-- The paired, inversely oriented boundary occurrence of a retained physical
edge. -/
noncomputable def projectivePolygonPostConeEdgeTargetDart
    {p : ℕ} [NeZero p]
    (z : CanonicalProjectiveConeKeptSymbol p) :
    ProjectivePolygonPostConeBoundaryDart p :=
  ((projectivePolygonPostConeEdgeTarget z).state,
    projectivePolygonPostConeEdgeTargetSide z)

/-- The target dart is exactly the side-pairing partner of the source dart. -/
theorem projectivePolygonPostConeEdgeTargetDart_eq_partner
    {p : ℕ} [NeZero p]
    (z : CanonicalProjectiveConeKeptSymbol p) :
    projectivePolygonPostConeEdgeTargetDart z =
      (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner
        (projectivePolygonPostConeEdgeSource z).state
        (projectivePolygonPostConeEdgeSide z) := by
  rfl

/-- The two oriented boundary occurrences of a retained physical edge are
distinct.  This holds even if the two incident polygon faces coincide. -/
theorem projectivePolygonPostConeEdgeSourceDart_ne_targetDart
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : CanonicalProjectiveConeKeptSymbol p) :
    projectivePolygonPostConeEdgeSourceDart z ≠
      projectivePolygonPostConeEdgeTargetDart z := by
  classical
  intro h
  have hterm : FreeGroup.of z = (FreeGroup.of z)⁻¹ := by
    calc
      FreeGroup.of z = canonicalProjectiveConePostConeBoundaryTerm p
          (projectivePolygonPostConeEdgeSourceDart z).1
          (projectivePolygonPostConeEdgeSourceDart z).2 := by
            simpa [projectivePolygonPostConeEdgeSourceDart] using
              (canonicalProjectiveConePostConeBoundaryTerm_edgeSource_eq z).symm
      _ = canonicalProjectiveConePostConeBoundaryTerm p
          (projectivePolygonPostConeEdgeTargetDart z).1
          (projectivePolygonPostConeEdgeTargetDart z).2 := by rw [h]
      _ = (FreeGroup.of z)⁻¹ := by
            simpa [projectivePolygonPostConeEdgeTargetDart,
              projectivePolygonPostConeEdgeTargetSide] using
              canonicalProjectiveConePostConeBoundaryTerm_edgeTarget_eq_inv hp hp2 z
  have hword := congrArg FreeGroup.toWord hterm
  simp only [FreeGroup.toWord_of, FreeGroup.toWord_inv] at hword
  simp [FreeGroup.invRev] at hword

/-- Direct substitution sends the source dart of each final physical edge to
its corresponding surviving free generator. -/
theorem canonicalProjectivePostConeDirectFinalSubstitution_sourceDart_of_final
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : CanonicalProjectiveConeKeptSymbol p)
    (hz : ¬ isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z) :
    canonicalProjectivePostConeDirectFinalSubstitution hp hp2
      (canonicalProjectiveConePostConeBoundaryTerm p
        (projectivePolygonPostConeEdgeSourceDart z).1
        (projectivePolygonPostConeEdgeSourceDart z).2) =
      FreeGroup.of ⟨z, hz⟩ := by
  rw [show canonicalProjectiveConePostConeBoundaryTerm p
      (projectivePolygonPostConeEdgeSourceDart z).1
      (projectivePolygonPostConeEdgeSourceDart z).2 = FreeGroup.of z by
    simpa [projectivePolygonPostConeEdgeSourceDart] using
      canonicalProjectiveConePostConeBoundaryTerm_edgeSource_eq z]
  exact canonicalProjectivePostConeDirectFinalSubstitution_of_kept hp hp2 ⟨z, hz⟩

/-- Direct substitution sends the target dart of each final physical edge to
the inverse of its surviving free generator. -/
theorem canonicalProjectivePostConeDirectFinalSubstitution_targetDart_of_final
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : CanonicalProjectiveConeKeptSymbol p)
    (hz : ¬ isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z) :
    canonicalProjectivePostConeDirectFinalSubstitution hp hp2
      (canonicalProjectiveConePostConeBoundaryTerm p
        (projectivePolygonPostConeEdgeTargetDart z).1
        (projectivePolygonPostConeEdgeTargetDart z).2) =
      (FreeGroup.of ⟨z, hz⟩)⁻¹ := by
  rw [show canonicalProjectiveConePostConeBoundaryTerm p
      (projectivePolygonPostConeEdgeTargetDart z).1
      (projectivePolygonPostConeEdgeTargetDart z).2 = (FreeGroup.of z)⁻¹ by
    simpa [projectivePolygonPostConeEdgeTargetDart,
      projectivePolygonPostConeEdgeTargetSide] using
      canonicalProjectiveConePostConeBoundaryTerm_edgeTarget_eq_inv hp hp2 z]
  rw [map_inv, canonicalProjectivePostConeDirectFinalSubstitution_of_kept hp hp2 ⟨z, hz⟩]

/-- Any boundary term carried by a final physical edge becomes the
corresponding signed final-alphabet letter under direct substitution. -/
theorem canonicalProjectivePostConeDirectFinalSubstitution_of_finalPhysicalCarrier
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide)
    (z : CanonicalProjectiveConeKeptSymbol p)
    (hz : ¬ isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z)
    (hcarrier : CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrierBy p q s z) :
    canonicalProjectivePostConeDirectFinalSubstitution hp hp2
      (canonicalProjectiveConePostConeBoundaryTerm p q s) =
        FreeGroup.of ⟨z, hz⟩ ∨
      canonicalProjectivePostConeDirectFinalSubstitution hp hp2
        (canonicalProjectiveConePostConeBoundaryTerm p q s) =
          (FreeGroup.of ⟨z, hz⟩)⁻¹ := by
  let k : Presented.GeneratorPartition.Kept
      (isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2) := ⟨z, hz⟩
  rcases hcarrier with hsource | htarget
  · left
    rw [hsource.2.2,
      canonicalProjectivePostConeDirectFinalSubstitution_of_kept hp hp2 k]
  · right
    rw [htarget.2.2, map_inv,
      canonicalProjectivePostConeDirectFinalSubstitution_of_kept hp hp2 k]

end

end SystolicGrowth
