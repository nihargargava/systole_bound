module

public import BuserSarnak.BuserSarnakProjectiveCanonicalTree
public import BuserSarnak.BuserSarnakProjectivePolygonPostConeConnectivity

@[expose] public section

/-!
# Cut predicates for the post-cone physical quiver

This module records the root component of the symmetrized physical quiver and
the elementary fact that a boundary crossing must use a canonical tree edge.
It is the global half of the finite tree--cotree argument; the remaining work
is local carrier bookkeeping around an octagon vertex.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete

noncomputable local instance buserSarnakProjectivePolygonPostConeCutRangeFintype
    (p : ℕ) [NeZero p] : Fintype (BuserSarnakProjectiveReductionRange p) :=
  Fintype.ofFinite _

/-- The physical-quiver vertex associated to a quotient state. -/
def projectivePolygonPostConeVertex
    {p : ℕ} [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p) :
    Quiver.Symmetrify (ProjectivePolygonPostConeFace p) :=
  canonicalProjectivePolygonFaceToPostConeFace
    (⟨q⟩ : ProjectivePolygonFace
      (canonicalBuserSarnakProjectiveQuotientSectionData p))

/-- States reachable from the identity through retained physical edges. -/
def projectivePolygonPostConeRootComponent
    (p : ℕ) [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p) : Prop :=
  Nonempty (Quiver.Path (projectivePolygonPostConeRoot p)
    (projectivePolygonPostConeVertex q))

/-- The identity state belongs to the root component. -/
theorem projectivePolygonPostConeRootComponent_one
    (p : ℕ) [NeZero p] :
    projectivePolygonPostConeRootComponent p 1 := by
  exact ⟨.nil⟩

/-- A physical path preserves membership in the root component in either
direction, because the physical quiver has been symmetrized. -/
theorem projectivePolygonPostConeRootComponent_iff_of_path
    {p : ℕ} [NeZero p]
    {q r : BuserSarnakProjectiveReductionRange p}
    (path : Quiver.Path (projectivePolygonPostConeVertex q)
      (projectivePolygonPostConeVertex r)) :
    projectivePolygonPostConeRootComponent p q ↔
      projectivePolygonPostConeRootComponent p r := by
  constructor
  · rintro ⟨rootPath⟩
    exact ⟨rootPath.comp path⟩
  · rintro ⟨rootPath⟩
    exact ⟨rootPath.comp path.reverse⟩

/-- A directed polygon side crosses the root component exactly when its two
incident faces have different membership. -/
def projectivePolygonPostConeCrossing
    {p : ℕ} [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide) : Prop :=
  ¬ (projectivePolygonPostConeRootComponent p q ↔
    projectivePolygonPostConeRootComponent p
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).1)

/-- Crossing the root-component cut is invariant under replacing a side by
its paired occurrence. -/
theorem projectivePolygonPostConeCrossing_partner_iff
    {p : ℕ} [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide) :
    projectivePolygonPostConeCrossing
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).1
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).2 ↔
      projectivePolygonPostConeCrossing q s := by
  let S := canonicalBuserSarnakProjectiveQuotientSectionData p
  have hinv := S.polygonSidePartner_involutive q s
  constructor
  · intro h hcomponent
    apply h
    change projectivePolygonPostConeRootComponent p (S.polygonSidePartner q s).1 ↔
      projectivePolygonPostConeRootComponent p
        (S.polygonSidePartner (S.polygonSidePartner q s).1
          (S.polygonSidePartner q s).2).1
    rw [hinv]
    exact hcomponent.symm
  · intro h hcomponent
    apply h
    have hcomponent' := hcomponent.symm
    rw [hinv] at hcomponent'
    exact hcomponent'

/-- If both raw labels of a polygon side survived the canonical tree, its
physical survivor edge identifies the two component memberships. -/
theorem projectivePolygonPostConeRootComponent_iff_of_raw_and_partner_nondegenerate
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide)
    (hraw : ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol q s))
    (hpartner : ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol
        ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).1
        ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).2)) :
    projectivePolygonPostConeRootComponent p q ↔
      projectivePolygonPostConeRootComponent p
        ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).1 := by
  obtain ⟨path⟩ := projectivePolygonPostCone_oneEdge_of_raw_and_partner_nondegenerate
    hp hp2 q s hraw hpartner
  exact projectivePolygonPostConeRootComponent_iff_of_path path

/-- Therefore every root-component crossing has a degenerate raw label at
one of its two side occurrences, hence is supported by the canonical tree. -/
theorem projectivePolygonPostConeCrossing_raw_or_partner_degenerate
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (s : ProjectivePolygonSide)
    (hcross : projectivePolygonPostConeCrossing q s) :
    (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
        ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol q s) ∨
      (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
        ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol
          ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).1
          ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner q s).2) := by
  classical
  by_contra h
  push Not at h
  exact hcross
    (projectivePolygonPostConeRootComponent_iff_of_raw_and_partner_nondegenerate
      hp hp2 q s h.1 h.2)

/-- If no polygon side crosses the physical root component, full polygon-face
connectivity propagates that component membership to every quotient state. -/
theorem projectivePolygonPostConeRootComponent_of_forall_not_crossing
    {p : ℕ} [NeZero p]
    (hcross : ∀ (q : BuserSarnakProjectiveReductionRange p)
      (s : ProjectivePolygonSide), ¬ projectivePolygonPostConeCrossing q s)
    (q : BuserSarnakProjectiveReductionRange p) :
    projectivePolygonPostConeRootComponent p q := by
  let S := canonicalBuserSarnakProjectiveQuotientSectionData p
  have hreaches := projectivePolygonFaceStep_reaches_all S q
  induction hreaches with
  | refl => exact projectivePolygonPostConeRootComponent_one p
  | @tail b c hpath hstep ih =>
      rcases hstep with ⟨s, hs⟩
      have hiff : projectivePolygonPostConeRootComponent p b ↔
          projectivePolygonPostConeRootComponent p
            (S.polygonSidePartner b s).1 := by
        exact Classical.not_not.mp (hcross b s)
      rw [hs] at hiff
      exact hiff.mp ih

/-- A state outside the physical root component forces a polygon-side
crossing somewhere in the connected full face quiver. -/
theorem exists_projectivePolygonPostConeCrossing_of_not_rootComponent
    {p : ℕ} [NeZero p]
    {q : BuserSarnakProjectiveReductionRange p}
    (hq : ¬ projectivePolygonPostConeRootComponent p q) :
    ∃ r : BuserSarnakProjectiveReductionRange p, ∃ s : ProjectivePolygonSide,
      projectivePolygonPostConeCrossing r s := by
  classical
  by_contra hnone
  apply hq
  apply projectivePolygonPostConeRootComponent_of_forall_not_crossing
  intro r s hcross
  exact hnone ⟨r, s, hcross⟩

end

end SystolicGrowth
