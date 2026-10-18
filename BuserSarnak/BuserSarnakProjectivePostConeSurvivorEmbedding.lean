module

public import BuserSarnak.BuserSarnakProjectivePostConeRootPartner
public import BuserSarnak.BuserSarnakProjectivePostConeRootWordDarts

@[expose] public section

/-!
# Embedding root-contour occurrences in original polygon darts

The exact endpoint equivalence places every literal root-contour position
at one retained physical polygon dart. This module identifies its image and
proves that the opposite-sign partner is the original polygon side pairing.
These are the domain and pairing interfaces for the remaining contraction
bridge. They do not identify cyclic successor with first return: the ordered
primal-tree contraction and dual-face traversal identities remain separate.
-/

namespace SystolicGrowth

noncomputable section

/-- Place a retained endpoint occurrence at its original polygon face and
side, before either tree contraction. -/
def canonicalProjectivePostConeSurvivingDart_embedding
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d : CanonicalProjectivePostConeSurvivingDart hp hp2) :
    CanonicalProjectivePolygonDart p :=
  ((canonicalProjectivePostConeSurvivingDartFace hp hp2 d).state,
    canonicalProjectivePostConeSurvivingDartSide hp hp2 d)

@[simp] theorem canonicalProjectivePostConeSurvivingDart_embedding_source
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : CanonicalProjectivePostConeFinalGenerator hp hp2) :
    canonicalProjectivePostConeSurvivingDart_embedding hp hp2 (Sum.inl z) =
      projectivePolygonPostConeEdgeSourceDart z.1 :=
  rfl

@[simp] theorem canonicalProjectivePostConeSurvivingDart_embedding_target
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : CanonicalProjectivePostConeFinalGenerator hp hp2) :
    canonicalProjectivePostConeSurvivingDart_embedding hp hp2 (Sum.inr z) =
      projectivePolygonPostConeEdgeTargetDart z.1 :=
  rfl

/-- Distinct retained endpoint occurrences occupy distinct original darts. -/
theorem canonicalProjectivePostConeSurvivingDart_embedding_injective
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    Function.Injective (canonicalProjectivePostConeSurvivingDart_embedding hp hp2) := by
  intro d e h
  apply canonicalProjectivePostConeSurvivingDart_face_side_injective hp hp2
  · apply ProjectivePolygonPostConeFace.stateEquiv.injective
    exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

/-- Interchanging the two endpoint constructors is the actual physical side
pairing on the original polygon, including cone-side occurrences. -/
theorem canonicalProjectivePostConeSurvivingDart_embedding_swap
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d : CanonicalProjectivePostConeSurvivingDart hp hp2) :
    canonicalProjectivePostConeSurvivingDart_embedding hp hp2 (Sum.swap d) =
      (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner
        (canonicalProjectivePostConeSurvivingDart_embedding hp hp2 d).1
        (canonicalProjectivePostConeSurvivingDart_embedding hp hp2 d).2 := by
  cases d with
  | inl z => exact projectivePolygonPostConeEdgeTargetDart_eq_partner z.1
  | inr z =>
      change projectivePolygonPostConeEdgeSourceDart z.1 =
        (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner
          (projectivePolygonPostConeEdgeTargetDart z.1).1
          (projectivePolygonPostConeEdgeTargetDart z.1).2
      rw [projectivePolygonPostConeEdgeTargetDart_eq_partner]
      exact ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner_involutive
          (projectivePolygonPostConeEdgeSource z.1).state
          (projectivePolygonPostConeEdgeSide z.1)).symm

/-- Decode a literal root-contour position as an original polygon dart. -/
def canonicalProjectivePostConeRawRootContourPosition_physicalEmbedding
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (i : Fin (canonicalProjectivePostConeRawRootContour hp hp2).length) :
    CanonicalProjectivePolygonDart p :=
  canonicalProjectivePostConeSurvivingDart_embedding hp hp2
    (canonicalProjectivePostConeRawRootContourPosition_endpointEquiv hp hp2 i)

/-- The physical decoder does not identify distinct literal positions. -/
theorem canonicalProjectivePostConeRawRootContourPosition_physicalEmbedding_injective
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    Function.Injective
      (canonicalProjectivePostConeRawRootContourPosition_physicalEmbedding hp hp2) :=
  (canonicalProjectivePostConeSurvivingDart_embedding_injective hp hp2).comp
    (canonicalProjectivePostConeRawRootContourPosition_endpointEquiv hp hp2).injective

/-- Literal positions cover precisely the original darts of the retained
endpoint occurrences; no extra dart is introduced by recursive splicing. -/
theorem canonicalProjectivePostConeRawRootContourPosition_physicalEmbedding_range
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    Set.range (canonicalProjectivePostConeRawRootContourPosition_physicalEmbedding hp hp2) =
      Set.range (canonicalProjectivePostConeSurvivingDart_embedding hp hp2) := by
  ext d
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨canonicalProjectivePostConeRawRootContourPosition_endpointEquiv hp hp2 i, rfl⟩
  · rintro ⟨x, rfl⟩
    refine ⟨(canonicalProjectivePostConeRawRootContourPosition_endpointEquiv hp hp2).symm x,
      ?_⟩
    simp [canonicalProjectivePostConeRawRootContourPosition_physicalEmbedding]

/-- Opposite-sign partners decode to the actual paired original polygon
darts. This does not assert the still-unproved successor/first-return law. -/
theorem canonicalProjectivePostConeRawRootContourPosition_physicalEmbedding_partner
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (i : Fin (canonicalProjectivePostConeRawRootContour hp hp2).length) :
    canonicalProjectivePostConeRawRootContourPosition_physicalEmbedding hp hp2
        (canonicalProjectivePostConeRawRootContour_partner hp hp2 i) =
      (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner
        (canonicalProjectivePostConeRawRootContourPosition_physicalEmbedding hp hp2 i).1
        (canonicalProjectivePostConeRawRootContourPosition_physicalEmbedding hp hp2 i).2 := by
  have h := canonicalProjectivePostConeRawRootContour_partner_endpoint hp hp2 i
  change canonicalProjectivePostConeRawRootContourPosition_endpointEquiv hp hp2
      (canonicalProjectivePostConeRawRootContour_partner hp hp2 i) =
    Sum.swap (canonicalProjectivePostConeRawRootContourPosition_endpointEquiv hp hp2 i) at h
  unfold canonicalProjectivePostConeRawRootContourPosition_physicalEmbedding
  rw [h, canonicalProjectivePostConeSurvivingDart_embedding_swap]

#print axioms canonicalProjectivePostConeSurvivingDart_embedding_injective
#print axioms canonicalProjectivePostConeSurvivingDart_embedding_swap
#print axioms canonicalProjectivePostConeRawRootContourPosition_physicalEmbedding_injective
#print axioms canonicalProjectivePostConeRawRootContourPosition_physicalEmbedding_range
#print axioms canonicalProjectivePostConeRawRootContourPosition_physicalEmbedding_partner

end

end SystolicGrowth
