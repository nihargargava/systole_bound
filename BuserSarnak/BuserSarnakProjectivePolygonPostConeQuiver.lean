module

public import BuserSarnak.BuserSarnakProjectivePolygonPostConeLabels
public import Vendored.ProCGroups.ReidemeisterSchreier.Quiver

@[expose] public section

/-!
# The physical post-cone polygon quiver

Each generator surviving the cone Tietze stage determines one physical polygon
edge.  This quiver keeps that generator as its arrow label.  Its
symmetrification is the correct target for the remaining dual-tree argument:
any arborescence in it automatically selects distinct retained generators.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete
open ReidemeisterSchreier.Discrete.Presentations

noncomputable local instance buserSarnakProjectivePolygonPostConeQuiverRangeFintype
    (p : ℕ) [NeZero p] : Fintype (BuserSarnakProjectiveReductionRange p) :=
  Fintype.ofFinite _

/-- A polygon face in the post-cone physical-edge quiver.  This wrapper keeps
its quiver distinct from the earlier directed-side-occurrence quiver. -/
structure ProjectivePolygonPostConeFace
    (p : ℕ) [NeZero p] where
  state : BuserSarnakProjectiveReductionRange p

namespace ProjectivePolygonPostConeFace

/-- Forgetting the wrapper identifies physical-quiver faces with quotient
states. -/
noncomputable def stateEquiv
    {p : ℕ} [NeZero p] :
    ProjectivePolygonPostConeFace p ≃ BuserSarnakProjectiveReductionRange p where
  toFun := ProjectivePolygonPostConeFace.state
  invFun := fun q => ⟨q⟩
  left_inv q := by cases q; rfl
  right_inv q := rfl

end ProjectivePolygonPostConeFace

noncomputable local instance projectivePolygonPostConeFaceFintype
    (p : ℕ) [NeZero p] : Fintype (ProjectivePolygonPostConeFace p) :=
  Fintype.ofEquiv _ ProjectivePolygonPostConeFace.stateEquiv.symm

noncomputable local instance projectivePolygonPostConeFaceDecidableEq
    (p : ℕ) [NeZero p] : DecidableEq (ProjectivePolygonPostConeFace p) :=
  Classical.decEq _

/-- Choose the positively oriented polygon side associated with a projective
octagon generator. -/
def ProjectiveOctagonGenerator.positivePolygonSide :
    ProjectiveOctagonGenerator → ProjectivePolygonSide
  | .a => .a
  | .c => .c
  | .e1 => .e1
  | .e2 => .e2
  | .e3 => .e3
  | .e4 => .e4

/-- The chosen positive side has the original projective generator label. -/
@[simp] theorem ProjectiveOctagonGenerator.positivePolygonSide_generator
    (x : ProjectiveOctagonGenerator) : x.positivePolygonSide.generator = x := by
  cases x <;> rfl

/-- The positive polygon side recovered from a retained post-cone generator. -/
def projectivePolygonPostConeEdgeSide
    {p : ℕ} [NeZero p]
    (z : CanonicalProjectiveConeKeptSymbol p) : ProjectivePolygonSide :=
  z.1.1.2.positivePolygonSide

/-- The face from which the physical edge labelled by `z` is traversed. -/
def projectivePolygonPostConeEdgeSource
    {p : ℕ} [NeZero p]
    (z : CanonicalProjectiveConeKeptSymbol p) : ProjectivePolygonPostConeFace p :=
  ⟨(canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideBase z.1.1.1
    (projectivePolygonPostConeEdgeSide z)⟩

/-- The face at the other end of the physical edge labelled by `z`. -/
def projectivePolygonPostConeEdgeTarget
    {p : ℕ} [NeZero p]
    (z : CanonicalProjectiveConeKeptSymbol p) : ProjectivePolygonPostConeFace p :=
  ⟨((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner
      (projectivePolygonPostConeEdgeSource z).state
      (projectivePolygonPostConeEdgeSide z)).1⟩

/-- A positive side reconstructed from its starting state has the expected raw
Schreier symbol. -/
theorem polygonSideRawSymbol_polygonSideBase_positive
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p)
    (x : ProjectiveOctagonGenerator) :
    S.polygonSideRawSymbol (S.polygonSideBase q x.positivePolygonSide)
      x.positivePolygonSide = (q, x) := by
  cases x
  · rfl
  · change
      (S.polygonSideStart (S.polygonSideBase q .c) .c,
        ProjectiveOctagonGenerator.c) = (q, ProjectiveOctagonGenerator.c)
    rw [S.polygonSideStart_base q .c]
  · change
      (S.polygonSideStart (S.polygonSideBase q .e1) .e1,
        ProjectiveOctagonGenerator.e1) = (q, ProjectiveOctagonGenerator.e1)
    rw [S.polygonSideStart_base q .e1]
  · change
      (S.polygonSideStart (S.polygonSideBase q .e2) .e2,
        ProjectiveOctagonGenerator.e2) = (q, ProjectiveOctagonGenerator.e2)
    rw [S.polygonSideStart_base q .e2]
  · change
      (S.polygonSideStart (S.polygonSideBase q .e3) .e3,
        ProjectiveOctagonGenerator.e3) = (q, ProjectiveOctagonGenerator.e3)
    rw [S.polygonSideStart_base q .e3]
  · change
      (S.polygonSideStart (S.polygonSideBase q .e4) .e4,
        ProjectiveOctagonGenerator.e4) = (q, ProjectiveOctagonGenerator.e4)
    rw [S.polygonSideStart_base q .e4]

/-- The positive side attached to a retained label recovers its underlying raw
Schreier symbol at the physical edge source. -/
theorem projectivePolygonPostConeEdgeSource_rawSymbol
    {p : ℕ} [NeZero p]
    (z : CanonicalProjectiveConeKeptSymbol p) :
    (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol
      (projectivePolygonPostConeEdgeSource z).state
      (projectivePolygonPostConeEdgeSide z) = z.1.1 := by
  simpa [projectivePolygonPostConeEdgeSource,
    projectivePolygonPostConeEdgeSide] using
    polygonSideRawSymbol_polygonSideBase_positive
      (canonicalBuserSarnakProjectiveQuotientSectionData p) z.1.1.1 z.1.1.2

/-- Forgetting the physical-edge wrapper gives the corresponding face of the
original directed polygon-side quiver. -/
def projectivePolygonPostConeFaceToPolygonFace
    {p : ℕ} [NeZero p]
    (q : ProjectivePolygonPostConeFace p) :
    ProjectivePolygonFace (canonicalBuserSarnakProjectiveQuotientSectionData p) :=
  ⟨q.state⟩

/-- An arrow records its unique retained generator label as well as the
endpoints determined by that label. -/
instance {p : ℕ} [NeZero p] : Quiver (ProjectivePolygonPostConeFace p) where
  Hom q r := {z : CanonicalProjectiveConeKeptSymbol p //
    projectivePolygonPostConeEdgeSource z = q ∧
      projectivePolygonPostConeEdgeTarget z = r}

/-- Each physical post-cone edge is an actual directed polygon-side pairing;
the physical quiver is therefore a labelled subquiver of the full face quiver.
-/
def projectivePolygonPostConeEdgeToPolygonSideArrow
    {p : ℕ} [NeZero p]
    {q r : ProjectivePolygonPostConeFace p} (e : q ⟶ r) :
    projectivePolygonPostConeFaceToPolygonFace q ⟶
      projectivePolygonPostConeFaceToPolygonFace r :=
  ⟨projectivePolygonPostConeEdgeSide e.1, by
    change ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner
      q.state (projectivePolygonPostConeEdgeSide e.1)).1 = r.state
    have hsource := congrArg ProjectivePolygonPostConeFace.state e.2.1
    have htarget := congrArg ProjectivePolygonPostConeFace.state e.2.2
    rw [← hsource, ← htarget]
    rfl⟩

/-- The identity quotient state, viewed as the root of the symmetrized
physical post-cone quiver. -/
def projectivePolygonPostConeRoot
    (p : ℕ) [NeZero p] :
    Quiver.Symmetrify (ProjectivePolygonPostConeFace p) :=
  ⟨1⟩

/-- Once survivor-edge connectivity is proved, Mathlib's geodesic construction
provides the canonical physical dual spanning tree. -/
noncomputable def projectivePolygonPostConeSpanningTree
    (p : ℕ) [NeZero p]
    [Quiver.RootedConnected (projectivePolygonPostConeRoot p)] :
    WideSubquiver (Quiver.Symmetrify (ProjectivePolygonPostConeFace p)) :=
  Quiver.geodesicSubtree (projectivePolygonPostConeRoot p)

/-- The conditional geodesic physical tree is an arborescence by construction.
The missing mathematical work is precisely its rooted-connectivity instance. -/
noncomputable instance projectivePolygonPostConeSpanningTreeArborescence
    (p : ℕ) [NeZero p]
    [Quiver.RootedConnected (projectivePolygonPostConeRoot p)] :
    Quiver.Arborescence (projectivePolygonPostConeSpanningTree p) := by
  change Quiver.Arborescence
    (Quiver.geodesicSubtree (projectivePolygonPostConeRoot p))
  infer_instance

noncomputable local instance physicalTreeFintype
    {p : ℕ} [NeZero p]
    (T : WideSubquiver (Quiver.Symmetrify (ProjectivePolygonPostConeFace p))) :
    Fintype T := by
  change Fintype (ProjectivePolygonPostConeFace p)
  infer_instance

noncomputable local instance physicalTreeDecidableEq
    {p : ℕ} [NeZero p]
    (T : WideSubquiver (Quiver.Symmetrify (ProjectivePolygonPostConeFace p))) :
    DecidableEq T := by
  change DecidableEq (ProjectivePolygonPostConeFace p)
  infer_instance

/-- All arrows of the physical post-cone quiver are in bijection with retained
generators. -/
noncomputable def projectivePolygonPostConeTotalEquivKept
    (p : ℕ) [NeZero p] :
    Quiver.Total (ProjectivePolygonPostConeFace p) ≃
      CanonicalProjectiveConeKeptSymbol p where
  toFun := fun e => e.hom.1
  invFun := fun z =>
    ⟨projectivePolygonPostConeEdgeSource z,
      projectivePolygonPostConeEdgeTarget z, ⟨z, rfl, rfl⟩⟩
  left_inv := by
    rintro ⟨q, r, ⟨z, hsource, htarget⟩⟩
    dsimp
    subst q
    subst r
    rfl
  right_inv := by
    intro z
    rfl

/-- Label an arborescence arrow in the symmetrized physical quiver by its
underlying retained generator. -/
noncomputable def projectivePolygonPostConeTreeArrowLabel
    {p : ℕ} [NeZero p]
    (T : WideSubquiver (Quiver.Symmetrify (ProjectivePolygonPostConeFace p)))
    [Quiver.Arborescence T] :
    Quiver.Total T → CanonicalProjectiveConeKeptSymbol p :=
  fun e => projectivePolygonPostConeTotalEquivKept p
    ((ReidemeisterSchreier.Quiver.coveredArrowEquivTotal T).symm e).1

/-- Distinct arrows selected by a physical-edge arborescence have distinct
post-cone generator labels. -/
theorem projectivePolygonPostConeTreeArrowLabel_injective
    {p : ℕ} [NeZero p]
    (T : WideSubquiver (Quiver.Symmetrify (ProjectivePolygonPostConeFace p)))
    [Quiver.Arborescence T] :
    Function.Injective (projectivePolygonPostConeTreeArrowLabel T) := by
  intro e f hef
  apply (ReidemeisterSchreier.Quiver.coveredArrowEquivTotal T).symm.injective
  apply Subtype.ext
  apply (projectivePolygonPostConeTotalEquivKept p).injective
  exact hef

/-- Any arborescence in the symmetrized physical quiver has one arrow per
non-root finite quotient state. -/
theorem natCard_projectivePolygonPostConeTree_total
    {p : ℕ} [NeZero p]
    (T : WideSubquiver (Quiver.Symmetrify (ProjectivePolygonPostConeFace p)))
    [Quiver.Arborescence T] :
    Nat.card (Quiver.Total T) = Nat.card (BuserSarnakProjectiveReductionRange p) - 1 := by
  rw [Nat.card_congr (ReidemeisterSchreier.Quiver.Arborescence.totalEquivNonRoot T)]
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype_compl]
  rw [Fintype.card_subtype_eq]
  rw [← Nat.card_eq_fintype_card]
  rw [Nat.card_congr ProjectivePolygonPostConeFace.stateEquiv.symm]
  change Nat.card (ProjectivePolygonPostConeFace p) - 1 =
    Nat.card (ProjectivePolygonPostConeFace p) - 1
  rfl

/-- At an admissible projective level, a physical post-cone arborescence has
exactly `halfImageIndex - 1` distinctly labelled arrows. -/
theorem natCard_projectivePolygonPostConeTree_total_eq_halfImageIndex_sub_one
    {p : ℕ} [NeZero p]
    (data : BuserSarnakCorrectionData p)
    (hp : p.Prime) (hp2 : p ≠ 2)
    (T : WideSubquiver (Quiver.Symmetrify (ProjectivePolygonPostConeFace p)))
    [Quiver.Arborescence T] :
    Nat.card (Quiver.Total T) = data.halfImageIndex - 1 := by
  rw [natCard_projectivePolygonPostConeTree_total,
    natCard_buserSarnakProjectiveReductionRange hp hp2 data]

end

end SystolicGrowth
