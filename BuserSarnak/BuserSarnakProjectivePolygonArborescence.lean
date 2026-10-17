module

public import BuserSarnak.BuserSarnakProjectivePolygonConnectivity
public import Vendored.ProCGroups.ReidemeisterSchreier.Quiver

@[expose] public section

/-!
# An edge-labelled projective polygon arborescence

The finite projective polygon faces form a directed multigraph: an arrow
retains the exact polygon-side label used by its pairing.  The proved face
reachability supplies a rooted-connected quiver, so Mathlib's geodesic
construction selects an arborescence without making a tree choice an input
assumption.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete
open ReidemeisterSchreier.Discrete.Presentations

/-- A polygon face, represented by its finite projective quotient state.  The
wrapper retains the section data as part of the vertex type, allowing arrows
to carry their concrete polygon-side labels. -/
structure ProjectivePolygonFace
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p) where
  state : BuserSarnakProjectiveReductionRange p

namespace ProjectivePolygonFace

noncomputable local instance rangeFintype
    (p : ℕ) [NeZero p] : Fintype (BuserSarnakProjectiveReductionRange p) :=
  Fintype.ofFinite _

/-- Forgetting the wrapper identifies polygon faces with their finite quotient
states. -/
noncomputable def stateEquiv
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p) :
    ProjectivePolygonFace S ≃ BuserSarnakProjectiveReductionRange p where
  toFun := ProjectivePolygonFace.state
  invFun := fun q => ⟨q⟩
  left_inv q := by cases q; rfl
  right_inv q := rfl

noncomputable local instance faceFintype
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p) :
    Fintype (ProjectivePolygonFace S) :=
  Fintype.ofEquiv _ (stateEquiv S).symm

noncomputable local instance faceDecidableEq
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p) :
    DecidableEq (ProjectivePolygonFace S) := Classical.decEq _

/-- Arrows record the exact directed polygon side whose pairing carries one
face to the next; parallel sides are therefore not collapsed. -/
instance {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p) :
    Quiver (ProjectivePolygonFace S) where
  Hom q r := {s : ProjectivePolygonSide //
    (S.polygonSidePartner q.state s).1 = r.state}

/-- The face based at the identity quotient state. -/
def root {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p) :
    ProjectivePolygonFace S := ⟨1⟩

/-- A proof-level face-reachability path gives a nonempty quiver path with the
same endpoints.  `Nonempty` permits elimination from the propositional
transitive closure while preserving the labelled arrows. -/
theorem nonemptyPathOfReflTransGen
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    {q r : BuserSarnakProjectiveReductionRange p} :
    Relation.ReflTransGen (projectivePolygonFaceStep S) q r →
      Nonempty (Quiver.Path (⟨q⟩ : ProjectivePolygonFace S) ⟨r⟩) := by
  intro h
  induction h with
  | refl => exact ⟨.nil⟩
  | tail hpath hstep ih =>
      rcases hstep with ⟨s, hs⟩
      rcases ih with ⟨path⟩
      exact ⟨path.cons ⟨s, hs⟩⟩

/-- The labelled polygon quiver is rooted-connected at the identity face. -/
theorem rootedConnected
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p) :
    Quiver.RootedConnected (root S) where
  nonempty_path q :=
    nonemptyPathOfReflTransGen S (by
      simpa [root] using projectivePolygonFaceStep_reaches_all S q.state)

/-- Use the proved rooted connectivity as the typeclass input for the
geodesic arborescence construction. -/
noncomputable instance rootedConnectedInstance
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p) :
    Quiver.RootedConnected (root S) := rootedConnected S

/-- A deterministic, edge-labelled spanning arborescence of polygon faces. -/
noncomputable def spanningTree
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p) :
    WideSubquiver (ProjectivePolygonFace S) :=
  Quiver.geodesicSubtree (root S)

/-- The selected polygon spanning subquiver is an arborescence. -/
noncomputable instance spanningTreeArborescence
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p) :
    Quiver.Arborescence (spanningTree S) := by
  change Quiver.Arborescence (Quiver.geodesicSubtree (root S))
  infer_instance

noncomputable local instance spanningTreeFintype
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p) :
    Fintype (spanningTree S) := by
  change Fintype (ProjectivePolygonFace S)
  infer_instance

noncomputable local instance spanningTreeDecidableEq
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p) :
    DecidableEq (spanningTree S) := by
  change DecidableEq (ProjectivePolygonFace S)
  infer_instance

/-- Each selected arborescence arrow is uniquely identified by its non-root
target face.  This is the cardinality bridge for the remaining `h - 1`
polygon eliminations. -/
noncomputable def totalEquivNonRoot
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p) :
    Quiver.Total (spanningTree S) ≃
      {q : spanningTree S // q ≠ Quiver.root (spanningTree S)} :=
  ReidemeisterSchreier.Quiver.Arborescence.totalEquivNonRoot (spanningTree S)

/-- The spanning tree has one labelled arrow for every non-root face. -/
theorem natCard_spanningTree_total
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p) :
    Nat.card (Quiver.Total (spanningTree S)) =
      Nat.card (BuserSarnakProjectiveReductionRange p) - 1 := by
  rw [Nat.card_congr (totalEquivNonRoot S)]
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype_compl]
  rw [Fintype.card_subtype_eq]
  rw [← Nat.card_eq_fintype_card]
  rw [Nat.card_congr (stateEquiv S).symm]
  change Nat.card (ProjectivePolygonFace S) - 1 =
    Nat.card (ProjectivePolygonFace S) - 1
  rfl

/-- At an admissible projective level, the arborescence contains exactly one
arrow for each of the `halfImageIndex - 1` non-root faces. -/
theorem natCard_spanningTree_total_eq_halfImageIndex_sub_one
    {p : ℕ} [NeZero p]
    (data : BuserSarnakCorrectionData p)
    (hp : p.Prime) (hp2 : p ≠ 2)
    (S : BuserSarnakProjectiveQuotientSectionData p) :
    Nat.card (Quiver.Total (spanningTree S)) = data.halfImageIndex - 1 := by
  rw [natCard_spanningTree_total,
    natCard_buserSarnakProjectiveReductionRange hp hp2 data]

end ProjectivePolygonFace

end

end SystolicGrowth
