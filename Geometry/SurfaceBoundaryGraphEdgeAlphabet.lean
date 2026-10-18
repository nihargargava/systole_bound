module

public import Geometry.SurfaceBoundaryGraphPaths
public import Mathlib.Data.Fintype.Card

@[expose] public section

/-!
# The actual non-tree edge alphabet

Choose the lower cyclic index in each original side pair. The selected
physical spanning-tree edges inject into this alphabet, including when the
graph has parallel sides. Its complement is the alphabet needed for the
open free-fundamental-group construction; no free-basis theorem is assumed.
-/

open Set UpperHalfPlane
open scoped Pointwise UpperHalfPlane

namespace SystolicGrowth.DirichletBoundarySegments

noncomputable section

variable {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}

/-- Exactly one original cyclic orientation from each physical side pair. -/
abbrev IntrinsicBoundaryPhysicalEdge (B : DirichletBoundarySegments X o) :=
  {i : Fin B.intrinsicBoundaryRadialCuts.card // i < B.intrinsicCyclicPairing i}

instance (B : DirichletBoundarySegments X o) : Fintype B.IntrinsicBoundaryPhysicalEdge :=
  Subtype.fintype (fun i => i < B.intrinsicCyclicPairing i)

/-- The physical edge represented by an original oriented side. -/
def intrinsicBoundaryPhysicalEdge (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) : B.IntrinsicBoundaryPhysicalEdge := by
  classical
  exact if h : i < B.intrinsicCyclicPairing i then ⟨i, h⟩ else
    ⟨B.intrinsicCyclicPairing i, by
      rw [B.intrinsicCyclicPairing_involutive]
      exact lt_of_le_of_ne (le_of_not_gt h) (B.intrinsicCyclicPairing_ne_self i)⟩

/-- Choosing the opposite original orientation does not change its physical edge. -/
theorem intrinsicBoundaryPhysicalEdge_pair (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryPhysicalEdge (B.intrinsicCyclicPairing i) =
      B.intrinsicBoundaryPhysicalEdge i := by
  classical
  by_cases h : i < B.intrinsicCyclicPairing i
  · have hpair : ¬B.intrinsicCyclicPairing i <
        B.intrinsicCyclicPairing (B.intrinsicCyclicPairing i) := by
      rw [B.intrinsicCyclicPairing_involutive]
      exact not_lt_of_ge h.le
    apply Subtype.ext
    simp only [intrinsicBoundaryPhysicalEdge, dif_pos h, dif_neg hpair]
    exact B.intrinsicCyclicPairing_involutive i
  · have hpair : B.intrinsicCyclicPairing i <
        B.intrinsicCyclicPairing (B.intrinsicCyclicPairing i) := by
      rw [B.intrinsicCyclicPairing_involutive]
      exact lt_of_le_of_ne (le_of_not_gt h) (B.intrinsicCyclicPairing_ne_self i)
    simp only [intrinsicBoundaryPhysicalEdge, dif_neg h, dif_pos hpair]

/-- Forgetting orientation preserves the actual unordered endpoint classes. -/
theorem intrinsicBoundaryPhysicalEdge_endpoints (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    s(B.intrinsicBoundaryGraphSideStart (B.intrinsicBoundaryPhysicalEdge i).val,
      B.intrinsicBoundaryGraphSideEnd (B.intrinsicBoundaryPhysicalEdge i).val) =
        s(B.intrinsicBoundaryGraphSideStart i, B.intrinsicBoundaryGraphSideEnd i) := by
  classical
  by_cases h : i < B.intrinsicCyclicPairing i
  · simp only [intrinsicBoundaryPhysicalEdge, dif_pos h]
  · simp only [intrinsicBoundaryPhysicalEdge, dif_neg h]
    rw [(B.intrinsicBoundaryGraphSide_pair_endpoints i).1,
      (B.intrinsicBoundaryGraphSide_pair_endpoints i).2, Sym2.eq_swap]

/-- The actual selected tree edge, represented by its original physical side. -/
def intrinsicBoundaryTreePhysicalEdge (B : DirichletBoundarySegments X o)
    (e : B.intrinsicBoundarySpanningTree.edgeSet) : B.IntrinsicBoundaryPhysicalEdge :=
  B.intrinsicBoundaryPhysicalEdge (B.intrinsicBoundaryTreeEdgeSide e)

theorem intrinsicBoundaryTreePhysicalEdge_injective (B : DirichletBoundarySegments X o) :
    Function.Injective B.intrinsicBoundaryTreePhysicalEdge := by
  intro e f hef
  apply Subtype.ext
  have h := congrArg (fun a : B.IntrinsicBoundaryPhysicalEdge =>
    s(B.intrinsicBoundaryGraphSideStart a.val, B.intrinsicBoundaryGraphSideEnd a.val)) hef
  change s(B.intrinsicBoundaryGraphSideStart
      (B.intrinsicBoundaryPhysicalEdge (B.intrinsicBoundaryTreeEdgeSide e)).val,
        B.intrinsicBoundaryGraphSideEnd
          (B.intrinsicBoundaryPhysicalEdge (B.intrinsicBoundaryTreeEdgeSide e)).val) =
    s(B.intrinsicBoundaryGraphSideStart
      (B.intrinsicBoundaryPhysicalEdge (B.intrinsicBoundaryTreeEdgeSide f)).val,
        B.intrinsicBoundaryGraphSideEnd
          (B.intrinsicBoundaryPhysicalEdge (B.intrinsicBoundaryTreeEdgeSide f)).val) at h
  rw [B.intrinsicBoundaryPhysicalEdge_endpoints,
    B.intrinsicBoundaryPhysicalEdge_endpoints] at h
  exact (B.intrinsicBoundaryTreeEdgeSide_endpoints e).symm.trans
    (h.trans (B.intrinsicBoundaryTreeEdgeSide_endpoints f))

instance (B : DirichletBoundarySegments X o) :
    Fintype B.intrinsicBoundarySpanningTree.edgeSet := Fintype.ofFinite _

/-- The genuine physical sides not chosen for the actual spanning tree. -/
abbrev IntrinsicBoundaryNonTreeEdge (B : DirichletBoundarySegments X o) :=
  {a : B.IntrinsicBoundaryPhysicalEdge // a ∉ range B.intrinsicBoundaryTreePhysicalEdge}

instance (B : DirichletBoundarySegments X o) : Fintype B.IntrinsicBoundaryNonTreeEdge :=
  Fintype.ofFinite _

/-- The non-tree alphabet and the selected tree partition the physical sides. -/
theorem intrinsicBoundaryNonTreeEdge_card_add_tree (B : DirichletBoundarySegments X o) :
    Fintype.card B.IntrinsicBoundaryNonTreeEdge +
      Fintype.card B.intrinsicBoundarySpanningTree.edgeSet =
        Fintype.card B.IntrinsicBoundaryPhysicalEdge := by
  classical
  have hsize : Fintype.card
      {a : B.IntrinsicBoundaryPhysicalEdge // a ∈ range B.intrinsicBoundaryTreePhysicalEdge} =
        Fintype.card B.intrinsicBoundarySpanningTree.edgeSet :=
    (Fintype.card_congr (Equiv.ofInjective B.intrinsicBoundaryTreePhysicalEdge
      B.intrinsicBoundaryTreePhysicalEdge_injective)).symm
  have hsum := Fintype.card_subtype_compl
    (fun a : B.IntrinsicBoundaryPhysicalEdge => a ∈ range B.intrinsicBoundaryTreePhysicalEdge)
  change Fintype.card B.IntrinsicBoundaryNonTreeEdge = _ at hsum
  have hle : Fintype.card B.intrinsicBoundarySpanningTree.edgeSet ≤
      Fintype.card B.IntrinsicBoundaryPhysicalEdge :=
    Fintype.card_le_of_injective B.intrinsicBoundaryTreePhysicalEdge
      B.intrinsicBoundaryTreePhysicalEdge_injective
  rw [hsize] at hsum
  rw [hsum, Nat.sub_add_cancel hle]

/-- The actual edge alphabet has the expected graph rank before any claim
that its generators form a free fundamental-group basis. -/
theorem intrinsicBoundaryNonTreeEdge_card_add_vertices (B : DirichletBoundarySegments X o) :
    Fintype.card B.IntrinsicBoundaryNonTreeEdge +
      Fintype.card B.IntrinsicBoundaryGraphVertex =
        Fintype.card B.IntrinsicBoundaryPhysicalEdge + 1 := by
  classical
  have htree := B.intrinsicBoundarySpanningTree_isTree.card_edgeFinset
  have hpartition := B.intrinsicBoundaryNonTreeEdge_card_add_tree
  rw [SimpleGraph.edgeFinset_card] at htree
  omega

end

end SystolicGrowth.DirichletBoundarySegments
