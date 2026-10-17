module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SurfaceBoundaryGraphTreeOrbit

@[expose] public section

/-!
# The actual tree involution as a product of physical side transpositions

This is the concrete permutation-algebra adapter for the selected spanning
tree.  Each abstract tree edge has one chosen original side and pairs that
side with its actual opposite orientation.  The proof identifies the
simultaneous involution already used by `SurfaceBoundaryGraphTreeOrbit` with
the ordered product of these literal swaps.  It proves no orbit statement.
-/

open Set UpperHalfPlane
open scoped Pointwise UpperHalfPlane Classical

namespace SystolicGrowth.DirichletBoundarySegments

noncomputable section

variable {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}

/-- The actual transposition contributed by one selected physical tree edge. -/
def intrinsicBoundaryTreeEdgeSwap (B : DirichletBoundarySegments X o)
    (e : B.intrinsicBoundarySpanningTree.edgeSet) :
    Equiv.Perm (Fin B.intrinsicBoundaryRadialCuts.card) :=
  Equiv.swap (B.intrinsicBoundaryTreeEdgeSide e)
    (B.intrinsicCyclicPairing (B.intrinsicBoundaryTreeEdgeSide e))

def intrinsicBoundaryTreeEdgeContains (B : DirichletBoundarySegments X o)
    (e : B.intrinsicBoundarySpanningTree.edgeSet)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) : Prop :=
  i = B.intrinsicBoundaryTreeEdgeSide e ∨
    i = B.intrinsicCyclicPairing (B.intrinsicBoundaryTreeEdgeSide e)

private theorem intrinsicBoundaryPhysicalEdge_eq_pair_or_self
    (B : DirichletBoundarySegments X o)
    (i j : Fin B.intrinsicBoundaryRadialCuts.card)
    (h : B.intrinsicBoundaryPhysicalEdge i = B.intrinsicBoundaryPhysicalEdge j) :
    i = j ∨ i = B.intrinsicCyclicPairing j := by
  classical
  have hv := congrArg (fun e : B.IntrinsicBoundaryPhysicalEdge => e.val) h
  by_cases hi : i < B.intrinsicCyclicPairing i <;>
    by_cases hj : j < B.intrinsicCyclicPairing j
  · simp only [intrinsicBoundaryPhysicalEdge, dif_pos hi, dif_pos hj] at hv
    exact Or.inl hv
  · simp only [intrinsicBoundaryPhysicalEdge, dif_pos hi, dif_neg hj] at hv
    exact Or.inr hv
  · simp only [intrinsicBoundaryPhysicalEdge, dif_neg hi, dif_pos hj] at hv
    right
    calc
      i = B.intrinsicCyclicPairing (B.intrinsicCyclicPairing i) :=
        (B.intrinsicCyclicPairing_involutive i).symm
      _ = B.intrinsicCyclicPairing j := congrArg B.intrinsicCyclicPairing hv
  · simp only [intrinsicBoundaryPhysicalEdge, dif_neg hi, dif_neg hj] at hv
    exact Or.inl (by
      calc
        i = B.intrinsicCyclicPairing (B.intrinsicCyclicPairing i) :=
          (B.intrinsicCyclicPairing_involutive i).symm
        _ = B.intrinsicCyclicPairing (B.intrinsicCyclicPairing j) :=
          congrArg B.intrinsicCyclicPairing hv
        _ = j := B.intrinsicCyclicPairing_involutive j)

private theorem intrinsicBoundaryTreeEdgeContains_iff_physicalEdge
    (B : DirichletBoundarySegments X o)
    (e : B.intrinsicBoundarySpanningTree.edgeSet)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryTreeEdgeContains e i ↔
      B.intrinsicBoundaryPhysicalEdge i = B.intrinsicBoundaryTreePhysicalEdge e := by
  constructor
  · rintro (rfl | rfl)
    · rfl
    · exact B.intrinsicBoundaryPhysicalEdge_pair _
  · intro hi
    have hphysical : B.intrinsicBoundaryPhysicalEdge i =
        B.intrinsicBoundaryPhysicalEdge (B.intrinsicBoundaryTreeEdgeSide e) := hi
    rcases intrinsicBoundaryPhysicalEdge_eq_pair_or_self B i
        (B.intrinsicBoundaryTreeEdgeSide e) hphysical with h | h
    · exact Or.inl h
    · exact Or.inr h

private theorem intrinsicBoundaryTreeEdgeContains_unique
    (B : DirichletBoundarySegments X o)
    {e f : B.intrinsicBoundarySpanningTree.edgeSet}
    {i : Fin B.intrinsicBoundaryRadialCuts.card}
    (he : B.intrinsicBoundaryTreeEdgeContains e i)
    (hf : B.intrinsicBoundaryTreeEdgeContains f i) : e = f := by
  rcases he with he | he <;> rcases hf with hf | hf
  · apply B.intrinsicBoundaryTreeEdgeSide_injective
    exact he.symm.trans hf
  · exfalso
    exact B.intrinsicBoundaryTreeEdgeSide_ne_pair e f (he.symm.trans hf)
  · exfalso
    exact B.intrinsicBoundaryTreeEdgeSide_ne_pair f e (hf.symm.trans he)
  · apply B.intrinsicBoundaryTreeEdgeSide_injective
    apply Function.Involutive.injective B.intrinsicCyclicPairing_involutive
    exact he.symm.trans hf

private theorem intrinsicBoundaryTreeEdgeContains_pair_iff
    (B : DirichletBoundarySegments X o)
    (e : B.intrinsicBoundarySpanningTree.edgeSet)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryTreeEdgeContains e (B.intrinsicCyclicPairing i) ↔
      B.intrinsicBoundaryTreeEdgeContains e i := by
  unfold intrinsicBoundaryTreeEdgeContains
  constructor
  · rintro (h | h)
    · right
      calc
        i = B.intrinsicCyclicPairing (B.intrinsicCyclicPairing i) :=
          (B.intrinsicCyclicPairing_involutive i).symm
        _ = B.intrinsicCyclicPairing (B.intrinsicBoundaryTreeEdgeSide e) :=
          congrArg B.intrinsicCyclicPairing h
    · left
      calc
        i = B.intrinsicCyclicPairing (B.intrinsicCyclicPairing i) :=
          (B.intrinsicCyclicPairing_involutive i).symm
        _ = B.intrinsicCyclicPairing (B.intrinsicCyclicPairing
            (B.intrinsicBoundaryTreeEdgeSide e)) := congrArg B.intrinsicCyclicPairing h
        _ = B.intrinsicBoundaryTreeEdgeSide e :=
          B.intrinsicCyclicPairing_involutive _
  · rintro (h | h)
    · right
      exact congrArg B.intrinsicCyclicPairing h
    · left
      calc
        B.intrinsicCyclicPairing i =
            B.intrinsicCyclicPairing
              (B.intrinsicCyclicPairing (B.intrinsicBoundaryTreeEdgeSide e)) :=
          congrArg B.intrinsicCyclicPairing h
        _ = B.intrinsicBoundaryTreeEdgeSide e :=
          B.intrinsicCyclicPairing_involutive _

private theorem intrinsicBoundaryTreeEdgeSwap_apply
    (B : DirichletBoundarySegments X o)
    (e : B.intrinsicBoundarySpanningTree.edgeSet)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryTreeEdgeSwap e i =
      if B.intrinsicBoundaryTreeEdgeContains e i then
        B.intrinsicCyclicPairing i else i := by
  classical
  unfold intrinsicBoundaryTreeEdgeSwap intrinsicBoundaryTreeEdgeContains
  by_cases hleft : i = B.intrinsicBoundaryTreeEdgeSide e
  · subst i
    simp
  · by_cases hright : i =
        B.intrinsicCyclicPairing (B.intrinsicBoundaryTreeEdgeSide e)
    · subst i
      simp only [Equiv.swap_apply_right, or_true, if_true]
      exact (B.intrinsicCyclicPairing_involutive _).symm
    · have hleft' : B.intrinsicBoundaryTreeEdgeSide e ≠ i := Ne.symm hleft
      have hright' : B.intrinsicCyclicPairing
          (B.intrinsicBoundaryTreeEdgeSide e) ≠ i := Ne.symm hright
      have hnot : ¬ (i = B.intrinsicBoundaryTreeEdgeSide e ∨
          i = B.intrinsicCyclicPairing (B.intrinsicBoundaryTreeEdgeSide e)) :=
        not_or.mpr ⟨hleft, hright⟩
      rw [Equiv.swap_apply_of_ne_of_ne hleft hright]
      simp [hnot]

private theorem intrinsicBoundaryTreeEdgeSwap_list_prod_apply
    (B : DirichletBoundarySegments X o)
    (l : List (B.intrinsicBoundarySpanningTree.edgeSet)) (hl : l.Nodup)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    (l.map B.intrinsicBoundaryTreeEdgeSwap).prod i =
      if ∃ e ∈ l, B.intrinsicBoundaryTreeEdgeContains e i then
        B.intrinsicCyclicPairing i else i := by
  classical
  induction l with
  | nil => simp
  | cons e l ih =>
      rw [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply, ih hl.of_cons]
      by_cases he : B.intrinsicBoundaryTreeEdgeContains e i
      · have htail : ¬ ∃ f ∈ l, B.intrinsicBoundaryTreeEdgeContains f i := by
          rintro ⟨f, hf, hfi⟩
          exact (List.nodup_cons.mp hl).1
            (B.intrinsicBoundaryTreeEdgeContains_unique he hfi ▸ hf)
        rw [if_neg htail, B.intrinsicBoundaryTreeEdgeSwap_apply]
        simp [he]
      · by_cases htail : ∃ f ∈ l, B.intrinsicBoundaryTreeEdgeContains f i
        · obtain ⟨f, hf, hfi⟩ := htail
          have htail' : ∃ f ∈ l, B.intrinsicBoundaryTreeEdgeContains f i :=
            ⟨f, hf, hfi⟩
          have hpair : ¬ B.intrinsicBoundaryTreeEdgeContains e
              (B.intrinsicCyclicPairing i) := by
            intro h
            have hfi' := (B.intrinsicBoundaryTreeEdgeContains_pair_iff f i).mpr hfi
            have hef := B.intrinsicBoundaryTreeEdgeContains_unique h hfi'
            have h' : B.intrinsicBoundaryTreeEdgeContains f
                (B.intrinsicCyclicPairing i) := by simpa only [hef] using h
            have h'' := (B.intrinsicBoundaryTreeEdgeContains_pair_iff f i).mp h'
            have h''' : B.intrinsicBoundaryTreeEdgeContains e i := by
              simpa only [hef] using h''
            exact he h'''
          rw [if_pos htail', B.intrinsicBoundaryTreeEdgeSwap_apply]
          simp [he, htail', hpair]
        · rw [if_neg htail, B.intrinsicBoundaryTreeEdgeSwap_apply]
          simp [he, htail]

/-- The simultaneous tree-pair involution in the surface construction is
exactly the product of the transpositions of its selected physical tree
sides. This equality is proved from the original side pairing and tree-side
enumeration; it does not assume any transitivity conclusion. -/
theorem intrinsicBoundaryTreePairingPerm_eq_treeEdgeSwapProduct
    (B : DirichletBoundarySegments X o) :
    B.intrinsicBoundaryTreePairingPerm =
      (((Finset.univ : Finset (B.intrinsicBoundarySpanningTree.edgeSet)).toList).map
        B.intrinsicBoundaryTreeEdgeSwap).prod := by
  classical
  apply Equiv.ext
  intro i
  rw [B.intrinsicBoundaryTreePairingPerm_apply,
    intrinsicBoundaryTreeEdgeSwap_list_prod_apply B _ (Finset.nodup_toList _) i]
  have hcontains :
      (∃ e ∈ (Finset.univ : Finset (B.intrinsicBoundarySpanningTree.edgeSet)).toList,
        B.intrinsicBoundaryTreeEdgeContains e i) ↔
        B.intrinsicBoundaryPhysicalEdge i ∈ range B.intrinsicBoundaryTreePhysicalEdge := by
    constructor
    · rintro ⟨e, he, hi⟩
      have hphysical := (B.intrinsicBoundaryTreeEdgeContains_iff_physicalEdge e i).mp hi
      exact Set.mem_range.mpr ⟨e, hphysical.symm⟩
    · intro hi
      obtain ⟨e, he⟩ := Set.mem_range.mp hi
      have hphysical : B.intrinsicBoundaryPhysicalEdge i =
          B.intrinsicBoundaryTreePhysicalEdge e := he.symm
      exact ⟨e, Finset.mem_toList.mpr (Finset.mem_univ _),
        (B.intrinsicBoundaryTreeEdgeContains_iff_physicalEdge e i).mpr hphysical⟩
  by_cases hret : B.intrinsicBoundaryRetainedSidePred i
  · have hnone : ¬ ∃ e ∈
      (Finset.univ : Finset (B.intrinsicBoundarySpanningTree.edgeSet)).toList,
        B.intrinsicBoundaryTreeEdgeContains e i := by
      intro hex
      exact hret (hcontains.mp hex)
    rw [if_pos hret, if_neg hnone]
  · have hi : B.intrinsicBoundaryPhysicalEdge i ∈
      range B.intrinsicBoundaryTreePhysicalEdge := by
      exact not_not.mp hret
    rw [if_neg hret, if_pos (hcontains.mpr hi)]

/-- Thus the exact permutation used for tree splicing is the original local
vertex transition multiplied by that explicit physical transposition product. -/
theorem intrinsicBoundaryTreeSplicedVertexPerm_eq_original_mul_treeEdgeSwapProduct
    (B : DirichletBoundarySegments X o) :
    B.intrinsicBoundaryTreeSplicedVertexPerm =
      B.intrinsicBoundaryOriginalVertexPerm *
        (((Finset.univ : Finset (B.intrinsicBoundarySpanningTree.edgeSet)).toList).map
          B.intrinsicBoundaryTreeEdgeSwap).prod := by
  rw [intrinsicBoundaryTreeSplicedVertexPerm,
    intrinsicBoundaryTreePairingPerm_eq_treeEdgeSwapProduct]

#print axioms intrinsicBoundaryPhysicalEdge_eq_pair_or_self
#print axioms intrinsicBoundaryTreePairingPerm_eq_treeEdgeSwapProduct
#print axioms intrinsicBoundaryTreeSplicedVertexPerm_eq_original_mul_treeEdgeSwapProduct

end

end SystolicGrowth.DirichletBoundarySegments
