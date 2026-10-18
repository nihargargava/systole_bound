module

public import Geometry.SurfaceBoundaryGraphEdgeAlphabet
public import Geometry.SurfaceBoundaryGraphPeripheralWord
public import Mathlib.GroupTheory.FreeGroup.Basic

@[expose] public section

/-!
# Free words evaluating to the actual physical boundary loops

The letters are the genuine physical non-tree sides, not edges of the
underlying simple graph. Their free-group homomorphism sends each letter to
its actual tree-rooted physical side loop. Original oriented sides have
signed words, with actual selected tree sides removed by their proved
nullhomotopies. This constructs no assumed free-basis equivalence.

The original perimeter word uses the reverse product because Mathlib's
fundamental-group multiplication reverses time-ordered path composition.
-/

open scoped UpperHalfPlane

namespace SystolicGrowth.DirichletBoundarySegments

noncomputable section

variable {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}

/-- The genuine homomorphism sending each physical non-tree letter to its
actual rooted side generator. -/
def intrinsicBoundaryFreeGeneratorHom (B : DirichletBoundarySegments X o)
    (r : B.IntrinsicBoundaryGraphVertex) :
    FreeGroup B.IntrinsicBoundaryNonTreeEdge →*
      FundamentalGroup B.IntrinsicBoundaryGraph (B.intrinsicBoundaryGraphVertexInclusion r) :=
  FreeGroup.lift (fun e => B.intrinsicBoundarySideGenerator r e.val.val)

@[simp]
theorem intrinsicBoundaryFreeGeneratorHom_of (B : DirichletBoundarySegments X o)
    (r : B.IntrinsicBoundaryGraphVertex) (e : B.IntrinsicBoundaryNonTreeEdge) :
    B.intrinsicBoundaryFreeGeneratorHom r (FreeGroup.of e) =
      B.intrinsicBoundarySideGenerator r e.val.val :=
  FreeGroup.lift_apply_of

/-- The signed free word of an original oriented side: actual selected tree
edges disappear, and the opposite orientation reverses a non-tree letter. -/
def intrinsicBoundaryFreeSideWord (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) : FreeGroup B.IntrinsicBoundaryNonTreeEdge := by
  classical
  exact if ht : B.intrinsicBoundaryPhysicalEdge i ∈ Set.range B.intrinsicBoundaryTreePhysicalEdge
    then 1 else
      if i < B.intrinsicCyclicPairing i then
        FreeGroup.of ⟨B.intrinsicBoundaryPhysicalEdge i, ht⟩ else
        (FreeGroup.of ⟨B.intrinsicBoundaryPhysicalEdge i, ht⟩)⁻¹

/-- Every side of an actually selected physical tree edge has trivial free word. -/
theorem intrinsicBoundaryFreeSideWord_eq_one_of_tree (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card)
    (ht : B.intrinsicBoundaryPhysicalEdge i ∈ Set.range B.intrinsicBoundaryTreePhysicalEdge) :
    B.intrinsicBoundaryFreeSideWord i = 1 := by
  classical
  rw [intrinsicBoundaryFreeSideWord, dif_pos ht]

@[simp]
theorem intrinsicBoundaryFreeSideWord_tree (B : DirichletBoundarySegments X o)
    (e : B.intrinsicBoundarySpanningTree.edgeSet) :
    B.intrinsicBoundaryFreeSideWord (B.intrinsicBoundaryTreeEdgeSide e) = 1 :=
  B.intrinsicBoundaryFreeSideWord_eq_one_of_tree _ ⟨e, rfl⟩

/-- The original physical pairing reverses the signed free side word. -/
@[simp]
theorem intrinsicBoundaryFreeSideWord_pair (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryFreeSideWord (B.intrinsicCyclicPairing i) =
      (B.intrinsicBoundaryFreeSideWord i)⁻¹ := by
  classical
  by_cases ht : B.intrinsicBoundaryPhysicalEdge i ∈ Set.range B.intrinsicBoundaryTreePhysicalEdge
  · simp only [intrinsicBoundaryFreeSideWord, B.intrinsicBoundaryPhysicalEdge_pair,
      dif_pos ht, inv_one]
  · by_cases h : i < B.intrinsicCyclicPairing i
    · have hp : ¬B.intrinsicCyclicPairing i <
          B.intrinsicCyclicPairing (B.intrinsicCyclicPairing i) := by
        rw [B.intrinsicCyclicPairing_involutive]
        exact not_lt_of_ge h.le
      simp only [intrinsicBoundaryFreeSideWord, B.intrinsicBoundaryPhysicalEdge_pair,
        dif_neg ht, if_pos h, if_neg hp]
    · have hp : B.intrinsicCyclicPairing i <
          B.intrinsicCyclicPairing (B.intrinsicCyclicPairing i) := by
        rw [B.intrinsicCyclicPairing_involutive]
        exact lt_of_le_of_ne (le_of_not_gt h) (B.intrinsicCyclicPairing_ne_self i)
      simp only [intrinsicBoundaryFreeSideWord, B.intrinsicBoundaryPhysicalEdge_pair,
        dif_neg ht, if_neg h, if_pos hp, inv_inv]

@[simp]
theorem intrinsicBoundaryFreeSideWord_paired_tree (B : DirichletBoundarySegments X o)
    (e : B.intrinsicBoundarySpanningTree.edgeSet) :
    B.intrinsicBoundaryFreeSideWord
      (B.intrinsicCyclicPairing (B.intrinsicBoundaryTreeEdgeSide e)) = 1 := by
  rw [intrinsicBoundaryFreeSideWord_pair, intrinsicBoundaryFreeSideWord_tree, inv_one]

private theorem physicalEdge_val (B : DirichletBoundarySegments X o)
    (a : B.IntrinsicBoundaryPhysicalEdge) : B.intrinsicBoundaryPhysicalEdge a.val = a := by
  classical
  apply Subtype.ext
  simp only [intrinsicBoundaryPhysicalEdge, dif_pos a.property]

/-- A canonical lower non-tree orientation has exactly its own free letter. -/
@[simp]
theorem intrinsicBoundaryFreeSideWord_nonTree (B : DirichletBoundarySegments X o)
    (e : B.IntrinsicBoundaryNonTreeEdge) :
    B.intrinsicBoundaryFreeSideWord e.val.val = FreeGroup.of e := by
  classical
  have ht : B.intrinsicBoundaryPhysicalEdge e.val.val ∉
      Set.range B.intrinsicBoundaryTreePhysicalEdge := by
    rw [physicalEdge_val]
    exact e.property
  rw [intrinsicBoundaryFreeSideWord, dif_neg ht, if_pos e.val.property]
  exact congrArg FreeGroup.of (Subtype.ext (physicalEdge_val B e.val))

/-- The canonical physical coefficient is trivial on the selected tree. -/
@[simp]
theorem intrinsicBoundaryFreeSideWord_treePhysical (B : DirichletBoundarySegments X o)
    (e : B.intrinsicBoundarySpanningTree.edgeSet) :
    B.intrinsicBoundaryFreeSideWord (B.intrinsicBoundaryTreePhysicalEdge e).val = 1 := by
  apply B.intrinsicBoundaryFreeSideWord_eq_one_of_tree
  rw [physicalEdge_val]
  exact ⟨e, rfl⟩

private theorem physicalEdge_sideGenerator (B : DirichletBoundarySegments X o)
    (r : B.IntrinsicBoundaryGraphVertex) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundarySideGenerator r (B.intrinsicBoundaryPhysicalEdge i).val =
      if i < B.intrinsicCyclicPairing i then B.intrinsicBoundarySideGenerator r i else
        (B.intrinsicBoundarySideGenerator r i)⁻¹ := by
  classical
  by_cases h : i < B.intrinsicCyclicPairing i
  · simp only [intrinsicBoundaryPhysicalEdge, dif_pos h, if_pos h]
  · simp only [intrinsicBoundaryPhysicalEdge, dif_neg h, if_neg h,
      intrinsicBoundarySideGenerator_pair]

private theorem sideGenerator_eq_one_of_tree (B : DirichletBoundarySegments X o)
    (r : B.IntrinsicBoundaryGraphVertex) (i : Fin B.intrinsicBoundaryRadialCuts.card)
    (ht : B.intrinsicBoundaryPhysicalEdge i ∈ Set.range B.intrinsicBoundaryTreePhysicalEdge) :
    B.intrinsicBoundarySideGenerator r i = 1 := by
  classical
  obtain ⟨e, he⟩ := ht
  have hcanon : B.intrinsicBoundarySideGenerator r (B.intrinsicBoundaryPhysicalEdge i).val = 1 := by
    rw [← he]
    change B.intrinsicBoundarySideGenerator r
      (B.intrinsicBoundaryPhysicalEdge (B.intrinsicBoundaryTreeEdgeSide e)).val = 1
    rw [physicalEdge_sideGenerator]
    split_ifs <;> simp only [intrinsicBoundarySideGenerator_tree, inv_one]
  by_cases h : i < B.intrinsicCyclicPairing i
  · simpa only [physicalEdge_sideGenerator, if_pos h] using hcanon
  · have hinv : (B.intrinsicBoundarySideGenerator r i)⁻¹ = 1 := by
      simpa only [physicalEdge_sideGenerator, if_neg h] using hcanon
    exact inv_eq_one.mp hinv

/-- Every signed free side word evaluates to the actual rooted physical side
generator. Tree triviality comes from the proved physical nullhomotopies. -/
theorem intrinsicBoundaryFreeGeneratorHom_sideWord (B : DirichletBoundarySegments X o)
    (r : B.IntrinsicBoundaryGraphVertex) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryFreeGeneratorHom r (B.intrinsicBoundaryFreeSideWord i) =
      B.intrinsicBoundarySideGenerator r i := by
  classical
  by_cases ht : B.intrinsicBoundaryPhysicalEdge i ∈ Set.range B.intrinsicBoundaryTreePhysicalEdge
  · rw [B.intrinsicBoundaryFreeSideWord_eq_one_of_tree i ht, map_one,
      sideGenerator_eq_one_of_tree B r i ht]
  · rw [intrinsicBoundaryFreeSideWord, dif_neg ht]
    by_cases h : i < B.intrinsicCyclicPairing i
    · rw [if_pos h, intrinsicBoundaryFreeGeneratorHom_of]
      simp only [intrinsicBoundaryPhysicalEdge, dif_pos h]
    · rw [if_neg h, map_inv, intrinsicBoundaryFreeGeneratorHom_of]
      simp only [intrinsicBoundaryPhysicalEdge, dif_neg h,
        intrinsicBoundarySideGenerator_pair, inv_inv]

/-- The literal time-ordered perimeter, as a free word with Mathlib's reversed
fundamental-group product convention. -/
def intrinsicBoundaryPerimeterFreeWord (B : DirichletBoundarySegments X o) :
    FreeGroup B.IntrinsicBoundaryNonTreeEdge :=
  (List.ofFn B.intrinsicBoundaryFreeSideWord).reverse.prod

/-- Evaluating the perimeter free word gives the reversed product of the
original actual side generators, retaining their cyclic order. -/
theorem intrinsicBoundaryFreeGeneratorHom_perimeterFreeWord_sideWord
    (B : DirichletBoundarySegments X o) (r : B.IntrinsicBoundaryGraphVertex) :
    B.intrinsicBoundaryFreeGeneratorHom r B.intrinsicBoundaryPerimeterFreeWord =
      (List.ofFn (B.intrinsicBoundarySideGenerator r)).reverse.prod := by
  rw [intrinsicBoundaryPerimeterFreeWord, MonoidHom.map_list_prod,
    List.map_reverse, List.map_ofFn]
  simp only [Function.comp_def, intrinsicBoundaryFreeGeneratorHom_sideWord]

/-- The free perimeter word evaluates to the actual rooted physical perimeter
loop, with no assumed graph presentation. -/
theorem intrinsicBoundaryFreeGeneratorHom_perimeterFreeWord
    (B : DirichletBoundarySegments X o) (r : B.IntrinsicBoundaryGraphVertex) :
    B.intrinsicBoundaryFreeGeneratorHom r B.intrinsicBoundaryPerimeterFreeWord =
      (⟦B.intrinsicBoundaryRootedPerimeterLoop r⟧ :
        FundamentalGroup B.IntrinsicBoundaryGraph (B.intrinsicBoundaryGraphVertexInclusion r)) := by
  rw [intrinsicBoundaryFreeGeneratorHom_perimeterFreeWord_sideWord]
  exact (B.intrinsicBoundaryRootedPerimeterLoop_sideWord r).symm

/-- The same free word retains the untouched original physical perimeter
basepoint through the already proved identity-map transport. -/
theorem intrinsicBoundaryGraphGeodLoop_freeWord_originalBasepoint
    (B : DirichletBoundarySegments X o) :
    (⟦B.intrinsicBoundaryGraphGeodLoop⟧ :
      FundamentalGroup B.IntrinsicBoundaryGraph (B.intrinsicBoundaryGraphVertices 0)) =
      FundamentalGroup.mapOfEq (ContinuousMap.id B.IntrinsicBoundaryGraph)
        B.intrinsicBoundaryGraphVertices_zero_eq_root.symm
        (B.intrinsicBoundaryFreeGeneratorHom B.intrinsicBoundaryPeripheralRoot
          B.intrinsicBoundaryPerimeterFreeWord) := by
  rw [intrinsicBoundaryFreeGeneratorHom_perimeterFreeWord_sideWord]
  exact B.intrinsicBoundaryGraphGeodLoop_sideWord_originalBasepoint

end

end SystolicGrowth.DirichletBoundarySegments
