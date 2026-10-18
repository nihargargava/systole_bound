module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SurfaceBoundaryGraphWordFunctor
public import Geometry.SurfaceBoundaryGraphSideSubdivision
public import Geometry.SurfaceBoundaryGraphFreeGenerators

@[expose] public section

/-!
# The actual free-word reader and its left inverse

The descended cover functor reads literal physical sides. Selected physical
tree connectors read one, so its based homomorphism sends each actual side
generator to its signed non-tree word. This proves a genuine left inverse of
the free-generator homomorphism, without assuming that the generators span.
-/

open Set CategoryTheory UpperHalfPlane
open scoped UpperHalfPlane Classical

set_option backward.isDefEq.respectTransparency false

namespace SystolicGrowth.DirichletBoundarySegments

noncomputable section

private theorem singleObjFunctor_map_pathCast
    {Y H : Type} [TopologicalSpace Y] [Group H]
    (F : FundamentalGroupoid Y ⥤ SingleObj H) {a b a' b' : Y}
    (p : Path a b) (ha : a' = a) (hb : b' = b) :
    (F.map (Path.Homotopic.Quotient.mk (p.cast ha hb)) : H) =
      F.map (Path.Homotopic.Quotient.mk p) := by
  cases ha
  cases hb
  rfl

private theorem singleObjFunctor_map_pathTrans
    {Y H : Type} [TopologicalSpace Y] [Group H]
    (F : FundamentalGroupoid Y ⥤ SingleObj H) {a b c : Y}
    (p : Path a b) (q : Path b c) :
    (F.map (Path.Homotopic.Quotient.mk (p.trans q)) : H) =
      F.map (Path.Homotopic.Quotient.mk q) * F.map (Path.Homotopic.Quotient.mk p) := by
  change F.map (Path.Homotopic.Quotient.mk p ≫ Path.Homotopic.Quotient.mk q) = _
  exact F.map_comp _ _

private theorem singleObjFunctor_map_pathSymm
    {Y H : Type} [TopologicalSpace Y] [Group H]
    (F : FundamentalGroupoid Y ⥤ SingleObj H) {a b : Y} (p : Path a b) :
    (F.map (Path.Homotopic.Quotient.mk p.symm) : H) =
      (F.map (Path.Homotopic.Quotient.mk p))⁻¹ := by
  have h : (F.map (Path.Homotopic.Quotient.mk p.symm) : H) *
      F.map (Path.Homotopic.Quotient.mk p) = 1 := by
    rw [← singleObjFunctor_map_pathTrans]
    rw [Path.Homotopic.Quotient.eq.mpr (Path.Homotopic.trans_symm p)]
    exact F.map_id (FundamentalGroupoid.mk a)
  exact eq_inv_of_mul_eq_one_left h

variable {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}

/-- The actual first cut is in the initial overlap arm of its physical side. -/
theorem intrinsicBoundaryGraphSideInitialCut_mem_initialOverlap
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryGraphSidePath i intrinsicBoundaryGraphSideInitialCut ∈
      B.intrinsicBoundaryGraphInitialOverlap i := by
  refine ⟨⟨3 / 10, by constructor <;> norm_num⟩, ?_, ?_⟩
  · change (3 / 10 : ℝ) < 1 / 3
    norm_num
  · change (B.intrinsicBoundaryGraphMidsectionHomeomorph i ⟨3 / 10, _⟩).1 = _
    rw [B.intrinsicBoundaryGraphMidsectionHomeomorph_apply]
    rfl

/-- The actual second cut is in the terminal overlap arm of its physical side. -/
theorem intrinsicBoundaryGraphSideTerminalCut_mem_terminalOverlap
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryGraphSidePath i intrinsicBoundaryGraphSideTerminalCut ∈
      B.intrinsicBoundaryGraphTerminalOverlap i := by
  refine ⟨⟨7 / 10, by constructor <;> norm_num⟩, ?_, ?_⟩
  · change (2 / 3 : ℝ) < 7 / 10
    norm_num
  · change (B.intrinsicBoundaryGraphMidsectionHomeomorph i ⟨7 / 10, _⟩).1 = _
    rw [B.intrinsicBoundaryGraphMidsectionHomeomorph_apply]
    rfl

variable {H : Type} [Group H]

/-- The genuine descended functor reads a canonical physical side as its assigned label. -/
theorem intrinsicBoundaryGraphWordFunctor_map_canonicalSide
    (B : DirichletBoundarySegments X o) (c : B.IntrinsicBoundaryPhysicalEdge → H)
    (e : B.IntrinsicBoundaryPhysicalEdge) :
    (B.intrinsicBoundaryGraphWordFunctor c).map
        (Path.Homotopic.Quotient.mk (B.intrinsicBoundaryGraphSidePath e.val)) = c e := by
  let F := B.intrinsicBoundaryGraphWordFunctor c
  have hmiddle := B.intrinsicBoundaryGraphWordFunctor_map_midsection c
    (B.intrinsicBoundaryGraphSideMiddleMidsectionPath e.val)
  rw [B.intrinsicBoundaryMidsectionGauge_terminal c _ e
      (B.intrinsicBoundaryGraphSideTerminalCut_mem_terminalOverlap e.val),
    B.intrinsicBoundaryMidsectionGauge_initial c _ e
      (B.intrinsicBoundaryGraphSideInitialCut_mem_initialOverlap e.val), inv_one, mul_one] at hmiddle
  have hread : F.map (Path.Homotopic.Quotient.mk
      (B.intrinsicBoundaryGraphSideSubdivision e.val)) = c e := by
    rw [intrinsicBoundaryGraphSideSubdivision, singleObjFunctor_map_pathCast,
      singleObjFunctor_map_pathTrans, singleObjFunctor_map_pathTrans,
      B.intrinsicBoundaryGraphWordFunctor_map_star c
        (B.intrinsicBoundaryGraphSideInitialStarPath e.val),
      B.intrinsicBoundaryGraphWordFunctor_map_star c
        (B.intrinsicBoundaryGraphSideTerminalStarPath e.val), hmiddle, mul_one, one_mul]
  have hclass := Path.Homotopic.Quotient.eq.mpr
    (B.intrinsicBoundaryGraphSideSubdivision_homotopic e.val)
  exact (congrArg (fun p => (F.map p : H)) hclass).symm.trans hread

/-- Original side reversal reads the inverse coefficient, including all endpoint casts. -/
theorem intrinsicBoundaryGraphWordFunctor_map_pairedSide
    (B : DirichletBoundarySegments X o) (c : B.IntrinsicBoundaryPhysicalEdge → H)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    (B.intrinsicBoundaryGraphWordFunctor c).map
        (Path.Homotopic.Quotient.mk (B.intrinsicBoundaryGraphSidePath (B.intrinsicCyclicPairing i))) =
      ((B.intrinsicBoundaryGraphWordFunctor c).map
        (Path.Homotopic.Quotient.mk (B.intrinsicBoundaryGraphSidePath i)))⁻¹ := by
  have h := congrArg
    (fun p => ((B.intrinsicBoundaryGraphWordFunctor c).map
      (Path.Homotopic.Quotient.mk p) : H)) (B.intrinsicBoundaryGraphSidePath_pair i)
  rw [singleObjFunctor_map_pathCast, singleObjFunctor_map_pathSymm] at h
  exact h

/-- The actual coefficients retained from the physical non-tree alphabet. -/
def intrinsicBoundaryFreeReaderCoefficients (B : DirichletBoundarySegments X o) :
    B.IntrinsicBoundaryPhysicalEdge → FreeGroup B.IntrinsicBoundaryNonTreeEdge :=
  fun e => B.intrinsicBoundaryFreeSideWord e.val

/-- Every original oriented side reads its signed original free word. -/
theorem intrinsicBoundaryGraphWordFunctor_map_freeSide
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    (B.intrinsicBoundaryGraphWordFunctor B.intrinsicBoundaryFreeReaderCoefficients).map
        (Path.Homotopic.Quotient.mk (B.intrinsicBoundaryGraphSidePath i)) =
      B.intrinsicBoundaryFreeSideWord i := by
  by_cases hi : i < B.intrinsicCyclicPairing i
  · exact B.intrinsicBoundaryGraphWordFunctor_map_canonicalSide
      B.intrinsicBoundaryFreeReaderCoefficients ⟨i, hi⟩
  · have hp : B.intrinsicCyclicPairing i <
        B.intrinsicCyclicPairing (B.intrinsicCyclicPairing i) := by
      rw [B.intrinsicCyclicPairing_involutive]
      exact lt_of_le_of_ne (le_of_not_gt hi) (B.intrinsicCyclicPairing_ne_self i)
    have h := B.intrinsicBoundaryGraphWordFunctor_map_canonicalSide
      B.intrinsicBoundaryFreeReaderCoefficients ⟨B.intrinsicCyclicPairing i, hp⟩
    change _ = B.intrinsicBoundaryFreeSideWord (B.intrinsicCyclicPairing i) at h
    rw [intrinsicBoundaryGraphWordFunctor_map_pairedSide,
      intrinsicBoundaryFreeSideWord_pair] at h
    have h' := congrArg (fun w : FreeGroup B.IntrinsicBoundaryNonTreeEdge => w⁻¹) h
    simpa only [inv_inv] using h'

/-- Every selected physical tree adjacency reads one, in either traversal direction. -/
theorem intrinsicBoundaryGraphWordFunctor_map_treeAdjacency
    (B : DirichletBoundarySegments X o) {v w : B.IntrinsicBoundaryGraphVertex}
    (h : B.intrinsicBoundarySpanningTree.Adj v w) :
    (B.intrinsicBoundaryGraphWordFunctor B.intrinsicBoundaryFreeReaderCoefficients).map
        (Path.Homotopic.Quotient.mk (B.intrinsicBoundaryTreeAdjacencyPath h)) =
      (1 : FreeGroup B.IntrinsicBoundaryNonTreeEdge) := by
  let e : B.intrinsicBoundarySpanningTree.edgeSet :=
    ⟨s(v, w), (B.intrinsicBoundarySpanningTree.mem_edgeSet).mpr h⟩
  let i := B.intrinsicBoundaryTreeEdgeSide e
  have hends := Sym2.eq_iff.mp (B.intrinsicBoundaryTreeEdgeSide_endpoints e)
  have hside : (B.intrinsicBoundaryGraphWordFunctor B.intrinsicBoundaryFreeReaderCoefficients).map
      (Path.Homotopic.Quotient.mk (B.intrinsicBoundaryGraphSidePath i)) =
        (1 : FreeGroup B.IntrinsicBoundaryNonTreeEdge) := by
    rw [B.intrinsicBoundaryGraphWordFunctor_map_freeSide, intrinsicBoundaryFreeSideWord_tree]
  rcases hends with ⟨hv, hw⟩ | ⟨hw, hv⟩
  · have hpath : B.intrinsicBoundaryTreeAdjacencyPath h =
        (B.intrinsicBoundaryGraphSidePath i).cast
          (congrArg B.intrinsicBoundaryGraphVertexInclusion hv).symm
          (congrArg B.intrinsicBoundaryGraphVertexInclusion hw).symm := by
      apply Path.ext
      funext t
      rw [B.intrinsicBoundaryTreeAdjacencyPath_apply]
      have hv' : B.intrinsicBoundaryGraphSideStart
          (B.intrinsicBoundaryTreeEdgeSide
            ⟨s(v, w), (B.intrinsicBoundarySpanningTree.mem_edgeSet).mpr h⟩) = v := hv
      simp only [if_pos hv']
      rfl
    rw [hpath, singleObjFunctor_map_pathCast]
    exact hside
  · have hi : B.intrinsicBoundaryGraphSideStart i ≠ v :=
      fun hi => h.ne (hi.symm.trans hw)
    have hpath : B.intrinsicBoundaryTreeAdjacencyPath h =
        (B.intrinsicBoundaryGraphSidePath i).symm.cast
          (congrArg B.intrinsicBoundaryGraphVertexInclusion hv).symm
          (congrArg B.intrinsicBoundaryGraphVertexInclusion hw).symm := by
      apply Path.ext
      funext t
      rw [B.intrinsicBoundaryTreeAdjacencyPath_apply]
      have hi' : B.intrinsicBoundaryGraphSideStart
          (B.intrinsicBoundaryTreeEdgeSide
            ⟨s(v, w), (B.intrinsicBoundarySpanningTree.mem_edgeSet).mpr h⟩) ≠ v := hi
      simp only [if_neg hi']
      rfl
    rw [hpath, singleObjFunctor_map_pathCast, singleObjFunctor_map_pathSymm, hside]
    change (1 : FreeGroup B.IntrinsicBoundaryNonTreeEdge)⁻¹ = 1
    exact inv_one

/-- Every actual tree-walk realization reads one; no assumed tree-word equation is used. -/
theorem intrinsicBoundaryGraphWordFunctor_map_treeWalk
    (B : DirichletBoundarySegments X o) {v w : B.IntrinsicBoundaryGraphVertex}
    (p : B.intrinsicBoundarySpanningTree.Walk v w) :
    (B.intrinsicBoundaryGraphWordFunctor B.intrinsicBoundaryFreeReaderCoefficients).map
        (Path.Homotopic.Quotient.mk (B.intrinsicBoundaryTreeWalkPath p)) =
      (1 : FreeGroup B.IntrinsicBoundaryNonTreeEdge) := by
  induction p with
  | nil =>
    exact (B.intrinsicBoundaryGraphWordFunctor B.intrinsicBoundaryFreeReaderCoefficients).map_id _
  | cons h p ih =>
    rw [intrinsicBoundaryTreeWalkPath_cons, singleObjFunctor_map_pathTrans,
      intrinsicBoundaryGraphWordFunctor_map_treeAdjacency, ih]
    change (1 : FreeGroup B.IntrinsicBoundaryNonTreeEdge) * 1 = 1
    exact one_mul _

/-- The original rooted physical tree connector has label one. -/
theorem intrinsicBoundaryGraphWordFunctor_map_treeConnector
    (B : DirichletBoundarySegments X o) (r v : B.IntrinsicBoundaryGraphVertex) :
    (B.intrinsicBoundaryGraphWordFunctor B.intrinsicBoundaryFreeReaderCoefficients).map
        (Path.Homotopic.Quotient.mk (B.intrinsicBoundaryTreeConnector r v)) =
      (1 : FreeGroup B.IntrinsicBoundaryNonTreeEdge) :=
  B.intrinsicBoundaryGraphWordFunctor_map_treeWalk _

/-- Word reading of the original actual based side generator. -/
theorem intrinsicBoundaryGraphWordHom_free_sideGenerator
    (B : DirichletBoundarySegments X o) (r : B.IntrinsicBoundaryGraphVertex)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryGraphWordHom B.intrinsicBoundaryFreeReaderCoefficients r
        (B.intrinsicBoundarySideGenerator r i) = B.intrinsicBoundaryFreeSideWord i := by
  rw [intrinsicBoundaryGraphWordHom_apply, intrinsicBoundarySideGenerator,
    intrinsicBoundarySideLoop, singleObjFunctor_map_pathTrans,
    singleObjFunctor_map_pathTrans, singleObjFunctor_map_pathSymm,
    intrinsicBoundaryGraphWordFunctor_map_treeConnector,
    intrinsicBoundaryGraphWordFunctor_map_treeConnector,
    intrinsicBoundaryGraphWordFunctor_map_freeSide]
  change (1 : FreeGroup B.IntrinsicBoundaryNonTreeEdge)⁻¹ *
    (B.intrinsicBoundaryFreeSideWord i * 1) = B.intrinsicBoundaryFreeSideWord i
  simp only [inv_one, one_mul, mul_one]

/-- The genuine based free-word reader on the original graph. -/
def intrinsicBoundaryFreeReader (B : DirichletBoundarySegments X o)
    (r : B.IntrinsicBoundaryGraphVertex) :
    FundamentalGroup B.IntrinsicBoundaryGraph (B.intrinsicBoundaryGraphVertexInclusion r) →*
      FreeGroup B.IntrinsicBoundaryNonTreeEdge :=
  B.intrinsicBoundaryGraphWordHom B.intrinsicBoundaryFreeReaderCoefficients r

@[simp]
theorem intrinsicBoundaryFreeReader_sideGenerator (B : DirichletBoundarySegments X o)
    (r : B.IntrinsicBoundaryGraphVertex) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryFreeReader r (B.intrinsicBoundarySideGenerator r i) =
      B.intrinsicBoundaryFreeSideWord i :=
  B.intrinsicBoundaryGraphWordHom_free_sideGenerator r i

/-- The actual reader is a left inverse of the original free-generator homomorphism. -/
theorem intrinsicBoundaryFreeReader_comp_freeGeneratorHom
    (B : DirichletBoundarySegments X o) (r : B.IntrinsicBoundaryGraphVertex) :
    (B.intrinsicBoundaryFreeReader r).comp (B.intrinsicBoundaryFreeGeneratorHom r) =
      MonoidHom.id (FreeGroup B.IntrinsicBoundaryNonTreeEdge) := by
  apply FreeGroup.ext_hom
  intro e
  rw [MonoidHom.comp_apply, intrinsicBoundaryFreeGeneratorHom_of,
    intrinsicBoundaryFreeReader_sideGenerator, intrinsicBoundaryFreeSideWord_nonTree]
  rfl

/-- Pointwise left inverse, retaining the actual generator and reader maps. -/
theorem intrinsicBoundaryFreeReader_leftInverse
    (B : DirichletBoundarySegments X o) (r : B.IntrinsicBoundaryGraphVertex) :
    Function.LeftInverse (B.intrinsicBoundaryFreeReader r) (B.intrinsicBoundaryFreeGeneratorHom r) := by
  intro w
  exact congrArg (fun f => f w) (B.intrinsicBoundaryFreeReader_comp_freeGeneratorHom r)

/-- Independence of the actual non-tree loops follows without a generation assumption. -/
theorem intrinsicBoundaryFreeGeneratorHom_injective
    (B : DirichletBoundarySegments X o) (r : B.IntrinsicBoundaryGraphVertex) :
    Function.Injective (B.intrinsicBoundaryFreeGeneratorHom r) :=
  (B.intrinsicBoundaryFreeReader_leftInverse r).injective

/-- The reader retains the original ordered physical perimeter word. -/
theorem intrinsicBoundaryFreeReader_rootedPerimeterLoop
    (B : DirichletBoundarySegments X o) (r : B.IntrinsicBoundaryGraphVertex) :
    B.intrinsicBoundaryFreeReader r
        (⟦B.intrinsicBoundaryRootedPerimeterLoop r⟧ :
          FundamentalGroup B.IntrinsicBoundaryGraph (B.intrinsicBoundaryGraphVertexInclusion r)) =
      B.intrinsicBoundaryPerimeterFreeWord := by
  rw [← intrinsicBoundaryFreeGeneratorHom_perimeterFreeWord]
  exact B.intrinsicBoundaryFreeReader_leftInverse r _

#print axioms intrinsicBoundaryGraphWordFunctor_map_canonicalSide
#print axioms intrinsicBoundaryGraphWordFunctor_map_freeSide
#print axioms intrinsicBoundaryGraphWordFunctor_map_treeConnector
#print axioms intrinsicBoundaryGraphWordHom_free_sideGenerator
#print axioms intrinsicBoundaryFreeReader_comp_freeGeneratorHom
#print axioms intrinsicBoundaryFreeGeneratorHom_injective
#print axioms intrinsicBoundaryFreeReader_rootedPerimeterLoop

end

end SystolicGrowth.DirichletBoundarySegments
