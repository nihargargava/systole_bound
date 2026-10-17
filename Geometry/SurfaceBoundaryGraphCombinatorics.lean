module

public import Geometry.SurfaceBoundaryGraphFundamentalGroup
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

/-! Finite vertex and spanning-tree data for the actual paired Dirichlet boundary graph.
The auxiliary simple graph is used only to choose a tree. The physical interval quotient
is unchanged, so its loops and parallel sides are not discarded. -/

open Set UpperHalfPlane
open scoped Pointwise UpperHalfPlane

namespace SystolicGrowth.DirichletBoundarySegments

noncomputable section

variable {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}

/-- Actual deck-orbit equivalence on the finite cyclic vertices, obtained by restricting
the already identified physical graph relation to literal zero parameters. -/
def intrinsicBoundaryGraphVertexSetoid (B : DirichletBoundarySegments X o) :
    Setoid (Fin B.intrinsicBoundaryRadialCuts.card) :=
  Setoid.comap (fun i ↦ (i, (0 : unitInterval))) B.intrinsicBoundaryIntervalSetoid

theorem intrinsicBoundaryGraphVertexSetoid_iff (B : DirichletBoundarySegments X o)
    (i j : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryGraphVertexSetoid i j ↔
      ∃ γ : X.deckGroup, γ • B.intrinsicCyclicVertex i = B.intrinsicCyclicVertex j :=
  B.intrinsicBoundaryIntervalSetoid_zero_iff i j

/-- The genuine finite quotient of actual cyclic vertices by actual deck orbits. -/
abbrev IntrinsicBoundaryGraphVertex (B : DirichletBoundarySegments X o) :=
  Quotient B.intrinsicBoundaryGraphVertexSetoid

instance (B : DirichletBoundarySegments X o) : Fintype B.IntrinsicBoundaryGraphVertex :=
  Fintype.ofFinite _

/-- The initial vertex class of the literal oriented side `i`. -/
def intrinsicBoundaryGraphSideStart (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) : B.IntrinsicBoundaryGraphVertex :=
  Quotient.mk _ i

/-- The terminal vertex class of the literal oriented side `i`. -/
def intrinsicBoundaryGraphSideEnd (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) : B.IntrinsicBoundaryGraphVertex :=
  B.intrinsicBoundaryGraphSideStart (finRotate B.intrinsicBoundaryRadialCuts.card i)

/-- The finite vertex quotient is exactly the zero-parameter vertices of the physical graph. -/
def intrinsicBoundaryGraphVertexEquivZero (B : DirichletBoundarySegments X o) :
    B.IntrinsicBoundaryGraphVertex ≃
      range (fun i : Fin B.intrinsicBoundaryRadialCuts.card ↦
        Quotient.mk B.intrinsicBoundaryIntervalSetoid (i, (0 : unitInterval))) :=
  Setoid.comapQuotientEquiv (fun i ↦ (i, (0 : unitInterval)))
    B.intrinsicBoundaryIntervalSetoid

/-- The actual vertex inclusion into the physical paired-side realization. -/
def intrinsicBoundaryGraphVertexInclusion (B : DirichletBoundarySegments X o) :
    B.IntrinsicBoundaryGraphVertex → Quotient B.intrinsicBoundaryIntervalSetoid :=
  fun v ↦ (B.intrinsicBoundaryGraphVertexEquivZero v).val

theorem intrinsicBoundaryGraphVertexInclusion_injective
    (B : DirichletBoundarySegments X o) :
    Function.Injective B.intrinsicBoundaryGraphVertexInclusion :=
  Subtype.val_injective.comp B.intrinsicBoundaryGraphVertexEquivZero.injective

@[simp]
theorem intrinsicBoundaryGraphVertexInclusion_start (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryGraphVertexInclusion (B.intrinsicBoundaryGraphSideStart i) =
      Quotient.mk B.intrinsicBoundaryIntervalSetoid (i, (0 : unitInterval)) := rfl

@[simp]
theorem intrinsicBoundaryGraphVertexInclusion_end (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryGraphVertexInclusion (B.intrinsicBoundaryGraphSideEnd i) =
      Quotient.mk B.intrinsicBoundaryIntervalSetoid (i, (1 : unitInterval)) :=
  (Quotient.sound (B.intrinsicBoundaryIntervalSetoid_next i)).symm

/-- The original paired-side involution reverses the actual endpoint classes. -/
theorem intrinsicBoundaryGraphSide_pair_endpoints (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryGraphSideStart (B.intrinsicCyclicPairing i) =
        B.intrinsicBoundaryGraphSideEnd i ∧
      B.intrinsicBoundaryGraphSideEnd (B.intrinsicCyclicPairing i) =
        B.intrinsicBoundaryGraphSideStart i := by
  obtain ⟨hstart, hend⟩ := B.inverse_smul_intrinsicCyclicVertices_eq_reverse i
  constructor
  · apply Eq.symm
    apply Quotient.sound
    exact (B.intrinsicBoundaryGraphVertexSetoid_iff _ _).2
      ⟨(B.intrinsicCyclicEdge i).1.1.1⁻¹, hend⟩
  · apply Eq.symm
    apply Quotient.sound
    exact (B.intrinsicBoundaryGraphVertexSetoid_iff _ _).2
      ⟨(B.intrinsicCyclicEdge i).1.1.1⁻¹, hstart⟩

/-- Auxiliary adjacency for choosing a spanning tree only. Every adjacency is witnessed
by an actual physical side; loops and parallel sides remain in the interval realization. -/
def intrinsicBoundaryUnderlyingGraph (B : DirichletBoundarySegments X o) :
    SimpleGraph B.IntrinsicBoundaryGraphVertex where
  Adj v w := v ≠ w ∧ ∃ i : Fin B.intrinsicBoundaryRadialCuts.card,
    (B.intrinsicBoundaryGraphSideStart i = v ∧ B.intrinsicBoundaryGraphSideEnd i = w) ∨
      (B.intrinsicBoundaryGraphSideStart i = w ∧ B.intrinsicBoundaryGraphSideEnd i = v)
  symm := ⟨by
    rintro v w ⟨hne, i, hi⟩
    exact ⟨hne.symm, i, hi.symm⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

/-- Each literal cyclic perimeter step is reachable, including a side whose endpoint
classes coincide. -/
theorem intrinsicBoundaryUnderlyingGraph_reachable_side
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryUnderlyingGraph.Reachable
      (B.intrinsicBoundaryGraphSideStart i) (B.intrinsicBoundaryGraphSideEnd i) := by
  by_cases h : B.intrinsicBoundaryGraphSideStart i = B.intrinsicBoundaryGraphSideEnd i
  · rw [h]
  · exact SimpleGraph.Adj.reachable (G := B.intrinsicBoundaryUnderlyingGraph)
      ⟨h, i, Or.inl ⟨rfl, rfl⟩⟩

/-- Repeated actual `finRotate` perimeter steps connect their starting vertex classes. -/
theorem intrinsicBoundaryUnderlyingGraph_reachable_rotate
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card)
    (k : ℕ) :
    B.intrinsicBoundaryUnderlyingGraph.Reachable (B.intrinsicBoundaryGraphSideStart i)
      (B.intrinsicBoundaryGraphSideStart
        ((finRotate B.intrinsicBoundaryRadialCuts.card)^[k] i)) := by
  induction k with
  | zero => exact SimpleGraph.Reachable.rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (B.intrinsicBoundaryUnderlyingGraph_reachable_side _)

/-- Connectivity is supplied by the actual cyclic perimeter, not by a graph-presentation
or a connectivity hypothesis. -/
theorem intrinsicBoundaryUnderlyingGraph_connected (B : DirichletBoundarySegments X o) :
    B.intrinsicBoundaryUnderlyingGraph.Connected := by
  have hpos : 0 < B.intrinsicBoundaryRadialCuts.card :=
    lt_of_lt_of_le (by decide : 0 < 3) B.three_le_intrinsicBoundaryRadialCuts_card
  letI : NeZero B.intrinsicBoundaryRadialCuts.card := ⟨hpos.ne'⟩
  apply (SimpleGraph.connected_iff_exists_forall_reachable
    B.intrinsicBoundaryUnderlyingGraph).2
  refine ⟨B.intrinsicBoundaryGraphSideStart 0, ?_⟩
  intro v
  induction v using Quotient.inductionOn with
  | _ i =>
    change B.intrinsicBoundaryUnderlyingGraph.Reachable
      (B.intrinsicBoundaryGraphSideStart 0) (B.intrinsicBoundaryGraphSideStart i)
    have hrotate : (finRotate B.intrinsicBoundaryRadialCuts.card)^[i.val] 0 = i := by
      rw [← finCycle_eq_finRotate_iterate]
      simp
    simpa only [hrotate] using B.intrinsicBoundaryUnderlyingGraph_reachable_rotate 0 i.val

/-- A genuine spanning tree on the same actual finite orbit-vertex quotient. -/
def intrinsicBoundarySpanningTree (B : DirichletBoundarySegments X o) :
    SimpleGraph B.IntrinsicBoundaryGraphVertex :=
  Classical.choose B.intrinsicBoundaryUnderlyingGraph_connected.exists_isTree_le

theorem intrinsicBoundarySpanningTree_le (B : DirichletBoundarySegments X o) :
    B.intrinsicBoundarySpanningTree ≤ B.intrinsicBoundaryUnderlyingGraph :=
  (Classical.choose_spec B.intrinsicBoundaryUnderlyingGraph_connected.exists_isTree_le).1

theorem intrinsicBoundarySpanningTree_isTree (B : DirichletBoundarySegments X o) :
    B.intrinsicBoundarySpanningTree.IsTree :=
  (Classical.choose_spec B.intrinsicBoundaryUnderlyingGraph_connected.exists_isTree_le).2

theorem Internal.SurfaceBoundaryGraphCombinatoricsHelpers.exists_side_of_tree_adj (B : DirichletBoundarySegments X o)
    {v w : B.IntrinsicBoundaryGraphVertex} (h : B.intrinsicBoundarySpanningTree.Adj v w) :
    ∃ i : Fin B.intrinsicBoundaryRadialCuts.card,
      (B.intrinsicBoundaryGraphSideStart i = v ∧ B.intrinsicBoundaryGraphSideEnd i = w) ∨
        (B.intrinsicBoundaryGraphSideStart i = w ∧ B.intrinsicBoundaryGraphSideEnd i = v) :=
  (B.intrinsicBoundarySpanningTree_le h).2

/-- A selected actual physical side witnessing each tree adjacency. Its orientation is
retained in the accompanying endpoint theorem. -/
def intrinsicBoundaryTreeAdjacencySide (B : DirichletBoundarySegments X o)
    (v w : B.IntrinsicBoundaryGraphVertex) (h : B.intrinsicBoundarySpanningTree.Adj v w) :
    Fin B.intrinsicBoundaryRadialCuts.card :=
  Classical.choose (Internal.SurfaceBoundaryGraphCombinatoricsHelpers.exists_side_of_tree_adj B h)

theorem intrinsicBoundaryTreeAdjacencySide_endpoints (B : DirichletBoundarySegments X o)
    (v w : B.IntrinsicBoundaryGraphVertex) (h : B.intrinsicBoundarySpanningTree.Adj v w) :
    (B.intrinsicBoundaryGraphSideStart (B.intrinsicBoundaryTreeAdjacencySide v w h) = v ∧
      B.intrinsicBoundaryGraphSideEnd (B.intrinsicBoundaryTreeAdjacencySide v w h) = w) ∨
    (B.intrinsicBoundaryGraphSideStart (B.intrinsicBoundaryTreeAdjacencySide v w h) = w ∧
      B.intrinsicBoundaryGraphSideEnd (B.intrinsicBoundaryTreeAdjacencySide v w h) = v) :=
  Classical.choose_spec (Internal.SurfaceBoundaryGraphCombinatoricsHelpers.exists_side_of_tree_adj B h)

end

end SystolicGrowth.DirichletBoundarySegments
