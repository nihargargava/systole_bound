module

public import Geometry.SurfaceBoundaryGraphCombinatorics

@[expose] public section

/-! Literal paths in the actual paired-side graph and rooted physical tree connectors.
These construct based side loops, without assuming a free fundamental-group presentation. -/

open Set UpperHalfPlane
open scoped Pointwise UpperHalfPlane

namespace SystolicGrowth.DirichletBoundarySegments

noncomputable section

variable {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}

local instance (B : DirichletBoundarySegments X o) : DecidableEq B.IntrinsicBoundaryGraphVertex :=
  Classical.decEq _

/-- The unchanged physical paired-interval realization. -/
abbrev IntrinsicBoundaryGraph (B : DirichletBoundarySegments X o) :=
  Quotient B.intrinsicBoundaryIntervalSetoid

/-- The literal quotient of the actual side interval, between its true vertex classes. -/
def intrinsicBoundaryGraphSidePath (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    Path (B.intrinsicBoundaryGraphVertexInclusion (B.intrinsicBoundaryGraphSideStart i))
      (B.intrinsicBoundaryGraphVertexInclusion (B.intrinsicBoundaryGraphSideEnd i)) where
  toFun t := Quotient.mk B.intrinsicBoundaryIntervalSetoid (i, t)
  continuous_toFun := continuous_quot_mk.comp (continuous_const.prodMk continuous_id)
  source' := rfl
  target' := (B.intrinsicBoundaryGraphVertexInclusion_end i).symm

@[simp]
theorem intrinsicBoundaryGraphSidePath_apply (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) (t : unitInterval) :
    B.intrinsicBoundaryGraphSidePath i t =
      Quotient.mk B.intrinsicBoundaryIntervalSetoid (i, t) := rfl

/-- The original physical pairing identifies precisely the reversed interval parameter. -/
theorem intrinsicBoundaryGraphSidePath_pair (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    (B.intrinsicBoundaryGraphSidePath (B.intrinsicCyclicPairing i)).cast
        (congrArg B.intrinsicBoundaryGraphVertexInclusion
          (B.intrinsicBoundaryGraphSide_pair_endpoints i).1).symm
        (congrArg B.intrinsicBoundaryGraphVertexInclusion
          (B.intrinsicBoundaryGraphSide_pair_endpoints i).2).symm =
      (B.intrinsicBoundaryGraphSidePath i).symm := by
  apply Path.ext
  funext t
  change Quotient.mk B.intrinsicBoundaryIntervalSetoid (B.intrinsicCyclicPairing i, t) =
    Quotient.mk B.intrinsicBoundaryIntervalSetoid (i, unitInterval.symm t)
  apply Eq.symm
  apply Quotient.sound
  apply (B.intrinsicBoundaryIntervalSetoid_iff _ _).2
  apply Or.inr ∘ Or.inl
  simp only [intrinsicBoundaryIntervalPair, unitInterval.symm_symm]

theorem Internal.SurfaceBoundaryGraphPathsHelpers.exists_physical_side_of_tree_edge (B : DirichletBoundarySegments X o)
    (e : B.intrinsicBoundarySpanningTree.edgeSet) :
    ∃ i : Fin B.intrinsicBoundaryRadialCuts.card,
      s(B.intrinsicBoundaryGraphSideStart i, B.intrinsicBoundaryGraphSideEnd i) = e.val := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.inductionOn with
  | _ v w =>
    have h : B.intrinsicBoundarySpanningTree.Adj v w :=
      (B.intrinsicBoundarySpanningTree.mem_edgeSet).mp he
    refine ⟨B.intrinsicBoundaryTreeAdjacencySide v w h, ?_⟩
    exact Sym2.eq_iff.mpr (B.intrinsicBoundaryTreeAdjacencySide_endpoints v w h)

/-- A physical side selected once per undirected tree edge. Reverse traversals therefore
use the same physical interval, not a potentially different parallel side. -/
def intrinsicBoundaryTreeEdgeSide (B : DirichletBoundarySegments X o)
    (e : B.intrinsicBoundarySpanningTree.edgeSet) :
    Fin B.intrinsicBoundaryRadialCuts.card :=
  Classical.choose (Internal.SurfaceBoundaryGraphPathsHelpers.exists_physical_side_of_tree_edge B e)

theorem intrinsicBoundaryTreeEdgeSide_endpoints (B : DirichletBoundarySegments X o)
    (e : B.intrinsicBoundarySpanningTree.edgeSet) :
    s(B.intrinsicBoundaryGraphSideStart (B.intrinsicBoundaryTreeEdgeSide e),
      B.intrinsicBoundaryGraphSideEnd (B.intrinsicBoundaryTreeEdgeSide e)) = e.val :=
  Classical.choose_spec (Internal.SurfaceBoundaryGraphPathsHelpers.exists_physical_side_of_tree_edge B e)

theorem intrinsicBoundaryTreeEdgeSide_injective (B : DirichletBoundarySegments X o) :
    Function.Injective B.intrinsicBoundaryTreeEdgeSide := by
  intro e f h
  apply Subtype.ext
  rw [← B.intrinsicBoundaryTreeEdgeSide_endpoints e,
    ← B.intrinsicBoundaryTreeEdgeSide_endpoints f, h]

/-- Distinct tree choices cannot accidentally select the two orientations of one physical edge. -/
theorem intrinsicBoundaryTreeEdgeSide_ne_pair (B : DirichletBoundarySegments X o)
    (e f : B.intrinsicBoundarySpanningTree.edgeSet) :
    B.intrinsicBoundaryTreeEdgeSide e ≠ B.intrinsicCyclicPairing (B.intrinsicBoundaryTreeEdgeSide f) := by
  intro h
  have hef : e = f := by
    apply Subtype.ext
    rw [← B.intrinsicBoundaryTreeEdgeSide_endpoints e,
      ← B.intrinsicBoundaryTreeEdgeSide_endpoints f, h]
    rw [(B.intrinsicBoundaryGraphSide_pair_endpoints _).1,
      (B.intrinsicBoundaryGraphSide_pair_endpoints _).2, Sym2.eq_swap]
  exact B.intrinsicCyclicPairing_ne_self _
    (h.symm.trans (congrArg B.intrinsicBoundaryTreeEdgeSide hef))

theorem intrinsicBoundaryTreeEdgeSide_adj (B : DirichletBoundarySegments X o)
    (e : B.intrinsicBoundarySpanningTree.edgeSet) :
    B.intrinsicBoundarySpanningTree.Adj
      (B.intrinsicBoundaryGraphSideStart (B.intrinsicBoundaryTreeEdgeSide e))
      (B.intrinsicBoundaryGraphSideEnd (B.intrinsicBoundaryTreeEdgeSide e)) := by
  apply (B.intrinsicBoundarySpanningTree.mem_edgeSet).mp
  rw [B.intrinsicBoundaryTreeEdgeSide_endpoints e]
  exact e.property

theorem Internal.SurfaceBoundaryGraphPathsHelpers.tree_side_endpoints (B : DirichletBoundarySegments X o)
    {v w : B.IntrinsicBoundaryGraphVertex} (h : B.intrinsicBoundarySpanningTree.Adj v w) :
    let i := B.intrinsicBoundaryTreeEdgeSide
      ⟨s(v, w), (B.intrinsicBoundarySpanningTree.mem_edgeSet).mpr h⟩
    (B.intrinsicBoundaryGraphSideStart i = v ∧ B.intrinsicBoundaryGraphSideEnd i = w) ∨
      (B.intrinsicBoundaryGraphSideStart i = w ∧ B.intrinsicBoundaryGraphSideEnd i = v) :=
  Sym2.eq_iff.mp (B.intrinsicBoundaryTreeEdgeSide_endpoints _)

/-- An actual path realizing an oriented adjacency in the selected spanning tree. -/
def intrinsicBoundaryTreeAdjacencyPath (B : DirichletBoundarySegments X o)
    {v w : B.IntrinsicBoundaryGraphVertex} (h : B.intrinsicBoundarySpanningTree.Adj v w) :
    Path (B.intrinsicBoundaryGraphVertexInclusion v)
      (B.intrinsicBoundaryGraphVertexInclusion w) := by
  classical
  let i := B.intrinsicBoundaryTreeEdgeSide
    ⟨s(v, w), (B.intrinsicBoundarySpanningTree.mem_edgeSet).mpr h⟩
  have hends : (B.intrinsicBoundaryGraphSideStart i = v ∧ B.intrinsicBoundaryGraphSideEnd i = w) ∨
      (B.intrinsicBoundaryGraphSideStart i = w ∧ B.intrinsicBoundaryGraphSideEnd i = v) :=
    Internal.SurfaceBoundaryGraphPathsHelpers.tree_side_endpoints B h
  refine
    { toFun := fun t ↦ if B.intrinsicBoundaryGraphSideStart i = v then
        B.intrinsicBoundaryGraphSidePath i t else (B.intrinsicBoundaryGraphSidePath i).symm t
      continuous_toFun := ?_
      source' := ?_
      target' := ?_ }
  · by_cases hi : B.intrinsicBoundaryGraphSideStart i = v
    · simpa only [if_pos hi] using (B.intrinsicBoundaryGraphSidePath i).continuous
    · simpa only [if_neg hi] using (B.intrinsicBoundaryGraphSidePath i).symm.continuous
  · rcases hends with ⟨hv, hw⟩ | ⟨hw, hv⟩
    · simp only [Path.source]
      rw [if_pos hv, hv]
    · have hi : B.intrinsicBoundaryGraphSideStart i ≠ v := fun hi ↦ h.ne (hi.symm.trans hw)
      simp only [Path.source]
      rw [if_neg hi, hv]
  · rcases hends with ⟨hv, hw⟩ | ⟨hw, hv⟩
    · simp only [Path.target]
      rw [if_pos hv, hw]
    · have hi : B.intrinsicBoundaryGraphSideStart i ≠ v := fun hi ↦ h.ne (hi.symm.trans hw)
      simp only [Path.target]
      rw [if_neg hi, hw]

theorem intrinsicBoundaryTreeAdjacencyPath_apply (B : DirichletBoundarySegments X o)
    {v w : B.IntrinsicBoundaryGraphVertex} (h : B.intrinsicBoundarySpanningTree.Adj v w)
    (t : unitInterval) :
    let i := B.intrinsicBoundaryTreeEdgeSide
      ⟨s(v, w), (B.intrinsicBoundarySpanningTree.mem_edgeSet).mpr h⟩
    B.intrinsicBoundaryTreeAdjacencyPath h t =
      if B.intrinsicBoundaryGraphSideStart i = v then
        Quotient.mk B.intrinsicBoundaryIntervalSetoid (i, t) else
        Quotient.mk B.intrinsicBoundaryIntervalSetoid (i, unitInterval.symm t) := by
  classical
  rfl

/-- Traversing a tree edge backwards is exactly reversal of the same physical path. -/
theorem intrinsicBoundaryTreeAdjacencyPath_symm (B : DirichletBoundarySegments X o)
    {v w : B.IntrinsicBoundaryGraphVertex} (h : B.intrinsicBoundarySpanningTree.Adj v w) :
    B.intrinsicBoundaryTreeAdjacencyPath h.symm =
      (B.intrinsicBoundaryTreeAdjacencyPath h).symm := by
  classical
  have hedge : (⟨s(w, v), (B.intrinsicBoundarySpanningTree.mem_edgeSet).mpr h.symm⟩ :
      B.intrinsicBoundarySpanningTree.edgeSet) =
      ⟨s(v, w), (B.intrinsicBoundarySpanningTree.mem_edgeSet).mpr h⟩ :=
    Subtype.ext Sym2.eq_swap
  let i := B.intrinsicBoundaryTreeEdgeSide
    ⟨s(v, w), (B.intrinsicBoundarySpanningTree.mem_edgeSet).mpr h⟩
  apply Path.ext
  funext t
  simp only [Path.symm_apply, Function.comp_apply, intrinsicBoundaryTreeAdjacencyPath_apply]
  rw [hedge]
  simp only [unitInterval.symm_symm]
  change (if B.intrinsicBoundaryGraphSideStart i = w then
      Quotient.mk B.intrinsicBoundaryIntervalSetoid (i, t) else
      Quotient.mk B.intrinsicBoundaryIntervalSetoid (i, unitInterval.symm t)) =
    if B.intrinsicBoundaryGraphSideStart i = v then
      Quotient.mk B.intrinsicBoundaryIntervalSetoid (i, unitInterval.symm t) else
      Quotient.mk B.intrinsicBoundaryIntervalSetoid (i, t)
  have hends : (B.intrinsicBoundaryGraphSideStart i = v ∧ B.intrinsicBoundaryGraphSideEnd i = w) ∨
      (B.intrinsicBoundaryGraphSideStart i = w ∧ B.intrinsicBoundaryGraphSideEnd i = v) :=
    Internal.SurfaceBoundaryGraphPathsHelpers.tree_side_endpoints B h
  rcases hends with ⟨hv, hw⟩ | ⟨hw, hv⟩
  · have hi : B.intrinsicBoundaryGraphSideStart i ≠ w := fun hi ↦ h.ne (hv.symm.trans hi)
    simp only [if_pos hv, if_neg hi]
  · have hi : B.intrinsicBoundaryGraphSideStart i ≠ v := fun hi ↦ h.ne (hi.symm.trans hw)
    simp only [if_pos hw, if_neg hi]

/-- The forward path along the selected tree side is literally its original interval path. -/
theorem intrinsicBoundaryTreeAdjacencyPath_selected (B : DirichletBoundarySegments X o)
    (e : B.intrinsicBoundarySpanningTree.edgeSet) :
    B.intrinsicBoundaryTreeAdjacencyPath (B.intrinsicBoundaryTreeEdgeSide_adj e) =
      B.intrinsicBoundaryGraphSidePath (B.intrinsicBoundaryTreeEdgeSide e) := by
  have hedge : (⟨s(B.intrinsicBoundaryGraphSideStart (B.intrinsicBoundaryTreeEdgeSide e),
      B.intrinsicBoundaryGraphSideEnd (B.intrinsicBoundaryTreeEdgeSide e)),
      (B.intrinsicBoundarySpanningTree.mem_edgeSet).mpr (B.intrinsicBoundaryTreeEdgeSide_adj e)⟩ :
      B.intrinsicBoundarySpanningTree.edgeSet) = e :=
    Subtype.ext (B.intrinsicBoundaryTreeEdgeSide_endpoints e)
  apply Path.ext
  funext t
  rw [intrinsicBoundaryTreeAdjacencyPath_apply, hedge]
  simp
  rfl

/-- Realize every walk in the selected tree by concatenating its actual physical sides. -/
def intrinsicBoundaryTreeWalkPath (B : DirichletBoundarySegments X o)
    {v w : B.IntrinsicBoundaryGraphVertex} (p : B.intrinsicBoundarySpanningTree.Walk v w) :
    Path (B.intrinsicBoundaryGraphVertexInclusion v)
      (B.intrinsicBoundaryGraphVertexInclusion w) :=
  match p with
  | .nil => Path.refl _
  | .cons h p => (B.intrinsicBoundaryTreeAdjacencyPath h).trans (B.intrinsicBoundaryTreeWalkPath p)

@[simp]
theorem intrinsicBoundaryTreeWalkPath_nil (B : DirichletBoundarySegments X o)
    (v : B.IntrinsicBoundaryGraphVertex) :
    B.intrinsicBoundaryTreeWalkPath (.nil : B.intrinsicBoundarySpanningTree.Walk v v) =
      Path.refl (B.intrinsicBoundaryGraphVertexInclusion v) := rfl

@[simp]
theorem intrinsicBoundaryTreeWalkPath_cons (B : DirichletBoundarySegments X o)
    {u v w : B.IntrinsicBoundaryGraphVertex} (h : B.intrinsicBoundarySpanningTree.Adj u v)
    (p : B.intrinsicBoundarySpanningTree.Walk v w) :
    B.intrinsicBoundaryTreeWalkPath (.cons h p) =
      (B.intrinsicBoundaryTreeAdjacencyPath h).trans (B.intrinsicBoundaryTreeWalkPath p) := rfl

/-- Combinatorial walk concatenation realizes actual path concatenation up to the
necessary reparametrization homotopy. -/
theorem intrinsicBoundaryTreeWalkPath_append_homotopic (B : DirichletBoundarySegments X o)
    {u v w : B.IntrinsicBoundaryGraphVertex} (p : B.intrinsicBoundarySpanningTree.Walk u v)
    (q : B.intrinsicBoundarySpanningTree.Walk v w) :
    (B.intrinsicBoundaryTreeWalkPath (p.append q)).Homotopic
      ((B.intrinsicBoundaryTreeWalkPath p).trans (B.intrinsicBoundaryTreeWalkPath q)) := by
  induction p with
  | nil => exact (Path.Homotopic.refl_trans (B.intrinsicBoundaryTreeWalkPath q)).symm
  | cons h p ih =>
    exact ((Path.Homotopic.refl (B.intrinsicBoundaryTreeAdjacencyPath h)).hcomp (ih q)).trans
      (Path.Homotopic.trans_assoc (B.intrinsicBoundaryTreeAdjacencyPath h)
        (B.intrinsicBoundaryTreeWalkPath p) (B.intrinsicBoundaryTreeWalkPath q)).symm

/-- Reversing an entire tree walk reverses its actual physical path up to homotopy. -/
theorem intrinsicBoundaryTreeWalkPath_reverse_homotopic (B : DirichletBoundarySegments X o)
    {v w : B.IntrinsicBoundaryGraphVertex} (p : B.intrinsicBoundarySpanningTree.Walk v w) :
    (B.intrinsicBoundaryTreeWalkPath p.reverse).Homotopic
      (B.intrinsicBoundaryTreeWalkPath p).symm := by
  induction p with
  | nil => exact Path.Homotopic.refl _
  | cons h p ih =>
    rw [SimpleGraph.Walk.reverse_cons]
    have hlast : (B.intrinsicBoundaryTreeWalkPath (.cons h.symm .nil)).Homotopic
        (B.intrinsicBoundaryTreeAdjacencyPath h).symm := by
      rw [intrinsicBoundaryTreeWalkPath_cons, intrinsicBoundaryTreeWalkPath_nil,
        intrinsicBoundaryTreeAdjacencyPath_symm]
      exact Path.Homotopic.trans_refl _
    simpa only [intrinsicBoundaryTreeWalkPath_cons, Path.trans_symm] using
      (B.intrinsicBoundaryTreeWalkPath_append_homotopic p.reverse (.cons h.symm .nil)).trans
        (ih.hcomp hlast)

/-- The unique simple combinatorial tree path from a chosen actual root vertex. -/
def intrinsicBoundaryRootedTreeWalk (B : DirichletBoundarySegments X o)
    (r v : B.IntrinsicBoundaryGraphVertex) : B.intrinsicBoundarySpanningTree.Walk r v :=
  Classical.choose (B.intrinsicBoundarySpanningTree_isTree.existsUnique_path r v)

theorem intrinsicBoundaryRootedTreeWalk_isPath (B : DirichletBoundarySegments X o)
    (r v : B.IntrinsicBoundaryGraphVertex) : (B.intrinsicBoundaryRootedTreeWalk r v).IsPath :=
  (Classical.choose_spec (B.intrinsicBoundarySpanningTree_isTree.existsUnique_path r v)).1

/-- Every simple tree walk is the chosen unique simple walk with its actual endpoints. -/
theorem intrinsicBoundaryRootedTreeWalk_eq_of_isPath (B : DirichletBoundarySegments X o)
    {r v : B.IntrinsicBoundaryGraphVertex} {p : B.intrinsicBoundarySpanningTree.Walk r v}
    (hp : p.IsPath) : p = B.intrinsicBoundaryRootedTreeWalk r v :=
  (B.intrinsicBoundarySpanningTree_isTree.existsUnique_path r v).unique hp
    (B.intrinsicBoundaryRootedTreeWalk_isPath r v)

private theorem rootedTreeWalk_cons_of_length_le (B : DirichletBoundarySegments X o)
    (r : B.IntrinsicBoundaryGraphVertex) {v w : B.IntrinsicBoundaryGraphVertex}
    (h : B.intrinsicBoundarySpanningTree.Adj v w)
    (hlen : (B.intrinsicBoundaryRootedTreeWalk v r).length ≤
      (B.intrinsicBoundaryRootedTreeWalk w r).length) :
    B.intrinsicBoundaryRootedTreeWalk w r = .cons h.symm (B.intrinsicBoundaryRootedTreeWalk v r) := by
  have hvpath := B.intrinsicBoundaryRootedTreeWalk_isPath v r
  have hnmem : w ∉ (B.intrinsicBoundaryRootedTreeWalk v r).support := by
    intro hw
    have htake : (B.intrinsicBoundaryRootedTreeWalk v r).takeUntil w hw = .cons h .nil :=
      (B.intrinsicBoundarySpanningTree_isTree.existsUnique_path v w).unique
        (hvpath.takeUntil hw) (SimpleGraph.Walk.IsPath.nil.cons (by simpa using h.ne))
    have hdrop : (B.intrinsicBoundaryRootedTreeWalk v r).dropUntil w hw =
        B.intrinsicBoundaryRootedTreeWalk w r :=
      B.intrinsicBoundaryRootedTreeWalk_eq_of_isPath (hvpath.dropUntil hw)
    rw [← SimpleGraph.Walk.take_spec (B.intrinsicBoundaryRootedTreeWalk v r) hw,
      htake, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons,
      SimpleGraph.Walk.length_nil, hdrop] at hlen
    omega
  exact (B.intrinsicBoundarySpanningTree_isTree.existsUnique_path w r).unique
    (B.intrinsicBoundaryRootedTreeWalk_isPath w r) (hvpath.cons hnmem)

@[simp]
theorem intrinsicBoundaryRootedTreeWalk_root (B : DirichletBoundarySegments X o)
    (r : B.IntrinsicBoundaryGraphVertex) : B.intrinsicBoundaryRootedTreeWalk r r = .nil :=
  (SimpleGraph.Walk.isPath_iff_nil.mp (B.intrinsicBoundaryRootedTreeWalk_isPath r r)).eq_nil

/-- Actual rooted connector paths in the physical realization of the selected tree. -/
def intrinsicBoundaryTreeConnector (B : DirichletBoundarySegments X o)
    (r v : B.IntrinsicBoundaryGraphVertex) :
    Path (B.intrinsicBoundaryGraphVertexInclusion r)
      (B.intrinsicBoundaryGraphVertexInclusion v) :=
  B.intrinsicBoundaryTreeWalkPath (B.intrinsicBoundaryRootedTreeWalk r v)

@[simp]
theorem intrinsicBoundaryTreeConnector_root (B : DirichletBoundarySegments X o)
    (r : B.IntrinsicBoundaryGraphVertex) : B.intrinsicBoundaryTreeConnector r r =
      Path.refl (B.intrinsicBoundaryGraphVertexInclusion r) := by
  simp only [intrinsicBoundaryTreeConnector, intrinsicBoundaryRootedTreeWalk_root,
    intrinsicBoundaryTreeWalkPath_nil]

/-- One physical tree edge followed by the unique connector to an actual endpoint is
homotopic to the unique connector from its other endpoint. -/
theorem intrinsicBoundaryTreeAdjacencyPath_connector_homotopic
    (B : DirichletBoundarySegments X o) (r : B.IntrinsicBoundaryGraphVertex)
    {v w : B.IntrinsicBoundaryGraphVertex} (h : B.intrinsicBoundarySpanningTree.Adj v w) :
    ((B.intrinsicBoundaryTreeAdjacencyPath h).trans (B.intrinsicBoundaryTreeConnector w r)).Homotopic
      (B.intrinsicBoundaryTreeConnector v r) := by
  change ((B.intrinsicBoundaryTreeAdjacencyPath h).trans
    (B.intrinsicBoundaryTreeWalkPath (B.intrinsicBoundaryRootedTreeWalk w r))).Homotopic
      (B.intrinsicBoundaryTreeWalkPath (B.intrinsicBoundaryRootedTreeWalk v r))
  by_cases hlen : (B.intrinsicBoundaryRootedTreeWalk v r).length ≤
      (B.intrinsicBoundaryRootedTreeWalk w r).length
  · rw [rootedTreeWalk_cons_of_length_le B r h hlen, intrinsicBoundaryTreeWalkPath_cons,
      B.intrinsicBoundaryTreeAdjacencyPath_symm h]
    exact (Path.Homotopic.trans_assoc (B.intrinsicBoundaryTreeAdjacencyPath h)
      (B.intrinsicBoundaryTreeAdjacencyPath h).symm
      (B.intrinsicBoundaryTreeWalkPath (B.intrinsicBoundaryRootedTreeWalk v r))).symm.trans
        (((Path.Homotopic.trans_symm (B.intrinsicBoundaryTreeAdjacencyPath h)).hcomp
          (Path.Homotopic.refl _)).trans (Path.Homotopic.refl_trans _))
  · rw [rootedTreeWalk_cons_of_length_le B r h.symm (le_of_not_ge hlen),
      intrinsicBoundaryTreeWalkPath_cons]

/-- Every actual tree-walk realization is homotopic, relative to its endpoints, to the
unique simple physical tree connector. This removes genuine backtracks, not physical
parallel edges outside the selected tree. -/
theorem intrinsicBoundaryTreeWalkPath_homotopic_connector (B : DirichletBoundarySegments X o)
    {v w : B.IntrinsicBoundaryGraphVertex} (p : B.intrinsicBoundarySpanningTree.Walk v w) :
    (B.intrinsicBoundaryTreeWalkPath p).Homotopic (B.intrinsicBoundaryTreeConnector v w) := by
  induction p with
  | nil =>
    rw [intrinsicBoundaryTreeWalkPath_nil, intrinsicBoundaryTreeConnector_root]
  | @cons v u w h p ih =>
    exact ((Path.Homotopic.refl (B.intrinsicBoundaryTreeAdjacencyPath h)).hcomp ih).trans
      (B.intrinsicBoundaryTreeAdjacencyPath_connector_homotopic w h)

/-- In particular, every actual closed walk in the selected physical tree is nullhomotopic. -/
theorem intrinsicBoundaryTreeWalkPath_closed_homotopic (B : DirichletBoundarySegments X o)
    {r : B.IntrinsicBoundaryGraphVertex} (p : B.intrinsicBoundarySpanningTree.Walk r r) :
    (B.intrinsicBoundaryTreeWalkPath p).Homotopic
      (Path.refl (B.intrinsicBoundaryGraphVertexInclusion r)) := by
  simpa only [intrinsicBoundaryTreeConnector_root] using
    B.intrinsicBoundaryTreeWalkPath_homotopic_connector p

/-- The rooted actual connectors are compatible with appending one physical tree edge. -/
theorem intrinsicBoundaryTreeConnector_adj_homotopic (B : DirichletBoundarySegments X o)
    (r : B.IntrinsicBoundaryGraphVertex) {v w : B.IntrinsicBoundaryGraphVertex}
    (h : B.intrinsicBoundarySpanningTree.Adj v w) :
    ((B.intrinsicBoundaryTreeConnector r v).trans (B.intrinsicBoundaryTreeAdjacencyPath h)).Homotopic
      (B.intrinsicBoundaryTreeConnector r w) := by
  have hsingle : (B.intrinsicBoundaryTreeWalkPath (.cons h .nil)).Homotopic
      (B.intrinsicBoundaryTreeAdjacencyPath h) := Path.Homotopic.trans_refl _
  exact ((Path.Homotopic.refl (B.intrinsicBoundaryTreeConnector r v)).hcomp hsingle.symm).trans
    ((B.intrinsicBoundaryTreeWalkPath_append_homotopic
      (B.intrinsicBoundaryRootedTreeWalk r v) (.cons h .nil)).symm.trans
      (B.intrinsicBoundaryTreeWalkPath_homotopic_connector _))

/-- The actual based side loop, retaining every physical side, including loops and parallel sides. -/
def intrinsicBoundarySideLoop (B : DirichletBoundarySegments X o)
    (r : B.IntrinsicBoundaryGraphVertex) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    Path (B.intrinsicBoundaryGraphVertexInclusion r) (B.intrinsicBoundaryGraphVertexInclusion r) :=
  ((B.intrinsicBoundaryTreeConnector r (B.intrinsicBoundaryGraphSideStart i)).trans
    (B.intrinsicBoundaryGraphSidePath i)).trans
      (B.intrinsicBoundaryTreeConnector r (B.intrinsicBoundaryGraphSideEnd i)).symm

/-- Its class in the based fundamental group of the unchanged physical graph. -/
def intrinsicBoundarySideGenerator (B : DirichletBoundarySegments X o)
    (r : B.IntrinsicBoundaryGraphVertex) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    FundamentalGroup B.IntrinsicBoundaryGraph (B.intrinsicBoundaryGraphVertexInclusion r) :=
  Path.Homotopic.Quotient.mk (B.intrinsicBoundarySideLoop r i)

private theorem rooted_loop_congr {A Y : Type*} [TopologicalSpace Y]
    (f : A → Y) {r : A} (q : (v : A) → Path (f r) (f v))
    {v w v' w' : A} (p : Path (f v) (f w)) (p' : Path (f v') (f w'))
    (hv : v' = v) (hw : w' = w)
    (hp : p'.cast (congrArg f hv).symm (congrArg f hw).symm = p) :
    ((q v').trans p').trans (q w').symm = ((q v).trans p).trans (q w).symm := by
  cases hv
  cases hw
  simp only [Path.cast_rfl_rfl] at hp
  rw [hp]

/-- The original paired side gives the inverse based loop, using the very same rooted
connectors at equal actual vertex classes. Only reassociation requires a homotopy. -/
theorem intrinsicBoundarySideLoop_pair_homotopic (B : DirichletBoundarySegments X o)
    (r : B.IntrinsicBoundaryGraphVertex) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    (B.intrinsicBoundarySideLoop r (B.intrinsicCyclicPairing i)).Homotopic
      (B.intrinsicBoundarySideLoop r i).symm := by
  have heq : B.intrinsicBoundarySideLoop r (B.intrinsicCyclicPairing i) =
      ((B.intrinsicBoundaryTreeConnector r (B.intrinsicBoundaryGraphSideEnd i)).trans
        (B.intrinsicBoundaryGraphSidePath i).symm).trans
        (B.intrinsicBoundaryTreeConnector r (B.intrinsicBoundaryGraphSideStart i)).symm :=
    rooted_loop_congr B.intrinsicBoundaryGraphVertexInclusion (B.intrinsicBoundaryTreeConnector r)
      (B.intrinsicBoundaryGraphSidePath i).symm
      (B.intrinsicBoundaryGraphSidePath (B.intrinsicCyclicPairing i))
      (B.intrinsicBoundaryGraphSide_pair_endpoints i).1
      (B.intrinsicBoundaryGraphSide_pair_endpoints i).2 (B.intrinsicBoundaryGraphSidePath_pair i)
  rw [heq]
  simpa only [intrinsicBoundarySideLoop, Path.trans_symm, Path.symm_symm] using
    Path.Homotopic.trans_assoc
      (B.intrinsicBoundaryTreeConnector r (B.intrinsicBoundaryGraphSideEnd i))
      (B.intrinsicBoundaryGraphSidePath i).symm
      (B.intrinsicBoundaryTreeConnector r (B.intrinsicBoundaryGraphSideStart i)).symm

@[simp]
theorem intrinsicBoundarySideGenerator_pair (B : DirichletBoundarySegments X o)
    (r : B.IntrinsicBoundaryGraphVertex) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundarySideGenerator r (B.intrinsicCyclicPairing i) =
      (B.intrinsicBoundarySideGenerator r i)⁻¹ := by
  change Path.Homotopic.Quotient.mk (B.intrinsicBoundarySideLoop r (B.intrinsicCyclicPairing i)) =
    Path.Homotopic.Quotient.symm (Path.Homotopic.Quotient.mk (B.intrinsicBoundarySideLoop r i))
  rw [← Path.Homotopic.Quotient.mk_symm]
  exact Path.Homotopic.Quotient.eq.mpr (B.intrinsicBoundarySideLoop_pair_homotopic r i)

/-- The based loop of each actually selected physical tree side is nullhomotopic. -/
theorem intrinsicBoundarySideLoop_tree_homotopic (B : DirichletBoundarySegments X o)
    (r : B.IntrinsicBoundaryGraphVertex) (e : B.intrinsicBoundarySpanningTree.edgeSet) :
    (B.intrinsicBoundarySideLoop r (B.intrinsicBoundaryTreeEdgeSide e)).Homotopic
      (Path.refl (B.intrinsicBoundaryGraphVertexInclusion r)) := by
  unfold intrinsicBoundarySideLoop
  rw [← B.intrinsicBoundaryTreeAdjacencyPath_selected e]
  exact ((B.intrinsicBoundaryTreeConnector_adj_homotopic r
    (B.intrinsicBoundaryTreeEdgeSide_adj e)).hcomp (Path.Homotopic.refl _)).trans
      (Path.Homotopic.trans_symm _)

@[simp]
theorem intrinsicBoundarySideGenerator_tree (B : DirichletBoundarySegments X o)
    (r : B.IntrinsicBoundaryGraphVertex) (e : B.intrinsicBoundarySpanningTree.edgeSet) :
    B.intrinsicBoundarySideGenerator r (B.intrinsicBoundaryTreeEdgeSide e) = 1 := by
  change Path.Homotopic.Quotient.mk (B.intrinsicBoundarySideLoop r (B.intrinsicBoundaryTreeEdgeSide e)) =
    Path.Homotopic.Quotient.refl (B.intrinsicBoundaryGraphVertexInclusion r)
  rw [← Path.Homotopic.Quotient.mk_refl]
  exact Path.Homotopic.Quotient.eq.mpr (B.intrinsicBoundarySideLoop_tree_homotopic r e)

@[simp]
theorem intrinsicBoundarySideGenerator_paired_tree (B : DirichletBoundarySegments X o)
    (r : B.IntrinsicBoundaryGraphVertex) (e : B.intrinsicBoundarySpanningTree.edgeSet) :
    B.intrinsicBoundarySideGenerator r
      (B.intrinsicCyclicPairing (B.intrinsicBoundaryTreeEdgeSide e)) = 1 := by
  rw [intrinsicBoundarySideGenerator_pair, intrinsicBoundarySideGenerator_tree, inv_one]

end

end SystolicGrowth.DirichletBoundarySegments
