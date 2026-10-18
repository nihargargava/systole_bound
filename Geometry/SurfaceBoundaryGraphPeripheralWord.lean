module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.Topology.Subpath
public import Mathlib.Data.List.OfFn
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Geometry.SurfaceBoundaryGraphPaths
public import Geometry.DirichletPolarBoundaryLoop

@[expose] public section

/-!
# The original peripheral traversal as a based side word

Rooted connector paths cancel in the fundamental groupoid. This retains the
original ordered sides and the actual root. Mathlib's fundamental-group
multiplication is reverse path composition, so a positively time-ordered
perimeter is the reverse product of its ordered based side generators.
-/

namespace SystolicGrowth

noncomputable section

set_option backward.isDefEq.respectTransparency false in
private theorem rootedPath_trans {Z : Type*} [TopologicalSpace Z] {b x y z : Z}
    (cx : Path b x) (cy : Path b y) (cz : Path b z)
    (p : Path x y) (q : Path y z) :
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((cy.trans q).trans cz.symm)) *
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((cx.trans p).trans cy.symm)) =
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk ((cx.trans (p.trans q)).trans cz.symm)) := by
  change Path.Homotopic.Quotient.trans
      (Path.Homotopic.Quotient.mk ((cx.trans p).trans cy.symm))
      (Path.Homotopic.Quotient.mk ((cy.trans q).trans cz.symm)) =
    Path.Homotopic.Quotient.mk ((cx.trans (p.trans q)).trans cz.symm)
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.trans_assoc]
  rw [← Path.Homotopic.Quotient.trans_assoc
    (Path.Homotopic.Quotient.symm (Path.Homotopic.Quotient.mk cy))
    (Path.Homotopic.Quotient.mk cy),
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]

set_option backward.isDefEq.respectTransparency false in
private theorem rootedPath_concat {Z : Type*} [TopologicalSpace Z] {n : ℕ}
    (v : Fin (n + 1) → Z) (p : ∀ i : Fin n, Path (v i.castSucc) (v i.succ))
    (b : Z) (c : ∀ i : Fin (n + 1), Path b (v i)) :
    FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk
          (((c 0).trans (Path.concat v p)).trans (c (Fin.last n)).symm)) =
      (List.ofFn fun i : Fin n =>
        FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk
            (((c i.castSucc).trans (p i)).trans (c i.succ).symm))).reverse.prod := by
  induction n with
  | zero =>
    simp only [Path.concat_zero, List.ofFn_zero, List.reverse_nil, List.prod_nil]
    change FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      (((c 0).trans (Path.refl (v 0))).trans (c 0).symm)) = 1
    simp only [Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.mk_refl, Path.Homotopic.Quotient.trans_refl,
      Path.Homotopic.Quotient.mk_symm, Path.Homotopic.Quotient.trans_symm]
    rfl
  | succ n ih =>
    rw [Path.concat_succ, List.ofFn_succ', List.concat_eq_append,
      List.reverse_concat, List.prod_cons]
    simp only [← Fin.castSucc_succ, Fin.succ_last]
    rw [← ih (v ∘ Fin.castSucc) (fun i => p i.castSucc)
      (fun i => c i.castSucc)]
    exact (rootedPath_trans (c 0) (c (Fin.last n).castSucc) (c (Fin.last (n + 1)))
      (Path.concat (v ∘ Fin.castSucc) (fun i => p i.castSucc)) (p (Fin.last n))).symm

namespace DirichletBoundarySegments

open scoped UpperHalfPlane

variable {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}

/-- The actual first cyclic vertex, in the original finite orbit-vertex quotient. -/
def intrinsicBoundaryPeripheralRoot (B : DirichletBoundarySegments X o) :
    B.IntrinsicBoundaryGraphVertex :=
  B.intrinsicBoundaryGraphSideStart
    ⟨0, lt_of_lt_of_le (by decide : 0 < 3) B.three_le_intrinsicBoundaryRadialCuts_card⟩

theorem intrinsicBoundaryGraphVertices_zero_eq_root (B : DirichletBoundarySegments X o) :
    B.intrinsicBoundaryGraphVertices 0 =
      B.intrinsicBoundaryGraphVertexInclusion B.intrinsicBoundaryPeripheralRoot :=
  (B.intrinsicBoundaryGraphVertices_castSucc
    ⟨0, lt_of_lt_of_le (by decide : 0 < 3) B.three_le_intrinsicBoundaryRadialCuts_card⟩).trans
      (B.intrinsicBoundaryGraphVertexInclusion_start _).symm

theorem intrinsicBoundaryGraphVertices_last_eq_zero (B : DirichletBoundarySegments X o) :
    B.intrinsicBoundaryGraphVertices (Fin.last B.intrinsicBoundaryRadialCuts.card) =
      B.intrinsicBoundaryGraphVertices 0 :=
  congrArg B.intrinsicBoundaryGraphFrontierMap B.intrinsicBoundaryFrontierVertices_last_eq_zero

theorem Internal.SurfaceBoundaryGraphPeripheralWordHelpers.perimeterVertex_exists (B : DirichletBoundarySegments X o)
    (i : Fin (B.intrinsicBoundaryRadialCuts.card + 1)) :
    ∃ v : B.IntrinsicBoundaryGraphVertex,
      B.intrinsicBoundaryGraphVertexInclusion v = B.intrinsicBoundaryGraphVertices i := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact ⟨B.intrinsicBoundaryPeripheralRoot,
      B.intrinsicBoundaryGraphVertices_zero_eq_root.symm.trans
        B.intrinsicBoundaryGraphVertices_last_eq_zero.symm⟩
  · exact ⟨B.intrinsicBoundaryGraphSideStart j,
      (B.intrinsicBoundaryGraphVertexInclusion_start j).trans
        (B.intrinsicBoundaryGraphVertices_castSucc j).symm⟩

def Internal.SurfaceBoundaryGraphPeripheralWordHelpers.perimeterVertex (B : DirichletBoundarySegments X o)
    (i : Fin (B.intrinsicBoundaryRadialCuts.card + 1)) : B.IntrinsicBoundaryGraphVertex :=
  Classical.choose (Internal.SurfaceBoundaryGraphPeripheralWordHelpers.perimeterVertex_exists B i)

theorem Internal.SurfaceBoundaryGraphPeripheralWordHelpers.perimeterVertex_spec (B : DirichletBoundarySegments X o)
    (i : Fin (B.intrinsicBoundaryRadialCuts.card + 1)) :
    B.intrinsicBoundaryGraphVertexInclusion (Internal.SurfaceBoundaryGraphPeripheralWordHelpers.perimeterVertex B i) =
      B.intrinsicBoundaryGraphVertices i :=
  Classical.choose_spec (Internal.SurfaceBoundaryGraphPeripheralWordHelpers.perimeterVertex_exists B i)

private theorem perimeterVertex_castSucc (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    Internal.SurfaceBoundaryGraphPeripheralWordHelpers.perimeterVertex B i.castSucc = B.intrinsicBoundaryGraphSideStart i := by
  apply B.intrinsicBoundaryGraphVertexInclusion_injective
  exact (Internal.SurfaceBoundaryGraphPeripheralWordHelpers.perimeterVertex_spec B i.castSucc).trans
    ((B.intrinsicBoundaryGraphVertices_castSucc i).trans
      (B.intrinsicBoundaryGraphVertexInclusion_start i).symm)

private theorem perimeterVertex_succ (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    Internal.SurfaceBoundaryGraphPeripheralWordHelpers.perimeterVertex B i.succ = B.intrinsicBoundaryGraphSideEnd i := by
  apply B.intrinsicBoundaryGraphVertexInclusion_injective
  exact (Internal.SurfaceBoundaryGraphPeripheralWordHelpers.perimeterVertex_spec B i.succ).trans
    ((B.intrinsicBoundaryGraphVertices_succ i).trans
      (B.intrinsicBoundaryGraphVertexInclusion_end i).symm)

private theorem perimeterVertex_zero (B : DirichletBoundarySegments X o) :
    Internal.SurfaceBoundaryGraphPeripheralWordHelpers.perimeterVertex B 0 = B.intrinsicBoundaryPeripheralRoot := by
  apply B.intrinsicBoundaryGraphVertexInclusion_injective
  exact (Internal.SurfaceBoundaryGraphPeripheralWordHelpers.perimeterVertex_spec B 0).trans B.intrinsicBoundaryGraphVertices_zero_eq_root

private theorem perimeterVertex_last (B : DirichletBoundarySegments X o) :
    Internal.SurfaceBoundaryGraphPeripheralWordHelpers.perimeterVertex B (Fin.last B.intrinsicBoundaryRadialCuts.card) =
      B.intrinsicBoundaryPeripheralRoot := by
  apply B.intrinsicBoundaryGraphVertexInclusion_injective
  exact (Internal.SurfaceBoundaryGraphPeripheralWordHelpers.perimeterVertex_spec B _).trans
    (B.intrinsicBoundaryGraphVertices_last_eq_zero.trans
      B.intrinsicBoundaryGraphVertices_zero_eq_root)

def Internal.SurfaceBoundaryGraphPeripheralWordHelpers.perimeterConnector (B : DirichletBoundarySegments X o)
    (r : B.IntrinsicBoundaryGraphVertex) (i : Fin (B.intrinsicBoundaryRadialCuts.card + 1)) :
    Path (B.intrinsicBoundaryGraphVertexInclusion r) (B.intrinsicBoundaryGraphVertices i) :=
  (B.intrinsicBoundaryTreeConnector r (Internal.SurfaceBoundaryGraphPeripheralWordHelpers.perimeterVertex B i)).cast
    rfl (Internal.SurfaceBoundaryGraphPeripheralWordHelpers.perimeterVertex_spec B i).symm

private theorem perimeterConnector_castSucc_apply (B : DirichletBoundarySegments X o)
    (r : B.IntrinsicBoundaryGraphVertex) (i : Fin B.intrinsicBoundaryRadialCuts.card)
    (t : unitInterval) :
    Internal.SurfaceBoundaryGraphPeripheralWordHelpers.perimeterConnector B r i.castSucc t =
      B.intrinsicBoundaryTreeConnector r (B.intrinsicBoundaryGraphSideStart i) t :=
  congrArg (fun v => B.intrinsicBoundaryTreeConnector r v t) (perimeterVertex_castSucc B i)

private theorem perimeterConnector_succ_apply (B : DirichletBoundarySegments X o)
    (r : B.IntrinsicBoundaryGraphVertex) (i : Fin B.intrinsicBoundaryRadialCuts.card)
    (t : unitInterval) :
    Internal.SurfaceBoundaryGraphPeripheralWordHelpers.perimeterConnector B r i.succ t =
      B.intrinsicBoundaryTreeConnector r (B.intrinsicBoundaryGraphSideEnd i) t :=
  congrArg (fun v => B.intrinsicBoundaryTreeConnector r v t) (perimeterVertex_succ B i)

private theorem perimeterConnector_zero_apply (B : DirichletBoundarySegments X o)
    (r : B.IntrinsicBoundaryGraphVertex) (t : unitInterval) :
    Internal.SurfaceBoundaryGraphPeripheralWordHelpers.perimeterConnector B r 0 t =
      B.intrinsicBoundaryTreeConnector r B.intrinsicBoundaryPeripheralRoot t :=
  congrArg (fun v => B.intrinsicBoundaryTreeConnector r v t) (perimeterVertex_zero B)

private theorem perimeterConnector_last_apply (B : DirichletBoundarySegments X o)
    (r : B.IntrinsicBoundaryGraphVertex) (t : unitInterval) :
    Internal.SurfaceBoundaryGraphPeripheralWordHelpers.perimeterConnector B r (Fin.last B.intrinsicBoundaryRadialCuts.card) t =
      B.intrinsicBoundaryTreeConnector r B.intrinsicBoundaryPeripheralRoot t :=
  congrArg (fun v => B.intrinsicBoundaryTreeConnector r v t) (perimeterVertex_last B)

/-- The original perimeter, based at an actual tree root by the actual tree connector. -/
def intrinsicBoundaryRootedPerimeterLoop (B : DirichletBoundarySegments X o)
    (r : B.IntrinsicBoundaryGraphVertex) :
    Path (B.intrinsicBoundaryGraphVertexInclusion r) (B.intrinsicBoundaryGraphVertexInclusion r) :=
  ((B.intrinsicBoundaryTreeConnector r B.intrinsicBoundaryPeripheralRoot).trans
    (B.intrinsicBoundaryGraphGeodLoop.cast B.intrinsicBoundaryGraphVertices_zero_eq_root.symm
      B.intrinsicBoundaryGraphVertices_zero_eq_root.symm)).trans
        (B.intrinsicBoundaryTreeConnector r B.intrinsicBoundaryPeripheralRoot).symm

set_option backward.isDefEq.respectTransparency false in
private theorem perimeterSideLoop_eq (B : DirichletBoundarySegments X o)
    (r : B.IntrinsicBoundaryGraphVertex) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    ((Internal.SurfaceBoundaryGraphPeripheralWordHelpers.perimeterConnector B r i.castSucc).trans
      ((B.intrinsicBoundaryFrontierGeodSidePath i).map
        B.intrinsicBoundaryGraphFrontierMap.continuous)).trans
          (Internal.SurfaceBoundaryGraphPeripheralWordHelpers.perimeterConnector B r i.succ).symm = B.intrinsicBoundarySideLoop r i := by
  apply Path.ext
  funext t
  simp only [Path.trans_apply, Path.symm_apply,
    Path.map_coe, Function.comp_apply, perimeterConnector_castSucc_apply, perimeterConnector_succ_apply,
    intrinsicBoundarySideLoop, intrinsicBoundaryGraphFrontierMap_geodSidePath,
    intrinsicBoundaryGraphSidePath_apply]

set_option backward.isDefEq.respectTransparency false in
private theorem perimeterConcatLoop_eq (B : DirichletBoundarySegments X o)
    (r : B.IntrinsicBoundaryGraphVertex) :
    ((Internal.SurfaceBoundaryGraphPeripheralWordHelpers.perimeterConnector B r 0).trans
      (Path.concat B.intrinsicBoundaryGraphVertices (fun i =>
        (B.intrinsicBoundaryFrontierGeodSidePath i).map
          B.intrinsicBoundaryGraphFrontierMap.continuous))).trans
            (Internal.SurfaceBoundaryGraphPeripheralWordHelpers.perimeterConnector B r (Fin.last B.intrinsicBoundaryRadialCuts.card)).symm =
      B.intrinsicBoundaryRootedPerimeterLoop r := by
  rw [intrinsicBoundaryRootedPerimeterLoop, intrinsicBoundaryGraphGeodLoop_eq_concat]
  apply Path.ext
  funext t
  simp only [Path.trans_apply, Path.symm_apply, Path.cast_coe, Function.comp_apply,
    perimeterConnector_zero_apply, perimeterConnector_last_apply]

set_option backward.isDefEq.respectTransparency false in
/-- The original closed perimeter telescopes to the ordered actual side generators.
The reverse product records Mathlib's multiplication convention, not a reversed traversal. -/
theorem intrinsicBoundaryRootedPerimeterLoop_sideWord (B : DirichletBoundarySegments X o)
    (r : B.IntrinsicBoundaryGraphVertex) :
    (⟦B.intrinsicBoundaryRootedPerimeterLoop r⟧ :
      FundamentalGroup B.IntrinsicBoundaryGraph (B.intrinsicBoundaryGraphVertexInclusion r)) =
        (List.ofFn (B.intrinsicBoundarySideGenerator r)).reverse.prod := by
  have h := rootedPath_concat B.intrinsicBoundaryGraphVertices
    (fun i => (B.intrinsicBoundaryFrontierGeodSidePath i).map
      B.intrinsicBoundaryGraphFrontierMap.continuous)
    (B.intrinsicBoundaryGraphVertexInclusion r) (Internal.SurfaceBoundaryGraphPeripheralWordHelpers.perimeterConnector B r)
  simp only [perimeterConcatLoop_eq] at h
  have hl : (fun i : Fin B.intrinsicBoundaryRadialCuts.card =>
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (((Internal.SurfaceBoundaryGraphPeripheralWordHelpers.perimeterConnector B r i.castSucc).trans
          ((B.intrinsicBoundaryFrontierGeodSidePath i).map
            B.intrinsicBoundaryGraphFrontierMap.continuous)).trans
              (Internal.SurfaceBoundaryGraphPeripheralWordHelpers.perimeterConnector B r i.succ).symm))) =
      B.intrinsicBoundarySideGenerator r := by
    funext i
    exact congrArg Path.Homotopic.Quotient.mk (perimeterSideLoop_eq B r i)
  exact h.trans (congrArg (fun f => (List.ofFn f).reverse.prod) hl)

set_option backward.isDefEq.respectTransparency false in
/-- At the original first vertex no connector conjugation remains. The casts identify
only the two proved descriptions of that same original physical basepoint. -/
theorem intrinsicBoundaryGraphGeodLoop_sideWord (B : DirichletBoundarySegments X o) :
    (⟦B.intrinsicBoundaryGraphGeodLoop.cast B.intrinsicBoundaryGraphVertices_zero_eq_root.symm
        B.intrinsicBoundaryGraphVertices_zero_eq_root.symm⟧ :
      FundamentalGroup B.IntrinsicBoundaryGraph
        (B.intrinsicBoundaryGraphVertexInclusion B.intrinsicBoundaryPeripheralRoot)) =
      (List.ofFn (B.intrinsicBoundarySideGenerator B.intrinsicBoundaryPeripheralRoot)).reverse.prod := by
  have h := B.intrinsicBoundaryRootedPerimeterLoop_sideWord B.intrinsicBoundaryPeripheralRoot
  change FundamentalGroup.fromPath
    (Path.Homotopic.Quotient.mk (B.intrinsicBoundaryRootedPerimeterLoop
      B.intrinsicBoundaryPeripheralRoot)) = _ at h
  simp only [intrinsicBoundaryRootedPerimeterLoop, intrinsicBoundaryTreeConnector_root,
    Path.refl_symm, Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_refl,
    Path.Homotopic.Quotient.refl_trans, Path.Homotopic.Quotient.trans_refl] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The word equation at the untouched original perimeter basepoint. The identity-map
transport uses only the proved equality of its two literal point descriptions. -/
theorem intrinsicBoundaryGraphGeodLoop_sideWord_originalBasepoint
    (B : DirichletBoundarySegments X o) :
    (⟦B.intrinsicBoundaryGraphGeodLoop⟧ :
      FundamentalGroup B.IntrinsicBoundaryGraph (B.intrinsicBoundaryGraphVertices 0)) =
      FundamentalGroup.mapOfEq (ContinuousMap.id B.IntrinsicBoundaryGraph)
        B.intrinsicBoundaryGraphVertices_zero_eq_root.symm
        ((List.ofFn (B.intrinsicBoundarySideGenerator B.intrinsicBoundaryPeripheralRoot)).reverse.prod) := by
  rw [← B.intrinsicBoundaryGraphGeodLoop_sideWord]
  symm
  refine (FundamentalGroup.mapOfEq_apply (ContinuousMap.id B.IntrinsicBoundaryGraph)
    B.intrinsicBoundaryGraphVertices_zero_eq_root.symm
    ⟦B.intrinsicBoundaryGraphGeodLoop.cast B.intrinsicBoundaryGraphVertices_zero_eq_root.symm
      B.intrinsicBoundaryGraphVertices_zero_eq_root.symm⟧).trans ?_
  apply congrArg Path.Homotopic.Quotient.mk
  apply Path.ext
  funext t
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual positive polar puncture generator is the ordered physical side
word. Both identity transports use proved descriptions of the same native
basepoint; no change of orientation or assumed free presentation is involved. -/
theorem intrinsicBoundaryGraphFundamentalGroupEquiv_polarOneTurn_sideWord
    (B : DirichletBoundarySegments X o) (r : ℝ) (hr : 0 < r)
    (hsys : 2 * r < X.systole) :
    B.intrinsicBoundaryGraphFundamentalGroupEquiv
        (X.dirichletPuncturePolarCircle o r hr hsys
          (B.intrinsicBoundaryAngularVertices 0))
        ⟦X.dirichletPuncturePolarOneTurn o r hr hsys
          (B.intrinsicBoundaryAngularVertices 0)⟧ =
      FundamentalGroup.mapOfEq (ContinuousMap.id B.IntrinsicBoundaryGraph)
        (B.intrinsicBoundaryGraphPolarBasepoint_eq r hr hsys).symm
        (FundamentalGroup.mapOfEq (ContinuousMap.id B.IntrinsicBoundaryGraph)
          B.intrinsicBoundaryGraphVertices_zero_eq_root.symm
          ((List.ofFn (B.intrinsicBoundarySideGenerator
            B.intrinsicBoundaryPeripheralRoot)).reverse.prod)) := by
  have hword := congrArg
    (FundamentalGroup.mapOfEq (ContinuousMap.id B.IntrinsicBoundaryGraph)
      (B.intrinsicBoundaryGraphPolarBasepoint_eq r hr hsys).symm)
    B.intrinsicBoundaryGraphGeodLoop_sideWord_originalBasepoint
  have hcast : FundamentalGroup.mapOfEq (ContinuousMap.id B.IntrinsicBoundaryGraph)
      (B.intrinsicBoundaryGraphPolarBasepoint_eq r hr hsys).symm
      ⟦B.intrinsicBoundaryGraphGeodLoop⟧ =
        ⟦B.intrinsicBoundaryGraphGeodLoop.cast
          (B.intrinsicBoundaryGraphPolarBasepoint_eq r hr hsys)
          (B.intrinsicBoundaryGraphPolarBasepoint_eq r hr hsys)⟧ := by
    refine (FundamentalGroup.mapOfEq_apply (ContinuousMap.id B.IntrinsicBoundaryGraph)
      (B.intrinsicBoundaryGraphPolarBasepoint_eq r hr hsys).symm
      ⟦B.intrinsicBoundaryGraphGeodLoop⟧).trans ?_
    apply congrArg Path.Homotopic.Quotient.mk
    apply Path.ext
    funext t
    rfl
  exact (B.intrinsicBoundaryGraphFundamentalGroupEquiv_polarOneTurn r hr hsys).trans
    (hcast.symm.trans hword)

end DirichletBoundarySegments

end

end SystolicGrowth
