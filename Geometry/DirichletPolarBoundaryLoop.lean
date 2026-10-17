module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.DirichletCyclicOrientation
public import Geometry.DirichletBoundaryCharts
public import Geometry.DirichletPuncturePolarLoop
public import Geometry.SurfaceBoundaryGraphFundamentalGroup
public import Geometry.GluingSeamFundamentalGroup
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Topology.Subpath

@[expose] public section

/-!
# The positive traversal of the actual Dirichlet boundary

Lift the sorted angular cuts to the real line, adding one positive period
at the final endpoint. Concatenation of the real segments is homotopic to
the straight lift. The native frontier homeomorphism and contractibility
of each actual closed side then identify the positive boundary loop with
the concatenation of the literal cyclic hyperbolic side paths.
-/

open Set UpperHalfPlane
open scoped UpperHalfPlane unitInterval ContinuousMap

namespace SystolicGrowth

noncomputable section

set_option backward.isDefEq.respectTransparency false in
private theorem path_map_concat {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {n : ℕ} (p : Fin (n + 1) → X)
    (F : ∀ k : Fin n, Path (p k.castSucc) (p k.succ))
    (f : X → Y) (hf : Continuous f) :
    (Path.concat p F).map hf =
      Path.concat (fun k => f (p k)) (fun k => (F k).map hf) := by
  induction n with
  | zero =>
    simp only [Path.concat_zero]
    rfl
  | succ n ih =>
    rw [Path.concat_succ, Path.map_trans, Path.concat_succ, ih]
    rfl

def Internal.DirichletPolarBoundaryLoopHelpers.cyclicAngleLift {m : ℕ} (hm : 0 < m) (ξ : Fin m → Circle)
    (i : Fin (m + 1)) : ℝ :=
  if h : (i : ℕ) < m then (ξ ⟨i, h⟩ : ℂ).arg
  else (ξ ⟨0, hm⟩ : ℂ).arg + 2 * Real.pi

private theorem cyclicAngleLift_castSucc {m : ℕ} (hm : 0 < m)
    (ξ : Fin m → Circle) (i : Fin m) :
    Internal.DirichletPolarBoundaryLoopHelpers.cyclicAngleLift hm ξ i.castSucc = (ξ i : ℂ).arg := by
  simp [Internal.DirichletPolarBoundaryLoopHelpers.cyclicAngleLift, i.isLt]

private theorem cyclicAngleLift_zero {m : ℕ} (hm : 0 < m) (ξ : Fin m → Circle) :
    Internal.DirichletPolarBoundaryLoopHelpers.cyclicAngleLift hm ξ 0 = (ξ ⟨0, hm⟩ : ℂ).arg := by
  simp [Internal.DirichletPolarBoundaryLoopHelpers.cyclicAngleLift, hm]

private theorem cyclicAngleLift_last {m : ℕ} (hm : 0 < m) (ξ : Fin m → Circle) :
    Internal.DirichletPolarBoundaryLoopHelpers.cyclicAngleLift hm ξ (Fin.last m) = (ξ ⟨0, hm⟩ : ℂ).arg + 2 * Real.pi := by
  simp [Internal.DirichletPolarBoundaryLoopHelpers.cyclicAngleLift]

set_option backward.isDefEq.respectTransparency false in
private theorem cyclicAngleLift_step {m : ℕ} (hm : 2 ≤ m) (ξ : Fin m → Circle)
    (hξ : StrictMono (fun i => (ξ i : ℂ).arg)) (i : Fin m) :
    Internal.DirichletPolarBoundaryLoopHelpers.cyclicAngleLift (by omega : 0 < m) ξ i.succ =
      Circle.angleDiff (ξ i) (ξ (finRotate m i)) + (ξ i : ℂ).arg := by
  cases m with
  | zero => omega
  | succ n =>
    by_cases hi : i = Fin.last n
    · subst i
      have harg : (ξ (0 : Fin (n + 1)) : ℂ).arg < (ξ (Fin.last n) : ℂ).arg :=
        hξ (show (0 : Fin (n + 1)) < Fin.last n by
        change 0 < n
        omega)
      rw [finRotate_last]
      simp only [Internal.DirichletPolarBoundaryLoopHelpers.cyclicAngleLift, Fin.val_succ, Fin.val_last, lt_self_iff_false,
        ↓reduceDIte, Circle.angleDiff, if_neg (not_le.mpr harg)]
      change (ξ (0 : Fin (n + 1)) : ℂ).arg + 2 * Real.pi =
        2 * Real.pi + (ξ (0 : Fin (n + 1)) : ℂ).arg -
          (ξ (Fin.last n) : ℂ).arg + (ξ (Fin.last n) : ℂ).arg
      ring
    · have hn := Fin.val_lt_last hi
      have hr := coe_finRotate_of_ne_last hi
      have harg := hξ ((lt_finRotate_iff_ne_last i).mpr hi)
      have hindex : (⟨(i : ℕ) + 1, by omega⟩ : Fin (n + 1)) =
          finRotate (n + 1) i := Fin.ext hr.symm
      simp only [Internal.DirichletPolarBoundaryLoopHelpers.cyclicAngleLift, Fin.val_succ, dif_pos (by omega : (i : ℕ) + 1 < n + 1),
        hindex, Circle.angleDiff, if_pos harg.le]
      ring

namespace DirichletBoundarySegments

variable {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
  (B : DirichletBoundarySegments X o)

/-- The actual sorted angles, with one positive period at the closing endpoint. -/
def intrinsicBoundaryAngleLift (i : Fin (B.intrinsicBoundaryRadialCuts.card + 1)) : ℝ :=
  Internal.DirichletPolarBoundaryLoopHelpers.cyclicAngleLift (by have h := B.three_le_intrinsicBoundaryRadialCuts_card; omega)
    (fun k => (B.intrinsicRadialCutEnumeration k).1) i

/-- The actual angular vertices, including the repeated closing vertex. -/
def intrinsicBoundaryAngularVertices
    (i : Fin (B.intrinsicBoundaryRadialCuts.card + 1)) : Circle :=
  Circle.exp (B.intrinsicBoundaryAngleLift i)

theorem intrinsicBoundaryAngularVertices_castSucc
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryAngularVertices i.castSucc =
      (B.intrinsicRadialCutEnumeration i).1 := by
  rw [intrinsicBoundaryAngularVertices, intrinsicBoundaryAngleLift,
    cyclicAngleLift_castSucc, Circle.exp_arg]

theorem intrinsicBoundaryAngularVertices_succ
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryAngularVertices i.succ =
      (B.intrinsicRadialCutEnumeration (finRotate B.intrinsicBoundaryRadialCuts.card i)).1 := by
  rw [intrinsicBoundaryAngularVertices, intrinsicBoundaryAngleLift,
    cyclicAngleLift_step B.two_le_intrinsicBoundaryRadialCuts_card _
      B.intrinsicRadialCutEnumeration_strictMono_arg,
    Circle.exp_add, Circle.exp_arg, Circle.exp_angleDiff_mul]

/-- The positively directed actual angular arc at a cyclic side. -/
def intrinsicBoundaryAngularSidePath (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    Path (B.intrinsicBoundaryAngularVertices i.castSucc)
      (B.intrinsicBoundaryAngularVertices i.succ) :=
  (Path.segment (B.intrinsicBoundaryAngleLift i.castSucc)
    (B.intrinsicBoundaryAngleLift i.succ)).map Circle.exp.continuous

theorem intrinsicBoundaryAngularSidePath_apply
    (i : Fin B.intrinsicBoundaryRadialCuts.card) (t : unitInterval) :
    B.intrinsicBoundaryAngularSidePath i t =
      Circle.path (B.intrinsicRadialCutEnumeration i).1
        (B.intrinsicRadialCutEnumeration (finRotate B.intrinsicBoundaryRadialCuts.card i)).1 t := by
  change Circle.exp (Path.segment _ _ t) = _
  rw [intrinsicBoundaryAngleLift, intrinsicBoundaryAngleLift,
    cyclicAngleLift_castSucc,
    cyclicAngleLift_step B.two_le_intrinsicBoundaryRadialCuts_card _
      B.intrinsicRadialCutEnumeration_strictMono_arg, Circle.path_apply]

theorem intrinsicBoundaryAngularVertices_last_eq_zero :
    B.intrinsicBoundaryAngularVertices (Fin.last B.intrinsicBoundaryRadialCuts.card) =
      B.intrinsicBoundaryAngularVertices 0 := by
  simp only [intrinsicBoundaryAngularVertices, intrinsicBoundaryAngleLift,
    cyclicAngleLift_last, cyclicAngleLift_zero, Circle.exp_add_two_pi]

/-- The ordered angular traversal, with the original first vertex as basepoint. -/
def intrinsicBoundaryAngularLoop :
    Path (B.intrinsicBoundaryAngularVertices 0) (B.intrinsicBoundaryAngularVertices 0) :=
  (Path.concat B.intrinsicBoundaryAngularVertices B.intrinsicBoundaryAngularSidePath).cast
    rfl B.intrinsicBoundaryAngularVertices_last_eq_zero.symm

/-- Sorted consecutive positive arcs traverse the actual circle exactly once. -/
theorem intrinsicBoundaryAngularLoop_homotopic_oneTurn :
    B.intrinsicBoundaryAngularLoop.Homotopic
      (circleOneTurnLoop (B.intrinsicBoundaryAngularVertices 0)) := by
  have h := (SimplyConnectedSpace.paths_homotopic
    (Path.concat B.intrinsicBoundaryAngleLift (fun i =>
      Path.segment (B.intrinsicBoundaryAngleLift i.castSucc)
        (B.intrinsicBoundaryAngleLift i.succ)))
    (Path.segment (B.intrinsicBoundaryAngleLift 0)
      (B.intrinsicBoundaryAngleLift (Fin.last B.intrinsicBoundaryRadialCuts.card)))).map
        ⟨Circle.exp, Circle.exp.continuous⟩
  rw [path_map_concat] at h
  have hcast := h.some.pathCast rfl B.intrinsicBoundaryAngularVertices_last_eq_zero.symm
  refine ⟨hcast.cast rfl ?_⟩
  apply Path.ext
  funext t
  change Circle.exp (AffineMap.lineMap (B.intrinsicBoundaryAngleLift 0)
    (B.intrinsicBoundaryAngleLift (Fin.last B.intrinsicBoundaryRadialCuts.card)) (t : ℝ)) =
      circleOneTurnLoop (B.intrinsicBoundaryAngularVertices 0) t
  rw [circleOneTurnLoop_apply]
  simp only [intrinsicBoundaryAngleLift, cyclicAngleLift_zero, cyclicAngleLift_last,
    intrinsicBoundaryAngularVertices, Circle.exp_arg]
  congr 1
  simp only [AffineMap.lineMap_apply, smul_eq_mul, vsub_eq_sub, vadd_eq_add]
  ring

/-- Actual frontier vertices, with the first vertex repeated at the end. -/
def intrinsicBoundaryFrontierVertices
    (i : Fin (B.intrinsicBoundaryRadialCuts.card + 1)) :
    ↥(frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o)) :=
  (X.dirichletBoundaryRadialHomeomorph o).symm (B.intrinsicBoundaryAngularVertices i)

theorem intrinsicBoundaryFrontierVertices_castSucc
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    (B.intrinsicBoundaryFrontierVertices i.castSucc).1 = B.intrinsicCyclicVertex i := by
  rw [intrinsicBoundaryFrontierVertices, B.intrinsicBoundaryAngularVertices_castSucc]
  rfl

theorem intrinsicBoundaryFrontierVertices_succ
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    (B.intrinsicBoundaryFrontierVertices i.succ).1 =
      B.intrinsicCyclicVertex (finRotate B.intrinsicBoundaryRadialCuts.card i) := by
  rw [intrinsicBoundaryFrontierVertices, B.intrinsicBoundaryAngularVertices_succ]
  rfl

theorem intrinsicCyclicClosedEdge_subset_frontier
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.closedEdgeImage B.intrinsicCornerCuts (B.intrinsicCyclicEdge i) ⊆
      frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) := by
  intro z hz
  rw [← B.iUnion_intrinsicCyclicClosedEdge_eq_frontier]
  exact mem_iUnion.mpr ⟨i, hz⟩

/-- The radial arc on one actual side, valued in the original frontier. -/
def intrinsicBoundaryFrontierRadialSidePath
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    Path (B.intrinsicBoundaryFrontierVertices i.castSucc)
      (B.intrinsicBoundaryFrontierVertices i.succ) :=
  (B.intrinsicBoundaryAngularSidePath i).map
    (X.dirichletBoundaryRadialHomeomorph o).symm.continuous

private theorem intrinsicBoundaryFrontierRadialSidePath_mem
    (i : Fin B.intrinsicBoundaryRadialCuts.card) (t : unitInterval) :
    (B.intrinsicBoundaryFrontierRadialSidePath i t).1 ∈
      Vendored.RiemannDynamics.geodSeg (B.intrinsicCyclicVertex i)
        (B.intrinsicCyclicVertex (finRotate B.intrinsicBoundaryRadialCuts.card i)) := by
  have hmem : B.intrinsicBoundaryAngularSidePath i t ∈
      Set.range (Circle.path (B.intrinsicRadialCutEnumeration i).1
        (B.intrinsicRadialCutEnumeration (finRotate B.intrinsicBoundaryRadialCuts.card i)).1) :=
    ⟨t, (B.intrinsicBoundaryAngularSidePath_apply i t).symm⟩
  rw [← B.intrinsicCyclicEdge_closedRadialImage i,
    ← X.image_radialHomeomorph_preimage_of_subset_frontier o
      (B.intrinsicCyclicClosedEdge_subset_frontier i)] at hmem
  obtain ⟨z, hz, hzeq⟩ := hmem
  have heq : (X.dirichletBoundaryRadialHomeomorph o).symm
      (B.intrinsicBoundaryAngularSidePath i t) = z := by
    rw [← hzeq, Homeomorph.symm_apply_apply]
  change ((X.dirichletBoundaryRadialHomeomorph o).symm
    (B.intrinsicBoundaryAngularSidePath i t)).1 ∈ _
  rw [heq, ← B.intrinsicCyclicEdge_closedImage_eq_geodSeg]
  exact hz

/-- The literal constant-speed hyperbolic path along one original cyclic side. -/
def intrinsicBoundaryFrontierGeodSidePath
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    Path (B.intrinsicBoundaryFrontierVertices i.castSucc)
      (B.intrinsicBoundaryFrontierVertices i.succ) where
  toFun t := ⟨Vendored.RiemannDynamics.geodInterp (B.intrinsicCyclicVertex i)
    (B.intrinsicCyclicVertex (finRotate B.intrinsicBoundaryRadialCuts.card i)) t,
    B.intrinsicCyclicClosedEdge_subset_frontier i (by
      rw [B.intrinsicCyclicEdge_closedImage_eq_geodSeg]
      exact Vendored.RiemannDynamics.geodInterp_mem_geodSeg _ _ t.2)⟩
  continuous_toFun := (Vendored.RiemannDynamics.continuous_geodInterp.comp
    (continuous_const.prodMk (continuous_const.prodMk continuous_subtype_val))).subtype_mk _
  source' := by
    apply Subtype.ext
    change Vendored.RiemannDynamics.geodInterp _ _ 0 = _
    rw [Vendored.RiemannDynamics.geodInterp_zero,
      B.intrinsicBoundaryFrontierVertices_castSucc]
  target' := by
    apply Subtype.ext
    change Vendored.RiemannDynamics.geodInterp _ _ 1 = _
    rw [Vendored.RiemannDynamics.geodInterp_one,
      B.intrinsicBoundaryFrontierVertices_succ]

/-- Both parametrizations are homotopic inside that same actual closed side. -/
theorem intrinsicBoundaryFrontierGeodSidePath_homotopic_radial
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    (B.intrinsicBoundaryFrontierGeodSidePath i).Homotopic
      (B.intrinsicBoundaryFrontierRadialSidePath i) := by
  let a := B.intrinsicCyclicVertex i
  let b := B.intrinsicCyclicVertex (finRotate B.intrinsicBoundaryRadialCuts.card i)
  letI : ContractibleSpace (Set.Icc (0 : ℝ) 1) :=
    (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by norm_num⟩
  letI : SimplyConnectedSpace (Vendored.RiemannDynamics.geodSeg a b) :=
    (geodSegHomeomorph a b (B.intrinsicCyclicVertex_next_ne i)).symm.toHomotopyEquiv.simplyConnectedSpace
  let x : Vendored.RiemannDynamics.geodSeg a b :=
    ⟨(B.intrinsicBoundaryFrontierVertices i.castSucc).1, by
      rw [B.intrinsicBoundaryFrontierVertices_castSucc]
      exact Vendored.RiemannDynamics.left_mem_geodSeg a b⟩
  let y : Vendored.RiemannDynamics.geodSeg a b :=
    ⟨(B.intrinsicBoundaryFrontierVertices i.succ).1, by
      rw [B.intrinsicBoundaryFrontierVertices_succ]
      exact Vendored.RiemannDynamics.right_mem_geodSeg a b⟩
  let p : Path x y :=
    { toFun := fun t => ⟨(B.intrinsicBoundaryFrontierGeodSidePath i t).1,
        Vendored.RiemannDynamics.geodInterp_mem_geodSeg a b t.2⟩
      continuous_toFun :=
        (continuous_subtype_val.comp (B.intrinsicBoundaryFrontierGeodSidePath i).continuous).subtype_mk _
      source' := by
        apply Subtype.ext
        exact congrArg (fun z : ↥(frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o)) =>
          (z : ℍ)) (B.intrinsicBoundaryFrontierGeodSidePath i).source
      target' := by
        apply Subtype.ext
        exact congrArg (fun z : ↥(frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o)) =>
          (z : ℍ)) (B.intrinsicBoundaryFrontierGeodSidePath i).target }
  let q : Path x y :=
    { toFun := fun t => ⟨(B.intrinsicBoundaryFrontierRadialSidePath i t).1,
        B.intrinsicBoundaryFrontierRadialSidePath_mem i t⟩
      continuous_toFun :=
        (continuous_subtype_val.comp (B.intrinsicBoundaryFrontierRadialSidePath i).continuous).subtype_mk _
      source' := by
        apply Subtype.ext
        exact congrArg (fun z : ↥(frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o)) =>
          (z : ℍ)) (B.intrinsicBoundaryFrontierRadialSidePath i).source
      target' := by
        apply Subtype.ext
        exact congrArg (fun z : ↥(frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o)) =>
          (z : ℍ)) (B.intrinsicBoundaryFrontierRadialSidePath i).target }
  let inclusion : C(Vendored.RiemannDynamics.geodSeg a b,
      ↥(frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o))) :=
    ⟨fun z => ⟨z.1, B.intrinsicCyclicClosedEdge_subset_frontier i (by
      rw [B.intrinsicCyclicEdge_closedImage_eq_geodSeg]
      exact z.2)⟩, continuous_subtype_val.subtype_mk _⟩
  have h := (SimplyConnectedSpace.paths_homotopic p q).map inclusion
  have hx : inclusion x = B.intrinsicBoundaryFrontierVertices i.castSucc := rfl
  have hy : inclusion y = B.intrinsicBoundaryFrontierVertices i.succ := rfl
  have hc := h.pathCast hx.symm hy.symm
  have hp : (p.map inclusion.continuous).cast hx.symm hy.symm =
      B.intrinsicBoundaryFrontierGeodSidePath i := by
    apply Path.ext
    funext t
    rfl
  have hq : (q.map inclusion.continuous).cast hx.symm hy.symm =
      B.intrinsicBoundaryFrontierRadialSidePath i := by
    apply Path.ext
    funext t
    rfl
  rw [hp, hq] at hc
  exact hc

theorem intrinsicBoundaryFrontierVertices_last_eq_zero :
    B.intrinsicBoundaryFrontierVertices (Fin.last B.intrinsicBoundaryRadialCuts.card) =
      B.intrinsicBoundaryFrontierVertices 0 :=
  congrArg (X.dirichletBoundaryRadialHomeomorph o).symm
    B.intrinsicBoundaryAngularVertices_last_eq_zero

/-- The literal ordered traversal of every actual hyperbolic boundary side. -/
def intrinsicBoundaryFrontierGeodLoop :
    Path (B.intrinsicBoundaryFrontierVertices 0) (B.intrinsicBoundaryFrontierVertices 0) :=
  (Path.concat B.intrinsicBoundaryFrontierVertices B.intrinsicBoundaryFrontierGeodSidePath).cast
    rfl B.intrinsicBoundaryFrontierVertices_last_eq_zero.symm

private theorem intrinsicBoundaryFrontierRadialConcat_eq :
    (Path.concat B.intrinsicBoundaryFrontierVertices B.intrinsicBoundaryFrontierRadialSidePath).cast
      rfl B.intrinsicBoundaryFrontierVertices_last_eq_zero.symm =
      B.intrinsicBoundaryAngularLoop.map (X.dirichletBoundaryRadialHomeomorph o).symm.continuous := by
  have h := path_map_concat B.intrinsicBoundaryAngularVertices
    B.intrinsicBoundaryAngularSidePath (X.dirichletBoundaryRadialHomeomorph o).symm
      (X.dirichletBoundaryRadialHomeomorph o).symm.continuous
  apply Path.ext
  funext t
  exact congrArg (fun p : Path (B.intrinsicBoundaryFrontierVertices 0)
    (B.intrinsicBoundaryFrontierVertices (Fin.last B.intrinsicBoundaryRadialCuts.card)) =>
      p t) h.symm

/-- The original positive one-turn boundary is the product of the actual
cyclic geodesic side paths, with its precise original basepoint and orientation. -/
theorem intrinsicBoundaryFrontierGeodLoop_homotopic_oneTurn :
    B.intrinsicBoundaryFrontierGeodLoop.Homotopic
      ((circleOneTurnLoop (B.intrinsicBoundaryAngularVertices 0)).map
        (X.dirichletBoundaryRadialHomeomorph o).symm.continuous) := by
  have h := (Path.Homotopic.concat_hcomp B.intrinsicBoundaryFrontierVertices
    B.intrinsicBoundaryFrontierGeodSidePath B.intrinsicBoundaryFrontierRadialSidePath
      B.intrinsicBoundaryFrontierGeodSidePath_homotopic_radial).pathCast
        rfl B.intrinsicBoundaryFrontierVertices_last_eq_zero.symm
  rw [B.intrinsicBoundaryFrontierRadialConcat_eq] at h
  exact h.trans (B.intrinsicBoundaryAngularLoop_homotopic_oneTurn.map
    ⟨(X.dirichletBoundaryRadialHomeomorph o).symm,
      (X.dirichletBoundaryRadialHomeomorph o).symm.continuous⟩)

/-- The actual frontier projection expressed in the physical paired-side graph. -/
def intrinsicBoundaryGraphFrontierMap :
    C(X.DirichletFrontier o, Quotient B.intrinsicBoundaryIntervalSetoid) :=
  (⟨B.intrinsicBoundaryGraphSpineHomeomorph.symm,
    B.intrinsicBoundaryGraphSpineHomeomorph.symm.continuous⟩ :
      C(X.dirichletBoundarySpine o, Quotient B.intrinsicBoundaryIntervalSetoid)).comp
    (X.dirichletFrontierSpineProjection o)

/-- The original cyclic frontier vertices in the actual physical graph. -/
def intrinsicBoundaryGraphVertices
    (i : Fin (B.intrinsicBoundaryRadialCuts.card + 1)) :
    Quotient B.intrinsicBoundaryIntervalSetoid :=
  B.intrinsicBoundaryGraphFrontierMap (B.intrinsicBoundaryFrontierVertices i)

/-- Each literal geodesic side is exactly its physical interval, with no
change of its orientation or unit-interval parameter. -/
theorem intrinsicBoundaryGraphFrontierMap_geodSidePath
    (i : Fin B.intrinsicBoundaryRadialCuts.card) (t : unitInterval) :
    B.intrinsicBoundaryGraphFrontierMap (B.intrinsicBoundaryFrontierGeodSidePath i t) =
      Quotient.mk B.intrinsicBoundaryIntervalSetoid (i, t) := by
  apply B.intrinsicBoundaryGraphSpineHomeomorph.injective
  change B.intrinsicBoundaryGraphSpineHomeomorph
      (B.intrinsicBoundaryGraphSpineHomeomorph.symm
        (X.dirichletFrontierSpineProjection o (B.intrinsicBoundaryFrontierGeodSidePath i t))) = _
  rw [Homeomorph.apply_symm_apply]
  rfl

/-- The starting endpoint remains the literal zero parameter of its side. -/
theorem intrinsicBoundaryGraphVertices_castSucc
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryGraphVertices i.castSucc =
      Quotient.mk B.intrinsicBoundaryIntervalSetoid (i, (0 : unitInterval)) := by
  exact (congrArg B.intrinsicBoundaryGraphFrontierMap
    (B.intrinsicBoundaryFrontierGeodSidePath i).source).symm.trans
      (B.intrinsicBoundaryGraphFrontierMap_geodSidePath i 0)

/-- The terminal endpoint remains the literal one parameter of its side. -/
theorem intrinsicBoundaryGraphVertices_succ
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryGraphVertices i.succ =
      Quotient.mk B.intrinsicBoundaryIntervalSetoid (i, (1 : unitInterval)) := by
  exact (congrArg B.intrinsicBoundaryGraphFrontierMap
    (B.intrinsicBoundaryFrontierGeodSidePath i).target).symm.trans
      (B.intrinsicBoundaryGraphFrontierMap_geodSidePath i 1)

/-- The actual ordered physical traversal of the original paired boundary sides. -/
def intrinsicBoundaryGraphGeodLoop :
    Path (B.intrinsicBoundaryGraphVertices 0) (B.intrinsicBoundaryGraphVertices 0) :=
  B.intrinsicBoundaryFrontierGeodLoop.map B.intrinsicBoundaryGraphFrontierMap.continuous

/-- Mapping the actual perimeter retains its original finite concatenation. -/
theorem intrinsicBoundaryGraphGeodLoop_eq_concat :
    B.intrinsicBoundaryGraphGeodLoop =
      (Path.concat B.intrinsicBoundaryGraphVertices (fun i =>
        (B.intrinsicBoundaryFrontierGeodSidePath i).map
          B.intrinsicBoundaryGraphFrontierMap.continuous)).cast rfl
            (congrArg B.intrinsicBoundaryGraphFrontierMap
              B.intrinsicBoundaryFrontierVertices_last_eq_zero).symm := by
  have h := path_map_concat B.intrinsicBoundaryFrontierVertices
    B.intrinsicBoundaryFrontierGeodSidePath B.intrinsicBoundaryGraphFrontierMap
      B.intrinsicBoundaryGraphFrontierMap.continuous
  apply Path.ext
  funext t
  exact congrArg (fun p => p t) h

/-- The ordered physical side traversal is the original positive frontier turn. -/
theorem intrinsicBoundaryGraphGeodLoop_homotopic_oneTurn :
    B.intrinsicBoundaryGraphGeodLoop.Homotopic
      ((circleOneTurnLoop (B.intrinsicBoundaryAngularVertices 0)).map
        ((B.intrinsicBoundaryGraphFrontierMap).comp
          ⟨(X.dirichletBoundaryRadialHomeomorph o).symm,
            (X.dirichletBoundaryRadialHomeomorph o).symm.continuous⟩).continuous) := by
  exact B.intrinsicBoundaryFrontierGeodLoop_homotopic_oneTurn.map
    B.intrinsicBoundaryGraphFrontierMap

/-- The retracted original polar basepoint is the original first physical vertex. -/
theorem intrinsicBoundaryGraphPolarBasepoint_eq (r : ℝ) (hr : 0 < r)
    (hsys : 2 * r < X.systole) :
    B.intrinsicBoundaryGraphSpineHomeomorph.symm
        (X.dirichletSpineRetraction o
          (X.dirichletPuncturePolarCircle o r hr hsys
            (B.intrinsicBoundaryAngularVertices 0))) =
      B.intrinsicBoundaryGraphVertices 0 := by
  change B.intrinsicBoundaryGraphSpineHomeomorph.symm
      (X.dirichletSpineRetraction o
        (X.dirichletPuncturePolarCircle o r hr hsys
          (B.intrinsicBoundaryAngularVertices 0))) =
    B.intrinsicBoundaryGraphSpineHomeomorph.symm
      (X.dirichletSpineRadialCircle o (B.intrinsicBoundaryAngularVertices 0))
  exact congrArg B.intrinsicBoundaryGraphSpineHomeomorph.symm
    (X.dirichletSpineRetraction_polarCircle o r hr hsys _)

set_option backward.isDefEq.respectTransparency false in
/-- The genuine punctured-surface equivalence takes its actual positive polar
generator to the ordered physical boundary traversal. The only cast is the
proved image of its original basepoint. -/
theorem intrinsicBoundaryGraphFundamentalGroupEquiv_polarOneTurn
    (r : ℝ) (hr : 0 < r) (hsys : 2 * r < X.systole) :
    B.intrinsicBoundaryGraphFundamentalGroupEquiv
        (X.dirichletPuncturePolarCircle o r hr hsys
          (B.intrinsicBoundaryAngularVertices 0))
        ⟦X.dirichletPuncturePolarOneTurn o r hr hsys
          (B.intrinsicBoundaryAngularVertices 0)⟧ =
      ⟦B.intrinsicBoundaryGraphGeodLoop.cast
        (B.intrinsicBoundaryGraphPolarBasepoint_eq r hr hsys)
        (B.intrinsicBoundaryGraphPolarBasepoint_eq r hr hsys)⟧ := by
  refine (B.intrinsicBoundaryGraphFundamentalGroupEquiv_loop
    (X.dirichletPuncturePolarCircle o r hr hsys (B.intrinsicBoundaryAngularVertices 0))
    (X.dirichletPuncturePolarOneTurn o r hr hsys
      (B.intrinsicBoundaryAngularVertices 0))).trans ?_
  apply Quotient.sound
  have hp :
      (((X.dirichletPuncturePolarOneTurn o r hr hsys
          (B.intrinsicBoundaryAngularVertices 0)).map
        (X.dirichletSpineRetraction o).continuous).map
          B.intrinsicBoundaryGraphSpineHomeomorph.symm.continuous).cast
            (B.intrinsicBoundaryGraphPolarBasepoint_eq r hr hsys).symm
            (B.intrinsicBoundaryGraphPolarBasepoint_eq r hr hsys).symm =
        (circleOneTurnLoop (B.intrinsicBoundaryAngularVertices 0)).map
          ((B.intrinsicBoundaryGraphFrontierMap).comp
            ⟨(X.dirichletBoundaryRadialHomeomorph o).symm,
              (X.dirichletBoundaryRadialHomeomorph o).symm.continuous⟩).continuous := by
    apply Path.ext
    funext t
    change B.intrinsicBoundaryGraphSpineHomeomorph.symm
      (X.dirichletSpineRetraction o
        (X.dirichletPuncturePolarCircle o r hr hsys
          (circleOneTurnLoop (B.intrinsicBoundaryAngularVertices 0) t))) = _
    rw [X.dirichletSpineRetraction_polarCircle o r hr hsys]
    rfl
  have h := B.intrinsicBoundaryGraphGeodLoop_homotopic_oneTurn.symm
  rw [← hp] at h
  have hc := h.pathCast (B.intrinsicBoundaryGraphPolarBasepoint_eq r hr hsys)
    (B.intrinsicBoundaryGraphPolarBasepoint_eq r hr hsys)
  exact hc

end DirichletBoundarySegments

end

end SystolicGrowth
