module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SurfaceBoundaryGraphActualRootedCycleTree
public import BuserSarnak.FinitePermutationFold

@[expose] public section

/-!
# Native permutation of the actual tree contraction

The regional rotation and physical edge-swap products identify the actual
rooted contraction with the original vertex permutation followed by the
simultaneous selected-tree pairing. The resulting orbit theorem is on the
native side indices used by the peripheral first-return construction.
-/

open Set UpperHalfPlane
open scoped Pointwise UpperHalfPlane Classical

namespace SystolicGrowth.DirichletBoundarySegments

noncomputable section

variable {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}

private theorem treeSplice_foldl_mul {M I : Type*} [Monoid M]
    (l : List I) (f : I → M) (a : M) :
    l.foldl (fun b i => b * f i) a = a * (l.map f).prod := by
  induction l generalizing a with
  | nil => simp
  | cons i l ih =>
      simp only [List.foldl_cons, List.map_cons, List.prod_cons, ih, mul_assoc]

private theorem treeSplice_foldl_congr {I M : Type*}
    (l : List I) (f h : M → I → M) (a : M)
    (heq : ∀ i ∈ l, ∀ b, f b i = h b i) :
    l.foldl f a = l.foldl h a := by
  induction l generalizing a with
  | nil => rfl
  | cons i l ih =>
      simp only [List.foldl_cons]
      rw [heq i List.mem_cons_self]
      exact ih _ (fun j hj => heq j (List.mem_cons_of_mem i hj))

/-- The permutation of every actual subtree contraction is its regional
native rotation followed by the swaps of its internal physical tree edges. -/
theorem intrinsicBoundaryActualRootedCycleContractionTrace_semantics
    (B : DirichletBoundarySegments X o)
    {q : B.IntrinsicBoundaryGraphVertex}
    {merged : List (Fin B.intrinsicBoundaryRadialCuts.card)}
    (trace : SystolicGrowth.RootedCycleContractionTrace
      B.intrinsicBoundaryActualRootedCycleTreeData q merged) :
    merged.formPerm =
      B.intrinsicBoundaryActualRestrictedVertexPerm
        (B.intrinsicBoundaryRootedTreeAncestor B.intrinsicBoundaryRootedTreeRoot q) *
      B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm
        B.intrinsicBoundaryRootedTreeRoot
        (B.intrinsicBoundaryActualRootedTreeStrictDescendantEdge q) := by
  classical
  induction trace with
  | node q childWords merged hchild hn hs hperm hphysical ih =>
      rw [hphysical]
      change (B.intrinsicBoundaryRootedTreeChildren B.intrinsicBoundaryRootedTreeRoot q).foldl
          (fun π e => π * (childWords e).formPerm *
            B.intrinsicBoundaryRootedChildTreeSwap B.intrinsicBoundaryRootedTreeRoot e)
          ((B.intrinsicBoundaryOrderedVertexBlock q).formPerm) = _
      let edges := B.intrinsicBoundaryRootedTreeChildren B.intrinsicBoundaryRootedTreeRoot q
      let rho := fun e : B.IntrinsicBoundaryRootedTreeChild B.intrinsicBoundaryRootedTreeRoot =>
        B.intrinsicBoundaryActualRestrictedVertexPerm
          (B.intrinsicBoundaryRootedTreeAncestor B.intrinsicBoundaryRootedTreeRoot e.val)
      let tau := fun e : B.IntrinsicBoundaryRootedTreeChild B.intrinsicBoundaryRootedTreeRoot =>
        B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm B.intrinsicBoundaryRootedTreeRoot
          (B.intrinsicBoundaryActualRootedTreeStrictDescendantEdge e.val)
      let chi := B.intrinsicBoundaryRootedChildTreeSwap B.intrinsicBoundaryRootedTreeRoot
      let rho0 := (B.intrinsicBoundaryOrderedVertexBlock q).formPerm
      have hfold : edges.foldl
          (fun π e => π * (childWords e).formPerm * chi e) rho0 =
          edges.foldl (fun π e => π * (rho e * tau e) * chi e) rho0 := by
        apply treeSplice_foldl_congr
        intro e he π
        rw [ih e he]
        rfl
      have hsplit := SystolicGrowth.foldl_interleaved_eq_split edges rho tau chi rho0 1
        (by intro e he; exact Commute.one_left _)
        (B.intrinsicBoundaryActualRootedTreeChildren_swap_vertex_commute q)
      simp only [mul_one] at hsplit
      have hswapFold : edges.foldl (fun π e => π * tau e * chi e) 1 =
          (edges.map (fun e => tau e * chi e)).prod := by
        simpa only [mul_assoc, one_mul] using
          treeSplice_foldl_mul edges (fun e => tau e * chi e) 1
      rw [hfold, hsplit, hswapFold, treeSplice_foldl_mul]
      exact congrArg₂ (· * ·)
        (B.intrinsicBoundaryActualRootedTreeChildren_vertexProduct q)
        (B.intrinsicBoundaryActualRootedTreeChildren_swapProduct q)

/-- The root contraction is exactly the native tree-spliced permutation. -/
theorem intrinsicBoundaryActualRootedCycleContractionTrace_root
    (B : DirichletBoundarySegments X o)
    {merged : List (Fin B.intrinsicBoundaryRadialCuts.card)}
    (trace : SystolicGrowth.RootedCycleContractionTrace
      B.intrinsicBoundaryActualRootedCycleTreeData
      B.intrinsicBoundaryRootedTreeRoot merged) :
    merged.formPerm = B.intrinsicBoundaryTreeSplicedVertexPerm := by
  rw [B.intrinsicBoundaryActualRootedCycleContractionTrace_semantics trace,
    B.intrinsicBoundaryActualRestrictedVertexPerm_root,
    B.intrinsicBoundaryActualRootedTreeRoot_swapProduct]
  rfl

/-- The actual native tree-spliced side permutation has one orbit. No global
transitivity or replacement permutation is an input. -/
theorem intrinsicBoundaryTreeSplicedVertexPerm_oneOrbit
    (B : DirichletBoundarySegments X o) :
    ∀ x y : Fin B.intrinsicBoundaryRadialCuts.card,
      ∃ n : ℕ, B.intrinsicBoundaryTreeSplicedVertexPerm^[n] x = y := by
  classical
  obtain ⟨merged, hnodup, hmem, trace⟩ := SystolicGrowth.rootedCycleContraction_exists
    B.intrinsicBoundaryActualRootedCycleTreeData B.intrinsicBoundaryRootedTreeRoot
  have hfull : ∀ d : Fin B.intrinsicBoundaryRadialCuts.card, d ∈ merged := by
    intro d
    apply (hmem d).mpr
    exact B.intrinsicBoundaryRootedTree_root_ancestor B.intrinsicBoundaryRootedTreeRoot
      (B.intrinsicBoundaryGraphSideEnd d)
  have hcard : 2 ≤ Fintype.card (Fin B.intrinsicBoundaryRadialCuts.card) := by
    simpa using le_trans (by decide : 2 ≤ 3) B.three_le_intrinsicBoundaryRadialCuts_card
  rw [← B.intrinsicBoundaryActualRootedCycleContractionTrace_root trace]
  exact SystolicGrowth.list_formPerm_oneOrbit_of_forall_mem merged hnodup hfull hcard

#print axioms intrinsicBoundaryActualRootedCycleContractionTrace_semantics
#print axioms intrinsicBoundaryActualRootedCycleContractionTrace_root
#print axioms intrinsicBoundaryTreeSplicedVertexPerm_oneOrbit

end

end SystolicGrowth.DirichletBoundarySegments
