module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SurfaceBoundaryRootedTreeAdapter

@[expose] public section

/-!
# Enumerating the actual selected tree edges by child vertices

Every edge of a finite tree has a unique endpoint farther from a fixed root.
This file identifies that endpoint with the non-root vertex whose parent edge
it is. The proof uses the actual selected tree and its path-height, and gets
surjectivity from the finite-tree edge count.
-/

open Set UpperHalfPlane
open scoped Pointwise UpperHalfPlane Classical

namespace SystolicGrowth.DirichletBoundarySegments

noncomputable section

variable {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}

/-- Distinct non-root vertices determine distinct parent edges. -/
theorem intrinsicBoundaryRootedTreeChildEdge_injective
    (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex) :
    Function.Injective (B.intrinsicBoundaryRootedTreeChildEdge root) := by
  intro e f hef
  have hsym := congrArg Subtype.val hef
  change s(B.intrinsicBoundaryRootedTreeParent root e.val, e.val) =
      s(B.intrinsicBoundaryRootedTreeParent root f.val, f.val) at hsym
  rcases Sym2.eq_iff.mp hsym with ⟨hparent, hchild⟩ | ⟨hparent, hchild⟩
  · exact Subtype.ext hchild
  · have he := B.intrinsicBoundaryRootedTreeParent_height_succ root e.val e.property
    have hf := B.intrinsicBoundaryRootedTreeParent_height_succ root f.val f.property
    rw [hparent] at he
    rw [← hchild] at hf
    have hcontra :
        B.intrinsicBoundaryRootedTreeHeight root f.val + 1 =
          B.intrinsicBoundaryRootedTreeHeight root e.val ∧
        B.intrinsicBoundaryRootedTreeHeight root e.val + 1 =
          B.intrinsicBoundaryRootedTreeHeight root f.val := ⟨he, hf⟩
    omega

/-- The non-root vertices of the actual spanning tree and its actual edges
have equal cardinality. -/
theorem intrinsicBoundaryRootedTreeChild_card_eq_edgeSet
    (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex) :
    Fintype.card (B.IntrinsicBoundaryRootedTreeChild root) =
      Fintype.card B.intrinsicBoundarySpanningTree.edgeSet := by
  classical
  have hvertices :
      Fintype.card (B.IntrinsicBoundaryRootedTreeChild root) + 1 =
        Fintype.card B.IntrinsicBoundaryGraphVertex := by
    have hrootCard :
        Fintype.card {v : B.IntrinsicBoundaryGraphVertex // v = root} = 1 := by
      classical
      let e : {v : B.IntrinsicBoundaryGraphVertex // v = root} ≃ PUnit.{1} :=
        { toFun := fun _ => PUnit.unit
          invFun := fun _ => ⟨root, rfl⟩
          left_inv := fun x => Subtype.ext x.property.symm
          right_inv := fun x => by cases x; rfl }
      rw [Fintype.card_congr e]
      simp
    rw [Fintype.card_subtype_compl (fun v : B.IntrinsicBoundaryGraphVertex => v = root)]
    rw [hrootCard]
    have hpos : 0 < Fintype.card B.IntrinsicBoundaryGraphVertex := Fintype.card_pos_iff.mpr ⟨root⟩
    omega
  have htree := B.intrinsicBoundarySpanningTree_isTree.card_edgeFinset
  rw [SimpleGraph.edgeFinset_card] at htree
  omega

/-- The parent-edge map is a bijection from non-root vertices to the actual
edge set of the selected tree. -/
theorem intrinsicBoundaryRootedTreeChildEdge_bijective
    (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex) :
    Function.Bijective (B.intrinsicBoundaryRootedTreeChildEdge root) := by
  classical
  apply (Fintype.bijective_iff_injective_and_card _).2
  exact ⟨B.intrinsicBoundaryRootedTreeChildEdge_injective root,
    B.intrinsicBoundaryRootedTreeChild_card_eq_edgeSet root⟩

/-- Every actual selected tree edge has exactly one non-root child endpoint. -/
theorem intrinsicBoundaryRootedTree_existsUnique_child_of_edge
    (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex)
    (edge : B.intrinsicBoundarySpanningTree.edgeSet) :
    ∃! child : B.IntrinsicBoundaryRootedTreeChild root,
      B.intrinsicBoundaryRootedTreeChildEdge root child = edge := by
  obtain ⟨child, hchild⟩ :=
    (B.intrinsicBoundaryRootedTreeChildEdge_bijective root).2 edge
  exact ⟨child, hchild, fun other hother =>
    B.intrinsicBoundaryRootedTreeChildEdge_injective root (hother.trans hchild.symm)⟩

end

end SystolicGrowth.DirichletBoundarySegments

#print axioms SystolicGrowth.DirichletBoundarySegments.intrinsicBoundaryRootedTreeChildEdge_injective
#print axioms SystolicGrowth.DirichletBoundarySegments.intrinsicBoundaryRootedTreeChild_card_eq_edgeSet
#print axioms SystolicGrowth.DirichletBoundarySegments.intrinsicBoundaryRootedTreeChildEdge_bijective
#print axioms SystolicGrowth.DirichletBoundarySegments.intrinsicBoundaryRootedTree_existsUnique_child_of_edge
