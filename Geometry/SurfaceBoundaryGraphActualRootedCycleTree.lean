module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SurfaceBoundaryGraphLocalCycleBlocks
public import Geometry.SurfaceBoundaryRootedTreeAdapter
public import Geometry.SurfaceBoundaryRootedTreeSwapProduct
public import Geometry.FiniteTreeCycleMerge

@[expose] public section

/-!
# The actual rooted cycle tree has one physical orbit

Instantiate the rooted cycle-contraction theorem with the real selected
spanning tree and the actual terminal-side blocks at quotient vertices. The
block support, rooted ancestry, and size bound are all supplied by proved
geometric/combinatorial APIs rather than hypotheses on a replacement model.
-/

open Set UpperHalfPlane
open scoped Pointwise UpperHalfPlane Classical

namespace SystolicGrowth.DirichletBoundarySegments

noncomputable section

variable {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}

/-- The rooted contraction data built from the actual selected graph tree and
the exact actual terminal-side block at each quotient vertex. -/
def intrinsicBoundaryActualRootedCycleTreeData
    (B : DirichletBoundarySegments X o) :
    SystolicGrowth.RootedCycleTreeData B.IntrinsicBoundaryGraphVertex
      (B.IntrinsicBoundaryRootedTreeChild B.intrinsicBoundaryRootedTreeRoot)
      (Fin B.intrinsicBoundaryRadialCuts.card) := by
  exact B.intrinsicBoundaryRootedCycleTreeData B.intrinsicBoundaryRootedTreeRoot
    B.intrinsicBoundaryOrderedVertexBlock
    B.intrinsicBoundaryOrderedVertexBlock_nodup
    B.intrinsicBoundaryOrderedVertexBlock_mem_iff

/-- Restrict the native vertex transition to a collection of actual quotient
vertices, fixing all side darts outside that collection. -/
def intrinsicBoundaryActualRestrictedVertexPerm
    (B : DirichletBoundarySegments X o)
    (A : B.IntrinsicBoundaryGraphVertex → Prop) :
    Equiv.Perm (Fin B.intrinsicBoundaryRadialCuts.card) := by
  classical
  exact Equiv.Perm.ofSubtype
    (B.intrinsicBoundaryOriginalVertexPerm.subtypePerm
      (p := fun d => A (B.intrinsicBoundaryGraphSideEnd d)) (by
        intro d
        rw [B.intrinsicBoundaryOriginalVertexPerm_preserves_sideEnd]))

theorem intrinsicBoundaryActualRestrictedVertexPerm_apply
    (B : DirichletBoundarySegments X o)
    (A : B.IntrinsicBoundaryGraphVertex → Prop)
    (d : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryActualRestrictedVertexPerm A d =
      if A (B.intrinsicBoundaryGraphSideEnd d) then
        B.intrinsicBoundaryOriginalVertexPerm d else d := by
  classical
  unfold intrinsicBoundaryActualRestrictedVertexPerm
  split_ifs with h
  · rw [Equiv.Perm.ofSubtype_apply_of_mem
      (p := fun d : Fin B.intrinsicBoundaryRadialCuts.card =>
        A (B.intrinsicBoundaryGraphSideEnd d)) _ h]
    rfl
  · exact Equiv.Perm.ofSubtype_apply_of_not_mem _ h

theorem intrinsicBoundaryActualRestrictedVertexPerm_congr
    (B : DirichletBoundarySegments X o)
    {A C : B.IntrinsicBoundaryGraphVertex → Prop}
    (h : ∀ q, A q ↔ C q) :
    B.intrinsicBoundaryActualRestrictedVertexPerm A =
      B.intrinsicBoundaryActualRestrictedVertexPerm C := by
  apply Equiv.ext
  intro d
  simp only [intrinsicBoundaryActualRestrictedVertexPerm_apply, h]

theorem intrinsicBoundaryActualRestrictedVertexPerm_mul
    (B : DirichletBoundarySegments X o)
    (A C : B.IntrinsicBoundaryGraphVertex → Prop)
    (hdis : ∀ q, A q → ¬ C q) :
    B.intrinsicBoundaryActualRestrictedVertexPerm A *
      B.intrinsicBoundaryActualRestrictedVertexPerm C =
    B.intrinsicBoundaryActualRestrictedVertexPerm (fun q => A q ∨ C q) := by
  classical
  apply Equiv.ext
  intro d
  rw [Equiv.Perm.mul_apply,
    intrinsicBoundaryActualRestrictedVertexPerm_apply B A
      (B.intrinsicBoundaryActualRestrictedVertexPerm C d),
    intrinsicBoundaryActualRestrictedVertexPerm_apply B C d,
    intrinsicBoundaryActualRestrictedVertexPerm_apply B (fun q => A q ∨ C q) d]
  by_cases hA : A (B.intrinsicBoundaryGraphSideEnd d)
  · have hC := hdis _ hA
    simp [hA, hC]
  · by_cases hC : C (B.intrinsicBoundaryGraphSideEnd d)
    · simp [hA, hC, B.intrinsicBoundaryOriginalVertexPerm_preserves_sideEnd]
    · simp [hA, hC]

@[simp] theorem intrinsicBoundaryActualRestrictedVertexPerm_false
    (B : DirichletBoundarySegments X o) :
    B.intrinsicBoundaryActualRestrictedVertexPerm (fun _ => False) = 1 := by
  apply Equiv.ext
  intro d
  simp [intrinsicBoundaryActualRestrictedVertexPerm_apply]

theorem intrinsicBoundaryActualRestrictedVertexPerm_list_prod
    (B : DirichletBoundarySegments X o) {I : Type*} (l : List I)
    (A : I → B.IntrinsicBoundaryGraphVertex → Prop)
    (hdis : l.Pairwise (fun i j => ∀ q, A i q → ¬ A j q)) :
    (l.map (fun i => B.intrinsicBoundaryActualRestrictedVertexPerm (A i))).prod =
      B.intrinsicBoundaryActualRestrictedVertexPerm (fun q => ∃ i ∈ l, A i q) := by
  induction l with
  | nil => simp
  | cons i l ih =>
      rw [List.map_cons, List.prod_cons, ih (List.pairwise_cons.mp hdis).2,
        intrinsicBoundaryActualRestrictedVertexPerm_mul]
      · apply intrinsicBoundaryActualRestrictedVertexPerm_congr
        intro q
        simp
      · intro q hi
        rintro ⟨j, hj, hjq⟩
        exact (List.pairwise_cons.mp hdis).1 j hj q hi hjq

/-- The full descendant region at the actual root is the entire vertex set, so
its restricted local rotation is the native permutation itself. -/
theorem intrinsicBoundaryActualRestrictedVertexPerm_root
    (B : DirichletBoundarySegments X o) :
    B.intrinsicBoundaryActualRestrictedVertexPerm
        (B.intrinsicBoundaryRootedTreeAncestor
          B.intrinsicBoundaryRootedTreeRoot B.intrinsicBoundaryRootedTreeRoot) =
      B.intrinsicBoundaryOriginalVertexPerm := by
  apply Equiv.ext
  intro d
  rw [intrinsicBoundaryActualRestrictedVertexPerm_apply]
  simp only [B.intrinsicBoundaryRootedTree_root_ancestor, if_true]

theorem intrinsicBoundaryOrderedVertexBlock_formPerm_eq_restricted
    (B : DirichletBoundarySegments X o)
    (q : B.IntrinsicBoundaryGraphVertex) :
    (B.intrinsicBoundaryOrderedVertexBlock q).formPerm =
      B.intrinsicBoundaryActualRestrictedVertexPerm (fun r => r = q) := by
  classical
  apply Equiv.ext
  intro d
  rw [intrinsicBoundaryActualRestrictedVertexPerm_apply]
  by_cases hd : B.intrinsicBoundaryGraphSideEnd d = q
  · have hmem := (B.intrinsicBoundaryOrderedVertexBlock_mem_iff q d).2 hd
    simpa [hd] using B.intrinsicBoundaryOrderedVertexBlock_formPerm q d hmem
  · have hnot : d ∉ B.intrinsicBoundaryOrderedVertexBlock q := by
      intro hmem
      exact hd ((B.intrinsicBoundaryOrderedVertexBlock_mem_iff q d).1 hmem)
    simpa [hd] using List.formPerm_apply_of_notMem hnot

/-- At one rooted-tree node, its actual local cycle followed by the disjoint
child-subtree rotations is exactly the native vertex permutation restricted
to that node's full descendant region. -/
theorem intrinsicBoundaryActualRootedTreeChildren_vertexProduct
    (B : DirichletBoundarySegments X o)
    (q : B.IntrinsicBoundaryGraphVertex) :
    (B.intrinsicBoundaryOrderedVertexBlock q).formPerm *
      ((B.intrinsicBoundaryRootedTreeChildren B.intrinsicBoundaryRootedTreeRoot q).map
        (fun e => B.intrinsicBoundaryActualRestrictedVertexPerm
          (B.intrinsicBoundaryRootedTreeAncestor B.intrinsicBoundaryRootedTreeRoot
            e.val))).prod =
      B.intrinsicBoundaryActualRestrictedVertexPerm
        (B.intrinsicBoundaryRootedTreeAncestor B.intrinsicBoundaryRootedTreeRoot q) := by
  classical
  let root := B.intrinsicBoundaryRootedTreeRoot
  let T := B.intrinsicBoundaryActualRootedCycleTreeData
  have hlocal : (B.intrinsicBoundaryOrderedVertexBlock q).formPerm =
      B.intrinsicBoundaryActualRestrictedVertexPerm (fun r => r = q) :=
    B.intrinsicBoundaryOrderedVertexBlock_formPerm_eq_restricted q
  have hdis :
      (B.intrinsicBoundaryRootedTreeChildren root q).Pairwise (fun e f =>
      ∀ r, B.intrinsicBoundaryRootedTreeAncestor root e.val r →
        ¬ B.intrinsicBoundaryRootedTreeAncestor root f.val r) := by
    change (T.children q).Pairwise (fun e f =>
      ∀ r, T.ancestor (T.target e) r → ¬ T.ancestor (T.target f) r)
    apply (T.children_nodup q).pairwise_of_forall_ne
    intro e he f hf hef r her hfr
    exact T.sibling_disjoint q e f he hf hef r her hfr
  have hchildProduct :=
    B.intrinsicBoundaryActualRestrictedVertexPerm_list_prod
      (B.intrinsicBoundaryRootedTreeChildren root q)
      (fun e r => B.intrinsicBoundaryRootedTreeAncestor root e.val r) hdis
  have hrootChildDisjoint : ∀ r, r = q →
      ¬ ∃ e ∈ B.intrinsicBoundaryRootedTreeChildren root q,
        B.intrinsicBoundaryRootedTreeAncestor root e.val r := by
    intro r hr hex
    subst r
    obtain ⟨e, he, hanc⟩ := hex
    change T.ancestor (T.target e) q at hanc
    have hheight := T.height_ancestor (T.target e) q hanc
    have hchild := T.height_child q e he
    omega
  rw [hlocal, hchildProduct,
    B.intrinsicBoundaryActualRestrictedVertexPerm_mul _ _ hrootChildDisjoint]
  apply B.intrinsicBoundaryActualRestrictedVertexPerm_congr
  intro r
  exact (B.intrinsicBoundaryRootedTree_ancestor_partition root q r).symm

/-- The selected tree edge below a non-root child belongs to the strict
descendant region of `q` precisely when its child endpoint lies below `q` and
is not `q` itself. The root is the actual selected-tree root throughout. -/
def intrinsicBoundaryActualRootedTreeStrictDescendantEdge
    (B : DirichletBoundarySegments X o)
    (q : B.IntrinsicBoundaryGraphVertex)
    (e : B.IntrinsicBoundaryRootedTreeChild B.intrinsicBoundaryRootedTreeRoot) : Prop :=
  B.intrinsicBoundaryRootedTreeAncestor B.intrinsicBoundaryRootedTreeRoot q e.val ∧
    e.val ≠ q

/-- Edges in the rooted subtree at child `e`, including its incoming edge. -/
def intrinsicBoundaryActualRootedTreeChildEdgeRegion
    (B : DirichletBoundarySegments X o)
    (e : B.IntrinsicBoundaryRootedTreeChild B.intrinsicBoundaryRootedTreeRoot) :
    B.IntrinsicBoundaryRootedTreeChild B.intrinsicBoundaryRootedTreeRoot → Prop :=
  fun f => B.intrinsicBoundaryRootedTreeAncestor
    B.intrinsicBoundaryRootedTreeRoot e.val f.val

/-- If a node is below `e`, then so is its parent, unless it is `e` itself.
This is the iteration-level fact needed for the physical source dart of an
edge in a descendant region. -/
theorem intrinsicBoundaryActualRootedTree_ancestor_parent
    (B : DirichletBoundarySegments X o)
    (e v : B.IntrinsicBoundaryGraphVertex)
    (hv : v ≠ B.intrinsicBoundaryRootedTreeRoot)
    (hev : B.intrinsicBoundaryRootedTreeAncestor
      B.intrinsicBoundaryRootedTreeRoot e v)
    (hve : v ≠ e) :
    B.intrinsicBoundaryRootedTreeAncestor B.intrinsicBoundaryRootedTreeRoot e
      (B.intrinsicBoundaryRootedTreeParent B.intrinsicBoundaryRootedTreeRoot v) := by
  let root := B.intrinsicBoundaryRootedTreeRoot
  let H := B.intrinsicBoundaryRootedTreeHeight root
  let P := B.intrinsicBoundaryRootedTreeParent root
  have hheight_ne : H e ≠ H v := by
    intro heq
    have hIter := hev.2
    change P^[H v - H e] v = e at hIter
    rw [heq] at hIter
    simp only [Nat.sub_self, Function.iterate_zero_apply] at hIter
    exact hve hIter
  have hlt : H e < H v := lt_of_le_of_ne hev.1 hheight_ne
  have hstep := B.intrinsicBoundaryRootedTreeParent_height_succ root v hv
  change H (P v) + 1 = H v at hstep
  have hdiff : H (P v) - H e = H v - H e - 1 := by omega
  have hn : H v - H e = (H v - H e - 1) + 1 := by omega
  have hIter := hev.2
  change P^[H v - H e] v = e at hIter
  rw [hn, Function.iterate_succ_apply] at hIter
  have hAnc : H e ≤ H (P v) := by omega
  change H e ≤ H (P v) ∧ P^[H (P v) - H e] (P v) = e
  exact ⟨hAnc, by rwa [hdiff]⟩

/-- The incoming edge of a strict descendant stays inside its branch. -/
theorem intrinsicBoundaryActualRootedTree_ancestor_parent_of_strictDescendant
    (B : DirichletBoundarySegments X o)
    (e : B.IntrinsicBoundaryGraphVertex)
    (f : B.IntrinsicBoundaryRootedTreeChild B.intrinsicBoundaryRootedTreeRoot)
    (hef : B.intrinsicBoundaryRootedTreeAncestor
      B.intrinsicBoundaryRootedTreeRoot e f.val)
    (hne : f.val ≠ e) :
    B.intrinsicBoundaryRootedTreeAncestor B.intrinsicBoundaryRootedTreeRoot e
      (B.intrinsicBoundaryRootedTreeParent B.intrinsicBoundaryRootedTreeRoot f.val) :=
  B.intrinsicBoundaryActualRootedTree_ancestor_parent e f.val f.property hef hne

/-- Both physical darts of every edge in one child region avoid the subtree of
a distinct sibling. The parent-end case is handled separately for the unique
incoming edge; all deeper parent endpoints remain in the original branch. -/
theorem intrinsicBoundaryActualRootedTreeChildEdgeRegion_endpoints_avoid_sibling
    (B : DirichletBoundarySegments X o)
    (q : B.IntrinsicBoundaryGraphVertex)
    {e f : B.IntrinsicBoundaryRootedTreeChild B.intrinsicBoundaryRootedTreeRoot}
    (he : e ∈ B.intrinsicBoundaryRootedTreeChildren
      B.intrinsicBoundaryRootedTreeRoot q)
    (hf : f ∈ B.intrinsicBoundaryRootedTreeChildren
      B.intrinsicBoundaryRootedTreeRoot q)
    (hef : e ≠ f)
    (k : B.IntrinsicBoundaryRootedTreeChild B.intrinsicBoundaryRootedTreeRoot)
    (hk : B.intrinsicBoundaryActualRootedTreeChildEdgeRegion e k) :
    ¬ B.intrinsicBoundaryRootedTreeAncestor B.intrinsicBoundaryRootedTreeRoot f.val
        (B.intrinsicBoundaryGraphSideEnd
          (B.intrinsicBoundaryRootedTreeChildSourceDart
            B.intrinsicBoundaryRootedTreeRoot k)) ∧
    ¬ B.intrinsicBoundaryRootedTreeAncestor B.intrinsicBoundaryRootedTreeRoot f.val
        (B.intrinsicBoundaryGraphSideEnd
          (B.intrinsicBoundaryRootedTreeChildTargetDart
            B.intrinsicBoundaryRootedTreeRoot k)) := by
  constructor
  · rw [B.intrinsicBoundaryRootedTreeChildSourceDart_end]
    by_cases hke : k.val = e.val
    · have hke' : k = e := Subtype.ext hke
      subst k
      have hparentE := (B.intrinsicBoundaryRootedTree_mem_children_iff
        B.intrinsicBoundaryRootedTreeRoot q e).mp he
      rw [hparentE]
      intro hAnc
      have hparent := (B.intrinsicBoundaryRootedTree_mem_children_iff
        B.intrinsicBoundaryRootedTreeRoot q f).mp hf
      have hstep := B.intrinsicBoundaryRootedTreeParent_height_succ
        B.intrinsicBoundaryRootedTreeRoot f.val f.property
      rw [hparent] at hstep
      have hheight := B.intrinsicBoundaryRootedTree_height_ancestor
        B.intrinsicBoundaryRootedTreeRoot f.val q hAnc
      omega
    · have hparentAnc := B.intrinsicBoundaryActualRootedTree_ancestor_parent
        e.val k.val k.property hk hke
      exact B.intrinsicBoundaryRootedTree_sibling_disjoint
        B.intrinsicBoundaryRootedTreeRoot q e f he hf hef
        (B.intrinsicBoundaryRootedTreeParent B.intrinsicBoundaryRootedTreeRoot k.val)
        hparentAnc
  · rw [B.intrinsicBoundaryRootedTreeChildTargetDart_end]
    exact B.intrinsicBoundaryRootedTree_sibling_disjoint
      B.intrinsicBoundaryRootedTreeRoot q e f he hf hef k.val hk

private theorem intrinsicBoundaryActualRestrictedChildTreeSwapPerm_disjoint_vertexPerm
    (B : DirichletBoundarySegments X o)
    (A : B.IntrinsicBoundaryRootedTreeChild B.intrinsicBoundaryRootedTreeRoot → Prop)
    (C : B.IntrinsicBoundaryGraphVertex → Prop)
    (hsource : ∀ child, A child → ¬ C
      (B.intrinsicBoundaryRootedTreeParent B.intrinsicBoundaryRootedTreeRoot child.val))
    (htarget : ∀ child, A child → ¬ C child.val) :
    Equiv.Perm.Disjoint
      (B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm
        B.intrinsicBoundaryRootedTreeRoot A)
      (B.intrinsicBoundaryActualRestrictedVertexPerm C) := by
  classical
  intro d
  by_cases hC : C (B.intrinsicBoundaryGraphSideEnd d)
  · left
    rw [B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm_apply, if_neg]
    rintro ⟨child, hA, hendpoint | hendpoint⟩
    · rw [hendpoint, B.intrinsicBoundaryRootedTreeChildSourceDart_end] at hC
      exact hsource child hA hC
    · rw [hendpoint, B.intrinsicBoundaryRootedTreeChildTargetDart_end] at hC
      exact htarget child hA hC
  · right
    rw [B.intrinsicBoundaryActualRestrictedVertexPerm_apply, if_neg hC]

private theorem intrinsicBoundaryActualRootedChildTreeSwap_disjoint_vertexPerm
    (B : DirichletBoundarySegments X o)
    (e : B.IntrinsicBoundaryRootedTreeChild B.intrinsicBoundaryRootedTreeRoot)
    (C : B.IntrinsicBoundaryGraphVertex → Prop)
    (hsource : ¬ C (B.intrinsicBoundaryRootedTreeParent
      B.intrinsicBoundaryRootedTreeRoot e.val))
    (htarget : ¬ C e.val) :
    Equiv.Perm.Disjoint
      (B.intrinsicBoundaryRootedChildTreeSwap
        B.intrinsicBoundaryRootedTreeRoot e)
      (B.intrinsicBoundaryActualRestrictedVertexPerm C) := by
  classical
  intro d
  by_cases hC : C (B.intrinsicBoundaryGraphSideEnd d)
  · left
    have hsourceDart : d ≠ B.intrinsicBoundaryRootedTreeChildSourceDart
        B.intrinsicBoundaryRootedTreeRoot e := by
      intro hd
      rw [hd, B.intrinsicBoundaryRootedTreeChildSourceDart_end] at hC
      exact hsource hC
    have htargetDart : d ≠ B.intrinsicBoundaryRootedTreeChildTargetDart
        B.intrinsicBoundaryRootedTreeRoot e := by
      intro hd
      rw [hd, B.intrinsicBoundaryRootedTreeChildTargetDart_end] at hC
      exact htarget hC
    change Equiv.swap
      (B.intrinsicBoundaryRootedTreeChildSourceDart
        B.intrinsicBoundaryRootedTreeRoot e)
      (B.intrinsicBoundaryRootedTreeChildTargetDart
        B.intrinsicBoundaryRootedTreeRoot e) d = d
    exact Equiv.swap_apply_of_ne_of_ne hsourceDart htargetDart
  · right
    rw [B.intrinsicBoundaryActualRestrictedVertexPerm_apply, if_neg hC]

/-- An earlier child branch's strict-descendant swaps and incoming physical
swap commute with a later sibling branch's restricted vertex rotation. -/
theorem intrinsicBoundaryActualRootedTreeChildren_swap_vertex_commute
    (B : DirichletBoundarySegments X o)
    (q : B.IntrinsicBoundaryGraphVertex) :
    (B.intrinsicBoundaryRootedTreeChildren
      B.intrinsicBoundaryRootedTreeRoot q).Pairwise (fun e f =>
        Commute
          (B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm
              B.intrinsicBoundaryRootedTreeRoot
              (fun k => B.intrinsicBoundaryActualRootedTreeStrictDescendantEdge
                e.val k) *
            B.intrinsicBoundaryRootedChildTreeSwap
              B.intrinsicBoundaryRootedTreeRoot e)
          (B.intrinsicBoundaryActualRestrictedVertexPerm
            (B.intrinsicBoundaryRootedTreeAncestor
              B.intrinsicBoundaryRootedTreeRoot f.val))) := by
  classical
  let root := B.intrinsicBoundaryRootedTreeRoot
  let T := B.intrinsicBoundaryActualRootedCycleTreeData
  apply (T.children_nodup q).pairwise_of_forall_ne
  intro e he f hf hef
  have havoid (k : B.IntrinsicBoundaryRootedTreeChild root)
      (hk : B.intrinsicBoundaryActualRootedTreeChildEdgeRegion e k) :=
    B.intrinsicBoundaryActualRootedTreeChildEdgeRegion_endpoints_avoid_sibling
      q he hf hef k hk
  have hsource : ∀ k,
      B.intrinsicBoundaryActualRootedTreeStrictDescendantEdge e.val k →
        ¬ B.intrinsicBoundaryRootedTreeAncestor root f.val
          (B.intrinsicBoundaryRootedTreeParent root k.val) := by
    intro k hk
    have h := (havoid k hk.1).1
    rw [B.intrinsicBoundaryRootedTreeChildSourceDart_end] at h
    exact h
  have htarget : ∀ k,
      B.intrinsicBoundaryActualRootedTreeStrictDescendantEdge e.val k →
        ¬ B.intrinsicBoundaryRootedTreeAncestor root f.val k.val := by
    intro k hk
    have h := (havoid k hk.1).2
    rw [B.intrinsicBoundaryRootedTreeChildTargetDart_end] at h
    exact h
  have hstrictDisjoint :=
    B.intrinsicBoundaryActualRestrictedChildTreeSwapPerm_disjoint_vertexPerm
      (fun k => B.intrinsicBoundaryActualRootedTreeStrictDescendantEdge e.val k)
      (B.intrinsicBoundaryRootedTreeAncestor root f.val) hsource htarget
  have hrefl : B.intrinsicBoundaryActualRootedTreeChildEdgeRegion e e := by
    exact (B.intrinsicBoundaryRootedTree_ancestor_partition root e.val e.val).mpr
      (Or.inl rfl)
  have havoidE := B.intrinsicBoundaryActualRootedTreeChildEdgeRegion_endpoints_avoid_sibling
    q he hf hef e hrefl
  have hsourceE : ¬ B.intrinsicBoundaryRootedTreeAncestor root f.val
      (B.intrinsicBoundaryRootedTreeParent root e.val) := by
    simpa [B.intrinsicBoundaryRootedTreeChildSourceDart_end] using havoidE.1
  have htargetE : ¬ B.intrinsicBoundaryRootedTreeAncestor root f.val e.val := by
    simpa [B.intrinsicBoundaryRootedTreeChildTargetDart_end] using havoidE.2
  have hswapDisjoint :=
    B.intrinsicBoundaryActualRootedChildTreeSwap_disjoint_vertexPerm e
      (B.intrinsicBoundaryRootedTreeAncestor root f.val) hsourceE htargetE
  exact (Equiv.Perm.Disjoint.mul_left hstrictDisjoint hswapDisjoint).commute

theorem intrinsicBoundaryActualRootedTreeStrictDescendantEdge_root
    (B : DirichletBoundarySegments X o) :
    ∀ e : B.IntrinsicBoundaryRootedTreeChild B.intrinsicBoundaryRootedTreeRoot,
      B.intrinsicBoundaryActualRootedTreeStrictDescendantEdge
        B.intrinsicBoundaryRootedTreeRoot e := by
  intro e
  exact ⟨B.intrinsicBoundaryRootedTree_root_ancestor
    B.intrinsicBoundaryRootedTreeRoot e.val, e.property⟩

theorem intrinsicBoundaryActualRootedTreeStrictDescendantEdge_root_iff
    (B : DirichletBoundarySegments X o)
    (e : B.IntrinsicBoundaryRootedTreeChild B.intrinsicBoundaryRootedTreeRoot) :
    B.intrinsicBoundaryActualRootedTreeStrictDescendantEdge
      B.intrinsicBoundaryRootedTreeRoot e ↔ True := by
  exact ⟨fun _ => trivial, fun _ => B.intrinsicBoundaryActualRootedTreeStrictDescendantEdge_root e⟩

theorem intrinsicBoundaryActualRootedTreeRoot_swapProduct
    (B : DirichletBoundarySegments X o) :
    B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm
        B.intrinsicBoundaryRootedTreeRoot
        (B.intrinsicBoundaryActualRootedTreeStrictDescendantEdge
          B.intrinsicBoundaryRootedTreeRoot) = B.intrinsicBoundaryTreePairingPerm := by
  calc
    B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm
        B.intrinsicBoundaryRootedTreeRoot
        (B.intrinsicBoundaryActualRootedTreeStrictDescendantEdge
          B.intrinsicBoundaryRootedTreeRoot) =
      B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm
        B.intrinsicBoundaryRootedTreeRoot (fun _ => True) := by
          apply B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm_congr
            B.intrinsicBoundaryRootedTreeRoot
          intro e
          exact B.intrinsicBoundaryActualRootedTreeStrictDescendantEdge_root_iff e
    _ = B.intrinsicBoundaryTreePairingPerm :=
      B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm_true
        B.intrinsicBoundaryRootedTreeRoot

/-- A branch-edge region is the disjoint union of the strict descendants of
its child endpoint and that child's single incoming edge. -/
theorem intrinsicBoundaryActualRootedTreeChildEdgeRegion_iff_strictDesc_or_self
    (B : DirichletBoundarySegments X o)
    (e f : B.IntrinsicBoundaryRootedTreeChild B.intrinsicBoundaryRootedTreeRoot) :
    B.intrinsicBoundaryActualRootedTreeChildEdgeRegion e f ↔
      B.intrinsicBoundaryActualRootedTreeStrictDescendantEdge e.val f ∨ f = e := by
  change B.intrinsicBoundaryRootedTreeAncestor B.intrinsicBoundaryRootedTreeRoot
      e.val f.val ↔ _
  constructor
  · intro h
    by_cases heq : f.val = e.val
    · exact Or.inr (Subtype.ext heq)
    · exact Or.inl ⟨h, heq⟩
  · rintro (⟨h, _⟩ | heq)
    · exact h
    · subst f
      exact (B.intrinsicBoundaryRootedTree_ancestor_partition
        B.intrinsicBoundaryRootedTreeRoot e.val e.val).mpr (Or.inl rfl)

theorem intrinsicBoundaryActualRootedTreeChildSwap_eq_region
    (B : DirichletBoundarySegments X o)
    (e : B.IntrinsicBoundaryRootedTreeChild B.intrinsicBoundaryRootedTreeRoot) :
    (B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm
        B.intrinsicBoundaryRootedTreeRoot
        (fun k => B.intrinsicBoundaryActualRootedTreeStrictDescendantEdge e.val k)) *
      B.intrinsicBoundaryRootedChildTreeSwap B.intrinsicBoundaryRootedTreeRoot e =
    B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm
      B.intrinsicBoundaryRootedTreeRoot
      (B.intrinsicBoundaryActualRootedTreeChildEdgeRegion e) := by
  let A := fun k : B.IntrinsicBoundaryRootedTreeChild
    B.intrinsicBoundaryRootedTreeRoot =>
      B.intrinsicBoundaryActualRootedTreeStrictDescendantEdge e.val k
  have hdis : ∀ k, ¬ (A k ∧ k = e) := by
    intro k h
    exact h.1.2 (congrArg Subtype.val h.2)
  have hsingle := B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm_singleton
    B.intrinsicBoundaryRootedTreeRoot e
  have hunion := B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm_union_mul
    B.intrinsicBoundaryRootedTreeRoot A (fun k => k = e) hdis
  change B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm
      B.intrinsicBoundaryRootedTreeRoot A *
        B.intrinsicBoundaryRootedChildTreeSwap
          B.intrinsicBoundaryRootedTreeRoot e = _
  rw [← hsingle, ← hunion]
  apply B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm_congr
    B.intrinsicBoundaryRootedTreeRoot
  intro k
  exact (B.intrinsicBoundaryActualRootedTreeChildEdgeRegion_iff_strictDesc_or_self e k).symm

/-- The child-subtree strict swaps followed by each actual incoming-edge
transposition partition the complete strict-descendant swap region at q. -/
theorem intrinsicBoundaryActualRootedTreeChildren_swapProduct
    (B : DirichletBoundarySegments X o)
    (q : B.IntrinsicBoundaryGraphVertex) :
    ((B.intrinsicBoundaryRootedTreeChildren
        B.intrinsicBoundaryRootedTreeRoot q).map (fun e =>
      B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm
          B.intrinsicBoundaryRootedTreeRoot
          (fun k => B.intrinsicBoundaryActualRootedTreeStrictDescendantEdge e.val k) *
        B.intrinsicBoundaryRootedChildTreeSwap
          B.intrinsicBoundaryRootedTreeRoot e)).prod =
      B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm
        B.intrinsicBoundaryRootedTreeRoot
        (B.intrinsicBoundaryActualRootedTreeStrictDescendantEdge q) := by
  classical
  let root := B.intrinsicBoundaryRootedTreeRoot
  let T := B.intrinsicBoundaryActualRootedCycleTreeData
  let children := B.intrinsicBoundaryRootedTreeChildren root q
  let region := fun e : B.IntrinsicBoundaryRootedTreeChild root =>
    B.intrinsicBoundaryActualRootedTreeChildEdgeRegion e
  have hfactor (e : B.IntrinsicBoundaryRootedTreeChild root) :
      B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm root
          (fun k => B.intrinsicBoundaryActualRootedTreeStrictDescendantEdge e.val k) *
        B.intrinsicBoundaryRootedChildTreeSwap root e =
      B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm root (region e) := by
    exact B.intrinsicBoundaryActualRootedTreeChildSwap_eq_region e
  have hpairwise : (children.map region).Pairwise
      (fun A C => ∀ k, ¬ (A k ∧ C k)) := by
    rw [List.pairwise_map]
    apply (T.children_nodup q).pairwise_of_forall_ne
    intro e he f hf hef k
    rintro ⟨hEk, hFk⟩
    exact B.intrinsicBoundaryRootedTree_sibling_disjoint
      root q e f he hf hef k.val hEk hFk
  have hfactorMap :
      children.map (fun e =>
        B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm root
            (fun k => B.intrinsicBoundaryActualRootedTreeStrictDescendantEdge e.val k) *
          B.intrinsicBoundaryRootedChildTreeSwap root e) =
      children.map (fun e =>
        B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm root (region e)) := by
    apply List.map_congr_left
    intro e he
    exact hfactor e
  have hmap :
      (children.map (fun e =>
        B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm root (region e))) =
      ((children.map region).map
        (B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm root)) := by
    rw [List.map_map]
    rfl
  rw [hfactorMap, hmap,
    B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm_list_prod root
      (children.map region) hpairwise]
  apply B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm_congr root
  intro k
  constructor
  · rintro ⟨A, hA, hAk⟩
    obtain ⟨e, he, hAe⟩ := List.mem_map.mp hA
    rw [← hAe] at hAk
    change B.intrinsicBoundaryRootedTreeAncestor root e.val k.val at hAk
    have hqk := (B.intrinsicBoundaryRootedTree_ancestor_partition root q k.val).mpr
      (Or.inr ⟨e, he, hAk⟩)
    have hparent := (B.intrinsicBoundaryRootedTree_mem_children_iff root q e).mp he
    have hstep := B.intrinsicBoundaryRootedTreeParent_height_succ root e.val e.property
    rw [hparent] at hstep
    refine ⟨hqk, ?_⟩
    intro heq
    rw [heq] at hAk
    have hheight := B.intrinsicBoundaryRootedTree_height_ancestor root e.val q hAk
    omega
  · intro hk
    have hpart := (B.intrinsicBoundaryRootedTree_ancestor_partition root q k.val).mp hk.1
    rcases hpart with heq | ⟨e, he, hEk⟩
    · exact (hk.2 heq).elim
    · exact ⟨region e, List.mem_map.mpr ⟨e, he, rfl⟩, hEk⟩

theorem intrinsicBoundaryActualRootedTreeStrictDescendantEdge_iff_children
    (B : DirichletBoundarySegments X o)
    (q : B.IntrinsicBoundaryGraphVertex)
    (f : B.IntrinsicBoundaryRootedTreeChild B.intrinsicBoundaryRootedTreeRoot) :
    B.intrinsicBoundaryActualRootedTreeStrictDescendantEdge q f ↔
      ∃ e ∈ B.intrinsicBoundaryRootedTreeChildren
          B.intrinsicBoundaryRootedTreeRoot q,
        B.intrinsicBoundaryRootedTreeAncestor
          B.intrinsicBoundaryRootedTreeRoot e.val f.val := by
  classical
  constructor
  · rintro ⟨hqf, hneq⟩
    have hpart := (B.intrinsicBoundaryRootedTree_ancestor_partition
      B.intrinsicBoundaryRootedTreeRoot q f.val).mp hqf
    rcases hpart with hsame | ⟨e, he, hef⟩
    · exact (hneq hsame).elim
    · exact ⟨e, he, hef⟩
  · rintro ⟨e, he, hef⟩
    have hqf := (B.intrinsicBoundaryRootedTree_ancestor_partition
      B.intrinsicBoundaryRootedTreeRoot q f.val).mpr (Or.inr ⟨e, he, hef⟩)
    have hchildHeight := B.intrinsicBoundaryRootedTreeParent_height_succ
      B.intrinsicBoundaryRootedTreeRoot e.val e.property
    have hparent := (B.intrinsicBoundaryRootedTree_mem_children_iff
      B.intrinsicBoundaryRootedTreeRoot q e).mp he
    rw [hparent] at hchildHeight
    have hlt : B.intrinsicBoundaryRootedTreeHeight
        B.intrinsicBoundaryRootedTreeRoot q <
        B.intrinsicBoundaryRootedTreeHeight B.intrinsicBoundaryRootedTreeRoot f.val := by
      exact lt_of_lt_of_le (by omega) hef.1
    exact ⟨hqf, fun h => by rw [h] at hlt; omega⟩

/-- Child-subtree edge regions partition all actual strict-descendant edges. -/
theorem intrinsicBoundaryActualRootedTreeChildEdgeRegion_partition
    (B : DirichletBoundarySegments X o)
    (q : B.IntrinsicBoundaryGraphVertex)
    (f : B.IntrinsicBoundaryRootedTreeChild B.intrinsicBoundaryRootedTreeRoot) :
    B.intrinsicBoundaryActualRootedTreeStrictDescendantEdge q f ↔
      ∃ e ∈ B.intrinsicBoundaryRootedTreeChildren
          B.intrinsicBoundaryRootedTreeRoot q,
        B.intrinsicBoundaryActualRootedTreeChildEdgeRegion e f := by
  simpa [intrinsicBoundaryActualRootedTreeChildEdgeRegion] using
    B.intrinsicBoundaryActualRootedTreeStrictDescendantEdge_iff_children q f

/-- Distinct immediate child regions are genuinely disjoint by rooted-tree
ancestry, not by a choice of edge ordering. -/
theorem intrinsicBoundaryActualRootedTreeChildEdgeRegion_disjoint
    (B : DirichletBoundarySegments X o)
    (q : B.IntrinsicBoundaryGraphVertex)
    {e f : B.IntrinsicBoundaryRootedTreeChild B.intrinsicBoundaryRootedTreeRoot}
    (he : e ∈ B.intrinsicBoundaryRootedTreeChildren
      B.intrinsicBoundaryRootedTreeRoot q)
    (hf : f ∈ B.intrinsicBoundaryRootedTreeChildren
      B.intrinsicBoundaryRootedTreeRoot q)
    (hef : e ≠ f) :
    ∀ k, B.intrinsicBoundaryActualRootedTreeChildEdgeRegion e k →
      ¬ B.intrinsicBoundaryActualRootedTreeChildEdgeRegion f k := by
  intro k hEk hFk
  exact B.intrinsicBoundaryRootedTree_sibling_disjoint
    B.intrinsicBoundaryRootedTreeRoot q e f he hf hef k.val hEk hFk

/-- The actual rooted tree and actual local cyclic blocks construct a physical
one-orbit permutation, with no residual ancestry, coverage, or cardinality
assumption. -/
theorem intrinsicBoundaryActualRootedCycleTree_exists_physicalOneOrbit
    (B : DirichletBoundarySegments X o) :
    ∃ childWords :
        B.IntrinsicBoundaryRootedTreeChild B.intrinsicBoundaryRootedTreeRoot →
          List (Fin B.intrinsicBoundaryRadialCuts.card),
      ∀ x y : Fin B.intrinsicBoundaryRadialCuts.card,
        ∃ n : ℕ,
          ((B.intrinsicBoundaryActualRootedCycleTreeData).physicalProduct
            B.intrinsicBoundaryRootedTreeRoot childWords)^[n] x = y := by
  classical
  let root := B.intrinsicBoundaryRootedTreeRoot
  let T := B.intrinsicBoundaryActualRootedCycleTreeData
  have hroot : ∀ d : Fin B.intrinsicBoundaryRadialCuts.card,
      T.ancestor root (T.vertex d) := by
    intro d
    change B.intrinsicBoundaryRootedTreeAncestor root root
      (B.intrinsicBoundaryGraphSideEnd d)
    exact B.intrinsicBoundaryRootedTree_root_ancestor root
      (B.intrinsicBoundaryGraphSideEnd d)
  have hcard : 2 ≤ Fintype.card (Fin B.intrinsicBoundaryRadialCuts.card) := by
    have hcardNat : 2 ≤ B.intrinsicBoundaryRadialCuts.card :=
      le_trans (by decide : 2 ≤ 3) B.three_le_intrinsicBoundaryRadialCuts_card
    simpa using hcardNat
  change ∃ childWords :
      B.IntrinsicBoundaryRootedTreeChild root →
        List (Fin B.intrinsicBoundaryRadialCuts.card),
    ∀ x y : Fin B.intrinsicBoundaryRadialCuts.card,
      ∃ n : ℕ, (T.physicalProduct root childWords)^[n] x = y
  exact SystolicGrowth.rootedCycleTree_exists_physicalOneOrbit T root hroot hcard

#print axioms intrinsicBoundaryActualRootedCycleTreeData
#print axioms intrinsicBoundaryActualRootedTreeChildren_vertexProduct
#print axioms intrinsicBoundaryActualRestrictedVertexPerm_root
#print axioms intrinsicBoundaryActualRootedTree_ancestor_parent
#print axioms intrinsicBoundaryActualRootedTreeChildEdgeRegion_endpoints_avoid_sibling
#print axioms intrinsicBoundaryActualRootedTreeChildSwap_eq_region
#print axioms intrinsicBoundaryActualRootedTreeChildren_swapProduct
#print axioms intrinsicBoundaryActualRootedTreeChildren_swap_vertex_commute
#print axioms intrinsicBoundaryActualRootedTreeRoot_swapProduct
#print axioms intrinsicBoundaryActualRootedCycleTree_exists_physicalOneOrbit

end

end SystolicGrowth.DirichletBoundarySegments
