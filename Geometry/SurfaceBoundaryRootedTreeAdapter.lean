module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SurfaceBoundaryGraphPaths
public import BuserSarnak.FiniteRootedCycleContraction

@[expose] public section

/-!
# Rooting the actual paired-side spanning tree

This file builds the rooted combinatorial frame on the native finite graph.
It is independent of the still-open identification of local vertex cycles
with the native successor permutation.
-/

open Set UpperHalfPlane
open scoped Pointwise UpperHalfPlane Classical

namespace SystolicGrowth.DirichletBoundarySegments

noncomputable section

variable {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}

/-- A fixed actual vertex of the connected paired-side graph. -/
def intrinsicBoundaryRootedTreeRoot (B : DirichletBoundarySegments X o) :
    B.IntrinsicBoundaryGraphVertex :=
  B.intrinsicBoundaryGraphSideStart ⟨0,
    Nat.zero_lt_of_lt B.three_le_intrinsicBoundaryRadialCuts_card⟩

/-- The root-distance is the length of the unique path in the selected tree. -/
def intrinsicBoundaryRootedTreeHeight (B : DirichletBoundarySegments X o)
    (root v : B.IntrinsicBoundaryGraphVertex) : ℕ :=
  (B.intrinsicBoundaryRootedTreeWalk root v).length

/-- The parent of a non-root vertex is the penultimate vertex on its unique
root path; the root is fixed to make iteration total. -/
def intrinsicBoundaryRootedTreeParent (B : DirichletBoundarySegments X o)
    (root v : B.IntrinsicBoundaryGraphVertex) : B.IntrinsicBoundaryGraphVertex :=
  if v = root then root else (B.intrinsicBoundaryRootedTreeWalk root v).penultimate

theorem intrinsicBoundaryRootedTreeHeight_root (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex) :
    B.intrinsicBoundaryRootedTreeHeight root root = 0 := by
  simp [intrinsicBoundaryRootedTreeHeight]

theorem intrinsicBoundaryRootedTreeParent_adj (B : DirichletBoundarySegments X o)
    (root v : B.IntrinsicBoundaryGraphVertex) (hv : v ≠ root) :
    B.intrinsicBoundarySpanningTree.Adj
      (B.intrinsicBoundaryRootedTreeParent root v) v := by
  have hlen : 0 < (B.intrinsicBoundaryRootedTreeWalk root v).length := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have hEq := SimpleGraph.Walk.eq_of_length_eq_zero hzero
    exact hv hEq.symm
  simpa [intrinsicBoundaryRootedTreeParent, hv] using
    (B.intrinsicBoundaryRootedTreeWalk root v).adj_penultimate
      (SimpleGraph.Walk.not_nil_iff_lt_length.mpr hlen)

theorem intrinsicBoundaryRootedTreeParent_height_succ
    (B : DirichletBoundarySegments X o)
    (root v : B.IntrinsicBoundaryGraphVertex) (hv : v ≠ root) :
    B.intrinsicBoundaryRootedTreeHeight root
        (B.intrinsicBoundaryRootedTreeParent root v) + 1 =
      B.intrinsicBoundaryRootedTreeHeight root v := by
  have hlen : 0 < (B.intrinsicBoundaryRootedTreeWalk root v).length := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have hEq := SimpleGraph.Walk.eq_of_length_eq_zero hzero
    exact hv hEq.symm
  let hdrop := (B.intrinsicBoundaryRootedTreeWalk root v).dropLast
  have hdropPath : hdrop.IsPath := by
    simpa [hdrop] using (B.intrinsicBoundaryRootedTreeWalk_isPath root v).dropLast
  have hpen : (B.intrinsicBoundaryRootedTreeWalk root v).penultimate =
      B.intrinsicBoundaryRootedTreeParent root v := by
    simp [intrinsicBoundaryRootedTreeParent, hv]
  let hdrop' := hdrop.copy rfl hpen
  have hdropPath' : hdrop'.IsPath := by
    exact (SimpleGraph.Walk.isPath_copy hdrop rfl hpen).mpr hdropPath
  have hdropEq : hdrop' = B.intrinsicBoundaryRootedTreeWalk root
      (B.intrinsicBoundaryRootedTreeParent root v) := by
    apply B.intrinsicBoundaryRootedTreeWalk_eq_of_isPath
    exact hdropPath'
  rw [intrinsicBoundaryRootedTreeHeight, intrinsicBoundaryRootedTreeHeight,
    ← hdropEq]
  have hlength : hdrop'.length =
      (B.intrinsicBoundaryRootedTreeWalk root v).dropLast.length := by
    simp [hdrop', hdrop]
  rw [hlength]
  exact SimpleGraph.Walk.length_dropLast_add_one
    (SimpleGraph.Walk.not_nil_iff_lt_length.mpr hlen)

private theorem intrinsicBoundaryRootedTreeParent_iter_height_eq_root
    (B : DirichletBoundarySegments X o)
    (root v : B.IntrinsicBoundaryGraphVertex) :
    (B.intrinsicBoundaryRootedTreeParent root) ^[
      B.intrinsicBoundaryRootedTreeHeight root v] v = root := by
  induction hheight : B.intrinsicBoundaryRootedTreeHeight root v using
      Nat.strong_induction_on generalizing v with
  | h n ih =>
      by_cases hv : v = root
      · subst v
        have hn : n = 0 := by
          simpa [B.intrinsicBoundaryRootedTreeHeight_root root] using hheight.symm
        rw [hn]
        simp
      · have hparent := B.intrinsicBoundaryRootedTreeParent_height_succ root v hv
        have hlt : B.intrinsicBoundaryRootedTreeHeight root
            (B.intrinsicBoundaryRootedTreeParent root v) < n := by
          rw [← hheight]
          omega
        have hrec := ih _ hlt (B.intrinsicBoundaryRootedTreeParent root v) rfl
        rw [← hheight, ← hparent, Function.iterate_succ_apply]
        exact hrec

private theorem intrinsicBoundaryRootedTreeWalk_reverse
    (B : DirichletBoundarySegments X o)
    (root v : B.IntrinsicBoundaryGraphVertex) :
    B.intrinsicBoundaryRootedTreeWalk v root =
      (B.intrinsicBoundaryRootedTreeWalk root v).reverse := by
  exact (B.intrinsicBoundaryRootedTreeWalk_eq_of_isPath
    (B.intrinsicBoundaryRootedTreeWalk_isPath root v).reverse).symm

private theorem intrinsicBoundaryRootedTreeWalk_cons_of_length_le
    (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex) {v w : B.IntrinsicBoundaryGraphVertex}
    (h : B.intrinsicBoundarySpanningTree.Adj v w)
    (hlen : (B.intrinsicBoundaryRootedTreeWalk v root).length ≤
      (B.intrinsicBoundaryRootedTreeWalk w root).length) :
    B.intrinsicBoundaryRootedTreeWalk w root =
      .cons h.symm (B.intrinsicBoundaryRootedTreeWalk v root) := by
  have hvpath := B.intrinsicBoundaryRootedTreeWalk_isPath v root
  have hnmem : w ∉ (B.intrinsicBoundaryRootedTreeWalk v root).support := by
    intro hw
    have htake : (B.intrinsicBoundaryRootedTreeWalk v root).takeUntil w hw = .cons h .nil :=
      (B.intrinsicBoundarySpanningTree_isTree.existsUnique_path v w).unique
        (hvpath.takeUntil hw) (SimpleGraph.Walk.IsPath.nil.cons (by simpa using h.ne))
    have hdrop : (B.intrinsicBoundaryRootedTreeWalk v root).dropUntil w hw =
        B.intrinsicBoundaryRootedTreeWalk w root :=
      B.intrinsicBoundaryRootedTreeWalk_eq_of_isPath (hvpath.dropUntil hw)
    rw [← SimpleGraph.Walk.take_spec (B.intrinsicBoundaryRootedTreeWalk v root) hw,
      htake, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons,
      SimpleGraph.Walk.length_nil, hdrop] at hlen
    omega
  exact (B.intrinsicBoundarySpanningTree_isTree.existsUnique_path w root).unique
    (B.intrinsicBoundaryRootedTreeWalk_isPath w root) (hvpath.cons hnmem)

private theorem intrinsicBoundaryRootedTreeParent_eq_of_adj_height_le
    (B : DirichletBoundarySegments X o)
    (root v w : B.IntrinsicBoundaryGraphVertex)
    (h : B.intrinsicBoundarySpanningTree.Adj v w)
    (hlen : B.intrinsicBoundaryRootedTreeHeight root v ≤
      B.intrinsicBoundaryRootedTreeHeight root w) :
    B.intrinsicBoundaryRootedTreeParent root w = v := by
  have hwne : w ≠ root := by
    intro hwr
    have hz : B.intrinsicBoundaryRootedTreeHeight root v = 0 := by
      rw [hwr, B.intrinsicBoundaryRootedTreeHeight_root] at hlen
      omega
    change (B.intrinsicBoundaryRootedTreeWalk root v).length = 0 at hz
    have hvr := (SimpleGraph.Walk.eq_of_length_eq_zero hz).symm
    exact h.ne (hvr.trans hwr.symm)
  have hlen' : (B.intrinsicBoundaryRootedTreeWalk v root).length ≤
      (B.intrinsicBoundaryRootedTreeWalk w root).length := by
    change (B.intrinsicBoundaryRootedTreeWalk root v).length ≤
      (B.intrinsicBoundaryRootedTreeWalk root w).length at hlen
    calc
      (B.intrinsicBoundaryRootedTreeWalk v root).length =
          (B.intrinsicBoundaryRootedTreeWalk root v).length := by
        rw [B.intrinsicBoundaryRootedTreeWalk_reverse, SimpleGraph.Walk.length_reverse]
      _ ≤ (B.intrinsicBoundaryRootedTreeWalk root w).length := hlen
      _ = (B.intrinsicBoundaryRootedTreeWalk w root).length := by
        rw [B.intrinsicBoundaryRootedTreeWalk_reverse, SimpleGraph.Walk.length_reverse]
  have hcons := B.intrinsicBoundaryRootedTreeWalk_cons_of_length_le root h hlen'
  calc
    B.intrinsicBoundaryRootedTreeParent root w =
        (B.intrinsicBoundaryRootedTreeWalk root w).penultimate := by
      simp [intrinsicBoundaryRootedTreeParent, hwne]
    _ = (B.intrinsicBoundaryRootedTreeWalk w root).snd := by
      calc
        _ = (B.intrinsicBoundaryRootedTreeWalk root w).reverse.snd :=
          (SimpleGraph.Walk.snd_reverse _).symm
        _ = (B.intrinsicBoundaryRootedTreeWalk w root).snd := by
          rw [← B.intrinsicBoundaryRootedTreeWalk_reverse]
    _ = v := by simp [hcons]

/-- Non-root vertices index the actual parent-to-child tree edges. -/
abbrev IntrinsicBoundaryRootedTreeChild (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex) :=
  {v : B.IntrinsicBoundaryGraphVertex // v ≠ root}

/-- The children of a vertex, listed without repetition from the finite native vertex type. -/
def intrinsicBoundaryRootedTreeChildren (B : DirichletBoundarySegments X o)
    (root q : B.IntrinsicBoundaryGraphVertex) :
    List (B.IntrinsicBoundaryRootedTreeChild root) := by
  classical
  exact (Finset.univ : Finset (B.IntrinsicBoundaryRootedTreeChild root)).toList.filter
    (fun e => decide (B.intrinsicBoundaryRootedTreeParent root e.val = q))

theorem intrinsicBoundaryRootedTree_mem_children_iff
    (B : DirichletBoundarySegments X o) (root q : B.IntrinsicBoundaryGraphVertex)
    (e : B.IntrinsicBoundaryRootedTreeChild root) :
    e ∈ B.intrinsicBoundaryRootedTreeChildren root q ↔
      B.intrinsicBoundaryRootedTreeParent root e.val = q := by
  classical
  simp [intrinsicBoundaryRootedTreeChildren]

/-- A vertex is an ancestor precisely when the unique parent iteration from it
reaches that vertex at the corresponding root-distance difference. -/
def intrinsicBoundaryRootedTreeAncestor (B : DirichletBoundarySegments X o)
    (root q r : B.IntrinsicBoundaryGraphVertex) : Prop :=
  B.intrinsicBoundaryRootedTreeHeight root q ≤
      B.intrinsicBoundaryRootedTreeHeight root r ∧
    (B.intrinsicBoundaryRootedTreeParent root) ^[
      B.intrinsicBoundaryRootedTreeHeight root r -
        B.intrinsicBoundaryRootedTreeHeight root q] r = q

theorem intrinsicBoundaryRootedTree_root_ancestor
    (B : DirichletBoundarySegments X o)
    (root v : B.IntrinsicBoundaryGraphVertex) :
    B.intrinsicBoundaryRootedTreeAncestor root root v := by
  rw [intrinsicBoundaryRootedTreeAncestor,
    B.intrinsicBoundaryRootedTreeHeight_root]
  exact ⟨Nat.zero_le _, by
    simpa using B.intrinsicBoundaryRootedTreeParent_iter_height_eq_root root v⟩

theorem intrinsicBoundaryRootedTreeHeight_eq_zero_iff
    (B : DirichletBoundarySegments X o) (root v : B.IntrinsicBoundaryGraphVertex) :
    B.intrinsicBoundaryRootedTreeHeight root v = 0 ↔ v = root := by
  constructor
  · intro h
    have hEq := SimpleGraph.Walk.eq_of_length_eq_zero h
    exact hEq.symm
  · intro h
    subst v
    exact B.intrinsicBoundaryRootedTreeHeight_root root

private theorem intrinsicBoundaryRootedTreeParentIter_height
    (B : DirichletBoundarySegments X o) (root v : B.IntrinsicBoundaryGraphVertex)
    (n : ℕ) (hn : n ≤ B.intrinsicBoundaryRootedTreeHeight root v) :
    B.intrinsicBoundaryRootedTreeHeight root
        ((B.intrinsicBoundaryRootedTreeParent root)^[n] v) + n =
      B.intrinsicBoundaryRootedTreeHeight root v := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hn' : n ≤ B.intrinsicBoundaryRootedTreeHeight root v := by omega
      have hcur : B.intrinsicBoundaryRootedTreeHeight root
          ((B.intrinsicBoundaryRootedTreeParent root)^[n] v) + n =
          B.intrinsicBoundaryRootedTreeHeight root v := ih hn'
      have hcurpos : 0 < B.intrinsicBoundaryRootedTreeHeight root
          ((B.intrinsicBoundaryRootedTreeParent root)^[n] v) := by omega
      have hcur_ne : (B.intrinsicBoundaryRootedTreeParent root)^[n] v ≠ root := by
        intro heq
        have hzero := (B.intrinsicBoundaryRootedTreeHeight_eq_zero_iff root _).mpr heq
        omega
      rw [Function.iterate_succ_apply']
      have hstep := B.intrinsicBoundaryRootedTreeParent_height_succ root _ hcur_ne
      omega

theorem intrinsicBoundaryRootedTree_height_ancestor
    (B : DirichletBoundarySegments X o) (root q r : B.IntrinsicBoundaryGraphVertex)
    (h : B.intrinsicBoundaryRootedTreeAncestor root q r) :
    B.intrinsicBoundaryRootedTreeHeight root q ≤
      B.intrinsicBoundaryRootedTreeHeight root r := h.1

theorem intrinsicBoundaryRootedTree_ancestor_partition
    (B : DirichletBoundarySegments X o) (root q r : B.IntrinsicBoundaryGraphVertex) :
    B.intrinsicBoundaryRootedTreeAncestor root q r ↔
      r = q ∨ ∃ e ∈ B.intrinsicBoundaryRootedTreeChildren root q,
        B.intrinsicBoundaryRootedTreeAncestor root e.val r := by
  classical
  constructor
  · intro h
    by_cases hqr : q = r
    · exact Or.inl hqr.symm
    · have hheight_ne : B.intrinsicBoundaryRootedTreeHeight root q ≠
          B.intrinsicBoundaryRootedTreeHeight root r := by
        intro heq
        have hrq : r = q := by
          simpa [heq] using h.2
        exact hqr hrq.symm
      have hlt := lt_of_le_of_ne h.1 hheight_ne
      let n := B.intrinsicBoundaryRootedTreeHeight root r -
        B.intrinsicBoundaryRootedTreeHeight root q
      have hn : 0 < n := by dsimp [n]; omega
      have hnm : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn.ne')
      let c := (B.intrinsicBoundaryRootedTreeParent root)^[n - 1] r
      have hcHeight : B.intrinsicBoundaryRootedTreeHeight root c =
          B.intrinsicBoundaryRootedTreeHeight root q + 1 := by
        have hiterHeight := B.intrinsicBoundaryRootedTreeParentIter_height root r (n - 1)
          (by dsimp [n]; omega)
        change B.intrinsicBoundaryRootedTreeHeight root c + (n - 1) =
          B.intrinsicBoundaryRootedTreeHeight root r at hiterHeight
        omega
      have hc_ne : c ≠ root := by
        intro hc
        have hzero := (B.intrinsicBoundaryRootedTreeHeight_eq_zero_iff root c).mpr hc
        omega
      have hiter : (B.intrinsicBoundaryRootedTreeParent root)^[n] r = q := by
        change (B.intrinsicBoundaryRootedTreeParent root) ^[
          B.intrinsicBoundaryRootedTreeHeight root r -
            B.intrinsicBoundaryRootedTreeHeight root q] r = q
        exact h.2
      have hparent_c : B.intrinsicBoundaryRootedTreeParent root c = q := by
        rw [← hnm, Function.iterate_succ_apply'] at hiter
        exact hiter
      have he : (⟨c, hc_ne⟩ : B.IntrinsicBoundaryRootedTreeChild root) ∈
          B.intrinsicBoundaryRootedTreeChildren root q :=
        (B.intrinsicBoundaryRootedTree_mem_children_iff root q ⟨c, hc_ne⟩).mpr hparent_c
      refine Or.inr ⟨⟨c, hc_ne⟩, he, ?_⟩
      refine ⟨?_, ?_⟩
      · rw [hcHeight]
        omega
      · have hdiff : B.intrinsicBoundaryRootedTreeHeight root r -
            B.intrinsicBoundaryRootedTreeHeight root c = n - 1 := by
          dsimp [n]
          omega
        dsimp [intrinsicBoundaryRootedTreeAncestor]
        rw [hdiff]
  · rintro (hqr | ⟨e, he, hchild⟩)
    · subst r
      exact ⟨le_rfl, by simp⟩
    · have hparent := (B.intrinsicBoundaryRootedTree_mem_children_iff root q e).mp he
      have hchildHeight := B.intrinsicBoundaryRootedTreeParent_height_succ root e.val e.property
      rw [hparent] at hchildHeight
      have hdiff : B.intrinsicBoundaryRootedTreeHeight root r -
          B.intrinsicBoundaryRootedTreeHeight root q =
        (B.intrinsicBoundaryRootedTreeHeight root r -
          B.intrinsicBoundaryRootedTreeHeight root e.val) + 1 := by
        have hle := hchild.1
        omega
      refine ⟨by omega, ?_⟩
      dsimp [intrinsicBoundaryRootedTreeAncestor] at hchild ⊢
      rw [hdiff, Function.iterate_succ_apply', hchild.2, hparent]

theorem intrinsicBoundaryRootedTree_sibling_disjoint
    (B : DirichletBoundarySegments X o) (root q : B.IntrinsicBoundaryGraphVertex)
    (e f : B.IntrinsicBoundaryRootedTreeChild root)
    (he : e ∈ B.intrinsicBoundaryRootedTreeChildren root q)
    (hf : f ∈ B.intrinsicBoundaryRootedTreeChildren root q) (hef : e ≠ f)
    (r : B.IntrinsicBoundaryGraphVertex)
    (her : B.intrinsicBoundaryRootedTreeAncestor root e.val r) :
    ¬ B.intrinsicBoundaryRootedTreeAncestor root f.val r := by
  intro hfr
  have hpe := (B.intrinsicBoundaryRootedTree_mem_children_iff root q e).mp he
  have hpf := (B.intrinsicBoundaryRootedTree_mem_children_iff root q f).mp hf
  have hhe := B.intrinsicBoundaryRootedTreeParent_height_succ root e.val e.property
  have hhf := B.intrinsicBoundaryRootedTreeParent_height_succ root f.val f.property
  rw [hpe] at hhe
  rw [hpf] at hhf
  have hdiff : B.intrinsicBoundaryRootedTreeHeight root r -
      B.intrinsicBoundaryRootedTreeHeight root e.val =
    B.intrinsicBoundaryRootedTreeHeight root r -
      B.intrinsicBoundaryRootedTreeHeight root f.val := by
    omega
  have hval : e.val = f.val := by
    rw [← her.2, ← hfr.2, hdiff]
  exact hef (Subtype.ext hval)

/-- The actual spanning-tree edge from a non-root child to its parent. -/
def intrinsicBoundaryRootedTreeChildEdge (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex)
    (e : B.IntrinsicBoundaryRootedTreeChild root) :
    B.intrinsicBoundarySpanningTree.edgeSet :=
  ⟨s(B.intrinsicBoundaryRootedTreeParent root e.val, e.val),
    (B.intrinsicBoundarySpanningTree.mem_edgeSet).mpr
      (B.intrinsicBoundaryRootedTreeParent_adj root e.val e.property)⟩

/-- The exact native side chosen by the actual selected tree edge for this
parent-child pair; this preserves the spanning tree's physical edge even when
parallel sides have the same quotient endpoints. -/
def intrinsicBoundaryRootedTreeChildSide (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex)
    (e : B.IntrinsicBoundaryRootedTreeChild root) :
    Fin B.intrinsicBoundaryRadialCuts.card :=
  B.intrinsicBoundaryTreeEdgeSide
    (B.intrinsicBoundaryRootedTreeChildEdge root e)

/-- The actual orientation of a tree edge whose terminal vertex is its parent. -/
def intrinsicBoundaryRootedTreeChildSourceDart (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex)
    (e : B.IntrinsicBoundaryRootedTreeChild root) :
    Fin B.intrinsicBoundaryRadialCuts.card :=
  if B.intrinsicBoundaryGraphSideStart (B.intrinsicBoundaryRootedTreeChildSide root e) =
      B.intrinsicBoundaryRootedTreeParent root e.val then
    B.intrinsicCyclicPairing (B.intrinsicBoundaryRootedTreeChildSide root e)
  else B.intrinsicBoundaryRootedTreeChildSide root e

/-- The paired side at the child end of the actual parent-child edge. -/
def intrinsicBoundaryRootedTreeChildTargetDart (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex)
    (e : B.IntrinsicBoundaryRootedTreeChild root) :
    Fin B.intrinsicBoundaryRadialCuts.card :=
  B.intrinsicCyclicPairing (B.intrinsicBoundaryRootedTreeChildSourceDart root e)

theorem intrinsicBoundaryRootedTreeChildSourceDart_end
    (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex)
    (e : B.IntrinsicBoundaryRootedTreeChild root) :
    B.intrinsicBoundaryGraphSideEnd
        (B.intrinsicBoundaryRootedTreeChildSourceDart root e) =
      B.intrinsicBoundaryRootedTreeParent root e.val := by
  classical
  let i := B.intrinsicBoundaryRootedTreeChildSide root e
  have hends := Sym2.eq_iff.mp
    (B.intrinsicBoundaryTreeEdgeSide_endpoints
      (B.intrinsicBoundaryRootedTreeChildEdge root e))
  change (B.intrinsicBoundaryGraphSideStart i =
      B.intrinsicBoundaryRootedTreeParent root e.val ∧
      B.intrinsicBoundaryGraphSideEnd i = e.val) ∨
    (B.intrinsicBoundaryGraphSideStart i = e.val ∧
      B.intrinsicBoundaryGraphSideEnd i = B.intrinsicBoundaryRootedTreeParent root e.val)
      at hends
  rcases hends with ⟨hstart, hend⟩ | ⟨hstart, hend⟩
  · change B.intrinsicBoundaryGraphSideEnd
      (if B.intrinsicBoundaryGraphSideStart i =
          B.intrinsicBoundaryRootedTreeParent root e.val then
        B.intrinsicCyclicPairing i else i) = _
    rw [if_pos hstart, (B.intrinsicBoundaryGraphSide_pair_endpoints i).2, hstart]
  · change B.intrinsicBoundaryGraphSideEnd
      (if B.intrinsicBoundaryGraphSideStart i =
          B.intrinsicBoundaryRootedTreeParent root e.val then
        B.intrinsicCyclicPairing i else i) = _
    have hnot : B.intrinsicBoundaryGraphSideStart i ≠
        B.intrinsicBoundaryRootedTreeParent root e.val := by
      intro h
      have hadj := B.intrinsicBoundaryRootedTreeParent_adj root e.val e.property
      exact hadj.ne (hstart.symm.trans h).symm
    rw [if_neg hnot, hend]

theorem intrinsicBoundaryRootedTreeChildSourceDart_start
    (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex)
    (e : B.IntrinsicBoundaryRootedTreeChild root) :
    B.intrinsicBoundaryGraphSideStart
        (B.intrinsicBoundaryRootedTreeChildSourceDart root e) = e.val := by
  classical
  let i := B.intrinsicBoundaryRootedTreeChildSide root e
  have hends := Sym2.eq_iff.mp
    (B.intrinsicBoundaryTreeEdgeSide_endpoints
      (B.intrinsicBoundaryRootedTreeChildEdge root e))
  change (B.intrinsicBoundaryGraphSideStart i =
      B.intrinsicBoundaryRootedTreeParent root e.val ∧
      B.intrinsicBoundaryGraphSideEnd i = e.val) ∨
    (B.intrinsicBoundaryGraphSideStart i = e.val ∧
      B.intrinsicBoundaryGraphSideEnd i = B.intrinsicBoundaryRootedTreeParent root e.val)
      at hends
  rcases hends with ⟨hstart, hend⟩ | ⟨hstart, hend⟩
  · change B.intrinsicBoundaryGraphSideStart
      (if B.intrinsicBoundaryGraphSideStart i =
          B.intrinsicBoundaryRootedTreeParent root e.val then
        B.intrinsicCyclicPairing i else i) = _
    rw [if_pos hstart, (B.intrinsicBoundaryGraphSide_pair_endpoints i).1, hend]
  · change B.intrinsicBoundaryGraphSideStart
      (if B.intrinsicBoundaryGraphSideStart i =
          B.intrinsicBoundaryRootedTreeParent root e.val then
        B.intrinsicCyclicPairing i else i) = _
    have hnot : B.intrinsicBoundaryGraphSideStart i ≠
        B.intrinsicBoundaryRootedTreeParent root e.val := by
      intro h
      have hadj := B.intrinsicBoundaryRootedTreeParent_adj root e.val e.property
      exact hadj.ne (hstart.symm.trans h).symm
    rw [if_neg hnot, hstart]

theorem intrinsicBoundaryRootedTreeChildTargetDart_end
    (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex)
    (e : B.IntrinsicBoundaryRootedTreeChild root) :
    B.intrinsicBoundaryGraphSideEnd
        (B.intrinsicBoundaryRootedTreeChildTargetDart root e) = e.val := by
  rw [intrinsicBoundaryRootedTreeChildTargetDart,
    (B.intrinsicBoundaryGraphSide_pair_endpoints
      (B.intrinsicBoundaryRootedTreeChildSourceDart root e)).2,
    B.intrinsicBoundaryRootedTreeChildSourceDart_start]

/-- The actual rooted-tree adapter, parameterized only by the future local
cyclic words. The block contract states exactly that each supplied word is a
nodup enumeration of one terminal-vertex fiber. All tree, ancestry, and
attachment-dart fields are constructed from the actual selected graph tree. -/
def intrinsicBoundaryRootedCycleTreeData
    (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex)
    (block : B.IntrinsicBoundaryGraphVertex →
      List (Fin B.intrinsicBoundaryRadialCuts.card))
    (block_nodup : ∀ q, (block q).Nodup)
    (mem_block_iff : ∀ q d,
      d ∈ block q ↔ B.intrinsicBoundaryGraphSideEnd d = q) :
    RootedCycleTreeData B.IntrinsicBoundaryGraphVertex
      (B.IntrinsicBoundaryRootedTreeChild root)
      (Fin B.intrinsicBoundaryRadialCuts.card) := by
  classical
  refine
    { height := B.intrinsicBoundaryRootedTreeHeight root
      children := B.intrinsicBoundaryRootedTreeChildren root
      children_nodup := ?_
      target := fun e => e.val
      height_child := ?_
      ancestor := B.intrinsicBoundaryRootedTreeAncestor root
      height_ancestor := ?_
      ancestor_partition := B.intrinsicBoundaryRootedTree_ancestor_partition root
      sibling_disjoint := ?_
      vertex := B.intrinsicBoundaryGraphSideEnd
      block := block
      block_nodup := block_nodup
      mem_block_iff := mem_block_iff
      sourceDart := B.intrinsicBoundaryRootedTreeChildSourceDart root
      targetDart := B.intrinsicBoundaryRootedTreeChildTargetDart root
      sourceDart_mem := ?_
      targetDart_mem := ?_ }
  · intro q
    unfold intrinsicBoundaryRootedTreeChildren
    exact (Finset.nodup_toList _).filter _
  · intro q e he
    have hparent := (B.intrinsicBoundaryRootedTree_mem_children_iff root q e).mp he
    have hheight := B.intrinsicBoundaryRootedTreeParent_height_succ root e.val e.property
    rw [hparent] at hheight
    omega
  · exact fun q r h => h.1
  · intro q e f he hf hef r her
    exact B.intrinsicBoundaryRootedTree_sibling_disjoint root q e f he hf hef r her
  · intro q e he
    have hparent := (B.intrinsicBoundaryRootedTree_mem_children_iff root q e).mp he
    exact (mem_block_iff q (B.intrinsicBoundaryRootedTreeChildSourceDart root e)).mpr (by
      rw [B.intrinsicBoundaryRootedTreeChildSourceDart_end, hparent])
  · intro q e he
    exact (mem_block_iff e.val
      (B.intrinsicBoundaryRootedTreeChildTargetDart root e)).mpr (by
        rw [B.intrinsicBoundaryRootedTreeChildTargetDart_end])

#print axioms intrinsicBoundaryRootedCycleTreeData
#print axioms intrinsicBoundaryRootedTree_root_ancestor

end

end SystolicGrowth.DirichletBoundarySegments
