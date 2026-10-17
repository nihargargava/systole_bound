module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SurfaceBoundaryRootedTreeEdgeEnumeration
public import Geometry.SurfaceBoundaryGraphTreePairingProduct

@[expose] public section

/-!
# Reindexing the actual simultaneous tree pairing by rooted children

The child order below is transported from the exact edge-set list through the
proved parent-edge bijection. This preserves the noncommutative product order
used by the simultaneous tree-pairing theorem; no order-independence claim is
needed.
-/

open Set UpperHalfPlane
open scoped Pointwise UpperHalfPlane Classical

namespace SystolicGrowth.DirichletBoundarySegments

noncomputable section

variable {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}

/-- The actual literal transposition attached to a rooted nonroot child. -/
def intrinsicBoundaryRootedChildTreeSwap (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex)
    (child : B.IntrinsicBoundaryRootedTreeChild root) :
    Equiv.Perm (Fin B.intrinsicBoundaryRadialCuts.card) :=
  Equiv.swap (B.intrinsicBoundaryRootedTreeChildSourceDart root child)
    (B.intrinsicBoundaryRootedTreeChildTargetDart root child)

/-- The rooted child edge equivalence, supplied by the actual finite-tree
edge enumeration. -/
def intrinsicBoundaryRootedChildEdgeEquiv
    (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex) :
    B.IntrinsicBoundaryRootedTreeChild root ≃
      B.intrinsicBoundarySpanningTree.edgeSet :=
  Equiv.ofBijective (B.intrinsicBoundaryRootedTreeChildEdge root)
    (B.intrinsicBoundaryRootedTreeChildEdge_bijective root)

/-- Each rooted-child swap is exactly the literal swap used for its actual
selected physical tree edge. -/
theorem intrinsicBoundaryRootedChildTreeSwap_eq_treeEdgeSwap
    (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex)
    (child : B.IntrinsicBoundaryRootedTreeChild root) :
    B.intrinsicBoundaryRootedChildTreeSwap root child =
    B.intrinsicBoundaryTreeEdgeSwap
        (B.intrinsicBoundaryRootedTreeChildEdge root child) := by
  classical
  let edge := B.intrinsicBoundaryRootedTreeChildEdge root child
  let side := B.intrinsicBoundaryTreeEdgeSide edge
  have hsource : B.intrinsicBoundaryRootedTreeChildSourceDart root child =
      if B.intrinsicBoundaryGraphSideStart side =
          B.intrinsicBoundaryRootedTreeParent root child.val then
        B.intrinsicCyclicPairing side else side := by
    rfl
  unfold intrinsicBoundaryRootedChildTreeSwap intrinsicBoundaryTreeEdgeSwap
  change Equiv.swap (B.intrinsicBoundaryRootedTreeChildSourceDart root child)
      (B.intrinsicCyclicPairing
        (B.intrinsicBoundaryRootedTreeChildSourceDart root child)) =
    Equiv.swap side (B.intrinsicCyclicPairing side)
  rw [hsource]
  by_cases hstart : B.intrinsicBoundaryGraphSideStart side =
      B.intrinsicBoundaryRootedTreeParent root child.val
  · simp only [if_pos hstart]
    rw [B.intrinsicCyclicPairing_involutive]
    exact Equiv.swap_comm _ _
  · simp only [if_neg hstart]

private theorem intrinsicBoundaryRootedChildSourceDart_physicalEdge
    (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex)
    (child : B.IntrinsicBoundaryRootedTreeChild root) :
    B.intrinsicBoundaryPhysicalEdge
        (B.intrinsicBoundaryRootedTreeChildSourceDart root child) =
      B.intrinsicBoundaryTreePhysicalEdge
        (B.intrinsicBoundaryRootedTreeChildEdge root child) := by
  classical
  let side := B.intrinsicBoundaryTreeEdgeSide
    (B.intrinsicBoundaryRootedTreeChildEdge root child)
  change B.intrinsicBoundaryPhysicalEdge
      (if B.intrinsicBoundaryGraphSideStart side =
          B.intrinsicBoundaryRootedTreeParent root child.val then
        B.intrinsicCyclicPairing side else side) =
    B.intrinsicBoundaryPhysicalEdge side
  split_ifs
  · exact B.intrinsicBoundaryPhysicalEdge_pair side
  · rfl

private theorem intrinsicBoundaryRootedChildTargetDart_physicalEdge
    (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex)
    (child : B.IntrinsicBoundaryRootedTreeChild root) :
    B.intrinsicBoundaryPhysicalEdge
        (B.intrinsicBoundaryRootedTreeChildTargetDart root child) =
      B.intrinsicBoundaryTreePhysicalEdge
        (B.intrinsicBoundaryRootedTreeChildEdge root child) := by
  rw [intrinsicBoundaryRootedTreeChildTargetDart,
    B.intrinsicBoundaryPhysicalEdge_pair,
    intrinsicBoundaryRootedChildSourceDart_physicalEdge]

/-- Endpoints of two distinct rooted-child swaps are pairwise distinct. The
proof descends endpoint darts to their actual physical edge, then uses the
tree-child equivalence and injectivity of the selected physical tree edges. -/
theorem intrinsicBoundaryRootedChildTreeSwap_endpoints_nodup
    (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex)
    {child₁ child₂ : B.IntrinsicBoundaryRootedTreeChild root}
    (hchildren : child₁ ≠ child₂) :
    [ B.intrinsicBoundaryRootedTreeChildSourceDart root child₁
    , B.intrinsicBoundaryRootedTreeChildTargetDart root child₁
    , B.intrinsicBoundaryRootedTreeChildSourceDart root child₂
    , B.intrinsicBoundaryRootedTreeChildTargetDart root child₂ ].Nodup := by
  classical
  let source₁ := B.intrinsicBoundaryRootedTreeChildSourceDart root child₁
  let target₁ := B.intrinsicBoundaryRootedTreeChildTargetDart root child₁
  let source₂ := B.intrinsicBoundaryRootedTreeChildSourceDart root child₂
  let target₂ := B.intrinsicBoundaryRootedTreeChildTargetDart root child₂
  have hphysical_ne :
      B.intrinsicBoundaryTreePhysicalEdge
          (B.intrinsicBoundaryRootedTreeChildEdge root child₁) ≠
        B.intrinsicBoundaryTreePhysicalEdge
          (B.intrinsicBoundaryRootedTreeChildEdge root child₂) := by
    intro h
    apply hchildren
    apply B.intrinsicBoundaryRootedTreeChildEdge_injective root
    exact B.intrinsicBoundaryTreePhysicalEdge_injective h
  have hsource₁ : B.intrinsicBoundaryPhysicalEdge source₁ =
      B.intrinsicBoundaryTreePhysicalEdge
        (B.intrinsicBoundaryRootedTreeChildEdge root child₁) :=
    B.intrinsicBoundaryRootedChildSourceDart_physicalEdge root child₁
  have htarget₁ : B.intrinsicBoundaryPhysicalEdge target₁ =
      B.intrinsicBoundaryTreePhysicalEdge
        (B.intrinsicBoundaryRootedTreeChildEdge root child₁) :=
    B.intrinsicBoundaryRootedChildTargetDart_physicalEdge root child₁
  have hsource₂ : B.intrinsicBoundaryPhysicalEdge source₂ =
      B.intrinsicBoundaryTreePhysicalEdge
        (B.intrinsicBoundaryRootedTreeChildEdge root child₂) :=
    B.intrinsicBoundaryRootedChildSourceDart_physicalEdge root child₂
  have htarget₂ : B.intrinsicBoundaryPhysicalEdge target₂ =
      B.intrinsicBoundaryTreePhysicalEdge
        (B.intrinsicBoundaryRootedTreeChildEdge root child₂) :=
    B.intrinsicBoundaryRootedChildTargetDart_physicalEdge root child₂
  have hcross (x : Fin B.intrinsicBoundaryRadialCuts.card)
      (hx : B.intrinsicBoundaryPhysicalEdge x =
        B.intrinsicBoundaryTreePhysicalEdge
          (B.intrinsicBoundaryRootedTreeChildEdge root child₁))
      (y : Fin B.intrinsicBoundaryRadialCuts.card)
      (hy : B.intrinsicBoundaryPhysicalEdge y =
        B.intrinsicBoundaryTreePhysicalEdge
          (B.intrinsicBoundaryRootedTreeChildEdge root child₂)) : x ≠ y := by
    intro hxy
    apply hphysical_ne
    calc
      B.intrinsicBoundaryTreePhysicalEdge
          (B.intrinsicBoundaryRootedTreeChildEdge root child₁) =
        B.intrinsicBoundaryPhysicalEdge x := hx.symm
      _ = B.intrinsicBoundaryPhysicalEdge y := congrArg B.intrinsicBoundaryPhysicalEdge hxy
      _ = B.intrinsicBoundaryTreePhysicalEdge
          (B.intrinsicBoundaryRootedTreeChildEdge root child₂) := hy
  have hsource_target₁ : source₁ ≠ target₁ := by
    change B.intrinsicBoundaryRootedTreeChildSourceDart root child₁ ≠
      B.intrinsicCyclicPairing
        (B.intrinsicBoundaryRootedTreeChildSourceDart root child₁)
    exact (B.intrinsicCyclicPairing_ne_self source₁).symm
  have hsource_target₂self : source₂ ≠ target₂ := by
    change B.intrinsicBoundaryRootedTreeChildSourceDart root child₂ ≠
      B.intrinsicCyclicPairing
        (B.intrinsicBoundaryRootedTreeChildSourceDart root child₂)
    exact (B.intrinsicCyclicPairing_ne_self source₂).symm
  have hsource_source₂ := hcross source₁ hsource₁ source₂ hsource₂
  have hsource_target₂ := hcross source₁ hsource₁ target₂ htarget₂
  have htarget_source₂ := hcross target₁ htarget₁ source₂ hsource₂
  have htarget_target₂ := hcross target₁ htarget₁ target₂ htarget₂
  change [source₁, target₁, source₂, target₂].Nodup
  refine List.nodup_cons.mpr ⟨?_, ?_⟩
  · simp only [List.mem_cons, not_or, List.not_mem_nil]
    exact ⟨hsource_target₁,
      ⟨hsource_source₂, ⟨hsource_target₂, by simp⟩⟩⟩
  refine List.nodup_cons.mpr ⟨?_, ?_⟩
  · simp only [List.mem_cons, not_or, List.not_mem_nil]
    exact ⟨htarget_source₂, ⟨htarget_target₂, by simp⟩⟩
  refine List.nodup_cons.mpr ⟨?_, ?_⟩
  · simp only [List.mem_cons, not_or, List.not_mem_nil]
    exact ⟨hsource_target₂self, by simp⟩
  exact List.nodup_singleton _

/-- Swaps associated to distinct children of one actual rooted vertex have
disjoint supports, since their four physical dart endpoints are distinct. -/
theorem intrinsicBoundaryRootedChildTreeSwap_disjoint
    (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex)
    {child₁ child₂ : B.IntrinsicBoundaryRootedTreeChild root}
    (hchildren : child₁ ≠ child₂) :
    Equiv.Perm.Disjoint (B.intrinsicBoundaryRootedChildTreeSwap root child₁)
      (B.intrinsicBoundaryRootedChildTreeSwap root child₂) := by
  unfold intrinsicBoundaryRootedChildTreeSwap
  exact Equiv.Perm.disjoint_swap_swap
    (B.intrinsicBoundaryRootedChildTreeSwap_endpoints_nodup root hchildren)

/-- Distinct sibling swaps therefore commute. This is the order exchange
needed when the recursive child traversal is aligned with the edge product. -/
theorem intrinsicBoundaryRootedChildTreeSwap_commute
    (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex)
    {child₁ child₂ : B.IntrinsicBoundaryRootedTreeChild root}
    (hchildren : child₁ ≠ child₂) :
    Commute (B.intrinsicBoundaryRootedChildTreeSwap root child₁)
      (B.intrinsicBoundaryRootedChildTreeSwap root child₂) :=
  (B.intrinsicBoundaryRootedChildTreeSwap_disjoint root hchildren).commute

/-- Whether the dart is an endpoint of one of the rooted-child swaps selected
by a predicate. -/
def intrinsicBoundaryRootedChildSwapContains
    (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex)
    (A : B.IntrinsicBoundaryRootedTreeChild root → Prop)
    (d : Fin B.intrinsicBoundaryRadialCuts.card) : Prop :=
  ∃ child, A child ∧
    (d = B.intrinsicBoundaryRootedTreeChildSourceDart root child ∨
      d = B.intrinsicBoundaryRootedTreeChildTargetDart root child)

/-- The simultaneous product of physical swaps selected by a rooted-child
predicate. The order is the native finite enumeration of the child subtype. -/
def intrinsicBoundaryRestrictedRootedChildTreeSwapPerm
    (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex)
    (A : B.IntrinsicBoundaryRootedTreeChild root → Prop) :
    Equiv.Perm (Fin B.intrinsicBoundaryRadialCuts.card) := by
  classical
  exact ((List.filter A
    ((Finset.univ : Finset (B.IntrinsicBoundaryRootedTreeChild root)).toList)).map
      (B.intrinsicBoundaryRootedChildTreeSwap root)).prod

def intrinsicBoundaryRootedChildSwapEndpoint
    (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex)
    (child : B.IntrinsicBoundaryRootedTreeChild root)
    (d : Fin B.intrinsicBoundaryRadialCuts.card) : Prop :=
  d = B.intrinsicBoundaryRootedTreeChildSourceDart root child ∨
    d = B.intrinsicBoundaryRootedTreeChildTargetDart root child

private theorem intrinsicBoundaryRootedChildSwapEndpoint_pair_iff
    (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex)
    (child : B.IntrinsicBoundaryRootedTreeChild root)
    (d : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryRootedChildSwapEndpoint root child
        (B.intrinsicCyclicPairing d) ↔
      B.intrinsicBoundaryRootedChildSwapEndpoint root child d := by
  unfold intrinsicBoundaryRootedChildSwapEndpoint
  constructor
  · rintro (h | h)
    · right
      calc
        d = B.intrinsicCyclicPairing (B.intrinsicCyclicPairing d) :=
          (B.intrinsicCyclicPairing_involutive d).symm
        _ = B.intrinsicCyclicPairing
            (B.intrinsicBoundaryRootedTreeChildSourceDart root child) :=
          congrArg B.intrinsicCyclicPairing h
        _ = B.intrinsicBoundaryRootedTreeChildTargetDart root child := by
          rw [intrinsicBoundaryRootedTreeChildTargetDart]
    · left
      calc
        d = B.intrinsicCyclicPairing (B.intrinsicCyclicPairing d) :=
          (B.intrinsicCyclicPairing_involutive d).symm
        _ = B.intrinsicCyclicPairing
            (B.intrinsicBoundaryRootedTreeChildTargetDart root child) :=
          congrArg B.intrinsicCyclicPairing h
        _ = B.intrinsicBoundaryRootedTreeChildSourceDart root child := by
          rw [intrinsicBoundaryRootedTreeChildTargetDart,
            B.intrinsicCyclicPairing_involutive]
  · rintro (h | h)
    · right
      calc
        B.intrinsicCyclicPairing d =
            B.intrinsicCyclicPairing
              (B.intrinsicBoundaryRootedTreeChildSourceDart root child) :=
          congrArg B.intrinsicCyclicPairing h
        _ = B.intrinsicBoundaryRootedTreeChildTargetDart root child := by
          rw [intrinsicBoundaryRootedTreeChildTargetDart]
    · left
      calc
        B.intrinsicCyclicPairing d =
            B.intrinsicCyclicPairing
              (B.intrinsicBoundaryRootedTreeChildTargetDart root child) :=
          congrArg B.intrinsicCyclicPairing h
        _ = B.intrinsicBoundaryRootedTreeChildSourceDart root child := by
          rw [intrinsicBoundaryRootedTreeChildTargetDart,
            B.intrinsicCyclicPairing_involutive]

private theorem intrinsicBoundaryRootedChild_eq_of_shared_endpoint
    (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex)
    {child₁ child₂ : B.IntrinsicBoundaryRootedTreeChild root}
    {d : Fin B.intrinsicBoundaryRadialCuts.card}
    (h₁ : B.intrinsicBoundaryRootedChildSwapEndpoint root child₁ d)
    (h₂ : B.intrinsicBoundaryRootedChildSwapEndpoint root child₂ d) :
    child₁ = child₂ := by
  have hphysical₁ : B.intrinsicBoundaryPhysicalEdge d =
      B.intrinsicBoundaryTreePhysicalEdge
        (B.intrinsicBoundaryRootedTreeChildEdge root child₁) := by
    rcases h₁ with h | h
    · rw [h]
      exact B.intrinsicBoundaryRootedChildSourceDart_physicalEdge root child₁
    · rw [h]
      exact B.intrinsicBoundaryRootedChildTargetDart_physicalEdge root child₁
  have hphysical₂ : B.intrinsicBoundaryPhysicalEdge d =
      B.intrinsicBoundaryTreePhysicalEdge
        (B.intrinsicBoundaryRootedTreeChildEdge root child₂) := by
    rcases h₂ with h | h
    · rw [h]
      exact B.intrinsicBoundaryRootedChildSourceDart_physicalEdge root child₂
    · rw [h]
      exact B.intrinsicBoundaryRootedChildTargetDart_physicalEdge root child₂
  apply B.intrinsicBoundaryRootedTreeChildEdge_injective root
  apply B.intrinsicBoundaryTreePhysicalEdge_injective
  exact hphysical₁.symm.trans hphysical₂

private theorem intrinsicBoundaryRootedChildTreeSwap_apply
    (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex)
    (child : B.IntrinsicBoundaryRootedTreeChild root)
    (d : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryRootedChildTreeSwap root child d =
      if B.intrinsicBoundaryRootedChildSwapEndpoint root child d then
        B.intrinsicCyclicPairing d else d := by
  classical
  let source := B.intrinsicBoundaryRootedTreeChildSourceDart root child
  let target := B.intrinsicBoundaryRootedTreeChildTargetDart root child
  have htarget : target = B.intrinsicCyclicPairing source := rfl
  have hsource_target : source ≠ target := by
    change B.intrinsicBoundaryRootedTreeChildSourceDart root child ≠
      B.intrinsicCyclicPairing
        (B.intrinsicBoundaryRootedTreeChildSourceDart root child)
    exact (B.intrinsicCyclicPairing_ne_self source).symm
  unfold intrinsicBoundaryRootedChildTreeSwap intrinsicBoundaryRootedChildSwapEndpoint
  by_cases hs : d = source
  · subst d
    rw [Equiv.swap_apply_left]
    rw [if_pos (Or.inl rfl)]
    exact htarget
  · by_cases ht : d = target
    · subst d
      rw [Equiv.swap_apply_right]
      rw [if_pos (Or.inr rfl)]
      rw [htarget]
      exact (B.intrinsicCyclicPairing_involutive source).symm
    · have hpair : d ≠ B.intrinsicCyclicPairing source := by
        intro h
        apply ht
        simpa [target, intrinsicBoundaryRootedTreeChildTargetDart] using h
      calc
        Equiv.swap source target d = d :=
          Equiv.swap_apply_of_ne_of_ne hs ht
        _ = if B.intrinsicBoundaryRootedChildSwapEndpoint root child d then
              B.intrinsicCyclicPairing d else d := by
          simp [intrinsicBoundaryRootedChildSwapEndpoint, source, target, hs, ht]

def intrinsicBoundaryRootedChildSwapListContains
    (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex)
    (children : List (B.IntrinsicBoundaryRootedTreeChild root))
    (d : Fin B.intrinsicBoundaryRadialCuts.card) : Prop :=
  ∃ child ∈ children, B.intrinsicBoundaryRootedChildSwapEndpoint root child d

private theorem intrinsicBoundaryRootedChildTreeSwapList_prod_apply
    (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex)
    (children : List (B.IntrinsicBoundaryRootedTreeChild root))
    (hchildren : children.Nodup)
    (d : Fin B.intrinsicBoundaryRadialCuts.card) :
    (children.map (B.intrinsicBoundaryRootedChildTreeSwap root)).prod d =
      if B.intrinsicBoundaryRootedChildSwapListContains root children d then
        B.intrinsicCyclicPairing d else d := by
  classical
  induction children with
  | nil => simp [intrinsicBoundaryRootedChildSwapListContains]
  | cons child tail ih =>
      rw [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply, ih hchildren.of_cons]
      by_cases hhead : B.intrinsicBoundaryRootedChildSwapEndpoint root child d
      · have htail : ¬
          B.intrinsicBoundaryRootedChildSwapListContains root tail d := by
          rintro ⟨other, hmem, hother⟩
          have hne : child ≠ other := by
            intro heq
            subst other
            exact (List.nodup_cons.mp hchildren).1 hmem
          exact hne
            (B.intrinsicBoundaryRootedChild_eq_of_shared_endpoint root hhead hother)
        have hfull : B.intrinsicBoundaryRootedChildSwapListContains root
            (child :: tail) d := ⟨child, by simp, hhead⟩
        rw [if_neg htail, B.intrinsicBoundaryRootedChildTreeSwap_apply]
        rw [if_pos hfull]
        simp [hhead]
      · by_cases htail :
          B.intrinsicBoundaryRootedChildSwapListContains root tail d
        · have htail_mem := htail
          rcases htail with ⟨other, hmem, hother⟩
          have hnotPair : ¬ B.intrinsicBoundaryRootedChildSwapEndpoint root child
              (B.intrinsicCyclicPairing d) := by
            intro hpair
            exact hhead
              ((B.intrinsicBoundaryRootedChildSwapEndpoint_pair_iff root child d).mp
                hpair)
          have hfull : B.intrinsicBoundaryRootedChildSwapListContains root
              (child :: tail) d := ⟨other, by simp [hmem], hother⟩
          rw [if_pos htail_mem, B.intrinsicBoundaryRootedChildTreeSwap_apply,
            if_pos hfull]
          simp [hnotPair]
        · have hfull : ¬ B.intrinsicBoundaryRootedChildSwapListContains root
              (child :: tail) d := by
            rintro ⟨other, hmem, hother⟩
            rcases List.mem_cons.mp hmem with heq | hmem_tail
            · subst other
              exact hhead hother
            · exact htail ⟨other, hmem_tail, hother⟩
          rw [if_neg htail, B.intrinsicBoundaryRootedChildTreeSwap_apply,
            if_neg hfull]
          simp [hhead]

/-- A restricted rooted-child product acts by the cyclic pairing exactly on
the selected physical dart endpoints, and fixes every other dart. -/
theorem intrinsicBoundaryRestrictedRootedChildTreeSwapPerm_apply
    (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex)
    (A : B.IntrinsicBoundaryRootedTreeChild root → Prop)
    (d : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm root A d =
      if B.intrinsicBoundaryRootedChildSwapContains root A d then
        B.intrinsicCyclicPairing d else d := by
  classical
  let children : List (B.IntrinsicBoundaryRootedTreeChild root) :=
    Finset.univ.toList
  have hnodup : (List.filter A children).Nodup := by
    exact (Finset.nodup_toList _).filter _
  have hformula := B.intrinsicBoundaryRootedChildTreeSwapList_prod_apply
    root (List.filter A children) hnodup d
  change ((List.filter A children).map
      (B.intrinsicBoundaryRootedChildTreeSwap root)).prod d = _
  rw [hformula]
  congr 1
  unfold intrinsicBoundaryRootedChildSwapListContains
    intrinsicBoundaryRootedChildSwapContains
  simp only [intrinsicBoundaryRootedChildSwapEndpoint]
  simp only [children, List.mem_filter, Finset.mem_toList, Finset.mem_univ,
    decide_eq_true_eq, true_and]

private theorem intrinsicBoundaryRootedChildSwapContains_pair_iff
    (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex)
    (A : B.IntrinsicBoundaryRootedTreeChild root → Prop)
    (d : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryRootedChildSwapContains root A
        (B.intrinsicCyclicPairing d) ↔
      B.intrinsicBoundaryRootedChildSwapContains root A d := by
  unfold intrinsicBoundaryRootedChildSwapContains
  constructor
  · rintro ⟨child, hA, hendpoint⟩
    exact ⟨child, hA,
      (B.intrinsicBoundaryRootedChildSwapEndpoint_pair_iff root child d).mp hendpoint⟩
  · rintro ⟨child, hA, hendpoint⟩
    exact ⟨child, hA,
      (B.intrinsicBoundaryRootedChildSwapEndpoint_pair_iff root child d).mpr hendpoint⟩

/-- Disjoint child predicates give disjoint restricted supports, so their
restricted swap products multiply to the product for their union. -/
theorem intrinsicBoundaryRestrictedRootedChildTreeSwapPerm_union_mul
    (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex)
    (A C : B.IntrinsicBoundaryRootedTreeChild root → Prop)
    (hdisjoint : ∀ child, ¬ (A child ∧ C child)) :
    B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm root
        (fun child => A child ∨ C child) =
      B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm root A *
        B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm root C := by
  apply Equiv.ext
  intro d
  simp only [Equiv.Perm.mul_apply,
    B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm_apply]
  have hunion :
      B.intrinsicBoundaryRootedChildSwapContains root (fun child => A child ∨ C child) d ↔
        B.intrinsicBoundaryRootedChildSwapContains root A d ∨
          B.intrinsicBoundaryRootedChildSwapContains root C d := by
    unfold intrinsicBoundaryRootedChildSwapContains
    constructor
    · rintro ⟨child, hchild, hend⟩
      rcases hchild with hA | hC
      · exact Or.inl ⟨child, hA, hend⟩
      · exact Or.inr ⟨child, hC, hend⟩
    · rintro (⟨child, hA, hend⟩ | ⟨child, hC, hend⟩)
      · exact ⟨child, Or.inl hA, hend⟩
      · exact ⟨child, Or.inr hC, hend⟩
  by_cases hA : B.intrinsicBoundaryRootedChildSwapContains root A d
  · have hC : ¬ B.intrinsicBoundaryRootedChildSwapContains root C d := by
      rintro ⟨childC, hC, hendC⟩
      obtain ⟨childA, hA, hendA⟩ := hA
      have heq := B.intrinsicBoundaryRootedChild_eq_of_shared_endpoint root hendA hendC
      subst childC
      exact hdisjoint childA ⟨hA, hC⟩
    simp [hA, hC, hunion]
  · by_cases hC : B.intrinsicBoundaryRootedChildSwapContains root C d
    · have hApair :
          ¬ B.intrinsicBoundaryRootedChildSwapContains root A
            (B.intrinsicCyclicPairing d) := by
        intro h
        exact hA
          ((B.intrinsicBoundaryRootedChildSwapContains_pair_iff root A d).mp h)
      simp [hA, hC, hApair, hunion]
    · simp [hA, hC, hunion]

/-- Predicate extensionally equal choices define the same restricted swap. -/
theorem intrinsicBoundaryRestrictedRootedChildTreeSwapPerm_congr
    (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex)
    {A C : B.IntrinsicBoundaryRootedTreeChild root → Prop}
    (hAC : ∀ child, A child ↔ C child) :
    B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm root A =
      B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm root C := by
  apply Equiv.ext
  intro d
  rw [B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm_apply,
    B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm_apply]
  have hcontains :
      B.intrinsicBoundaryRootedChildSwapContains root A d ↔
        B.intrinsicBoundaryRootedChildSwapContains root C d := by
    unfold intrinsicBoundaryRootedChildSwapContains
    constructor
    · rintro ⟨child, hA, hend⟩
      exact ⟨child, (hAC child).mp hA, hend⟩
    · rintro ⟨child, hC, hend⟩
      exact ⟨child, (hAC child).mpr hC, hend⟩
  rw [if_congr hcontains rfl rfl]

/-- The empty choice predicate contributes the identity permutation. -/
theorem intrinsicBoundaryRestrictedRootedChildTreeSwapPerm_false
    (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex) :
    B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm root (fun _ => False) = 1 := by
  apply Equiv.ext
  intro d
  rw [B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm_apply]
  simp [intrinsicBoundaryRootedChildSwapContains]

/-- The predicate containing exactly one rooted child gives precisely that
child's physical transposition. -/
theorem intrinsicBoundaryRestrictedRootedChildTreeSwapPerm_singleton
    (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex)
    (child : B.IntrinsicBoundaryRootedTreeChild root) :
    B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm root
        (fun other => other = child) =
      B.intrinsicBoundaryRootedChildTreeSwap root child := by
  apply Equiv.ext
  intro d
  rw [B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm_apply,
    B.intrinsicBoundaryRootedChildTreeSwap_apply]
  have hcontains :
      B.intrinsicBoundaryRootedChildSwapContains root (fun other => other = child) d ↔
        B.intrinsicBoundaryRootedChildSwapEndpoint root child d := by
    unfold intrinsicBoundaryRootedChildSwapContains
    constructor
    · rintro ⟨other, rfl, hend⟩
      exact hend
    · intro hend
      exact ⟨child, rfl, hend⟩
  rw [if_congr hcontains rfl rfl]

/-- A finite list of pairwise disjoint child predicates composes by multiplying
their restricted swap permutations in list order. -/
theorem intrinsicBoundaryRestrictedRootedChildTreeSwapPerm_list_prod
    (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex)
    (predicates : List (B.IntrinsicBoundaryRootedTreeChild root → Prop))
    (hdisjoint : predicates.Pairwise
      (fun A C => ∀ child, ¬ (A child ∧ C child))) :
    (predicates.map (B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm root)).prod =
      B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm root
        (fun child => ∃ A ∈ predicates, A child) := by
  induction predicates with
  | nil =>
      simp only [List.map_nil, List.prod_nil]
      simpa using (B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm_false root).symm
  | cons A tail ih =>
      have hparts := List.pairwise_cons.mp hdisjoint
      have htail : tail.Pairwise (fun A C => ∀ child, ¬ (A child ∧ C child)) :=
        hparts.2
      have hdisj_tail : ∀ child, ¬ (A child ∧ ∃ C ∈ tail, C child) := by
        intro child h
        rcases h with ⟨hA, C, hCmem, hC⟩
        exact hparts.1 C hCmem child ⟨hA, hC⟩
      have hpred :
          (fun child => ∃ C ∈ A :: tail, C child) =
            (fun child => A child ∨ ∃ C ∈ tail, C child) := by
        funext child
        apply propext
        constructor
        · rintro ⟨C, hCmem, hC⟩
          rcases List.mem_cons.mp hCmem with hCA | hCtail
          · left
            simpa [hCA] using hC
          · exact Or.inr ⟨C, hCtail, hC⟩
        · rintro (hA | ⟨C, hCtail, hC⟩)
          · exact ⟨A, List.mem_cons_self, hA⟩
          · exact ⟨C, List.mem_cons_of_mem A hCtail, hC⟩
      rw [List.map_cons, List.prod_cons, ih htail]
      rw [← B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm_union_mul
        root A (fun child => ∃ C ∈ tail, C child) hdisj_tail]
      rw [hpred]

private theorem intrinsicBoundaryPhysicalEdge_eq_pair_or_self
    (B : DirichletBoundarySegments X o)
    (i j : Fin B.intrinsicBoundaryRadialCuts.card)
    (h : B.intrinsicBoundaryPhysicalEdge i = B.intrinsicBoundaryPhysicalEdge j) :
    i = j ∨ i = B.intrinsicCyclicPairing j := by
  classical
  have hv := congrArg (fun e : B.IntrinsicBoundaryPhysicalEdge => e.val) h
  by_cases hi : i < B.intrinsicCyclicPairing i <;>
    by_cases hj : j < B.intrinsicCyclicPairing j
  · simp only [intrinsicBoundaryPhysicalEdge, dif_pos hi, dif_pos hj] at hv
    exact Or.inl hv
  · simp only [intrinsicBoundaryPhysicalEdge, dif_pos hi, dif_neg hj] at hv
    exact Or.inr hv
  · simp only [intrinsicBoundaryPhysicalEdge, dif_neg hi, dif_pos hj] at hv
    right
    calc
      i = B.intrinsicCyclicPairing (B.intrinsicCyclicPairing i) :=
        (B.intrinsicCyclicPairing_involutive i).symm
      _ = B.intrinsicCyclicPairing j := congrArg B.intrinsicCyclicPairing hv
  · simp only [intrinsicBoundaryPhysicalEdge, dif_neg hi, dif_neg hj] at hv
    exact Or.inl (by
      calc
        i = B.intrinsicCyclicPairing (B.intrinsicCyclicPairing i) :=
          (B.intrinsicCyclicPairing_involutive i).symm
        _ = B.intrinsicCyclicPairing (B.intrinsicCyclicPairing j) :=
          congrArg B.intrinsicCyclicPairing hv
        _ = j := B.intrinsicCyclicPairing_involutive j)

private theorem intrinsicBoundaryRootedChildSwapContains_true_iff_treePhysicalEdge
    (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex)
    (d : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryRootedChildSwapContains root (fun _ => True) d ↔
      B.intrinsicBoundaryPhysicalEdge d ∈ Set.range B.intrinsicBoundaryTreePhysicalEdge := by
  constructor
  · rintro ⟨child, _, hend⟩
    rcases hend with hs | ht
    · refine ⟨B.intrinsicBoundaryRootedTreeChildEdge root child, ?_⟩
      rw [hs]
      exact (B.intrinsicBoundaryRootedChildSourceDart_physicalEdge root child).symm
    · refine ⟨B.intrinsicBoundaryRootedTreeChildEdge root child, ?_⟩
      rw [ht]
      exact (B.intrinsicBoundaryRootedChildTargetDart_physicalEdge root child).symm
  · rintro ⟨edge, hedge⟩
    obtain ⟨child, hchild⟩ :=
      (B.intrinsicBoundaryRootedTreeChildEdge_bijective root).2 edge
    have hphysical : B.intrinsicBoundaryPhysicalEdge d =
        B.intrinsicBoundaryPhysicalEdge
          (B.intrinsicBoundaryRootedTreeChildSourceDart root child) := by
      calc
        B.intrinsicBoundaryPhysicalEdge d =
            B.intrinsicBoundaryTreePhysicalEdge edge := hedge.symm
        _ = B.intrinsicBoundaryTreePhysicalEdge
            (B.intrinsicBoundaryRootedTreeChildEdge root child) :=
          congrArg B.intrinsicBoundaryTreePhysicalEdge hchild.symm
        _ = B.intrinsicBoundaryPhysicalEdge
            (B.intrinsicBoundaryRootedTreeChildSourceDart root child) :=
          (B.intrinsicBoundaryRootedChildSourceDart_physicalEdge root child).symm
    rcases B.intrinsicBoundaryPhysicalEdge_eq_pair_or_self d
        (B.intrinsicBoundaryRootedTreeChildSourceDart root child) hphysical with h | h
    · exact ⟨child, trivial, Or.inl h⟩
    · refine ⟨child, trivial, Or.inr ?_⟩
      calc
        d = B.intrinsicCyclicPairing
            (B.intrinsicBoundaryRootedTreeChildSourceDart root child) := h
        _ = B.intrinsicBoundaryRootedTreeChildTargetDart root child := rfl

/-- Taking all nonroot children recovers the actual simultaneous pairing of
the selected spanning-tree physical sides. -/
theorem intrinsicBoundaryRestrictedRootedChildTreeSwapPerm_true
    (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex) :
    B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm root (fun _ => True) =
      B.intrinsicBoundaryTreePairingPerm := by
  apply Equiv.ext
  intro d
  rw [B.intrinsicBoundaryRestrictedRootedChildTreeSwapPerm_apply,
    B.intrinsicBoundaryTreePairingPerm_apply]
  by_cases htree :
      B.intrinsicBoundaryPhysicalEdge d ∈ Set.range B.intrinsicBoundaryTreePhysicalEdge
  · have hret : ¬ B.intrinsicBoundaryRetainedSidePred d := by
      simpa [intrinsicBoundaryRetainedSidePred] using htree
    rw [if_pos ((B.intrinsicBoundaryRootedChildSwapContains_true_iff_treePhysicalEdge
      root d).2 htree), if_neg hret]
  · have hret : B.intrinsicBoundaryRetainedSidePred d := by
      simpa [intrinsicBoundaryRetainedSidePred] using htree
    rw [if_neg ((B.intrinsicBoundaryRootedChildSwapContains_true_iff_treePhysicalEdge
      root d).not.mpr htree), if_pos hret]

/-- An enumeration of all nonroot children, ordered by the actual edge-set
enumeration transported along the parent-edge equivalence. -/
def intrinsicBoundaryRootedChildSwapOrder
    (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex) :
    List (B.IntrinsicBoundaryRootedTreeChild root) :=
  ((Finset.univ : Finset (B.intrinsicBoundarySpanningTree.edgeSet)).toList).map
    (B.intrinsicBoundaryRootedChildEdgeEquiv root).symm

/-- The product of the actual edge swaps in that exact rooted-child order. -/
def intrinsicBoundaryRootedChildTreeSwapProduct
    (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex) :
    Equiv.Perm (Fin B.intrinsicBoundaryRadialCuts.card) :=
  (B.intrinsicBoundaryRootedChildSwapOrder root).map
    (B.intrinsicBoundaryRootedChildTreeSwap root) |>.prod

theorem intrinsicBoundaryRootedChildSwapOrder_nodup
    (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex) :
    (B.intrinsicBoundaryRootedChildSwapOrder root).Nodup := by
  classical
  unfold intrinsicBoundaryRootedChildSwapOrder
  exact List.Nodup.map
    (B.intrinsicBoundaryRootedChildEdgeEquiv root).symm.injective
    (Finset.nodup_toList _)

theorem intrinsicBoundaryRootedChild_mem_swapOrder
    (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex)
    (child : B.IntrinsicBoundaryRootedTreeChild root) :
    child ∈ B.intrinsicBoundaryRootedChildSwapOrder root := by
  classical
  unfold intrinsicBoundaryRootedChildSwapOrder
  apply List.mem_map.mpr
  refine ⟨B.intrinsicBoundaryRootedTreeChildEdge root child,
    Finset.mem_toList.mpr (Finset.mem_univ _), ?_⟩
  simp [intrinsicBoundaryRootedChildEdgeEquiv]

/-- The simultaneous tree pairing is exactly the product of its actual
physical transpositions indexed by all nonroot children. The child list is
the edge list transported through the proved bijection, so the order agrees
literally with the existing product rather than relying on swaps commuting. -/
theorem intrinsicBoundaryTreePairingPerm_eq_rootedChildTreeSwapProduct
    (B : DirichletBoundarySegments X o)
    (root : B.IntrinsicBoundaryGraphVertex) :
    B.intrinsicBoundaryTreePairingPerm =
      B.intrinsicBoundaryRootedChildTreeSwapProduct root := by
  classical
  rw [B.intrinsicBoundaryTreePairingPerm_eq_treeEdgeSwapProduct]
  let edgeEquiv := B.intrinsicBoundaryRootedChildEdgeEquiv root
  have hmap :
      (((Finset.univ : Finset (B.intrinsicBoundarySpanningTree.edgeSet)).toList).map
          edgeEquiv.symm).map (B.intrinsicBoundaryRootedChildTreeSwap root) =
        ((Finset.univ : Finset (B.intrinsicBoundarySpanningTree.edgeSet)).toList).map
          B.intrinsicBoundaryTreeEdgeSwap := by
    rw [List.map_map]
    apply List.map_congr_left
    intro edge hedge
    calc
      B.intrinsicBoundaryRootedChildTreeSwap root (edgeEquiv.symm edge) =
          B.intrinsicBoundaryTreeEdgeSwap
            (B.intrinsicBoundaryRootedTreeChildEdge root (edgeEquiv.symm edge)) :=
        B.intrinsicBoundaryRootedChildTreeSwap_eq_treeEdgeSwap root (edgeEquiv.symm edge)
      _ = B.intrinsicBoundaryTreeEdgeSwap edge := by
        congr 1
        exact edgeEquiv.apply_symm_apply edge
  change ((((Finset.univ : Finset (B.intrinsicBoundarySpanningTree.edgeSet)).toList).map
      B.intrinsicBoundaryTreeEdgeSwap).prod) =
    (((Finset.univ : Finset (B.intrinsicBoundarySpanningTree.edgeSet)).toList).map
      edgeEquiv.symm |>.map (B.intrinsicBoundaryRootedChildTreeSwap root)).prod
  rw [← hmap]

#print axioms intrinsicBoundaryRootedChildTreeSwap_eq_treeEdgeSwap
#print axioms intrinsicBoundaryRootedChildTreeSwap_endpoints_nodup
#print axioms intrinsicBoundaryRootedChildTreeSwap_disjoint
#print axioms intrinsicBoundaryRootedChildTreeSwap_commute
#print axioms intrinsicBoundaryTreePairingPerm_eq_rootedChildTreeSwapProduct
#print axioms intrinsicBoundaryRestrictedRootedChildTreeSwapPerm_apply
#print axioms intrinsicBoundaryRestrictedRootedChildTreeSwapPerm_congr
#print axioms intrinsicBoundaryRestrictedRootedChildTreeSwapPerm_false
#print axioms intrinsicBoundaryRestrictedRootedChildTreeSwapPerm_union_mul
#print axioms intrinsicBoundaryRestrictedRootedChildTreeSwapPerm_list_prod
#print axioms intrinsicBoundaryRestrictedRootedChildTreeSwapPerm_singleton
#print axioms intrinsicBoundaryRestrictedRootedChildTreeSwapPerm_true

end

end SystolicGrowth.DirichletBoundarySegments
