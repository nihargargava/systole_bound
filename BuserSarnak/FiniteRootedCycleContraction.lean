module

public import BuserSarnak.FiniteCycleSplice
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

/-!
# Global contraction of a finite rooted family of local cycles

Local blocks are attached along a finite rooted tree.  Strictly increasing
height makes the descendant recursion well founded.  The construction retains
the exact region support and an inductive trace of the ordered physical edge
splices; no global cycle or contraction witness is assumed.
-/

namespace SystolicGrowth

/-- Local rooted-tree and dart-incidence data for a cycle contraction. -/
structure RootedCycleTreeData (V E D : Type*) where
  height : V → ℕ
  children : V → List E
  children_nodup : ∀ q, (children q).Nodup
  target : E → V
  height_child : ∀ q e, e ∈ children q → height q < height (target e)
  ancestor : V → V → Prop
  height_ancestor : ∀ q r, ancestor q r → height q ≤ height r
  ancestor_partition : ∀ q r,
    ancestor q r ↔ r = q ∨ ∃ e ∈ children q, ancestor (target e) r
  sibling_disjoint : ∀ q e f,
    e ∈ children q → f ∈ children q → e ≠ f →
      ∀ r, ancestor (target e) r → ¬ ancestor (target f) r
  vertex : D → V
  block : V → List D
  block_nodup : ∀ q, (block q).Nodup
  mem_block_iff : ∀ q d, d ∈ block q ↔ vertex d = q
  sourceDart : E → D
  targetDart : E → D
  sourceDart_mem : ∀ q e, e ∈ children q → sourceDart e ∈ block q
  targetDart_mem : ∀ q e, e ∈ children q → targetDart e ∈ block (target e)

namespace RootedCycleTreeData

variable {V E D : Type*} (T : RootedCycleTreeData V E D)

theorem ancestor_self (q : V) : T.ancestor q q :=
  (T.ancestor_partition q q).mpr (Or.inl rfl)

/-- Child attachment pivots are successors of the physical target darts.
Thus the outgoing swap in the list-splice lemma represents crossing the
physical tree edge before applying the child's local permutation. -/
def attachments [DecidableEq D] (q : V) (childWords : E → List D) :
    List (CycleSpliceAttachment D) :=
  (T.children q).map fun e =>
    { block := childWords e
      source := T.sourceDart e
      target := List.formPerm (childWords e) (T.targetDart e) }

/-- Ordered product of child cycle permutations and actual tree-edge swaps. -/
def physicalProduct [DecidableEq D] (q : V) (childWords : E → List D) : Equiv.Perm D :=
  (T.children q).foldl
    (fun π e => π * List.formPerm (childWords e) *
      Equiv.swap (T.sourceDart e) (T.targetDart e))
    (List.formPerm (T.block q))

/-- Moving the attachment pivot forward through the child permutation
converts the successor-splice product to the actual physical edge swap. -/
theorem attachments_product_eq_physicalProduct [DecidableEq D]
    (q : V) (childWords : E → List D)
    (hfix : ∀ e ∈ T.children q,
      List.formPerm (childWords e) (T.sourceDart e) = T.sourceDart e) :
    cycleSpliceAttachmentProduct (T.block q) (T.attachments q childWords) =
      T.physicalProduct q childWords := by
  unfold cycleSpliceAttachmentProduct attachments physicalProduct
  have hfold : ∀ (edges : List E) (π : Equiv.Perm D),
      (∀ e ∈ edges,
        List.formPerm (childWords e) (T.sourceDart e) = T.sourceDart e) →
      (edges.map (fun e =>
        ({ block := childWords e
           source := T.sourceDart e
           target := List.formPerm (childWords e) (T.targetDart e) } :
          CycleSpliceAttachment D))).foldl
          (fun π child => π * Equiv.swap child.source child.target *
            List.formPerm child.block) π =
        edges.foldl
          (fun π e => π * List.formPerm (childWords e) *
            Equiv.swap (T.sourceDart e) (T.targetDart e)) π := by
    intro edges
    induction edges with
    | nil => intro π _; rfl
    | cons e edges ih =>
        intro π hfix
        simp only [List.map_cons, List.foldl_cons]
        have hswap :
            Equiv.swap (T.sourceDart e)
                (List.formPerm (childWords e) (T.targetDart e)) *
              List.formPerm (childWords e) =
            List.formPerm (childWords e) *
              Equiv.swap (T.sourceDart e) (T.targetDart e) := by
          rw [Equiv.mul_swap_eq_swap_mul,
            hfix e (List.mem_cons_self)]
        rw [mul_assoc, hswap, ← mul_assoc]
        exact ih _ (fun f hf => hfix f (List.mem_cons_of_mem e hf))
  exact hfold _ _ hfix

end RootedCycleTreeData

/-- Every node records the actual child contractions and the exact ordered
successor-splice permutation of its merged boundary word. -/
inductive RootedCycleContractionTrace
    {V E D : Type*} [DecidableEq D] (T : RootedCycleTreeData V E D) :
    V → List D → Prop
  | node (q : V) (childWords : E → List D) (merged : List D)
      (childTrace : ∀ e ∈ T.children q,
        RootedCycleContractionTrace T (T.target e) (childWords e))
      (nodup : merged.Nodup)
      (support : ∀ d, d ∈ merged ↔ T.ancestor q (T.vertex d))
      (permutation : List.formPerm merged =
        cycleSpliceAttachmentProduct (T.block q) (T.attachments q childWords))
      (physicalPermutation : List.formPerm merged = T.physicalProduct q childWords) :
      RootedCycleContractionTrace T q merged

namespace RootedCycleContractionTrace

variable {V E D : Type*} [DecidableEq D] {T : RootedCycleTreeData V E D}
  {q : V} {merged : List D}

/-- Every recorded contraction word retains its certified nodup invariant. -/
theorem nodup (h : RootedCycleContractionTrace T q merged) : merged.Nodup := by
  cases h with
  | node _ _ _ _ hn _ _ _ => exact hn

/-- Support is certified at each node of a contraction trace. -/
theorem mem_iff (h : RootedCycleContractionTrace T q merged) (d : D) :
    d ∈ merged ↔ T.ancestor q (T.vertex d) := by
  cases h with
  | node _ _ _ _ _ hs _ _ => exact hs d

end RootedCycleContractionTrace

namespace RootedCycleTreeData

variable {V E D : Type*} [Fintype V]
  (T : RootedCycleTreeData V E D)

/-- Descendant height leaves strictly less distance to the finite maximum. -/
theorem remainingHeight_child_lt (q : V) (e : E) (he : e ∈ T.children q) :
    Finset.univ.sup T.height - T.height (T.target e) <
      Finset.univ.sup T.height - T.height q := by
  have htarget : T.height (T.target e) ≤ Finset.univ.sup T.height :=
    Finset.le_sup (Finset.mem_univ _)
  have hchild := T.height_child q e he
  omega

end RootedCycleTreeData

/-- Fold every descendant block into a single nodup word, retaining exact
region support and an actual finite contraction trace. -/
theorem rootedCycleContraction_exists
    {V E D : Type*} [Fintype V] [DecidableEq D]
    (T : RootedCycleTreeData V E D) (q : V) :
    ∃ merged : List D,
      merged.Nodup ∧
      (∀ d, d ∈ merged ↔ T.ancestor q (T.vertex d)) ∧
      RootedCycleContractionTrace T q merged := by
  classical
  induction q using
      (measure (fun q => Finset.univ.sup T.height - T.height q)).wf.induction with
  | h q ih =>
      have hchild : ∀ e ∈ T.children q,
          ∃ merged : List D, merged.Nodup ∧
            (∀ d, d ∈ merged ↔ T.ancestor (T.target e) (T.vertex d)) ∧
            RootedCycleContractionTrace T (T.target e) merged := by
        intro e he
        exact ih (T.target e) (T.remainingHeight_child_lt q e he)
      let childWords : E → List D := fun e =>
        if he : e ∈ T.children q then Classical.choose (hchild e he) else []
      have hchildSpec : ∀ e ∈ T.children q,
          (childWords e).Nodup ∧
            (∀ d, d ∈ childWords e ↔ T.ancestor (T.target e) (T.vertex d)) ∧
            RootedCycleContractionTrace T (T.target e) (childWords e) := by
        intro e he
        simpa only [childWords, dif_pos he] using Classical.choose_spec (hchild e he)
      have hrootChildDisjoint : ∀ e ∈ T.children q,
          List.Disjoint (T.block q) (childWords e) := by
        intro e he
        apply List.disjoint_left.mpr
        intro d hdRoot hdChild
        have hvertex := (T.mem_block_iff q d).mp hdRoot
        have hancestor := ((hchildSpec e he).2.1 d).mp hdChild
        have hheight := T.height_ancestor (T.target e) (T.vertex d) hancestor
        have hchildHeight := T.height_child q e he
        rw [hvertex] at hheight
        omega
      have hsiblingDisjoint : (T.children q).Pairwise
          (fun e f => List.Disjoint (childWords e) (childWords f)) := by
        apply (T.children_nodup q).pairwise_of_forall_ne
        intro e he f hf hne
        apply List.disjoint_left.mpr
        intro d hdE hdF
        exact T.sibling_disjoint q e f he hf hne (T.vertex d)
          (((hchildSpec e he).2.1 d).mp hdE)
          (((hchildSpec f hf).2.1 d).mp hdF)
      have hdisjoint :
          (T.block q :: (T.attachments q childWords).map
            CycleSpliceAttachment.block).Pairwise List.Disjoint := by
        simp only [RootedCycleTreeData.attachments, List.map_map, Function.comp_def]
        apply List.pairwise_cons.mpr
        refine ⟨?_, ?_⟩
        · intro block hblock
          obtain ⟨e, he, rfl⟩ := List.mem_map.mp hblock
          exact hrootChildDisjoint e he
        · exact List.pairwise_map.mpr hsiblingDisjoint
      have hblocksNodup : ∀ a ∈ T.attachments q childWords, a.block.Nodup := by
        intro a ha
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
        exact (hchildSpec e he).1
      have hpivots : ∀ a ∈ T.attachments q childWords,
          a.source ∈ T.block q ∧ a.target ∈ a.block := by
        intro a ha
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
        refine ⟨T.sourceDart_mem q e he, ?_⟩
        have htargetLocal := T.targetDart_mem q e he
        have htargetVertex := (T.mem_block_iff (T.target e) _).mp htargetLocal
        have htarget : T.targetDart e ∈ childWords e :=
          ((hchildSpec e he).2.1 _).mpr (by
            rw [htargetVertex]
            exact T.ancestor_self (T.target e))
        exact List.formPerm_apply_mem_of_mem htarget
      obtain ⟨merged, hnodup, hmem, hperm⟩ :=
        formPerm_splice_blocks_fold (T.block q) (T.attachments q childWords)
          (T.block_nodup q) hblocksNodup hdisjoint hpivots
      have hsupport : ∀ d, d ∈ merged ↔ T.ancestor q (T.vertex d) := by
        intro d
        rw [hmem, T.ancestor_partition]
        constructor
        · rintro (hroot | ⟨a, ha, hd⟩)
          · exact Or.inl ((T.mem_block_iff q d).mp hroot)
          · obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
            exact Or.inr ⟨e, he, ((hchildSpec e he).2.1 d).mp hd⟩
        · rintro (hroot | ⟨e, he, hd⟩)
          · exact Or.inl ((T.mem_block_iff q d).mpr hroot)
          · apply Or.inr
            refine ⟨_, List.mem_map.mpr ⟨e, he, rfl⟩, ?_⟩
            exact ((hchildSpec e he).2.1 d).mpr hd
      refine ⟨merged, hnodup, hsupport, ?_⟩
      exact RootedCycleContractionTrace.node q childWords merged
          (fun e he => (hchildSpec e he).2.2) hnodup hsupport hperm (hperm.trans <|
            T.attachments_product_eq_physicalProduct q childWords (by
              intro e he
              apply List.formPerm_apply_of_notMem
              intro hsource
              exact (List.disjoint_left.mp (hrootChildDisjoint e he))
                (T.sourceDart_mem q e he) hsource))

#print axioms SystolicGrowth.RootedCycleTreeData.remainingHeight_child_lt
#print axioms SystolicGrowth.RootedCycleTreeData.attachments_product_eq_physicalProduct
#print axioms SystolicGrowth.RootedCycleContractionTrace.nodup
#print axioms SystolicGrowth.RootedCycleContractionTrace.mem_iff
#print axioms SystolicGrowth.rootedCycleContraction_exists

end SystolicGrowth
