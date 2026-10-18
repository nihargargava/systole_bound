module

public import BuserSarnak.BuserSarnakProjectiveCanonicalTree

@[expose] public section

/-!
# Regions of the canonical projective primal tree

Primal ancestry is prefix containment of canonical positive representatives.
These regions partition the quotient vertices at every rooted tree edge; they
are not the face regions of the independent dual tree.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete

noncomputable local instance buserSarnakProjectivePrimalRegionsRangeFintype
    (p : ℕ) [NeZero p] : Fintype (BuserSarnakProjectiveReductionRange p) :=
  Fintype.ofFinite _

/-- Primal ancestry in the canonical shortest-predecessor tree. -/
def canonicalProjectivePrimalAncestor (p : ℕ) [NeZero p]
    (q r : BuserSarnakProjectiveReductionRange p) : Prop :=
  canonicalPositiveProjectiveWord p q <+: canonicalPositiveProjectiveWord p r

/-- The quotient vertices below a primal-tree vertex, including that vertex. -/
def canonicalProjectivePrimalRegion (p : ℕ) [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p) : Set (BuserSarnakProjectiveReductionRange p) :=
  {r | canonicalProjectivePrimalAncestor p q r}

@[simp] theorem canonicalProjectivePrimalAncestor_refl
    {p : ℕ} [NeZero p] (q : BuserSarnakProjectiveReductionRange p) :
    canonicalProjectivePrimalAncestor p q q := List.prefix_rfl

theorem canonicalProjectivePrimalAncestor_trans
    {p : ℕ} [NeZero p] {q r t : BuserSarnakProjectiveReductionRange p}
    (hqr : canonicalProjectivePrimalAncestor p q r)
    (hrt : canonicalProjectivePrimalAncestor p r t) :
    canonicalProjectivePrimalAncestor p q t := hqr.trans hrt

@[simp] theorem canonicalProjectivePrimalAncestor_root
    {p : ℕ} [NeZero p] (q : BuserSarnakProjectiveReductionRange p) :
    canonicalProjectivePrimalAncestor p 1 q := by
  unfold canonicalProjectivePrimalAncestor
  rw [canonicalPositiveProjectiveWord]
  simp

theorem canonicalProjectivePrimalAncestor_antisymm
    {p : ℕ} [NeZero p] {q r : BuserSarnakProjectiveReductionRange p}
    (hqr : canonicalProjectivePrimalAncestor p q r)
    (hrq : canonicalProjectivePrimalAncestor p r q) : q = r := by
  have hword := hqr.eq_of_length (hqr.length_le.antisymm hrq.length_le)
  simpa only [positiveProjectiveEval_canonicalPositiveProjectiveWord] using
    congrArg (positiveProjectiveEval p) hword

theorem canonicalProjectivePrimalAncestor_height_le
    {p : ℕ} [NeZero p] {q r : BuserSarnakProjectiveReductionRange p}
    (hqr : canonicalProjectivePrimalAncestor p q r) :
    canonicalProjectiveWordHeight p q ≤ canonicalProjectiveWordHeight p r :=
  hqr.length_le

/-- A primal tree edge appends exactly its positive generator. -/
theorem canonicalPositiveProjectiveWord_treeTarget
    {p : ℕ} [NeZero p] (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p) :
    canonicalPositiveProjectiveWord p (canonicalProjectiveTreeTarget p z) =
      canonicalPositiveProjectiveWord p z.1.1 ++ [z.1.2] := by
  have hpair : Function.Injective
      (fun x : ProjectiveOctagonGenerator => (x, true)) := by
    intro x y hxy
    exact congrArg Prod.fst hxy
  apply hpair.list_map
  simpa only [canonicalProjectiveTreeTarget, canonicalBuserSarnakProjectiveDegenerateTarget,
    positiveSignedProjectiveWord, List.map_append, List.map_singleton] using
    canonicalBuserSarnakProjective_isDegenerate_word z.2

theorem canonicalProjectivePrimalAncestor_of_child
    {p : ℕ} [NeZero p] (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p) :
    canonicalProjectivePrimalAncestor p z.1.1 (canonicalProjectiveTreeTarget p z) := by
  unfold canonicalProjectivePrimalAncestor
  rw [canonicalPositiveProjectiveWord_treeTarget]
  exact List.prefix_append _ _

theorem canonicalProjectiveWordHeight_treeTarget_eq_succ
    {p : ℕ} [NeZero p] (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p) :
    canonicalProjectiveWordHeight p (canonicalProjectiveTreeTarget p z) =
      canonicalProjectiveWordHeight p z.1.1 + 1 := by
  unfold canonicalProjectiveWordHeight
  rw [canonicalPositiveProjectiveWord_treeTarget]
  simp

theorem canonicalProjectiveTreeTarget_ne_source
    {p : ℕ} [NeZero p] (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p) :
    canonicalProjectiveTreeTarget p z ≠ z.1.1 := by
  intro h
  have hlt := canonicalProjectiveWordHeight_lt_treeTarget z
  rw [h] at hlt
  exact (lt_irrefl _ hlt)

/-- Appending a canonical positive letter characterizes a deleted primal edge. -/
theorem canonicalProjective_isDegenerate_of_word_append
    {p : ℕ} [NeZero p] {q : BuserSarnakProjectiveReductionRange p}
    {x : ProjectiveOctagonGenerator}
    (hword : canonicalPositiveProjectiveWord p
        ((CanonicalProjectiveTreeSchreierData p).transition q x) =
      canonicalPositiveProjectiveWord p q ++ [x]) :
    (CanonicalProjectiveTreeSchreierData p).IsDegenerateSchreierSymbol (q, x) := by
  change FreeGroup.mk (positiveSignedProjectiveWord
      (canonicalPositiveProjectiveWord p
        ((CanonicalProjectiveTreeSchreierData p).transition q x))) =
    FreeGroup.mk (positiveSignedProjectiveWord (canonicalPositiveProjectiveWord p q)) *
      FreeGroup.of x
  rw [hword]
  simp only [positiveSignedProjectiveWord, List.map_append, List.map_singleton]
  rw [← FreeGroup.mul_mk]
  rfl

/-- Two children of the same primal vertex cannot share a descendant. -/
theorem canonicalProjectivePrimalAncestor_sibling_unique
    {p : ℕ} [NeZero p]
    {z w : CanonicalBuserSarnakProjectiveDegenerateSymbol p}
    {r : BuserSarnakProjectiveReductionRange p}
    (hsource : z.1.1 = w.1.1)
    (hz : canonicalProjectivePrimalAncestor p (canonicalProjectiveTreeTarget p z) r)
    (hw : canonicalProjectivePrimalAncestor p (canonicalProjectiveTreeTarget p w) r) :
    z = w := by
  have hlength : (canonicalPositiveProjectiveWord p
      (canonicalProjectiveTreeTarget p z)).length =
      (canonicalPositiveProjectiveWord p (canonicalProjectiveTreeTarget p w)).length := by
    rw [canonicalPositiveProjectiveWord_treeTarget,
      canonicalPositiveProjectiveWord_treeTarget, hsource]
    simp
  have hwords : canonicalPositiveProjectiveWord p (canonicalProjectiveTreeTarget p z) =
      canonicalPositiveProjectiveWord p (canonicalProjectiveTreeTarget p w) := by
    rw [List.prefix_iff_eq_take.mp hz, List.prefix_iff_eq_take.mp hw, hlength]
  apply canonicalBuserSarnakProjectiveDegenerateTarget_injective p
  apply Subtype.ext
  simpa only [positiveProjectiveEval_canonicalPositiveProjectiveWord,
    canonicalProjectiveTreeTarget] using
    congrArg (positiveProjectiveEval p) hwords

theorem canonicalProjectivePrimalRegion_sibling_disjoint
    {p : ℕ} [NeZero p]
    {z w : CanonicalBuserSarnakProjectiveDegenerateSymbol p}
    (hsource : z.1.1 = w.1.1) (hne : z ≠ w) :
    Disjoint (canonicalProjectivePrimalRegion p (canonicalProjectiveTreeTarget p z))
      (canonicalProjectivePrimalRegion p (canonicalProjectiveTreeTarget p w)) := by
  rw [Set.disjoint_left]
  intro r hz hw
  exact hne (canonicalProjectivePrimalAncestor_sibling_unique hsource hz hw)

/-- Every strict descendant enters through one uniquely determined child. -/
theorem canonicalProjectivePrimalAncestor_existsUnique_child
    {p : ℕ} [NeZero p] {q r : BuserSarnakProjectiveReductionRange p}
    (hqr : canonicalProjectivePrimalAncestor p q r) (hne : r ≠ q) :
    ∃! z : CanonicalBuserSarnakProjectiveDegenerateSymbol p,
      z.1.1 = q ∧
        canonicalProjectivePrimalAncestor p (canonicalProjectiveTreeTarget p z) r := by
  rcases hqr with ⟨rest, hcat⟩
  cases rest with
  | nil =>
      simp only [List.append_nil] at hcat
      have hstate : q = r := by
        simpa only [positiveProjectiveEval_canonicalPositiveProjectiveWord] using
          congrArg (positiveProjectiveEval p) hcat
      exact False.elim (hne hstate.symm)
  | cons x tail =>
      have hprefix : (canonicalPositiveProjectiveWord p q ++ [x]) ++ tail =
          canonicalPositiveProjectiveWord p r := by
        simpa only [List.append_assoc, List.singleton_append] using hcat
      have hchildword := canonicalPositiveProjectiveWord_prefixState p r
        (canonicalPositiveProjectiveWord p q ++ [x]) tail hprefix
      have heval : positiveProjectiveEval p (canonicalPositiveProjectiveWord p q ++ [x]) =
          (CanonicalProjectiveTreeSchreierData p).transition q x := by
        rw [positiveProjectiveEval_append, positiveProjectiveEval_singleton,
          positiveProjectiveEval_canonicalPositiveProjectiveWord,
          canonicalBuserSarnakProjective_transition_eq_mul]
      rw [heval] at hchildword
      let z : CanonicalBuserSarnakProjectiveDegenerateSymbol p :=
        ⟨(q, x), canonicalProjective_isDegenerate_of_word_append hchildword⟩
      have hz : canonicalProjectivePrimalAncestor p (canonicalProjectiveTreeTarget p z) r := by
        unfold canonicalProjectivePrimalAncestor
        rw [canonicalPositiveProjectiveWord_treeTarget]
        exact ⟨tail, hprefix⟩
      refine ⟨z, ⟨rfl, hz⟩, ?_⟩
      intro w hw
      exact canonicalProjectivePrimalAncestor_sibling_unique hw.1 hw.2 hz

/-- The exact root-plus-children partition used by primal contraction. -/
theorem canonicalProjectivePrimalAncestor_iff_eq_or_child
    {p : ℕ} [NeZero p] (q r : BuserSarnakProjectiveReductionRange p) :
    canonicalProjectivePrimalAncestor p q r ↔ r = q ∨
      ∃ z : CanonicalBuserSarnakProjectiveDegenerateSymbol p, z.1.1 = q ∧
        canonicalProjectivePrimalAncestor p (canonicalProjectiveTreeTarget p z) r := by
  classical
  constructor
  · intro hqr
    by_cases h : r = q
    · exact Or.inl h
    · exact Or.inr (ExistsUnique.exists
        (canonicalProjectivePrimalAncestor_existsUnique_child hqr h))
  · rintro (rfl | ⟨z, hsource, hz⟩)
    · exact canonicalProjectivePrimalAncestor_refl _
    · have hqz := canonicalProjectivePrimalAncestor_of_child z
      rw [hsource] at hqz
      exact canonicalProjectivePrimalAncestor_trans hqz hz

/-- No child region contains its parent vertex. -/
theorem canonicalProjectivePrimalAncestor_not_child_parent
    {p : ℕ} [NeZero p] (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p) :
    ¬ canonicalProjectivePrimalAncestor p (canonicalProjectiveTreeTarget p z) z.1.1 := by
  intro h
  have hle := canonicalProjectivePrimalAncestor_height_le h
  have hlt := canonicalProjectiveWordHeight_lt_treeTarget z
  omega

@[simp] theorem mem_canonicalProjectivePrimalRegion
    {p : ℕ} [NeZero p] (q r : BuserSarnakProjectiveReductionRange p) :
    r ∈ canonicalProjectivePrimalRegion p q ↔ canonicalProjectivePrimalAncestor p q r := Iff.rfl

@[simp] theorem canonicalProjectivePrimalRegion_root
    {p : ℕ} [NeZero p] :
    canonicalProjectivePrimalRegion p (1 : BuserSarnakProjectiveReductionRange p) =
      Set.univ := by
  ext r
  simp

/-- The local vertex block is disjoint from every region below its children. -/
theorem canonicalProjectivePrimalRegion_child_disjoint_parent
    {p : ℕ} [NeZero p] (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p) :
    Disjoint (canonicalProjectivePrimalRegion p (canonicalProjectiveTreeTarget p z))
      {z.1.1} := by
  rw [Set.disjoint_singleton_right]
  exact canonicalProjectivePrimalAncestor_not_child_parent z

/-- All child regions in the rooted partition are pairwise disjoint. -/
theorem canonicalProjectivePrimalRegion_children_pairwiseDisjoint
    {p : ℕ} [NeZero p] (q : BuserSarnakProjectiveReductionRange p) :
    Pairwise (fun z w :
      {z : CanonicalBuserSarnakProjectiveDegenerateSymbol p // z.1.1 = q} =>
      Disjoint (canonicalProjectivePrimalRegion p (canonicalProjectiveTreeTarget p z.1))
        (canonicalProjectivePrimalRegion p (canonicalProjectiveTreeTarget p w.1))) := by
  intro z w hne
  apply canonicalProjectivePrimalRegion_sibling_disjoint (z.2.trans w.2.symm)
  intro hzw
  exact hne (Subtype.ext hzw)

theorem canonicalProjectivePrimalRegion_partition
    {p : ℕ} [NeZero p] (q : BuserSarnakProjectiveReductionRange p) :
    canonicalProjectivePrimalRegion p q = {q} ∪
      ⋃ z : {z : CanonicalBuserSarnakProjectiveDegenerateSymbol p // z.1.1 = q},
        canonicalProjectivePrimalRegion p (canonicalProjectiveTreeTarget p z.1) := by
  ext r
  simp only [mem_canonicalProjectivePrimalRegion, Set.mem_union, Set.mem_singleton_iff,
    Set.mem_iUnion]
  rw [canonicalProjectivePrimalAncestor_iff_eq_or_child]
  constructor
  · rintro (h | ⟨z, hsource, hz⟩)
    · exact Or.inl h
    · exact Or.inr ⟨⟨z, hsource⟩, hz⟩
  · rintro (h | ⟨z, hz⟩)
    · exact Or.inl h
    · exact Or.inr ⟨z.1, z.2, hz⟩

#print axioms canonicalPositiveProjectiveWord_treeTarget
#print axioms canonicalProjectivePrimalAncestor_existsUnique_child
#print axioms canonicalProjectivePrimalRegion_partition
#print axioms canonicalProjectivePrimalRegion_sibling_disjoint

end

end SystolicGrowth
