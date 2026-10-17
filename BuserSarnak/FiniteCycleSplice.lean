module

public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import BuserSarnak.FiniteOrbitFirstReturn

@[expose] public section

/-!
# Joining two disjoint cyclic boundary blocks

This is a small reusable permutation lemma for the tree-contraction route:
once two disjoint cyclic boundary blocks have been cut at their joining edge,
their concatenation gives one cycle. The geometric development still has to
identify each actual contraction with this operation.
-/

namespace SystolicGrowth

/-- Appending a nonempty right block to a cyclic list can be split at its
first element: the old left block is first closed at that pivot, then the
right cycle is traversed. -/
theorem formPerm_append_cons_eq
    {α : Type*} [DecidableEq α] (left : List α) (head : α) (tail : List α) :
    List.formPerm (left ++ head :: tail) =
      List.formPerm (left ++ [head]) * List.formPerm (head :: tail) := by
  induction left with
  | nil => simp
  | cons a left ih =>
    cases left with
    | nil => simp [List.formPerm_cons_cons]
    | cons b left =>
      simp only [List.cons_append, List.formPerm_cons_cons]
      have hih := congrArg (fun π : Equiv.Perm α => Equiv.swap a b * π) ih
      simpa only [List.cons_append, List.formPerm_cons_cons, mul_assoc] using hih

/-- Exact successor law for splicing two cyclic boundary blocks. If the left
block ends at `a` and the right starts at `b`, their concatenated cycle is
obtained by swapping precisely those two outgoing successors between the
separate block cycles. -/
theorem formPerm_append_splice_eq
    {α : Type*} [DecidableEq α]
    (pre suffix : List α) (a b : α) :
    List.formPerm (pre ++ [a] ++ b :: suffix) =
      List.formPerm (pre ++ [a]) * Equiv.swap a b *
        List.formPerm (b :: suffix) := by
  rw [show pre ++ [a] ++ b :: suffix = (pre ++ [a]) ++ b :: suffix by
    simp [List.append_assoc]]
  rw [formPerm_append_cons_eq]
  rw [show pre ++ [a] ++ [b] = pre ++ [a, b] by simp [List.append_assoc],
    List.formPerm_append_pair]

/-- Swapping the two cut successors of disjoint cyclic blocks merges them
into one cycle. This is the direct permutation form of a tree-edge
contraction; concrete dart blocks still need to be identified separately. -/
theorem formPerm_splice_isCycle
    {α : Type*} [DecidableEq α]
    (pre suffix : List α) (a b : α)
    (hnodup : (pre ++ [a] ++ b :: suffix).Nodup)
    (hlength : 2 ≤ (pre ++ [a] ++ b :: suffix).length) :
    Equiv.Perm.IsCycle
      (List.formPerm (pre ++ [a]) * Equiv.swap a b *
        List.formPerm (b :: suffix)) := by
  rw [← formPerm_append_splice_eq]
  exact List.isCycle_formPerm hnodup hlength

private theorem list_exists_split_mem {α : Type*} (l : List α) {a : α}
    (ha : a ∈ l) : ∃ pre post, l = pre ++ a :: post := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
      rcases List.mem_cons.mp ha with hxa | htail
      · subst x
        exact ⟨[], xs, rfl⟩
      · obtain ⟨pre, post, hsplit⟩ := ih htail
        exact ⟨x :: pre, post, by simp [hsplit]⟩

/-- Construct the explicit nodup list for the merged component after a
successor splice at arbitrary marked pivots. Its membership predicate is the
union of the original blocks, and its `formPerm` is the successor-swap
product. This is the state-carrying form needed for iterating tree splices. -/
theorem formPerm_splice_word_of_mem
    {α : Type*} [DecidableEq α]
    (left right : List α) (a b : α)
    (hleftNodup : left.Nodup) (hrightNodup : right.Nodup)
    (hdisjoint : List.Disjoint left right)
    (ha : a ∈ left) (hb : b ∈ right) :
    ∃ merged : List α,
      merged.Nodup ∧
      (∀ x, x ∈ merged ↔ x ∈ left ∨ x ∈ right) ∧
      List.formPerm merged =
        List.formPerm left * Equiv.swap a b * List.formPerm right := by
  obtain ⟨preLeft, postLeft, hleftSplit⟩ := list_exists_split_mem left ha
  obtain ⟨preRight, postRight, hrightSplit⟩ := list_exists_split_mem right hb
  let leftShift := preLeft.length + 1
  let rightShift := preRight.length
  have hleftRot : left.rotate leftShift = postLeft ++ preLeft ++ [a] := by
    rw [hleftSplit, List.rotate_eq_drop_append_take]
    · rw [List.drop_append, List.take_append]
      simp [leftShift, List.drop_eq_nil_of_le, List.take_eq_self_iff]
    · simp [leftShift]
  have hrightRot : right.rotate rightShift = b :: postRight ++ preRight := by
    rw [hrightSplit, List.rotate_eq_drop_append_take]
    · rw [List.drop_append, List.take_append]
      simp [rightShift]
    · simp [rightShift]
  let merged := left.rotate leftShift ++ right.rotate rightShift
  have hleftRotNodup : (left.rotate leftShift).Nodup :=
    (List.nodup_rotate).2 hleftNodup
  have hrightRotNodup : (right.rotate rightShift).Nodup :=
    (List.nodup_rotate).2 hrightNodup
  have hrotDisjoint : List.Disjoint (left.rotate leftShift) (right.rotate rightShift) := by
    apply List.disjoint_left.mpr
    intro x hx hy
    exact (List.disjoint_left.mp hdisjoint) (List.mem_rotate.mp hx) (List.mem_rotate.mp hy)
  have hmergedNodup : merged.Nodup := by
    dsimp [merged]
    rw [List.nodup_append']
    exact ⟨hleftRotNodup, hrightRotNodup, hrotDisjoint⟩
  have hmergedMem : ∀ x, x ∈ merged ↔ x ∈ left ∨ x ∈ right := by
    intro x
    simp [merged, List.mem_rotate]
  have hleftPerm : List.formPerm (postLeft ++ preLeft ++ [a]) = List.formPerm left := by
    rw [← hleftRot]
    exact List.formPerm_rotate left hleftNodup leftShift
  have hrightPerm : List.formPerm (b :: postRight ++ preRight) = List.formPerm right := by
    rw [← hrightRot]
    exact List.formPerm_rotate right hrightNodup rightShift
  change List.formPerm (b :: (postRight ++ preRight)) = List.formPerm right at hrightPerm
  have hmergedFormPerm : List.formPerm merged =
      List.formPerm left * Equiv.swap a b * List.formPerm right := by
    dsimp [merged]
    calc
      List.formPerm (left.rotate leftShift ++ right.rotate rightShift) =
          List.formPerm ((postLeft ++ preLeft) ++ [a] ++
            b :: (postRight ++ preRight)) := by
        rw [hleftRot, hrightRot]
        simp [List.append_assoc]
      _ = List.formPerm ((postLeft ++ preLeft) ++ [a]) *
          Equiv.swap a b * List.formPerm (b :: (postRight ++ preRight)) :=
        formPerm_append_splice_eq (postLeft ++ preLeft) (postRight ++ preRight) a b
      _ = List.formPerm left * Equiv.swap a b * List.formPerm right := by
        rw [hleftPerm, hrightPerm]
  exact ⟨merged, hmergedNodup, hmergedMem, hmergedFormPerm⟩

/-- One child block to be attached to an already accumulated cyclic block.
The source pivot is required to lie in the original root block; consequently
it remains available after any number of earlier attachments. -/
structure CycleSpliceAttachment (α : Type*) where
  block : List α
  source : α
  target : α

/-- The permutation predicted by attaching a list of child blocks in order. -/
def cycleSpliceAttachmentProduct
    {α : Type*} [DecidableEq α] (root : List α)
    (attachments : List (CycleSpliceAttachment α)) : Equiv.Perm α :=
  attachments.foldl
    (fun π child => π * Equiv.swap child.source child.target *
      List.formPerm child.block)
    (List.formPerm root)

/-- A finite sequence of pairwise disjoint blocks can be folded into one
nodup cyclic word by successively splicing each child at its marked pivots.
The result retains exact support and the ordered successor-swap product.
This is the abstract list-fold needed by the concrete rooted-tree induction. -/
theorem formPerm_splice_blocks_fold
    {α : Type*} [DecidableEq α]
    (root : List α) (attachments : List (CycleSpliceAttachment α))
    (hrootNodup : root.Nodup)
    (hblocksNodup : ∀ child ∈ attachments, child.block.Nodup)
    (hdisjoint : (root :: attachments.map CycleSpliceAttachment.block).Pairwise
      List.Disjoint)
    (hpivots : ∀ child ∈ attachments,
      child.source ∈ root ∧ child.target ∈ child.block) :
    ∃ merged : List α,
      merged.Nodup ∧
      (∀ x, x ∈ merged ↔ x ∈ root ∨
        ∃ child ∈ attachments, x ∈ child.block) ∧
      List.formPerm merged = cycleSpliceAttachmentProduct root attachments := by
  induction attachments generalizing root with
  | nil =>
      refine ⟨root, hrootNodup, ?_, ?_⟩
      · intro x
        simp
      · rfl
  | cons child rest ih =>
      have hpair :
          (root :: child.block :: rest.map CycleSpliceAttachment.block).Pairwise
            List.Disjoint := by
        simpa using hdisjoint
      have hrootChild : List.Disjoint root child.block :=
        (List.pairwise_cons.mp hpair).1 child.block (by simp)
      have htailPair :
          (child.block :: rest.map CycleSpliceAttachment.block).Pairwise
            List.Disjoint :=
        (List.pairwise_cons.mp hpair).2
      have hchildNodup : child.block.Nodup := hblocksNodup child (by simp)
      have hchildPivots := hpivots child (by simp)
      obtain ⟨first, hfirstNodup, hfirstMem, hfirstPerm⟩ :=
        formPerm_splice_word_of_mem root child.block child.source child.target
          hrootNodup hchildNodup hrootChild hchildPivots.1 hchildPivots.2
      have hfirstDisjointRest :
          (first :: rest.map CycleSpliceAttachment.block).Pairwise List.Disjoint := by
        apply List.pairwise_cons.mpr
        refine ⟨?_, ?_⟩
        · intro block hblock
          have hrootBlock : List.Disjoint root block := by
            exact (List.pairwise_cons.mp hpair).1 block (by simp [hblock])
          have hchildBlock : List.Disjoint child.block block :=
            (List.pairwise_cons.mp htailPair).1 block hblock
          apply List.disjoint_left.mpr
          intro x hxFirst hxBlock
          rcases (hfirstMem x).mp hxFirst with hxRoot | hxChild
          · exact (List.disjoint_left.mp hrootBlock) hxRoot hxBlock
          · exact (List.disjoint_left.mp hchildBlock) hxChild hxBlock
        · exact (List.pairwise_cons.mp htailPair).2
      have hrestNodup : ∀ next ∈ rest, next.block.Nodup := by
        intro next hnext
        exact hblocksNodup next (by simp [hnext])
      have hrestPivots : ∀ next ∈ rest,
          next.source ∈ first ∧ next.target ∈ next.block := by
        intro next hnext
        have h := hpivots next (by simp [hnext])
        exact ⟨(hfirstMem next.source).2 (Or.inl h.1), h.2⟩
      obtain ⟨merged, hmergedNodup, hmergedMem, hmergedPerm⟩ :=
        ih first hfirstNodup hrestNodup hfirstDisjointRest hrestPivots
      refine ⟨merged, hmergedNodup, ?_, ?_⟩
      · intro x
        rw [hmergedMem, hfirstMem]
        simp [List.mem_cons, or_assoc]
      · have hperm' : List.formPerm merged =
            List.foldl
              (fun π next => π * Equiv.swap next.source next.target *
                List.formPerm next.block)
              (List.formPerm first) rest := by
          simpa [cycleSpliceAttachmentProduct] using hmergedPerm
        rw [hfirstPerm] at hperm'
        simpa [cycleSpliceAttachmentProduct, List.foldl_cons] using hperm'

/-- Splicing two disjoint cycles at arbitrary marked occurrences still
produces one cycle. The lists may first be cyclically rotated so the left
pivot is last and the right pivot is first. -/
theorem formPerm_splice_isCycle_of_mem
    {α : Type*} [DecidableEq α]
    (left right : List α) (a b : α)
    (hleftNodup : left.Nodup) (hrightNodup : right.Nodup)
    (hdisjoint : List.Disjoint left right)
    (ha : a ∈ left) (hb : b ∈ right)
    (hlenLeft : 2 ≤ left.length) (hlenRight : 2 ≤ right.length) :
    Equiv.Perm.IsCycle (List.formPerm left * Equiv.swap a b * List.formPerm right) := by
  obtain ⟨preLeft, postLeft, hleftSplit⟩ := list_exists_split_mem left ha
  obtain ⟨preRight, postRight, hrightSplit⟩ := list_exists_split_mem right hb
  let leftShift := preLeft.length + 1
  let rightShift := preRight.length
  have hleftRot : left.rotate leftShift = postLeft ++ preLeft ++ [a] := by
    rw [hleftSplit, List.rotate_eq_drop_append_take]
    · rw [List.drop_append, List.take_append]
      simp [leftShift, List.drop_eq_nil_of_le, List.take_eq_self_iff]
    · simp [leftShift]
  have hrightRot : right.rotate rightShift = b :: postRight ++ preRight := by
    rw [hrightSplit, List.rotate_eq_drop_append_take]
    · rw [List.drop_append, List.take_append]
      simp [rightShift]
    · simp [rightShift]
  have hleftRotNodup : (left.rotate leftShift).Nodup :=
    (List.nodup_rotate).2 hleftNodup
  have hrightRotNodup : (right.rotate rightShift).Nodup :=
    (List.nodup_rotate).2 hrightNodup
  have hrotDisjoint : List.Disjoint (left.rotate leftShift) (right.rotate rightShift) := by
    apply List.disjoint_left.mpr
    intro x hx hy
    apply (List.disjoint_left.mp hdisjoint)
    · exact List.mem_rotate.mp hx
    · exact List.mem_rotate.mp hy
  have hrotNodup : ((left.rotate leftShift) ++ (right.rotate rightShift)).Nodup := by
    rw [List.nodup_append']
    exact ⟨hleftRotNodup, hrightRotNodup, hrotDisjoint⟩
  have hconcatLength : 2 ≤ left.length + right.length := by
    have hfour : 4 ≤ left.length + right.length :=
      Nat.add_le_add hlenLeft hlenRight
    omega
  have hrotLength : 2 ≤ ((left.rotate leftShift) ++ (right.rotate rightShift)).length := by
    simpa [List.length_append, List.length_rotate] using hconcatLength
  have hsplicedNodup :
      ((postLeft ++ preLeft) ++ [a] ++ b :: (postRight ++ preRight)).Nodup := by
    simpa [hleftRot, hrightRot, List.append_assoc] using hrotNodup
  have hsplicedLength :
      2 ≤ ((postLeft ++ preLeft) ++ [a] ++ b :: (postRight ++ preRight)).length := by
    simpa [hleftRot, hrightRot, List.append_assoc] using hrotLength
  have hcycle := formPerm_splice_isCycle
    (postLeft ++ preLeft) (postRight ++ preRight) a b hsplicedNodup hsplicedLength
  have hleftPerm : List.formPerm (postLeft ++ preLeft ++ [a]) = List.formPerm left := by
    rw [← hleftRot]
    exact List.formPerm_rotate left hleftNodup leftShift
  have hrightPerm : List.formPerm (b :: postRight ++ preRight) = List.formPerm right := by
    rw [← hrightRot]
    exact List.formPerm_rotate right hrightNodup rightShift
  change List.formPerm (b :: (postRight ++ preRight)) = List.formPerm right at hrightPerm
  rw [hleftPerm, hrightPerm] at hcycle
  exact hcycle

/-- Restrict a finite permutation cycle to its moved points. Its action is
transitive in the natural-number iterate sense used by first-return lemmas. -/
theorem isCycle_support_iterate_transitive
    {α : Type*} [Finite α] (f : Equiv.Perm α) (hf : Equiv.Perm.IsCycle f) :
    ∀ x y : {a : α // f a ≠ a},
      ∃ n : ℕ, (fun a : {a : α // f a ≠ a} =>
        ⟨f a.1, by
          intro h
          exact a.2 (f.injective h)⟩)^[n] x = y := by
  let g : {a : α // f a ≠ a} → {a : α // f a ≠ a} := fun a =>
    ⟨f a.1, by
      intro h
      exact a.2 (f.injective h)⟩
  have hval : ∀ (n : ℕ) (x : {a : α // f a ≠ a}),
      (g^[n] x).1 = (f^[n]) x.1 := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      change f (g^[n] x).1 = f ((f^[n]) x.1)
      rw [ih]
  intro x y
  obtain ⟨n, hn⟩ := hf.exists_pow_eq x.2 y.2
  refine ⟨n, ?_⟩
  apply Subtype.ext
  rw [hval]
  simpa only [Equiv.Perm.coe_pow] using hn

/-- The restriction of a permutation to its moved-point support. -/
def cycleSupportMap {α : Type*} (f : Equiv.Perm α) :
    {a : α // f a ≠ a} → {a : α // f a ≠ a} := fun a =>
  ⟨f a.1, by
    intro h
    exact a.2 (f.injective h)⟩

theorem cycleSupportMap_injective {α : Type*} (f : Equiv.Perm α) :
    Function.Injective (cycleSupportMap f) := by
  intro x y h
  apply Subtype.ext
  exact f.injective (congrArg Subtype.val h)

/-- The induced first-return map on any nonempty subset of the moved-point
support of a finite permutation cycle is transitive. This packages the
post-deletion half of a cycle contraction. -/
theorem isCycle_support_firstReturn_one_orbit
    {α : Type*} [Finite α] (f : Equiv.Perm α) (hf : Equiv.Perm.IsCycle f)
    (P : {a : α // f a ≠ a} → Prop) [DecidablePred P]
    (hP : ∃ a, P a) :
    let hreturn : ∀ x : {a : {a : α // f a ≠ a} // P a},
        ∃ n : ℕ, 0 < n ∧ P ((cycleSupportMap f)^[n] x.1) :=
      fun x => finiteOrbit_exists_positive_hit (cycleSupportMap f)
        (cycleSupportMap_injective f) (isCycle_support_iterate_transitive f hf)
        P hP x.1
    ∀ x y : {a : {a : α // f a ≠ a} // P a},
      ∃ k : ℕ,
        (finiteOrbitFirstReturn (cycleSupportMap f) P hreturn)^[k] x = y := by
  dsimp only
  let hreturn : ∀ x : {a : {a : α // f a ≠ a} // P a},
      ∃ n : ℕ, 0 < n ∧ P ((cycleSupportMap f)^[n] x.1) :=
    fun x => finiteOrbit_exists_positive_hit (cycleSupportMap f)
      (cycleSupportMap_injective f) (isCycle_support_iterate_transitive f hf)
      P hP x.1
  exact finiteOrbitFirstReturn_one_orbit (cycleSupportMap f)
    (cycleSupportMap_injective f)
    (isCycle_support_iterate_transitive f hf) P hP

theorem formPerm_append_isCycle_of_disjoint
    {α : Type*} [DecidableEq α] (left right : List α)
    (hleft : left.Nodup) (hright : right.Nodup)
    (hdisjoint : List.Disjoint left right)
    (hlength : 2 ≤ (left ++ right).length) :
    Equiv.Perm.IsCycle (List.formPerm (left ++ right)) := by
  apply List.isCycle_formPerm
  · rw [List.nodup_append']
    refine ⟨hleft, hright, ?_⟩
    intro a ha hb
    exact (List.disjoint_left.mp hdisjoint ha) hb
  · exact hlength

end SystolicGrowth

#print axioms SystolicGrowth.formPerm_append_isCycle_of_disjoint
#print axioms SystolicGrowth.formPerm_append_splice_eq
#print axioms SystolicGrowth.formPerm_splice_isCycle
#print axioms SystolicGrowth.formPerm_splice_word_of_mem
#print axioms SystolicGrowth.formPerm_splice_blocks_fold
#print axioms SystolicGrowth.formPerm_splice_isCycle_of_mem
#print axioms SystolicGrowth.isCycle_support_iterate_transitive
#print axioms SystolicGrowth.isCycle_support_firstReturn_one_orbit
