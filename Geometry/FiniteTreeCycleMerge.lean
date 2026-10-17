module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import BuserSarnak.FiniteRootedCycleContraction

@[expose] public section

/-!
# One cycle from a finite rooted tree of cyclic dart blocks

This module isolates the finite combinatorics of tree-splicing cyclic blocks.
The input consists of actual local cyclic words, their dart-to-vertex map, and
an explicit rooted-tree attachment contract (`RootedCycleTreeData`).  The
recursive constructor builds the merged word; it does not assume a global
orbit.  At each attachment the source pivot lies in the accumulated parent
block and the target pivot in the child block, and the splice lemma proves
that the two cycles merge.

The theorem below certifies the resulting *recursive physical product*.  A
consumer wishing to identify that product with `f * treePairing` must still
prove that exact permutation factorization for its chosen simultaneous
pairing convention; that algebraic identification is deliberately not
smuggled in as a tree-data field.
-/

namespace SystolicGrowth

noncomputable section

private theorem list_length_eq_card_of_nodup_of_forall_mem
    {D : Type*} [Fintype D] [DecidableEq D] (word : List D)
    (hnodup : word.Nodup) (hfull : ∀ d : D, d ∈ word) :
    word.length = Fintype.card D := by
  let e : Fin word.length ≃ D := List.Nodup.getEquivOfForallMemList word hnodup hfull
  have hcard := Fintype.card_congr e
  simpa using hcard

/-- A nodup list exhausting a finite type gives one cyclic permutation. -/
theorem list_formPerm_isCycle_of_forall_mem
    {D : Type*} [Fintype D] [DecidableEq D] (word : List D)
    (hnodup : word.Nodup) (hfull : ∀ d : D, d ∈ word)
    (hcard : 2 ≤ Fintype.card D) :
    Equiv.Perm.IsCycle (List.formPerm word) := by
  apply List.isCycle_formPerm hnodup
  rw [list_length_eq_card_of_nodup_of_forall_mem word hnodup hfull]
  exact hcard

/-- The same exhaustive cyclic word has one natural iterate-orbit. -/
theorem list_formPerm_oneOrbit_of_forall_mem
    {D : Type*} [Fintype D] [DecidableEq D] (word : List D)
    (hnodup : word.Nodup) (hfull : ∀ d : D, d ∈ word)
    (hcard : 2 ≤ Fintype.card D) :
    ∀ x y : D, ∃ n : ℕ, (List.formPerm word)^[n] x = y := by
  intro x y
  have hlen : 2 ≤ word.length := by
    rw [list_length_eq_card_of_nodup_of_forall_mem word hnodup hfull]
    exact hcard
  have hcycle : Equiv.Perm.IsCycle (List.formPerm word) :=
    List.isCycle_formPerm hnodup hlen
  have hx : List.formPerm word x ≠ x := by
    exact (List.formPerm_apply_mem_ne_self_iff word hnodup x (hfull x)).mpr hlen
  have hy : List.formPerm word y ≠ y := by
    exact (List.formPerm_apply_mem_ne_self_iff word hnodup y (hfull y)).mpr hlen
  obtain ⟨n, hn⟩ := hcycle.exists_pow_eq hx hy
  refine ⟨n, ?_⟩
  simpa only [Equiv.Perm.coe_pow, Function.iterate_fixed] using hn

/-- The inductive tree trace supplies a single cyclic permutation whenever
its merged word covers every dart.  No one-orbit or cycle hypothesis is an
input: the orbit follows from the actual nodup word and its full support. -/
theorem RootedCycleContractionTrace.physicalProduct_isCycle
    {V E D : Type*} [Fintype D] [DecidableEq D]
    {T : RootedCycleTreeData V E D} {q : V} {merged : List D}
    (trace : RootedCycleContractionTrace T q merged)
    (hfull : ∀ d : D, d ∈ merged) (hcard : 2 ≤ Fintype.card D) :
    ∃ childWords : E → List D,
      Equiv.Perm.IsCycle (T.physicalProduct q childWords) := by
  cases trace with
  | node q childWords merged childTrace nodup support permutation physicalPermutation =>
      refine ⟨childWords, ?_⟩
      rw [← physicalPermutation]
      exact list_formPerm_isCycle_of_forall_mem merged nodup hfull hcard

/-- If an independently verified factorization identifies the rooted splice
word with a simultaneous original-rotation/tree-pairing product, the latter
is one cycle.  The hypothesis is an equality of permutations, not an orbit
claim; this isolates the exact algebraic bridge needed by consumers. -/
theorem RootedCycleContractionTrace.isCycle_of_treePairing_factorization
    {V E D : Type*} [Fintype D] [DecidableEq D]
    {T : RootedCycleTreeData V E D} {q : V} {merged : List D}
    (trace : RootedCycleContractionTrace T q merged)
    (hfull : ∀ d : D, d ∈ merged) (hcard : 2 ≤ Fintype.card D)
    (rotation treePairing : Equiv.Perm D)
    (hfactor : List.formPerm merged = rotation * treePairing) :
    Equiv.Perm.IsCycle (rotation * treePairing) := by
  rw [← hfactor]
  exact list_formPerm_isCycle_of_forall_mem merged trace.nodup hfull hcard

/-- Natural-iterate version of the explicit factorization bridge. -/
theorem RootedCycleContractionTrace.oneOrbit_of_treePairing_factorization
    {V E D : Type*} [Fintype D] [DecidableEq D]
    {T : RootedCycleTreeData V E D} {q : V} {merged : List D}
    (trace : RootedCycleContractionTrace T q merged)
    (hfull : ∀ d : D, d ∈ merged) (hcard : 2 ≤ Fintype.card D)
    (rotation treePairing : Equiv.Perm D)
    (hfactor : List.formPerm merged = rotation * treePairing) :
    ∀ x y : D, ∃ n : ℕ, (rotation * treePairing)^[n] x = y := by
  intro x y
  have hlen : 2 ≤ merged.length := by
    rw [list_length_eq_card_of_nodup_of_forall_mem merged trace.nodup hfull]
    exact hcard
  have hcycle : Equiv.Perm.IsCycle (List.formPerm merged) :=
    List.isCycle_formPerm trace.nodup hlen
  have hx : List.formPerm merged x ≠ x := by
    exact (List.formPerm_apply_mem_ne_self_iff merged trace.nodup x (hfull x)).mpr hlen
  have hy : List.formPerm merged y ≠ y := by
    exact (List.formPerm_apply_mem_ne_self_iff merged trace.nodup y (hfull y)).mpr hlen
  obtain ⟨n, hn⟩ := hcycle.exists_pow_eq hx hy
  refine ⟨n, ?_⟩
  rw [← hfactor]
  simpa only [Equiv.Perm.coe_pow, Function.iterate_fixed] using hn

/-- A rooted finite cycle tree whose root region contains all darts constructs
an actual recursive tree-spliced one-cycle permutation.  The output retains
the merged word, exact support, and child-cycle choices for later comparison
with a concrete global pairing involution. -/
theorem rootedCycleTree_exists_physicalOneCycle
    {V E D : Type*} [Fintype V] [Fintype D] [DecidableEq D]
    (T : RootedCycleTreeData V E D) (root : V)
    (hroot : ∀ d : D, T.ancestor root (T.vertex d))
    (hcard : 2 ≤ Fintype.card D) :
    ∃ merged : List D, ∃ childWords : E → List D,
      merged.Nodup ∧ (∀ d : D, d ∈ merged) ∧
      List.formPerm merged = T.physicalProduct root childWords ∧
      Equiv.Perm.IsCycle (T.physicalProduct root childWords) := by
  obtain ⟨merged, hnodup, hmem, trace⟩ := rootedCycleContraction_exists T root
  cases trace with
  | node q childWords merged childTrace traceNodup support permutation physicalPermutation =>
      refine ⟨merged, childWords, traceNodup, ?_, physicalPermutation, ?_⟩
      · intro d
        exact (support d).mpr (hroot d)
      · rw [← physicalPermutation]
        exact list_formPerm_isCycle_of_forall_mem merged traceNodup
          (fun d => (support d).mpr (hroot d)) hcard

/-- The preceding constructed permutation acts transitively by natural
iteration on the entire dart type, not merely on the nonfixed support. -/
theorem rootedCycleTree_exists_physicalOneOrbit
    {V E D : Type*} [Fintype V] [Fintype D] [DecidableEq D]
    (T : RootedCycleTreeData V E D) (root : V)
    (hroot : ∀ d : D, T.ancestor root (T.vertex d))
    (hcard : 2 ≤ Fintype.card D) :
    ∃ childWords : E → List D,
      ∀ x y : D, ∃ n : ℕ, (T.physicalProduct root childWords)^[n] x = y := by
  obtain ⟨merged, childWords, hnodup, hfull, hperm, hcycle⟩ :=
    rootedCycleTree_exists_physicalOneCycle T root hroot hcard
  refine ⟨childWords, ?_⟩
  intro x y
  have hx : T.physicalProduct root childWords x ≠ x := by
    rw [← hperm]
    exact (List.formPerm_apply_mem_ne_self_iff merged hnodup x (hfull x)).mpr (by
      rw [list_length_eq_card_of_nodup_of_forall_mem merged hnodup hfull]
      exact hcard)
  have hy : T.physicalProduct root childWords y ≠ y := by
    rw [← hperm]
    exact (List.formPerm_apply_mem_ne_self_iff merged hnodup y (hfull y)).mpr (by
      rw [list_length_eq_card_of_nodup_of_forall_mem merged hnodup hfull]
      exact hcard)
  obtain ⟨n, hn⟩ := hcycle.exists_pow_eq hx hy
  refine ⟨n, ?_⟩
  simpa only [Equiv.Perm.coe_pow, Function.iterate_fixed] using hn

#print axioms list_formPerm_isCycle_of_forall_mem
#print axioms list_formPerm_oneOrbit_of_forall_mem
#print axioms rootedCycleTree_exists_physicalOneCycle
#print axioms rootedCycleTree_exists_physicalOneOrbit
#print axioms RootedCycleContractionTrace.isCycle_of_treePairing_factorization
#print axioms RootedCycleContractionTrace.oneOrbit_of_treePairing_factorization

end

end SystolicGrowth
