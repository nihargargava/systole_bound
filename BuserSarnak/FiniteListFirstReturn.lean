module

public import BuserSarnak.FiniteOrbitCyclicGap
public import BuserSarnak.FinitePermutationFirstReturn

@[expose] public section

/-!
# Exact first return of a filtered cyclic list

Deleting occurrences from a nodup cyclic list realizes the first-return
map of its original cyclic permutation. This includes retained points outside
the displayed list, which both permutations fix. The proof preserves ordered
cyclic adjacency and its last-to-first seam, not merely list support.
-/

namespace SystolicGrowth

noncomputable section

variable {X : Type*} [DecidableEq X]

/-- The cyclic-list permutation advances the exact literal position. -/
theorem list_formPerm_apply_cyclic_get (l : List X) (hn : l.Nodup)
    (i : Fin l.length) :
    l.formPerm (l.get i) = l.get (cyclicSucc i) := by
  cases l with
  | nil => exact Fin.elim0 i
  | cons a l =>
    rcases i with ⟨k, hk⟩
    by_cases hlt : k < l.length
    · have hsucc : cyclicSucc (⟨k, hk⟩ : Fin (a :: l).length) =
          ⟨k + 1, by simpa using Nat.succ_lt_succ hlt⟩ :=
        finRotate_of_lt hlt
      rw [hsucc]
      exact List.formPerm_apply_lt_getElem (a :: l) hn k
        (by simpa using Nat.succ_lt_succ hlt)
    · have hlast : k = l.length := by
        simp only [List.length_cons] at hk
        omega
      subst k
      have hsucc : cyclicSucc (⟨l.length, hk⟩ : Fin (a :: l).length) =
          ⟨0, by simp⟩ := finRotate_last'
      rw [hsucc]
      exact List.formPerm_apply_getElem_length a l

/-- The displayed cyclic list, closed with its first point, follows its
actual permutation at every edge, including the wraparound edge. -/
theorem list_formPerm_isChain_cyclic (l : List X) (hn : l.Nodup) :
    (l ++ l.take 1).IsChain (fun x y => l.formPerm x = y) := by
  have hlinear : l.IsChain (fun x y => l.formPerm x = y) :=
    List.isChain_iff_getElem.mpr fun i hi =>
      List.formPerm_apply_lt_getElem l hn i hi
  cases l with
  | nil => exact .nil
  | cons a l =>
    have hclosed : ((a :: l) ++ [a]).IsChain
        (fun x y => (a :: l).formPerm x = y) := by
      apply hlinear.append (.singleton a)
      intro x hx y hy
      rcases List.mem_getLast?_eq_getLast hx with ⟨_, rfl⟩
      have hy' : y = a := (by simpa using hy : a = y).symm
      subst y
      exact List.formPerm_apply_getLast a l
    simpa only [List.take_succ_cons, List.take_zero] using hclosed

/-- Ordered deletion preserves the positive omitted-only gap across every
pair of successive retained occurrences. Empty retained lists are allowed. -/
theorem list_formPerm_filter_isChain_gaps (l : List X) (hn : l.Nodup)
    (P : X → Prop) [DecidablePred P] :
    (l.filter (fun x => decide (P x)) ++
      (l.filter (fun x => decide (P x))).take 1).IsChain
        (PositiveOrbitGap l.formPerm P) := by
  apply positiveOrbitGap_isChain_filter_cyclic
  exact (list_formPerm_isChain_cyclic l hn).imp fun x y (hxy : l.formPerm x = y) =>
    hxy ▸ positiveOrbitGap_step l.formPerm P x

/-- Filtering a nodup cyclic list is exactly first return of its original
permutation, including retained points outside the list (which remain fixed). -/
theorem list_formPerm_filter_eq_firstReturn [Finite X]
    (l : List X) (hn : l.Nodup) (P : X → Prop) [DecidablePred P]
    (x : {x : X // P x}) :
    (l.filter (fun z => decide (P z))).formPerm x.val =
      (finitePermutationFirstReturn l.formPerm P x).val := by
  by_cases hx : x.val ∈ l
  · let retained := l.filter (fun z => decide (P z))
    have hmem : ∀ y ∈ retained, P y := by
      intro y hy
      exact of_decide_eq_true (List.mem_filter.mp hy).2
    have hxret : x.val ∈ retained := by
      exact List.mem_filter.mpr ⟨hx, decide_eq_true x.property⟩
    obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hxret
    let i : Fin retained.length := ⟨k, hk⟩
    have hget' : retained.get i = x.val := hget
    have hsub : (⟨retained.get i, hmem _ (List.get_mem retained i)⟩ :
        {y : X // P y}) = x := Subtype.ext hget'
    have hreturn := positiveOrbitGap_cyclic_firstReturn l.formPerm P
      (finitePermutation_exists_positive_return l.formPerm P)
      retained hmem (list_formPerm_filter_isChain_gaps l hn P) i
    change (finitePermutationFirstReturn l.formPerm P
      ⟨retained.get i, hmem _ (List.get_mem retained i)⟩).val =
        retained.get (cyclicSucc i) at hreturn
    rw [hsub] at hreturn
    calc
      retained.formPerm x.val = retained.formPerm (retained.get i) :=
        congrArg retained.formPerm hget'.symm
      _ = retained.get (cyclicSucc i) :=
        list_formPerm_apply_cyclic_get retained (hn.filter _) i
      _ = (finitePermutationFirstReturn l.formPerm P x).val := hreturn.symm
  · have hxret : x.val ∉ l.filter (fun z => decide (P z)) :=
      fun h => hx (List.mem_filter.mp h).1
    have hfix : l.formPerm x.val = x.val := List.formPerm_apply_of_notMem hx
    rw [List.formPerm_apply_of_notMem hxret,
      finitePermutationFirstReturn_val_eq_of_mem_apply l.formPerm P x
        (by rw [hfix]; exact x.property), hfix]

#print axioms list_formPerm_apply_cyclic_get
#print axioms list_formPerm_isChain_cyclic
#print axioms list_formPerm_filter_isChain_gaps
#print axioms list_formPerm_filter_eq_firstReturn

end

end SystolicGrowth
