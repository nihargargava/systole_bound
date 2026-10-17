module

public import BuserSarnak.FiniteOrbitGapChain
public import BuserSarnak.OrientableWicksNielsen

@[expose] public section

/-!
# Recognizing cyclic first return from an ordered gap chain

Closing a literal list with its first point records the wraparound edge.
Each adjacent positive gap with retained endpoints is then exactly first
return. The statement concerns ordered occurrences, not only list support.
-/

namespace SystolicGrowth

/-- An explicitly closed chain gives the relation at every cyclic successor. -/
theorem isChain_cyclic_get {X : Type*} {R : X → X → Prop} {l : List X}
    (h : (l ++ l.take 1).IsChain R) (i : Fin l.length) :
    R (l.get i) (l.get (cyclicSucc i)) := by
  cases l with
  | nil => exact Fin.elim0 i
  | cons a l =>
      rcases i with ⟨k, hk⟩
      by_cases hlt : k < l.length
      · have hsucc : cyclicSucc (⟨k, hk⟩ : Fin (a :: l).length) =
          ⟨k + 1, by simpa using Nat.succ_lt_succ hlt⟩ :=
          finRotate_of_lt hlt
        rw [hsucc]
        exact h.left_of_append.getElem k (by simpa using Nat.succ_lt_succ hlt)
      · have hlast : k = l.length := by simp only [List.length_cons] at hk; omega
        subst k
        have hsucc : cyclicSucc (⟨l.length, hk⟩ : Fin (a :: l).length) =
            ⟨0, by simp⟩ := finRotate_last'
        rw [hsucc]
        have hrel := h.getElem l.length (by simp)
        simpa only [List.take_succ_cons, List.take_zero, List.get_eq_getElem,
          List.getElem_append, List.length_cons, Nat.lt_succ_self,
          Nat.lt_irrefl, ↓reduceDIte, Nat.sub_self, List.getElem_cons_zero] using hrel

/-- Changing only the proof of the position domain preserves cyclic order. -/
theorem cyclicSucc_cast {m n : ℕ} (h : m = n) (i : Fin m) :
    Fin.cast h (cyclicSucc i) = cyclicSucc (Fin.cast h i) := by
  subst n
  rfl

/-- An ordered physical decoder inherits every cyclic adjacency of its
literal occurrence list, including the last-to-first edge. -/
theorem isChain_cyclic_ofFn {X : Type*} {R : X → X → Prop} {n : ℕ}
    (e : Fin n → X)
    (h : (List.ofFn e ++ (List.ofFn e).take 1).IsChain R) (i : Fin n) :
    R (e i) (e (cyclicSucc i)) := by
  have hlen : (List.ofFn e).length = n := List.length_ofFn
  have hrel := isChain_cyclic_get h (Fin.cast hlen.symm i)
  simpa only [List.get_ofFn, cyclicSucc_cast, Fin.cast_cast,
    Fin.cast_refl, id_eq] using hrel

/-- Filtering a closed gap chain keeps the last-to-first gap even when its
initial anchor is omitted or the entire retained list is empty. -/
theorem positiveOrbitGap_isChain_filter_cyclic
    {X : Type*} {f : X → X} {P : X → Prop} [DecidablePred P]
    {l : List X} (h : (l ++ l.take 1).IsChain (PositiveOrbitGap f P)) :
    (l.filter (fun x => decide (P x)) ++
      (l.filter (fun x => decide (P x))).take 1).IsChain (PositiveOrbitGap f P) := by
  cases l with
  | nil => exact .nil
  | cons a l =>
      have hopen : (a :: l ++ [a]).IsChain (PositiveOrbitGap f P) := by
        simpa only [List.take_succ_cons, List.take_zero, List.cons_append] using h
      have hfilter := positiveOrbitGap_isChain_filter_open hopen
      by_cases ha : P a
      · simpa only [List.filter_cons, ha, decide_true, ↓reduceIte,
          List.take_succ_cons, List.take_zero, List.cons_append] using hfilter
      · simpa only [List.filter_cons, ha, decide_false, Bool.false_eq_true,
          ↓reduceIte] using positiveOrbitGap_isChain_close_erase_sentinel hfilter ha

/-- A cyclic omitted-gap chain of retained points realizes first return at
each literal list position. -/
theorem positiveOrbitGap_cyclic_firstReturn
    {X : Type*} (f : X → X) (P : X → Prop) [DecidablePred P]
    (hreturn : ∀ x : {x : X // P x}, ∃ n : ℕ, 0 < n ∧ P (f^[n] x.1))
    (l : List X) (hmem : ∀ x ∈ l, P x)
    (hchain : (l ++ l.take 1).IsChain (PositiveOrbitGap f P))
    (i : Fin l.length) :
    (finiteOrbitFirstReturn f P hreturn
      ⟨l.get i, hmem _ (List.get_mem l i)⟩).val = l.get (cyclicSucc i) := by
  exact PositiveOrbitGap.firstReturn_val_eq hreturn _
    (isChain_cyclic_get hchain i) (hmem _ (List.get_mem l (cyclicSucc i)))

/-- A retained occurrence decoder realizes positive first return from a
literal cyclic gap chain, without any support-only argument. -/
theorem positiveOrbitGap_cyclic_firstReturn_ofFn
    {X : Type*} (f : X → X) (P : X → Prop) [DecidablePred P]
    (hreturn : ∀ x : {x : X // P x}, ∃ n : ℕ, 0 < n ∧ P (f^[n] x.1))
    {n : ℕ} (e : Fin n → X) (hmem : ∀ i, P (e i))
    (hchain : (List.ofFn e ++ (List.ofFn e).take 1).IsChain (PositiveOrbitGap f P))
    (i : Fin n) :
    (finiteOrbitFirstReturn f P hreturn ⟨e i, hmem i⟩).val = e (cyclicSucc i) :=
  PositiveOrbitGap.firstReturn_val_eq hreturn _
    (isChain_cyclic_ofFn e hchain i) (hmem (cyclicSucc i))

#print axioms isChain_cyclic_get
#print axioms isChain_cyclic_ofFn
#print axioms positiveOrbitGap_isChain_filter_cyclic
#print axioms positiveOrbitGap_cyclic_firstReturn
#print axioms positiveOrbitGap_cyclic_firstReturn_ofFn

end SystolicGrowth
