module

public import BuserSarnak.FiniteOrbitGap
public import Mathlib.Data.List.Chain

@[expose] public section

/-!
# Literal chains of positive orbit gaps

Open tours retain their two endpoint sentinels even when those endpoints are
omitted. Only omitted interior points may be bypassed: a retained intermediate
point is never treated as a transitivity pivot.
-/

namespace SystolicGrowth

variable {X : Type*} {f : X → X} {P : X → Prop}

/-- A literal open chain collapses to a single positive gap when every
interior point is omitted. The interior list may be empty. -/
theorem positiveOrbitGap_of_isChain_open {a b : X} {l : List X}
    (h : List.IsChain (PositiveOrbitGap f P) (a :: l ++ [b]))
    (homitted : ∀ x ∈ l, ¬ P x) : PositiveOrbitGap f P a b := by
  induction l generalizing a with
  | nil => simpa only [List.cons_append, List.nil_append, List.isChain_pair] using h
  | cons c l ih =>
      simp only [List.cons_append] at h
      exact h.rel.trans_of_not_mem
        (ih h.tail (fun x hx => homitted x (List.mem_cons_of_mem c hx)))
        (homitted c List.mem_cons_self)

/-- Erase an omitted pivot from any literal chain. No nonemptiness or nodup
premise is needed; endpoints and singleton lists are handled as well. -/
theorem positiveOrbitGap_isChain_erase_omitted {a : X} {pre post : List X}
    (h : List.IsChain (PositiveOrbitGap f P) (pre ++ a :: post))
    (ha : ¬ P a) : List.IsChain (PositiveOrbitGap f P) (pre ++ post) := by
  induction pre with
  | nil => exact h.tail
  | cons b pre ih =>
      simp only [List.cons_append] at h ⊢
      cases pre with
      | nil =>
          cases post with
          | nil => exact .singleton b
          | cons c post =>
              exact .cons_cons (h.rel.trans_of_not_mem h.tail.rel ha) h.tail.tail
      | cons c pre => exact .cons_cons h.rel (ih h.tail)

/-- Filtering omitted interior points preserves each positive-gap adjacency.
The two endpoint sentinels are kept regardless of their retained status. -/
theorem positiveOrbitGap_isChain_filter_open [DecidablePred P]
    {a b : X} {l : List X}
    (h : List.IsChain (PositiveOrbitGap f P) (a :: l ++ [b])) :
    List.IsChain (PositiveOrbitGap f P)
      (a :: l.filter (fun x => decide (P x)) ++ [b]) := by
  induction l generalizing a with
  | nil => simpa using h
  | cons c l ih =>
      simp only [List.cons_append] at h
      by_cases hc : P c
      · simp only [List.filter_cons, hc, decide_true, ↓reduceIte,
          List.cons_append]
        exact List.IsChain.cons_cons h.rel (ih h.tail)
      · have hskip : List.IsChain (PositiveOrbitGap f P) (a :: l ++ [b]) := by
          exact positiveOrbitGap_isChain_erase_omitted (pre := [a]) h hc
        simpa only [List.filter_cons, hc, decide_false, Bool.false_eq_true,
          ↓reduceIte] using ih hskip

/-- Two open tours concatenate across an omitted common sentinel, erasing
that sentinel instead of asserting transitivity through a retained point. -/
theorem positiveOrbitGap_isChain_append_erase_middle
    {a b c : X} {left right : List X}
    (hleft : List.IsChain (PositiveOrbitGap f P) (a :: left ++ [b]))
    (hright : List.IsChain (PositiveOrbitGap f P) (b :: right ++ [c]))
    (hb : ¬ P b) :
    List.IsChain (PositiveOrbitGap f P) (a :: (left ++ right) ++ [c]) := by
  have hboth : List.IsChain (PositiveOrbitGap f P)
      ((a :: left) ++ b :: (right ++ [c])) :=
    List.isChain_split.mpr ⟨hleft, hright⟩
  simpa only [List.cons_append, List.append_assoc] using
    positiveOrbitGap_isChain_erase_omitted hboth hb

/-- Expand each consecutive base point by a literal open tour ending at its
base successor. The tours join by a single shared endpoint, which is not
duplicated in the resulting list. Empty tails and empty base lists are allowed. -/
theorem isChain_flatMap_open_tours {R : X → X → Prop}
    (successor : X → X) (tail : X → List X) {base : List X} {b : X}
    (hbase : List.IsChain (fun d e => successor d = e) (base ++ [b]))
    (htour : ∀ d ∈ base, List.IsChain R (d :: tail d ++ [successor d])) :
    List.IsChain R (base.flatMap (fun d => d :: tail d) ++ [b]) := by
  induction base with
  | nil => exact .singleton b
  | cons d base ih =>
      cases base with
      | nil =>
          have hsuccessor : successor d = b := hbase.rel
          simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
            hsuccessor] using htour d List.mem_cons_self
      | cons e base =>
          have hsuccessor : successor d = e := hbase.rel
          have hfirst : List.IsChain R ((d :: tail d) ++ [e]) := by
            simpa only [hsuccessor] using htour d List.mem_cons_self
          have hrest : List.IsChain R
              ((e :: base).flatMap (fun d => d :: tail d) ++ [b]) :=
            ih hbase.tail (fun x hx => htour x (List.mem_cons_of_mem d hx))
          simp only [List.flatMap_cons, List.append_assoc] at hrest ⊢
          exact List.isChain_split.mpr ⟨hfirst, hrest⟩

/-- A fixed anchor can precede an expanded sequence of open tours. The
anchor's initial adjacency also covers the case of an empty sequence. -/
theorem isChain_cons_flatMap_open_tours {R : X → X → Prop}
    (successor : X → X) (tail : X → List X) {a b : X} {base : List X}
    (hbase : List.IsChain (fun d e => successor d = e) (base ++ [b]))
    (htour : ∀ d ∈ base, List.IsChain R (d :: tail d ++ [successor d]))
    (hanchor : R a (base.head?.getD b)) :
    List.IsChain R (a :: base.flatMap (fun d => d :: tail d) ++ [b]) := by
  cases base with
  | nil => simpa only [List.flatMap_nil, List.nil_append, List.head?_nil,
      Option.getD_none, List.cons_append, List.isChain_pair] using hanchor
  | cons d base =>
      have hrest := isChain_flatMap_open_tours successor tail hbase htour
      simp only [List.flatMap_cons, List.cons_append] at hrest ⊢
      exact .cons_cons hanchor hrest

/-- Closing an open tour through an omitted sentinel gives the literal
cyclic chain on its interior, including the empty-interior case. -/
theorem positiveOrbitGap_isChain_close_erase_sentinel
    {a : X} {l : List X}
    (h : List.IsChain (PositiveOrbitGap f P) (a :: l ++ [a]))
    (ha : ¬ P a) :
    List.IsChain (PositiveOrbitGap f P) (l ++ l.take 1) := by
  cases l with
  | nil => exact .nil
  | cons b l =>
      simp only [List.cons_append] at h
      have hclosed : List.IsChain (PositiveOrbitGap f P)
          ((b :: l) ++ a :: [b]) :=
        List.isChain_split.mpr ⟨h.tail, List.isChain_pair.mpr h.rel⟩
      simpa only [List.take_succ_cons, List.take_zero, List.cons_append,
        List.nil_append] using positiveOrbitGap_isChain_erase_omitted hclosed ha

#print axioms positiveOrbitGap_of_isChain_open
#print axioms positiveOrbitGap_isChain_filter_open
#print axioms positiveOrbitGap_isChain_append_erase_middle
#print axioms positiveOrbitGap_isChain_close_erase_sentinel
#print axioms isChain_flatMap_open_tours
#print axioms isChain_cons_flatMap_open_tours

end SystolicGrowth
