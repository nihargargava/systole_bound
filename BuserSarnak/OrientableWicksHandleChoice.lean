module

public import BuserSarnak.OrientableWicksNielsen
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.TakeDrop

@[expose] public section

/-!
# Handle-choice consequences of one-vertex Wicks data

An arc closed under occurrence pairing would give a proper invariant region
for the vertex rotation. Thus every paired chord has a genuinely crossing
chord; this is derived from the certificate, not supplied as an extra input.
-/

namespace SystolicGrowth

noncomputable section

namespace OrientableWicksCertificate

variable {X : Type*} [Fintype X] {w : SignedWord X}

/-- The signed occurrence inventory makes literal lookup injective. -/
theorem literal_get_injective (C : OrientableWicksCertificate w) :
    Function.Injective w.get := by
  intro i j hij
  rcases C.exhaustive i with hi | hi <;> rcases C.exhaustive j with hj | hj
  · have hx : (w.get i).1 = (w.get j).1 := congrArg Prod.fst hij
    exact hi.trans ((congrArg C.positive hx).trans hj.symm)
  · have hsign : true = false := by
      calc
        true = (w.get i).2 := by rw [hi, C.positive_spec]
        _ = (w.get j).2 := congrArg Prod.snd hij
        _ = false := by rw [hj, C.negative_spec]
    cases hsign
  · have hsign : false = true := by
      calc
        false = (w.get i).2 := by rw [hi, C.negative_spec]
        _ = (w.get j).2 := congrArg Prod.snd hij
        _ = true := by rw [hj, C.positive_spec]
    cases hsign
  · have hx : (w.get i).1 = (w.get j).1 := congrArg Prod.fst hij
    exact hi.trans ((congrArg C.negative hx).trans hj.symm)

/-- Every signed letter occurs at most once in the unreduced contour. -/
theorem literal_nodup (C : OrientableWicksCertificate w) : w.Nodup :=
  List.nodup_iff_injective_get.mpr C.literal_get_injective

/-- A nonempty rotation-closed set contains every occurrence in a one-vertex word. -/
theorem forall_of_rotation_closed (C : OrientableWicksCertificate w)
    (P : Fin w.length → Prop) (hclosed : ∀ i, P i → P (C.rotation i))
    (i : Fin w.length) (hi : P i) : ∀ j, P j := by
  intro j
  have hiter : ∀ n : ℕ, P (C.rotation^[n] i) := by
    intro n
    induction n with
    | zero => exact hi
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact hclosed _ ih
  obtain ⟨n, hn⟩ := C.one_orbit i j
  exact hn ▸ hiter n

/-- One-vertex rotation cannot fix a dart: its distinct partner is in the same orbit. -/
theorem rotation_ne_self (C : OrientableWicksCertificate w) (i : Fin w.length) :
    C.rotation i ≠ i := by
  intro hfix
  have hsame : C.partner i = i :=
    C.forall_of_rotation_closed (fun j => j = i)
      (by intro j hj; subst j; exact hfix) i rfl (C.partner i)
  exact C.partner_ne i hsame

/-- Consecutive boundary occurrences cannot be the two ends of one paired edge. -/
theorem partner_ne_cyclicSucc (C : OrientableWicksCertificate w) (i : Fin w.length) :
    C.partner i ≠ cyclicSucc i := by
  intro h
  apply C.rotation_ne_self (C.partner i)
  rw [C.rotation_eq, C.partner_involutive]
  exact h.symm

/-- The partner of the positive occurrence is the displayed negative occurrence. -/
theorem partner_positive (C : OrientableWicksCertificate w) (x : X) :
    C.partner (C.positive x) = C.negative x := by
  have hget : w.get (C.partner (C.positive x)) = (x, false) := by
    rw [C.partner_spec, C.positive_spec]
    rfl
  rcases C.exhaustive (C.partner (C.positive x)) with hpos | hneg
  · have hpositive : (w.get (C.partner (C.positive x))).2 = true := by
      rw [hpos, C.positive_spec]
    have hnegative : (w.get (C.partner (C.positive x))).2 = false :=
      congrArg Prod.snd hget
    rw [hpositive] at hnegative
    cases hnegative
  · have hlabel : (w.get (C.partner (C.positive x))).1 = x :=
      congrArg Prod.fst hget
    rw [hlabel] at hneg
    exact hneg

/-- The partner of the negative occurrence is the displayed positive occurrence. -/
theorem partner_negative (C : OrientableWicksCertificate w) (x : X) :
    C.partner (C.negative x) = C.positive x := by
  rw [← C.partner_positive x, C.partner_involutive]

/-- Cyclic successor has no wrap when an ordinary successor lies below the length. -/
theorem cyclicSucc_val_of_succ_lt {n : ℕ} (i : Fin n) (hi : i.val + 1 < n) :
    (cyclicSucc i).val = i.val + 1 := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
      have hlt : i.val < n := by omega
      exact congrArg Fin.val (finRotate_of_lt hlt)

/-- Every chord whose endpoints are listed in increasing order is crossed by
another chord. The crossing occurrence is strictly inside the chord interval;
its partner is strictly outside the closed interval. -/
theorem exists_crossing_of_lt (C : OrientableWicksCertificate w)
    (i j : Fin w.length) (hij : i.val < j.val) (hpair : C.partner i = j) :
    ∃ k : Fin w.length, i.val < k.val ∧ k.val < j.val ∧
      ((C.partner k).val < i.val ∨ j.val < (C.partner k).val) := by
  by_contra hnone
  have hpair' : C.partner j = i := by
    rw [← hpair, C.partner_involutive]
  have hinterior : ∀ k : Fin w.length, i.val < k.val → k.val < j.val →
      i.val < (C.partner k).val ∧ (C.partner k).val < j.val := by
    intro k hik hkj
    have hnot : ¬ ((C.partner k).val < i.val ∨ j.val < (C.partner k).val) := by
      intro hcross
      exact hnone ⟨k, hik, hkj, hcross⟩
    have hne_i : C.partner k ≠ i := by
      intro h
      have hk : k = j := by
        have heq := congrArg C.partner h
        rw [C.partner_involutive k, hpair] at heq
        exact heq
      have hval := congrArg Fin.val hk
      omega
    have hne_j : C.partner k ≠ j := by
      intro h
      have hk : k = i := by
        have heq := congrArg C.partner h
        rw [C.partner_involutive k, hpair'] at heq
        exact heq
      have hval := congrArg Fin.val hk
      omega
    have hval_i : (C.partner k).val ≠ i.val := fun h => hne_i (Fin.ext h)
    have hval_j : (C.partner k).val ≠ j.val := fun h => hne_j (Fin.ext h)
    omega
  let P := fun k : Fin w.length => i.val < k.val ∧ k.val ≤ j.val
  have hclosed : ∀ k, P k → P (C.rotation k) := by
    intro k hk
    by_cases hkj : k = j
    · subst k
      rw [C.rotation_eq, hpair']
      have hi := cyclicSucc_val_of_succ_lt i (by have hj := j.isLt; omega)
      change i.val < (cyclicSucc i).val ∧ (cyclicSucc i).val ≤ j.val
      rw [hi]
      omega
    · have hkjval : k.val < j.val := by
        have hne : k.val ≠ j.val := fun h => hkj (Fin.ext h)
        change i.val < k.val ∧ k.val ≤ j.val at hk
        omega
      have hp := hinterior k hk.1 hkjval
      have hsucc := cyclicSucc_val_of_succ_lt (C.partner k)
        (by have hj := j.isLt; omega)
      rw [C.rotation_eq]
      change i.val < (cyclicSucc (C.partner k)).val ∧
        (cyclicSucc (C.partner k)).val ≤ j.val
      rw [hsucc]
      omega
  have hall := C.forall_of_rotation_closed P hclosed j ⟨hij, le_rfl⟩ i
  exact (lt_irrefl i.val) hall.1

/-- Each alphabet generator has a crossing occurrence with a distinct label.
The smaller/larger endpoints retain their positive or negative provenance;
no cyclic relabeling or nonempty-interior assumption is needed. -/
theorem exists_distinct_crossing (C : OrientableWicksCertificate w) (x : X) :
    ∃ (a b k : Fin w.length),
      ((a = C.positive x ∧ b = C.negative x) ∨
        (a = C.negative x ∧ b = C.positive x)) ∧
      a.val < k.val ∧ k.val < b.val ∧
      ((C.partner k).val < a.val ∨ b.val < (C.partner k).val) ∧
      (w.get k).1 ≠ x := by
  have hdistinct : C.positive x ≠ C.negative x := by
    intro heq
    have hget := congrArg w.get heq
    rw [C.positive_spec, C.negative_spec] at hget
    have hsign := congrArg Prod.snd hget
    cases hsign
  have hval_ne : (C.positive x).val ≠ (C.negative x).val :=
    fun heq => hdistinct (Fin.ext heq)
  have hlabel_ne : ∀ a b k : Fin w.length,
      ((a = C.positive x ∧ b = C.negative x) ∨
        (a = C.negative x ∧ b = C.positive x)) →
      a.val < k.val → k.val < b.val → (w.get k).1 ≠ x := by
    intro a b k hab hak hkb hlabel
    rcases C.exhaustive k with hk | hk
    · rw [hlabel] at hk
      rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · rw [ha, hk] at hak
        exact (lt_irrefl _) hak
      · rw [hb, hk] at hkb
        exact (lt_irrefl _) hkb
    · rw [hlabel] at hk
      rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · rw [hb, hk] at hkb
        exact (lt_irrefl _) hkb
      · rw [ha, hk] at hak
        exact (lt_irrefl _) hak
  rcases lt_or_gt_of_ne hval_ne with hlt | hgt
  · obtain ⟨k, hak, hkb, hcross⟩ :=
      C.exists_crossing_of_lt (C.positive x) (C.negative x) hlt (C.partner_positive x)
    have hab : (C.positive x = C.positive x ∧ C.negative x = C.negative x) ∨
        (C.positive x = C.negative x ∧ C.negative x = C.positive x) :=
      Or.inl ⟨rfl, rfl⟩
    exact ⟨_, _, k, hab, hak, hkb, hcross, hlabel_ne _ _ k hab hak hkb⟩
  · obtain ⟨k, hak, hkb, hcross⟩ :=
      C.exists_crossing_of_lt (C.negative x) (C.positive x) hgt (C.partner_negative x)
    have hab : (C.negative x = C.positive x ∧ C.positive x = C.negative x) ∨
        (C.negative x = C.negative x ∧ C.positive x = C.positive x) :=
      Or.inr ⟨rfl, rfl⟩
    exact ⟨_, _, k, hab, hak, hkb, hcross, hlabel_ne _ _ k hab hak hkb⟩

/-- A nonempty alphabet supplies two alternating paired chords in the literal
linear order. Their orientation bits may subsequently be normalized by
generator inversions; the chord choice itself needs no rotation assumption. -/
theorem exists_alternating_positions (C : OrientableWicksCertificate w) (x : X) :
    ∃ (a b c d : Fin w.length),
      a.val < b.val ∧ b.val < c.val ∧ c.val < d.val ∧
      C.partner a = c ∧ C.partner b = d ∧
      (w.get a).1 ≠ (w.get b).1 := by
  obtain ⟨a, b, k, hab, hak, hkb, hcross, hlabel_ne⟩ := C.exists_distinct_crossing x
  have hpair : C.partner a = b := by
    rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [ha, hb]
      exact C.partner_positive x
    · rw [ha, hb]
      exact C.partner_negative x
  have ha_label : (w.get a).1 = x := by
    rcases hab with ⟨ha, _⟩ | ⟨ha, _⟩
    · rw [ha, C.positive_spec]
    · rw [ha, C.negative_spec]
  rcases hcross with hleft | hright
  · refine ⟨C.partner k, a, k, b, hleft, hak, hkb,
      C.partner_involutive k, hpair, ?_⟩
    rw [C.partner_label_eq, ha_label]
    exact hlabel_ne
  · refine ⟨a, k, b, C.partner k, hak, hkb, hright, hpair, rfl, ?_⟩
    rw [ha_label]
    exact Ne.symm hlabel_ne

private theorem drop_split_at_position {A : Type*} (l : List A) (m : ℕ)
    (j : Fin l.length) (hm : m ≤ j.val) :
    l.drop m = (l.drop m).take (j.val - m) ++ l.get j :: l.drop (j.val + 1) := by
  have hsplit := List.drop_take_append_drop l m (j.val - m)
  rw [Nat.add_sub_of_le hm, List.drop_eq_getElem_cons j.isLt] at hsplit
  exact hsplit.symm

/-- Four strictly ordered positions give the exact five intervening literal
blocks, including the possibly empty prefix, suffix, and inner intervals. -/
theorem exists_blocks_at_four_positions {A : Type*} (l : List A)
    (a b c d : Fin l.length) (hab : a.val < b.val) (hbc : b.val < c.val)
    (hcd : c.val < d.val) :
    ∃ U V W T Z : List A,
      l = U ++ l.get a :: (V ++ l.get b :: (W ++ l.get c :: (T ++ l.get d :: Z))) := by
  refine ⟨l.take a.val,
    (l.drop (a.val + 1)).take (b.val - (a.val + 1)),
    (l.drop (b.val + 1)).take (c.val - (b.val + 1)),
    (l.drop (c.val + 1)).take (d.val - (c.val + 1)), l.drop (d.val + 1), ?_⟩
  conv_lhs => rw [← List.take_append_drop a.val l]
  conv_lhs => rw [List.drop_eq_getElem_cons a.isLt]
  conv_lhs => rw [drop_split_at_position l (a.val + 1) b (by omega)]
  conv_lhs => rw [drop_split_at_position l (b.val + 1) c (by omega)]
  conv_lhs => rw [drop_split_at_position l (c.val + 1) d (by omega)]
  rfl

/-- The certificate supplies a literal alternating four-letter split.
Generator inversions can normalize the two displayed orientation bits; no
crossing, split, or block-existence premise is assumed. -/
theorem exists_alternating_blocks (C : OrientableWicksCertificate w) (initial : X) :
    ∃ (x y : X) (sx sy : Bool) (A B D E F : SignedWord X), x ≠ y ∧
      w = A ++ (x, sx) :: (B ++ (y, sy) ::
        (D ++ (x, !sx) :: (E ++ (y, !sy) :: F))) := by
  obtain ⟨a, b, c, d, hab, hbc, hcd, hpaira, hpairb, hlabel_ne⟩ :=
    C.exists_alternating_positions initial
  obtain ⟨A, B, D, E, F, hsplit⟩ :=
    exists_blocks_at_four_positions w a b c d hab hbc hcd
  refine ⟨(w.get a).1, (w.get b).1, (w.get a).2, (w.get b).2,
    A, B, D, E, F, hlabel_ne, ?_⟩
  have hc : w.get c = ((w.get a).1, !(w.get a).2) := by
    rw [← hpaira, C.partner_spec]
  have hd : w.get d = ((w.get b).1, !(w.get b).2) := by
    rw [← hpairb, C.partner_spec]
  rw [hc, hd] at hsplit
  simpa only [Prod.mk.eta] using hsplit

private theorem residual_marker_not_mem [DecidableEq X]
    (C : OrientableWicksCertificate w)
    (x y : X) (sx sy : Bool) (A B D E F : SignedWord X)
    (hsplit : w = A ++ (x, sx) :: (B ++ (y, sy) ::
      (D ++ (x, !sx) :: (E ++ (y, !sy) :: F))))
    (letter : X × Bool)
    (hletter : letter = (x, sx) ∨ letter = (y, sy) ∨
      letter = (x, !sx) ∨ letter = (y, !sy)) :
    letter ∉ A ++ B ++ D ++ E ++ F := by
  have hc : w.count letter ≤ 1 := (List.nodup_iff_count_le_one.mp C.literal_nodup) letter
  rw [hsplit] at hc
  apply List.count_eq_zero.mp
  simp only [List.count_append]
  rcases hletter with h | h | h | h <;> subst letter <;>
    simp only [List.count_append, List.count_cons, beq_self_eq_true, if_true] at hc <;>
    omega

/-- Every remainder block avoids both crossing generators, in both signs.
This follows from the literal inventory, not from freely reduced equality. -/
theorem blocks_avoid_crossing_labels (C : OrientableWicksCertificate w)
    (x y : X) (sx sy : Bool) (A B D E F : SignedWord X)
    (hsplit : w = A ++ (x, sx) :: (B ++ (y, sy) ::
      (D ++ (x, !sx) :: (E ++ (y, !sy) :: F)))) :
    ∀ letter ∈ A ++ B ++ D ++ E ++ F, letter.1 ≠ x ∧ letter.1 ≠ y := by
  classical
  intro letter hmem
  have hn (t : X × Bool) (ht : t = (x, sx) ∨ t = (y, sy) ∨
      t = (x, !sx) ∨ t = (y, !sy)) : t ∉ A ++ B ++ D ++ E ++ F :=
    residual_marker_not_mem C x y sx sy A B D E F hsplit t ht
  constructor
  · intro hlabel
    have heq : letter = (x, sx) ∨ letter = (x, !sx) := by
      cases letter with
      | mk z bit =>
          dsimp only at hlabel
          subst z
          cases bit <;> cases sx <;> simp
    rcases heq with heq | heq
    · exact hn letter (Or.inl heq) hmem
    · exact hn letter (Or.inr (Or.inr (Or.inl heq))) hmem
  · intro hlabel
    have heq : letter = (y, sy) ∨ letter = (y, !sy) := by
      cases letter with
      | mk z bit =>
          dsimp only at hlabel
          subst z
          cases bit <;> cases sy <;> simp
    rcases heq with heq | heq
    · exact hn letter (Or.inr (Or.inl heq)) hmem
    · exact hn letter (Or.inr (Or.inr (Or.inr heq))) hmem

/-- Complete literal handle choice: two distinct alternating labels and five
remainder blocks which avoid both labels. Only an alphabet element is needed
to select a nonempty case; the certificate proves every other obligation. -/
theorem exists_alternating_blocks_avoiding (C : OrientableWicksCertificate w) (initial : X) :
    ∃ (x y : X) (sx sy : Bool) (A B D E F : SignedWord X), x ≠ y ∧
      (w = A ++ (x, sx) :: (B ++ (y, sy) ::
        (D ++ (x, !sx) :: (E ++ (y, !sy) :: F)))) ∧
      (∀ letter ∈ A ++ B ++ D ++ E ++ F, letter.1 ≠ x ∧ letter.1 ≠ y) := by
  obtain ⟨x, y, sx, sy, A, B, D, E, F, hxy, hsplit⟩ :=
    C.exists_alternating_blocks initial
  exact ⟨x, y, sx, sy, A, B, D, E, F, hxy, hsplit,
    C.blocks_avoid_crossing_labels x y sx sy A B D E F hsplit⟩
#print axioms rotation_ne_self
#print axioms partner_ne_cyclicSucc
#print axioms exists_crossing_of_lt
#print axioms exists_distinct_crossing
#print axioms exists_alternating_positions
#print axioms exists_alternating_blocks
#print axioms exists_alternating_blocks_avoiding

end OrientableWicksCertificate

end

end SystolicGrowth
