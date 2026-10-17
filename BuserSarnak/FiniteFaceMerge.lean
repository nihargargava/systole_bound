module

public import BuserSarnak.FiniteCycleSplice

@[expose] public section

/-!
# Exact dynamics of a dual-face merge

The outgoing-successor convention is `face * swap a b`.  This differs from
the intermediate-pivot convention `left * swap a b * right` used by the
cyclic-block splice lemmas.  The lemmas below keep this distinction explicit
and compare induced vertex dynamics through first return, not through words
in a free group.
-/

namespace SystolicGrowth

noncomputable section

/-- A dart is deleted from a permutation by bypassing its incoming edge and
fixing the deleted dart.  This is a positional operation, not word reduction. -/
def faceDeleteDart {X : Type*} [DecidableEq X]
    (face : Equiv.Perm X) (a : X) : Equiv.Perm X :=
  Equiv.swap a (face a) * face

@[simp] theorem faceDeleteDart_apply_self
    {X : Type*} [DecidableEq X] (face : Equiv.Perm X) (a : X) :
    faceDeleteDart face a a = a := by
  simp [faceDeleteDart, Equiv.Perm.mul_apply]

theorem faceDeleteDart_apply_of_ne
    {X : Type*} [DecidableEq X] (face : Equiv.Perm X) (a x : X) (hx : x ≠ a) :
    faceDeleteDart face a x = if face x = a then face a else face x := by
  by_cases hxa : face x = a
  · simp [faceDeleteDart, Equiv.Perm.mul_apply, hxa]
  · have hxf : face x ≠ face a := fun h => hx (face.injective h)
    simp [faceDeleteDart, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne hxa hxf, hxa]

/-- The permutation bypass operation exactly realizes deletion of the head
of a nodup cyclic list, including the singleton case. -/
theorem faceDeleteDart_formPerm_cons
    {X : Type*} [DecidableEq X] (a : X) (tail : List X)
    (h : (a :: tail).Nodup) :
    faceDeleteDart (a :: tail).formPerm a = tail.formPerm := by
  cases tail with
  | nil => simp [faceDeleteDart]; rfl
  | cons b tail =>
    rw [faceDeleteDart, List.formPerm_apply_head a b tail h,
      List.formPerm_cons_cons, ← mul_assoc, Equiv.swap_mul_self, one_mul]

/-- Deleting any marked occurrence from a nodup cyclic list is exactly the
same permutation operation, irrespective of its chosen linearization. -/
theorem faceDeleteDart_formPerm_split
    {X : Type*} [DecidableEq X] (pre post : List X) (a : X)
    (h : (pre ++ a :: post).Nodup) :
    faceDeleteDart (pre ++ a :: post).formPerm a = (pre ++ post).formPerm := by
  have hrot : (a :: (post ++ pre)).Nodup := by
    have : ((pre ++ a :: post).rotate pre.length).Nodup :=
      (List.nodup_rotate).2 h
    simpa [List.rotate_append_length_eq, List.cons_append] using this
  have hperm : (pre ++ a :: post).formPerm = (a :: (post ++ pre)).formPerm := by
    simpa [List.rotate_append_length_eq, List.cons_append] using
      (List.formPerm_rotate (pre ++ a :: post) h pre.length).symm
  have htail : (pre ++ post).Nodup := by
    exact h.sublist (by simp)
  rw [hperm, faceDeleteDart_formPerm_cons a (post ++ pre) hrot]
  simpa [List.rotate_append_length_eq] using
    List.formPerm_rotate (pre ++ post) htail pre.length

/-- A stated positive hit with no earlier retained point determines the
first-return endpoint independently of the chosen existence proof. -/
theorem finiteOrbitFirstReturn_val_eq_of_first_hit
    {X : Type*} (f : X → X) (P : X → Prop) [DecidablePred P]
    (hreturn : ∀ x : {x : X // P x}, ∃ n : ℕ, 0 < n ∧ P (f^[n] x.1))
    (x : {x : X // P x}) (n : ℕ) (hn : 0 < n) (hhit : P (f^[n] x.1))
    (hbefore : ∀ k, 0 < k → k < n → ¬ P (f^[k] x.1)) :
    (finiteOrbitFirstReturn f P hreturn x).1 = f^[n] x.1 := by
  have hle : finiteOrbitFirstReturnTime f P hreturn x ≤ n :=
    Nat.find_min' (hreturn x) ⟨hn, hhit⟩
  have hge : n ≤ finiteOrbitFirstReturnTime f P hreturn x := by
    by_contra h
    exact hbefore _ (finiteOrbitFirstReturnTime_pos f P hreturn x)
      (Nat.lt_of_not_ge h) (finiteOrbitFirstReturnTime_hit f P hreturn x)
  rw [finiteOrbitFirstReturn_val, le_antisymm hle hge]

/-- Bypassing two distinct deleted darts skips at most two intermediate
states.  This proves existence and minimality of the return directly, even
without finiteness or a global orbit hypothesis. -/
theorem faceDeleteTwoDarts_first_hit
    {X : Type*} [DecidableEq X] (face : Equiv.Perm X) (a b x : X)
    (hab : a ≠ b) (hxa : x ≠ a) (hxb : x ≠ b) :
    ∃ n : ℕ, 0 < n ∧ n ≤ 3 ∧
      face^[n] x = faceDeleteDart (faceDeleteDart face a) b x ∧
      (face^[n] x ≠ a ∧ face^[n] x ≠ b) ∧
      ∀ k, 0 < k → k < n → ¬ (face^[k] x ≠ a ∧ face^[k] x ≠ b) := by
  by_cases hfa : face x = a
  · have haa : face a ≠ a := fun h => hxa (face.injective (hfa.trans h.symm))
    by_cases hab' : face a = b
    · have hba : face b ≠ a := fun h => hxb (face.injective (hfa.trans h.symm))
      have hbb : face b ≠ b := fun h => hab (face.injective (hab'.trans h.symm))
      refine ⟨3, by omega, le_rfl, ?_, ?_, ?_⟩
      · simp [Function.iterate_succ_apply', hfa, hab', faceDeleteDart_apply_of_ne,
          hxa, hxb, hab.symm, hba]
      · simpa [Function.iterate_succ_apply', hfa, hab'] using And.intro hba hbb
      · intro k hk hkn
        have hk' : k = 1 ∨ k = 2 := by omega
        rcases hk' with rfl | rfl <;> simp [Function.iterate_succ_apply', hfa, hab']
    · refine ⟨2, by omega, by omega, ?_, ?_, ?_⟩
      · simp [Function.iterate_succ_apply', hfa, faceDeleteDart_apply_of_ne,
          hxa, hxb, hab']
      · simpa [Function.iterate_succ_apply', hfa] using And.intro haa hab'
      · intro k hk hkn
        have : k = 1 := by omega
        subst k
        simp [hfa]
  · by_cases hfb : face x = b
    · have hbb : face b ≠ b := fun h => hxb (face.injective (hfb.trans h.symm))
      by_cases hba' : face b = a
      · have haa : face a ≠ a := fun h => hab.symm (face.injective (hba'.trans h.symm))
        have hab' : face a ≠ b := fun h => hxa (face.injective (hfb.trans h.symm))
        refine ⟨3, by omega, le_rfl, ?_, ?_, ?_⟩
        · simp [Function.iterate_succ_apply', hfb, hba', faceDeleteDart_apply_of_ne,
            hxa, hxb, hab.symm]
        · simpa [Function.iterate_succ_apply', hfb, hba'] using And.intro haa hab'
        · intro k hk hkn
          have hk' : k = 1 ∨ k = 2 := by omega
          rcases hk' with rfl | rfl <;> simp [Function.iterate_succ_apply', hfb, hba']
      · refine ⟨2, by omega, by omega, ?_, ?_, ?_⟩
        · simp [Function.iterate_succ_apply', hfb, faceDeleteDart_apply_of_ne,
            hxa, hxb, hab.symm, hba']
        · simpa [Function.iterate_succ_apply', hfb] using And.intro hba' hbb
        · intro k hk hkn
          have : k = 1 := by omega
          subst k
          simp [hfb]
    · refine ⟨1, by omega, by omega, ?_, ?_, ?_⟩
      · simp [faceDeleteDart_apply_of_ne, hxa, hxb, hfa, hfb]
      · simpa using And.intro hfa hfb
      · intro k hk hkn
        omega

/-- The exact survivor action of deleting a pair of darts is first return of
the original face permutation.  Its existence premise can always be supplied
by `faceDeleteTwoDarts_first_hit`. -/
theorem faceDeleteTwoDarts_eq_firstReturn
    {X : Type*} [DecidableEq X] (face : Equiv.Perm X) (a b : X) (hab : a ≠ b)
    (hreturn : ∀ x : {x : X // x ≠ a ∧ x ≠ b}, ∃ n : ℕ, 0 < n ∧
      (face^[n] x.1 ≠ a ∧ face^[n] x.1 ≠ b))
    (x : {x : X // x ≠ a ∧ x ≠ b}) :
    faceDeleteDart (faceDeleteDart face a) b x.1 =
      (finiteOrbitFirstReturn face (fun z => z ≠ a ∧ z ≠ b) hreturn x).1 := by
  obtain ⟨n, hn, _, hiter, hhit, hbefore⟩ :=
    faceDeleteTwoDarts_first_hit face a b x.1 hab x.2.1 x.2.2
  rw [finiteOrbitFirstReturn_val_eq_of_first_hit face
    (fun z => z ≠ a ∧ z ≠ b) hreturn x n hn hhit hbefore]
  exact hiter.symm

/-- Two dynamics with the same first positive step and the same transitions
outside the retained set have identical positive first-return times. -/
theorem finiteOrbitFirstReturnTime_eq_of_deleted_transitions
    {X : Type*} (f g : X → X) (P : X → Prop) [DecidablePred P]
    (hf : ∀ x : {x : X // P x}, ∃ n : ℕ, 0 < n ∧ P (f^[n] x.1))
    (hg : ∀ x : {x : X // P x}, ∃ n : ℕ, 0 < n ∧ P (g^[n] x.1))
    (x y : {x : X // P x})
    (hfirst : f x.1 = g y.1)
    (hdeleted : ∀ z, ¬ P z → f z = g z) :
    finiteOrbitFirstReturnTime f P hf x =
      finiteOrbitFirstReturnTime g P hg y := by
  let t := finiteOrbitFirstReturnTime f P hf x
  have htpos : 0 < t := finiteOrbitFirstReturnTime_pos f P hf x
  have hbefore : ∀ n, 0 < n → n < t → ¬ P (f^[n] x.1) := by
    intro n hn hnt hhit
    have hle : t ≤ n := Nat.find_min' (hf x) ⟨hn, hhit⟩
    omega
  have hsteps : ∀ n, 0 < n → n ≤ t → f^[n] x.1 = g^[n] y.1 := by
    intro n
    induction n with
    | zero => intro hn; omega
    | succ n ih =>
        intro hn hnt
        by_cases hn0 : n = 0
        · subst n
          simpa using hfirst
        · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
            ← ih hnpos (by omega)]
          exact hdeleted _ (hbefore n hnpos (by omega))
  have hgt : P (g^[t] y.1) := by
    rw [← hsteps t htpos le_rfl]
    exact finiteOrbitFirstReturnTime_hit f P hf x
  have hgle : finiteOrbitFirstReturnTime g P hg y ≤ t :=
    Nat.find_min' (hg y) ⟨htpos, hgt⟩
  have hft : t ≤ finiteOrbitFirstReturnTime g P hg y := by
    apply Nat.find_min' (hf x)
    refine ⟨finiteOrbitFirstReturnTime_pos g P hg y, ?_⟩
    rw [hsteps _ (finiteOrbitFirstReturnTime_pos g P hg y) hgle]
    exact finiteOrbitFirstReturnTime_hit g P hg y
  exact le_antisymm hft hgle

/-- The corresponding positive first-return endpoints coincide.  The starting
points can differ: only their first positive steps must agree. -/
theorem finiteOrbitFirstReturn_val_eq_of_deleted_transitions
    {X : Type*} (f g : X → X) (P : X → Prop) [DecidablePred P]
    (hf : ∀ x : {x : X // P x}, ∃ n : ℕ, 0 < n ∧ P (f^[n] x.1))
    (hg : ∀ x : {x : X // P x}, ∃ n : ℕ, 0 < n ∧ P (g^[n] x.1))
    (x y : {x : X // P x})
    (hfirst : f x.1 = g y.1)
    (hdeleted : ∀ z, ¬ P z → f z = g z) :
    (finiteOrbitFirstReturn f P hf x).1 =
      (finiteOrbitFirstReturn g P hg y).1 := by
  let t := finiteOrbitFirstReturnTime f P hf x
  have hsteps : ∀ n, 0 < n → n ≤ t → f^[n] x.1 = g^[n] y.1 := by
    intro n
    induction n with
    | zero => intro hn; omega
    | succ n ih =>
        intro hn hnt
        by_cases hn0 : n = 0
        · subst n
          simpa using hfirst
        · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
            ← ih hnpos (by omega)]
          apply hdeleted
          intro hhit
          have hle : t ≤ n := Nat.find_min' (hf x) ⟨hnpos, hhit⟩
          omega
  rw [finiteOrbitFirstReturn_val, finiteOrbitFirstReturn_val,
    ← finiteOrbitFirstReturnTime_eq_of_deleted_transitions f g P hf hg x y
      hfirst hdeleted]
  exact hsteps t (finiteOrbitFirstReturnTime_pos f P hf x) le_rfl

/-- The actual ordered word for a forward-pivot face merge has the outgoing
successor-swap permutation.  The pivots may be the only darts in either face;
no artificial nonempty-tail condition is needed. -/
theorem formPerm_face_merge_split
    {X : Type*} [DecidableEq X] (pre post : List X) (a b : X)
    (h : (pre ++ a :: (post ++ [b])).Nodup) :
    (pre ++ a :: (post ++ [b])).formPerm =
      ((pre ++ [a]).formPerm * (b :: post).formPerm) * Equiv.swap a b := by
  have htail : (a :: (post ++ [b])).Nodup := h.of_append_right
  have hpost : (b :: post).Nodup := by
    have hpost' : (post ++ [b]).Nodup := htail.of_cons
    have : ((post ++ [b]).rotate post.length).Nodup :=
      (List.nodup_rotate).2 hpost'
    simpa [List.rotate_append_length_eq] using this
  have hcut : (a :: (post ++ [b])).formPerm =
      (post ++ [b]).formPerm * Equiv.swap a b := by
    calc
      _ = ((a :: (post ++ [b])).rotate 1).formPerm :=
        (List.formPerm_rotate _ htail 1).symm
      _ = (post ++ [b, a]).formPerm := by simp [List.append_assoc]
      _ = (post ++ [b]).formPerm * Equiv.swap a b := by
        rw [List.formPerm_append_pair, Equiv.swap_comm b a]
  have hright : (post ++ [b]).formPerm = (b :: post).formPerm := by
    simpa using List.formPerm_rotate (b :: post) hpost 1
  rw [formPerm_append_cons_eq pre a (post ++ [b]), hcut, hright, mul_assoc]

/-- Erasing the paired pivots from the literal merged word gives the exact
double-bypass permutation, with the retained cyclic order unchanged. -/
theorem formPerm_face_merge_deleted
    {X : Type*} [DecidableEq X] (pre post : List X) (a b : X)
    (h : (pre ++ a :: (post ++ [b])).Nodup) :
    (pre ++ post).formPerm =
      faceDeleteDart (faceDeleteDart (pre ++ a :: (post ++ [b])).formPerm a) b := by
  have hdeleted : (pre ++ post ++ [b]).Nodup :=
    h.sublist (by simp [List.append_assoc])
  rw [faceDeleteDart_formPerm_split pre (post ++ [b]) a h]
  simpa [List.append_assoc] using
    (faceDeleteDart_formPerm_split (pre ++ post) [] b hdeleted).symm

/-- The literal face word after paired-pivot erasure realizes first return of
the outgoing-spliced face map on every surviving dart. -/
theorem formPerm_face_merge_deleted_eq_firstReturn
    {X : Type*} [DecidableEq X] (pre post : List X) (a b : X) (hab : a ≠ b)
    (h : (pre ++ a :: (post ++ [b])).Nodup)
    (hreturn : ∀ x : {x : X // x ≠ a ∧ x ≠ b}, ∃ n : ℕ, 0 < n ∧
      ((pre ++ a :: (post ++ [b])).formPerm^[n] x.1 ≠ a ∧
        (pre ++ a :: (post ++ [b])).formPerm^[n] x.1 ≠ b))
    (x : {x : X // x ≠ a ∧ x ≠ b}) :
    (pre ++ post).formPerm x.1 =
      (finiteOrbitFirstReturn (pre ++ a :: (post ++ [b])).formPerm
        (fun z => z ≠ a ∧ z ≠ b) hreturn x).1 := by
  rw [formPerm_face_merge_deleted pre post a b h]
  exact faceDeleteTwoDarts_eq_firstReturn _ a b hab hreturn x

/-- Merging the outgoing successors at marked darts of disjoint nodup faces
produces a nodup cyclic list with exactly their combined support.  Notice the
rightmost swap: the separate face map is `left.formPerm * right.formPerm`. -/
theorem formPerm_face_merge_of_mem
    {X : Type*} [DecidableEq X]
    (left right : List X) (a b : X)
    (hl : left.Nodup) (hr : right.Nodup) (hd : left.Disjoint right)
    (ha : a ∈ left) (hb : b ∈ right) :
    ∃ merged : List X,
      merged.Nodup ∧
      (∀ x, x ∈ merged ↔ x ∈ left ∨ x ∈ right) ∧
      merged.formPerm = (left.formPerm * right.formPerm) * Equiv.swap a b := by
  have har : a ∉ right := fun h => (List.disjoint_left.mp hd) ha h
  have hfix : right.formPerm a = a := List.formPerm_apply_of_notMem har
  obtain ⟨merged, hnodup, hmem, hperm⟩ :=
    formPerm_splice_word_of_mem left right a (right.formPerm b) hl hr hd ha
      (List.formPerm_apply_mem_of_mem hb)
  refine ⟨merged, hnodup, hmem, ?_⟩
  rw [mul_assoc, Equiv.mul_swap_eq_swap_mul, hfix, ← mul_assoc]
  exact hperm

/-- Exact local vertex law for deleting a paired edge after merging its two
faces.  The partner permutation need only be identified on the deleted darts
and shown to preserve retained darts.  No transitivity assumption is used. -/
theorem finiteFaceMerge_vertex_firstReturn
    {X : Type*} [DecidableEq X]
    (face partner : Equiv.Perm X) (a b : X)
    (ha : partner a = b) (hb : partner b = a)
    (hpreserve : ∀ x, x ≠ a → x ≠ b → partner x ≠ a ∧ partner x ≠ b)
    (hface : ∀ x : {x : X // x ≠ a ∧ x ≠ b},
      ∃ n : ℕ, 0 < n ∧
        ((face * Equiv.swap a b : Equiv.Perm X)^[n] x.1 ≠ a ∧
          (face * Equiv.swap a b : Equiv.Perm X)^[n] x.1 ≠ b))
    (hvertex : ∀ x : {x : X // x ≠ a ∧ x ≠ b},
      ∃ n : ℕ, 0 < n ∧
        ((face * partner : Equiv.Perm X)^[n] x.1 ≠ a ∧
          (face * partner : Equiv.Perm X)^[n] x.1 ≠ b))
    (x : {x : X // x ≠ a ∧ x ≠ b}) :
    (finiteOrbitFirstReturn (face * Equiv.swap a b)
      (fun z => z ≠ a ∧ z ≠ b) hface
      ⟨partner x.1, hpreserve x.1 x.2.1 x.2.2⟩).1 =
    (finiteOrbitFirstReturn (face * partner)
      (fun z => z ≠ a ∧ z ≠ b) hvertex x).1 := by
  classical
  apply finiteOrbitFirstReturn_val_eq_of_deleted_transitions
  · simp only [Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_of_ne_of_ne
      (hpreserve x.1 x.2.1 x.2.2).1 (hpreserve x.1 x.2.1 x.2.2).2]
  · intro z hz
    have hz' : z = a ∨ z = b := by
      by_cases hza : z = a
      · exact Or.inl hza
      · exact Or.inr (not_ne_iff.mp (fun hzb => hz ⟨hza, hzb⟩))
    rcases hz' with rfl | rfl <;>
      simp [Equiv.Perm.mul_apply, ha, hb]

#print axioms finiteOrbitFirstReturnTime_eq_of_deleted_transitions
#print axioms finiteOrbitFirstReturn_val_eq_of_deleted_transitions
#print axioms faceDeleteDart_formPerm_split
#print axioms faceDeleteTwoDarts_first_hit
#print axioms faceDeleteTwoDarts_eq_firstReturn
#print axioms formPerm_face_merge_split
#print axioms formPerm_face_merge_deleted
#print axioms formPerm_face_merge_deleted_eq_firstReturn
#print axioms formPerm_face_merge_of_mem
#print axioms finiteFaceMerge_vertex_firstReturn

end

end SystolicGrowth
