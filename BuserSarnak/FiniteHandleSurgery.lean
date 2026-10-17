module

public import BuserSarnak.FiniteFaceMerge
public import BuserSarnak.FinitePermutationFirstReturn
public import BuserSarnak.FiniteListFirstReturn

@[expose] public section

/-!
# Exact face permutation of a crossing-handle extraction

The four marked occurrences appear in alternating order. Two outgoing
successor swaps rearrange the literal cyclic list; deleting the four marked
occurrences leaves the residual order `B₁ C₂ A C₁ B₂`. This is a positional
identity, independent of free-group cancellation.
-/

namespace SystolicGrowth

noncomputable section

/-- Moving a literal prefix to the end preserves a nodup list's cyclic map. -/
theorem formPerm_append_rotate {X : Type*} [DecidableEq X]
    (left right : List X) (h : (left ++ right).Nodup) :
    (right ++ left).formPerm = (left ++ right).formPerm := by
  simpa only [List.rotate_append_length_eq] using
    List.formPerm_rotate (left ++ right) h left.length

private theorem nodup_append_rotate {X : Type*} (left right : List X)
    (h : (left ++ right).Nodup) : (right ++ left).Nodup :=
  (show (right ++ left).Perm (left ++ right) from List.perm_append_comm).nodup_iff.mpr h

/-- The original literal cyclic order around a crossing pair of chords. -/
def crossingHandleOriginal {X : Type*} (A B₁ B₂ C₁ C₂ : List X)
    (a b c d : X) : List X :=
  A ++ [a] ++ B₁ ++ [b] ++ B₂ ++ [c] ++ C₁ ++ [d] ++ C₂

/-- The full order after swapping outgoing successors at both paired chords. -/
def crossingHandleAugmented {X : Type*} (A B₁ B₂ C₁ C₂ : List X)
    (a b c d : X) : List X :=
  B₁ ++ [b] ++ C₂ ++ A ++ [a] ++ C₁ ++ [d] ++ B₂ ++ [c]

/-- The residual literal order after removing both marked chords. -/
def crossingHandleResidual {X : Type*} (A B₁ B₂ C₁ C₂ : List X) : List X :=
  B₁ ++ C₂ ++ A ++ C₁ ++ B₂

/-- The augmented word rearranges occurrences without introducing or
identifying any dart. -/
theorem crossingHandleAugmented_perm {X : Type*} [DecidableEq X]
    (A B₁ B₂ C₁ C₂ : List X) (a b c d : X) :
    (crossingHandleAugmented A B₁ B₂ C₁ C₂ a b c d).Perm
      (crossingHandleOriginal A B₁ B₂ C₁ C₂ a b c d) := by
  apply List.perm_iff_count.mpr
  intro x
  simp only [crossingHandleOriginal, crossingHandleAugmented, List.count_append]
  omega

/-- Handle surgery preserves occurrence uniqueness, including empty blocks. -/
theorem crossingHandleAugmented_nodup {X : Type*} [DecidableEq X]
    (A B₁ B₂ C₁ C₂ : List X) (a b c d : X)
    (h : (crossingHandleOriginal A B₁ B₂ C₁ C₂ a b c d).Nodup) :
    (crossingHandleAugmented A B₁ B₂ C₁ C₂ a b c d).Nodup :=
  (crossingHandleAugmented_perm A B₁ B₂ C₁ C₂ a b c d).nodup_iff.mpr h

/-- The literal handle rearrangement has exactly the outgoing-successor
map of the two paired-chord swaps. No orbit or residual-certificate premise
is used. -/
theorem crossingHandleAugmented_formPerm {X : Type*} [DecidableEq X]
    (A B₁ B₂ C₁ C₂ : List X) (a b c d : X)
    (h : (crossingHandleOriginal A B₁ B₂ C₁ C₂ a b c d).Nodup) :
    (crossingHandleAugmented A B₁ B₂ C₁ C₂ a b c d).formPerm =
      (crossingHandleOriginal A B₁ B₂ C₁ C₂ a b c d).formPerm *
        Equiv.swap a c * Equiv.swap b d := by
  have hrot₁ : (B₁ ++ [b] ++ B₂ ++ c :: (C₁ ++ [d] ++ C₂ ++ A ++ [a])).Nodup := by
    have hr := nodup_append_rotate (A ++ [a])
      (B₁ ++ [b] ++ B₂ ++ [c] ++ C₁ ++ [d] ++ C₂)
      (by simpa [crossingHandleOriginal, List.append_assoc] using h)
    simpa [List.append_assoc, List.cons_append] using hr
  have heq₁ : (crossingHandleOriginal A B₁ B₂ C₁ C₂ a b c d).formPerm =
      (B₁ ++ [b] ++ B₂ ++ c :: (C₁ ++ [d] ++ C₂ ++ A ++ [a])).formPerm := by
    have hr := formPerm_append_rotate (A ++ [a])
      (B₁ ++ [b] ++ B₂ ++ [c] ++ C₁ ++ [d] ++ C₂)
      (by simpa [crossingHandleOriginal, List.append_assoc] using h)
    simpa [crossingHandleOriginal, List.append_assoc, List.cons_append] using hr.symm
  have haug := crossingHandleAugmented_nodup A B₁ B₂ C₁ C₂ a b c d h
  have hrot₂ : (B₂ ++ [c] ++ B₁ ++ b :: (C₂ ++ A ++ [a] ++ C₁ ++ [d])).Nodup := by
    have hr := nodup_append_rotate
      (B₁ ++ [b] ++ C₂ ++ A ++ [a] ++ C₁ ++ [d]) (B₂ ++ [c])
      (by simpa [crossingHandleAugmented, List.append_assoc] using haug)
    simpa [List.append_assoc, List.cons_append] using hr
  have heq₂ : (crossingHandleAugmented A B₁ B₂ C₁ C₂ a b c d).formPerm =
      (B₂ ++ [c] ++ B₁ ++ b :: (C₂ ++ A ++ [a] ++ C₁ ++ [d])).formPerm := by
    have hr := formPerm_append_rotate
      (B₁ ++ [b] ++ C₂ ++ A ++ [a] ++ C₁ ++ [d]) (B₂ ++ [c])
      (by simpa [crossingHandleAugmented, List.append_assoc] using haug)
    simpa [crossingHandleAugmented, List.append_assoc, List.cons_append] using hr.symm
  have hl : (B₁ ++ [b] ++ B₂ ++ [c]).Nodup := by
    exact hrot₁.sublist (by simp [List.append_assoc])
  have hr : (a :: (C₁ ++ [d] ++ C₂ ++ A)).Nodup := by
    have ht : (C₁ ++ [d] ++ C₂ ++ A ++ [a]).Nodup :=
      hrot₁.of_append_right.of_cons
    have htrot := nodup_append_rotate (C₁ ++ [d] ++ C₂ ++ A) [a] ht
    simpa using htrot
  have hleft : (B₂ ++ [c] ++ B₁ ++ [b]).formPerm =
      (B₁ ++ [b] ++ B₂ ++ [c]).formPerm := by
    simpa [List.append_assoc] using formPerm_append_rotate (B₁ ++ [b]) (B₂ ++ [c])
      (by simpa [List.append_assoc] using hl)
  have hright : (d :: (C₂ ++ A ++ [a] ++ C₁)).formPerm =
      (a :: (C₁ ++ [d] ++ C₂ ++ A)).formPerm := by
    simpa [List.append_assoc, List.cons_append] using
      formPerm_append_rotate (a :: C₁) (d :: (C₂ ++ A))
        (by simpa [List.append_assoc, List.cons_append] using hr)
  rw [heq₁, heq₂, formPerm_face_merge_split _ _ c a hrot₁,
    formPerm_face_merge_split _ _ b d hrot₂, hleft, hright,
    Equiv.swap_comm c a]
  simp only [mul_assoc, Equiv.swap_mul_self, one_mul]

/-- The survivor set removes exactly the four occurrences of the chosen handle. -/
def crossingHandleRetained {X : Type*} (a b c d z : X) : Prop :=
  z ≠ a ∧ z ≠ b ∧ z ≠ c ∧ z ≠ d

instance crossingHandleRetained_decidable {X : Type*} [DecidableEq X]
    (a b c d : X) : DecidablePred (crossingHandleRetained a b c d) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- An actual partner permutation exchanging the marked chords preserves
every other dart. This is derived from injectivity, not a residual input. -/
theorem crossingHandle_partner_retained {X : Type*}
    (partner : Equiv.Perm X) (a b c d : X)
    (ha : partner a = c) (hb : partner b = d)
    (hc : partner c = a) (hd : partner d = b)
    (x : {z : X // crossingHandleRetained a b c d z}) :
    crossingHandleRetained a b c d (partner x.1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    exact x.2.2.2.1 (partner.injective (h.trans hc.symm))
  · intro h
    exact x.2.2.2.2 (partner.injective (h.trans hd.symm))
  · intro h
    exact x.2.1 (partner.injective (h.trans ha.symm))
  · intro h
    exact x.2.2.1 (partner.injective (h.trans hb.symm))

/-- The first-return vertex dynamics of deleting a crossing handle are
exactly those of the old vertex permutation. Both existence proofs come
from finite permutation periodicity. -/
theorem crossingHandle_vertex_firstReturn {X : Type*} [Finite X] [DecidableEq X]
    (face partner : Equiv.Perm X) (a b c d : X) (hmarks : [a, b, c, d].Nodup)
    (ha : partner a = c) (hb : partner b = d)
    (hc : partner c = a) (hd : partner d = b)
    (x : {z : X // crossingHandleRetained a b c d z}) :
    (finitePermutationFirstReturn
      (face * Equiv.swap a c * Equiv.swap b d)
      (crossingHandleRetained a b c d)
      ⟨partner x.1, crossingHandle_partner_retained partner a b c d ha hb hc hd x⟩).1 =
    (finitePermutationFirstReturn (face * partner)
      (crossingHandleRetained a b c d) x).1 := by
  have hab : a ≠ b := by simpa using (hmarks.sublist (by simp) : [a, b].Nodup)
  have had : a ≠ d := by simpa using (hmarks.sublist (by simp) : [a, d].Nodup)
  have hcb : c ≠ b := by simpa [ne_comm] using
    (hmarks.sublist (by simp) : [b, c].Nodup)
  have hcd : c ≠ d := by simpa using (hmarks.sublist (by simp) : [c, d].Nodup)
  apply finiteOrbitFirstReturn_val_eq_of_deleted_transitions
  · have hx := crossingHandle_partner_retained partner a b c d ha hb hc hd x
    simp only [Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_of_ne_of_ne hx.2.1 hx.2.2.2,
      Equiv.swap_apply_of_ne_of_ne hx.1 hx.2.2.1]
  · intro z hz
    have hz' : z = a ∨ z = b ∨ z = c ∨ z = d := by
      unfold crossingHandleRetained at hz
      by_cases hza : z = a
      · exact Or.inl hza
      by_cases hzb : z = b
      · exact Or.inr (Or.inl hzb)
      by_cases hzc : z = c
      · exact Or.inr (Or.inr (Or.inl hzc))
      by_cases hzd : z = d
      · exact Or.inr (Or.inr (Or.inr hzd))
      exact (hz ⟨hza, hzb, hzc, hzd⟩).elim
    rcases hz' with rfl | rfl | rfl | rfl
    · simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hab had, ha]
    · simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne had.symm hcd.symm, hb]
    · simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hcb hcd, hc]
    · simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hab.symm hcb.symm, hd]

/-- The residual order is the exact retained filter of the augmented list. -/
theorem crossingHandleAugmented_filter {X : Type*} [DecidableEq X]
    (A B₁ B₂ C₁ C₂ : List X) (a b c d : X)
    (hblocks : ∀ z ∈ A ++ B₁ ++ B₂ ++ C₁ ++ C₂,
      crossingHandleRetained a b c d z) :
    (crossingHandleAugmented A B₁ B₂ C₁ C₂ a b c d).filter
      (fun z => decide (crossingHandleRetained a b c d z)) =
      crossingHandleResidual A B₁ B₂ C₁ C₂ := by
  have hparts : (∀ z ∈ A, crossingHandleRetained a b c d z) ∧
      (∀ z ∈ B₁, crossingHandleRetained a b c d z) ∧
      (∀ z ∈ B₂, crossingHandleRetained a b c d z) ∧
      (∀ z ∈ C₁, crossingHandleRetained a b c d z) ∧
      (∀ z ∈ C₂, crossingHandleRetained a b c d z) := by
    simpa only [List.mem_append, or_imp, forall_and, and_assoc] using hblocks
  have hfilter (l : List X) (hl : ∀ z ∈ l, crossingHandleRetained a b c d z) :
      l.filter (fun z => decide (crossingHandleRetained a b c d z)) = l :=
    List.filter_eq_self.mpr fun z hz => decide_eq_true (hl z hz)
  simp only [crossingHandleAugmented, crossingHandleResidual, List.filter_append]
  rw [hfilter A hparts.1, hfilter B₁ hparts.2.1, hfilter B₂ hparts.2.2.1,
    hfilter C₁ hparts.2.2.2.1, hfilter C₂ hparts.2.2.2.2]
  simp [crossingHandleRetained]

/-- The actual residual cyclic map, applied after partnering a retained dart,
is the old vertex map's positive first return. This is an exact positional
surgery law, not an orbit premise about a newly chosen permutation. -/
theorem crossingHandleResidual_vertex_firstReturn {X : Type*} [Finite X] [DecidableEq X]
    (A B₁ B₂ C₁ C₂ : List X) (a b c d : X)
    (h : (crossingHandleOriginal A B₁ B₂ C₁ C₂ a b c d).Nodup)
    (hblocks : ∀ z ∈ A ++ B₁ ++ B₂ ++ C₁ ++ C₂,
      crossingHandleRetained a b c d z)
    (partner : Equiv.Perm X)
    (ha : partner a = c) (hb : partner b = d)
    (hc : partner c = a) (hd : partner d = b)
    (x : {z : X // crossingHandleRetained a b c d z}) :
    (crossingHandleResidual A B₁ B₂ C₁ C₂).formPerm (partner x.1) =
    (finitePermutationFirstReturn
      ((crossingHandleOriginal A B₁ B₂ C₁ C₂ a b c d).formPerm * partner)
      (crossingHandleRetained a b c d) x).1 := by
  have hmarks : [a, b, c, d].Nodup := by
    refine h.sublist ?_
    simp only [crossingHandleOriginal, List.append_assoc, List.singleton_append]
    apply List.sublist_append_of_sublist_right
    apply List.Sublist.cons_cons
    apply List.sublist_append_of_sublist_right
    apply List.Sublist.cons_cons
    apply List.sublist_append_of_sublist_right
    apply List.Sublist.cons_cons
    apply List.sublist_append_of_sublist_right
    simp
  rw [← crossingHandleAugmented_filter A B₁ B₂ C₁ C₂ a b c d hblocks]
  rw [list_formPerm_filter_eq_firstReturn _
    (crossingHandleAugmented_nodup A B₁ B₂ C₁ C₂ a b c d h)
    (crossingHandleRetained a b c d)
    ⟨partner x.1, crossingHandle_partner_retained partner a b c d ha hb hc hd x⟩]
  rw [crossingHandleAugmented_formPerm A B₁ B₂ C₁ C₂ a b c d h]
  exact crossingHandle_vertex_firstReturn _ partner a b c d hmarks ha hb hc hd x

end

end SystolicGrowth

#print axioms SystolicGrowth.crossingHandleAugmented_formPerm
#print axioms SystolicGrowth.crossingHandle_vertex_firstReturn
#print axioms SystolicGrowth.crossingHandleResidual_vertex_firstReturn
