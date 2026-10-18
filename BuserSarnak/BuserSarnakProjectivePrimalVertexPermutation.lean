module

public import BuserSarnak.BuserSarnakProjectiveVertexOrbitSupport
public import BuserSarnak.BuserSarnakProjectivePrimalTreeRegions

@[expose] public section

/-!
# Local vertex permutations and disjoint primal tree swaps

The permutation of each explicit eight-dart block is the actual polygon
vertex rotation on that block, and the identity elsewhere. Distinct canonical
tree edges have disjoint paired dart carriers, hence their swaps commute.
-/

namespace SystolicGrowth

noncomputable section

open scoped Classical

noncomputable local instance buserSarnakProjectivePrimalPermutationEdgeFintype
    (p : ℕ) [NeZero p] : Fintype (CanonicalBuserSarnakProjectiveDegenerateSymbol p) :=
  Fintype.ofFinite _

/-- The permutation of an explicit vertex orbit follows the actual rotation. -/
theorem projectiveVertexDartOrbitList_formPerm_apply_of_mem
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (a d : CanonicalProjectivePolygonDart p)
    (hd : d ∈ projectiveVertexDartOrbitList S a) :
    List.formPerm (projectiveVertexDartOrbitList S a) d =
      S.polygonVertexRotateDart d := by
  classical
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp hd
  have hform := List.formPerm_apply_getElem (projectiveVertexDartOrbitList S a)
    (projectiveVertexDartOrbitList_nodup S a) i.val
    (by simpa only [projectiveVertexDartOrbitList_length] using i.isLt)
  simp only [projectiveVertexDartOrbitList, List.length_ofFn, List.getElem_ofFn] at hform
  dsimp only [projectiveVertexDartOrbitList]
  rw [hform]
  by_cases hlt : i.val + 1 < 8
  · rw [Nat.mod_eq_of_lt hlt, Function.iterate_succ_apply']
  · have hlast : i.val = 7 := by omega
    rw [hlast]
    have hperiod := S.polygonVertexRotateDart_iterate_eight a.1 a.2
    simpa only [Nat.reduceAdd, Nat.mod_self, Function.iterate_zero, id_eq,
      Function.iterate_succ_apply'] using hperiod.symm

/-- On its actual primal support a local block acts by vertex rotation. -/
theorem projectivePrimalVertexDartOrbitList_formPerm_apply_of_start_eq
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p)
    (d : CanonicalProjectivePolygonDart p)
    (hstart : S.polygonSideStart d.1 d.2 = q) :
    List.formPerm (projectivePrimalVertexDartOrbitList S q) d =
      S.polygonVertexRotateDart d := by
  exact projectiveVertexDartOrbitList_formPerm_apply_of_mem S (q, .a) d
    ((mem_projectivePrimalVertexDartOrbitList_iff S q d).mpr hstart)

/-- Away from its primal support a local block fixes every dart. -/
theorem projectivePrimalVertexDartOrbitList_formPerm_apply_of_start_ne
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p)
    (d : CanonicalProjectivePolygonDart p)
    (hstart : S.polygonSideStart d.1 d.2 ≠ q) :
    List.formPerm (projectivePrimalVertexDartOrbitList S q) d = d := by
  classical
  apply List.formPerm_apply_of_notMem
  simpa only [mem_projectivePrimalVertexDartOrbitList_iff] using hstart

/-- Pointwise semantics of the concrete local primal cycle permutation. -/
theorem projectivePrimalVertexDartOrbitList_formPerm_apply
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p)
    (q : BuserSarnakProjectiveReductionRange p)
    (d : CanonicalProjectivePolygonDart p) :
    List.formPerm (projectivePrimalVertexDartOrbitList S q) d =
      if S.polygonSideStart d.1 d.2 = q then S.polygonVertexRotateDart d else d := by
  classical
  split_ifs with hstart
  · exact projectivePrimalVertexDartOrbitList_formPerm_apply_of_start_eq S q d hstart
  · exact projectivePrimalVertexDartOrbitList_formPerm_apply_of_start_ne S q d hstart

/-- Source carriers distinguish the actual deleted Schreier symbols. -/
theorem canonicalProjectivePolygonTreeSourceDart_injective
    {p : ℕ} [NeZero p] :
    Function.Injective (@canonicalProjectivePolygonTreeSourceDart p _) := by
  intro z w h
  apply Subtype.ext
  have hraw := congrArg
    (fun d : CanonicalProjectivePolygonDart p =>
      (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol d.1 d.2) h
  simpa only [canonicalProjectivePolygonTreeSourceDart_rawSymbol] using hraw

/-- A source carrier can never be a target carrier, even of another edge:
pairing such an equality would reverse both strict height inequalities. -/
theorem canonicalProjectivePolygonTreeSourceDart_ne_targetDart
    {p : ℕ} [NeZero p]
    (z w : CanonicalBuserSarnakProjectiveDegenerateSymbol p) :
    canonicalProjectivePolygonTreeSourceDart z ≠
      canonicalProjectivePolygonTreeTargetDart w := by
  intro h
  have hp := congrArg
    (fun d : CanonicalProjectivePolygonDart p =>
      (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner d.1 d.2) h
  have hreverse : canonicalProjectivePolygonTreeTargetDart z =
      canonicalProjectivePolygonTreeSourceDart w := by
    rw [← canonicalProjectivePolygonTreeTargetDart_eq_partner,
      polygonSidePartner_canonicalProjectivePolygonTreeTargetDart] at hp
    exact hp
  have hz := canonicalProjectiveWordHeight_sourceCarrier_lt_targetCarrier z
  have hw := canonicalProjectiveWordHeight_sourceCarrier_lt_targetCarrier w
  rw [h, hreverse] at hz
  omega

/-- Every actual paired tree carrier belongs to exactly one tree edge. -/
theorem isCanonicalProjectivePolygonTreeCarrier_unique
    {p : ℕ} [NeZero p]
    {z w : CanonicalBuserSarnakProjectiveDegenerateSymbol p}
    {d : CanonicalProjectivePolygonDart p}
    (hz : IsCanonicalProjectivePolygonTreeCarrier z d)
    (hw : IsCanonicalProjectivePolygonTreeCarrier w d) : z = w := by
  rcases hz with hz | hz <;> rcases hw with hw | hw
  · exact canonicalProjectivePolygonTreeSourceDart_injective (hz.symm.trans hw)
  · exact False.elim (canonicalProjectivePolygonTreeSourceDart_ne_targetDart z w
      (hz.symm.trans hw))
  · exact False.elim (canonicalProjectivePolygonTreeSourceDart_ne_targetDart w z
      (hw.symm.trans hz))
  · exact canonicalProjectivePolygonTreeTargetDart_injective (hz.symm.trans hw)

/-- The physical paired-dart swap for an oriented canonical primal edge. -/
noncomputable def canonicalProjectivePrimalTreeCarrierSwap
    {p : ℕ} [NeZero p]
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p) :
    Equiv.Perm (CanonicalProjectivePolygonDart p) :=
  Equiv.swap (canonicalProjectivePolygonTreeSourceDart z)
    (canonicalProjectivePolygonTreeTargetDart z)

/-- Distinct canonical primal edges act on disjoint dart carriers. -/
theorem canonicalProjectivePrimalTreeCarrierSwap_disjoint
    {p : ℕ} [NeZero p]
    {z w : CanonicalBuserSarnakProjectiveDegenerateSymbol p}
    (hne : z ≠ w) :
    Equiv.Perm.Disjoint (canonicalProjectivePrimalTreeCarrierSwap z)
      (canonicalProjectivePrimalTreeCarrierSwap w) := by
  classical
  intro d
  by_cases hz : IsCanonicalProjectivePolygonTreeCarrier z d
  · right
    have hw : ¬ IsCanonicalProjectivePolygonTreeCarrier w d := by
      intro hw
      exact hne (isCanonicalProjectivePolygonTreeCarrier_unique hz hw)
    dsimp only [canonicalProjectivePrimalTreeCarrierSwap]
    apply Equiv.swap_apply_of_ne_of_ne
    · intro hd
      exact hw (Or.inl hd)
    · intro hd
      exact hw (Or.inr hd)
  · left
    dsimp only [canonicalProjectivePrimalTreeCarrierSwap]
    apply Equiv.swap_apply_of_ne_of_ne
    · intro hd
      exact hz (Or.inl hd)
    · intro hd
      exact hz (Or.inr hd)

theorem canonicalProjectivePrimalTreeCarrierSwap_commute
    {p : ℕ} [NeZero p]
    (z w : CanonicalBuserSarnakProjectiveDegenerateSymbol p) :
    Commute (canonicalProjectivePrimalTreeCarrierSwap z)
      (canonicalProjectivePrimalTreeCarrierSwap w) := by
  by_cases h : z = w
  · rw [h]
  · exact (canonicalProjectivePrimalTreeCarrierSwap_disjoint h).commute

/-- The set of paired carriers of an edge is stable under the actual polygon
side pairing. -/
theorem isCanonicalProjectivePolygonTreeCarrier_partner
    {p : ℕ} [NeZero p]
    {z : CanonicalBuserSarnakProjectiveDegenerateSymbol p}
    {d : CanonicalProjectivePolygonDart p}
    (hd : IsCanonicalProjectivePolygonTreeCarrier z d) :
    IsCanonicalProjectivePolygonTreeCarrier z
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner d.1 d.2) := by
  rcases hd with rfl | rfl
  · right
    exact (canonicalProjectivePolygonTreeTargetDart_eq_partner z).symm
  · left
    exact polygonSidePartner_canonicalProjectivePolygonTreeTargetDart z

theorem isCanonicalProjectivePolygonTreeCarrier_partner_iff
    {p : ℕ} [NeZero p]
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p)
    (d : CanonicalProjectivePolygonDart p) :
    IsCanonicalProjectivePolygonTreeCarrier z
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner d.1 d.2) ↔
      IsCanonicalProjectivePolygonTreeCarrier z d := by
  constructor
  · intro h
    have hp := isCanonicalProjectivePolygonTreeCarrier_partner h
    simpa only [BuserSarnakProjectiveQuotientSectionData.polygonSidePartner_involutive] using hp
  · exact isCanonicalProjectivePolygonTreeCarrier_partner

theorem canonicalProjectivePrimalTreeCarrierSwap_apply_of_carrier
    {p : ℕ} [NeZero p]
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p)
    (d : CanonicalProjectivePolygonDart p)
    (hd : IsCanonicalProjectivePolygonTreeCarrier z d) :
    canonicalProjectivePrimalTreeCarrierSwap z d =
      (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner d.1 d.2 := by
  classical
  unfold canonicalProjectivePrimalTreeCarrierSwap
  rcases hd with rfl | rfl
  · rw [Equiv.swap_apply_left]
    exact canonicalProjectivePolygonTreeTargetDart_eq_partner z
  · rw [Equiv.swap_apply_right]
    exact (polygonSidePartner_canonicalProjectivePolygonTreeTargetDart z).symm

theorem canonicalProjectivePrimalTreeCarrierSwap_apply_of_not_carrier
    {p : ℕ} [NeZero p]
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p)
    (d : CanonicalProjectivePolygonDart p)
    (hd : ¬ IsCanonicalProjectivePolygonTreeCarrier z d) :
    canonicalProjectivePrimalTreeCarrierSwap z d = d := by
  classical
  unfold canonicalProjectivePrimalTreeCarrierSwap
  apply Equiv.swap_apply_of_ne_of_ne
  · exact fun h => hd (Or.inl h)
  · exact fun h => hd (Or.inr h)

/-- An arbitrary nodup list of actual tree swaps pairs exactly its listed
carriers, regardless of the ordering of those edges. -/
theorem canonicalProjectivePrimalTreeCarrierSwap_list_prod_apply
    {p : ℕ} [NeZero p]
    (l : List (CanonicalBuserSarnakProjectiveDegenerateSymbol p)) (hl : l.Nodup)
    (d : CanonicalProjectivePolygonDart p) :
    (l.map canonicalProjectivePrimalTreeCarrierSwap).prod d =
      if ∃ z ∈ l, IsCanonicalProjectivePolygonTreeCarrier z d then
        (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner d.1 d.2
      else d := by
  classical
  induction l with
  | nil => simp
  | cons z l ih =>
      rw [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply, ih hl.of_cons]
      by_cases hz : IsCanonicalProjectivePolygonTreeCarrier z d
      · have htail : ¬ ∃ w ∈ l, IsCanonicalProjectivePolygonTreeCarrier w d := by
          rintro ⟨w, hw, hwd⟩
          have hwz := isCanonicalProjectivePolygonTreeCarrier_unique hwd hz
          exact hl.notMem (hwz ▸ hw)
        rw [if_neg htail, canonicalProjectivePrimalTreeCarrierSwap_apply_of_carrier z d hz]
        rw [if_pos ⟨z, List.mem_cons_self, hz⟩]
      · by_cases htail : ∃ w ∈ l, IsCanonicalProjectivePolygonTreeCarrier w d
        · rw [if_pos htail]
          have hpartner : ¬ IsCanonicalProjectivePolygonTreeCarrier z
              ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner
                d.1 d.2) := by
            simpa only [isCanonicalProjectivePolygonTreeCarrier_partner_iff] using hz
          rw [canonicalProjectivePrimalTreeCarrierSwap_apply_of_not_carrier z _ hpartner]
          rw [if_pos (by
            obtain ⟨w, hw, hwd⟩ := htail
            exact ⟨w, List.mem_cons_of_mem z hw, hwd⟩)]
        · rw [if_neg htail, canonicalProjectivePrimalTreeCarrierSwap_apply_of_not_carrier z d hz]
          rw [if_neg (by
            rintro ⟨w, hw, hwd⟩
            rcases List.mem_cons.mp hw with rfl | hw
            · exact hz hwd
            · exact htail ⟨w, hw, hwd⟩)]

/-- The product of all actual canonical primal tree swaps. Disjointness makes
its semantics independent of the finite enumeration. -/
noncomputable def canonicalProjectivePrimalTreeSwapPerm
    (p : ℕ) [NeZero p] : Equiv.Perm (CanonicalProjectivePolygonDart p) :=
  ((Finset.univ : Finset (CanonicalBuserSarnakProjectiveDegenerateSymbol p)).toList.map
    canonicalProjectivePrimalTreeCarrierSwap).prod

theorem canonicalProjectivePrimalTreeSwapPerm_apply
    {p : ℕ} [NeZero p] (d : CanonicalProjectivePolygonDart p) :
    canonicalProjectivePrimalTreeSwapPerm p d =
      if ∃ z : CanonicalBuserSarnakProjectiveDegenerateSymbol p,
          IsCanonicalProjectivePolygonTreeCarrier z d then
        (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner d.1 d.2
      else d := by
  unfold canonicalProjectivePrimalTreeSwapPerm
  rw [canonicalProjectivePrimalTreeCarrierSwap_list_prod_apply _ (Finset.nodup_toList _)]
  simp

/-- The actual bijective polygon rotation as a permutation of all darts. -/
noncomputable def projectivePolygonVertexRotationPerm
    {p : ℕ} [NeZero p] (S : BuserSarnakProjectiveQuotientSectionData p) :
    Equiv.Perm (CanonicalProjectivePolygonDart p) :=
  Equiv.ofBijective S.polygonVertexRotateDart S.polygonVertexRotateDart_bijective

@[simp] theorem projectivePolygonVertexRotationPerm_apply
    {p : ℕ} [NeZero p] (S : BuserSarnakProjectiveQuotientSectionData p)
    (d : CanonicalProjectivePolygonDart p) :
    projectivePolygonVertexRotationPerm S d = S.polygonVertexRotateDart d := rfl

/-- The concrete full-dart map after all primal tree successor swaps. Its
comparison with the recursively traced root cycle is a separate obligation. -/
noncomputable def canonicalProjectivePrimalTreeModifiedVertexPerm
    (p : ℕ) [NeZero p] : Equiv.Perm (CanonicalProjectivePolygonDart p) :=
  projectivePolygonVertexRotationPerm (canonicalBuserSarnakProjectiveQuotientSectionData p) *
    canonicalProjectivePrimalTreeSwapPerm p

theorem canonicalProjectivePrimalTreeModifiedVertexPerm_apply
    {p : ℕ} [NeZero p] (d : CanonicalProjectivePolygonDart p) :
    canonicalProjectivePrimalTreeModifiedVertexPerm p d =
      if ∃ z : CanonicalBuserSarnakProjectiveDegenerateSymbol p,
          IsCanonicalProjectivePolygonTreeCarrier z d then
        (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonVertexRotateDart
          ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner d.1 d.2)
      else
        (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonVertexRotateDart d := by
  unfold canonicalProjectivePrimalTreeModifiedVertexPerm
  rw [Equiv.Perm.mul_apply, canonicalProjectivePrimalTreeSwapPerm_apply]
  split_ifs <;> rfl

/-- At a tree carrier, the paired-dart swap cancels the side crossing, so
the modified map simply follows the successor side of the same face. -/
theorem canonicalProjectivePrimalTreeModifiedVertexPerm_apply_faceSuccessor
    {p : ℕ} [NeZero p] (d : CanonicalProjectivePolygonDart p) :
    canonicalProjectivePrimalTreeModifiedVertexPerm p d =
      if ∃ z : CanonicalBuserSarnakProjectiveDegenerateSymbol p,
          IsCanonicalProjectivePolygonTreeCarrier z d then
        (d.1, d.2.next)
      else
        (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonVertexRotateDart d := by
  rw [canonicalProjectivePrimalTreeModifiedVertexPerm_apply]
  split_ifs
  · change
      (((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner
          ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner d.1 d.2).1
          ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner d.1 d.2).2).1,
        ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner
          ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner d.1 d.2).1
          ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner d.1 d.2).2).2.next) = _
    rw [BuserSarnakProjectiveQuotientSectionData.polygonSidePartner_involutive]
  · rfl

#print axioms projectiveVertexDartOrbitList_formPerm_apply_of_mem
#print axioms projectivePrimalVertexDartOrbitList_formPerm_apply
#print axioms canonicalProjectivePolygonTreeSourceDart_ne_targetDart
#print axioms isCanonicalProjectivePolygonTreeCarrier_unique
#print axioms canonicalProjectivePrimalTreeCarrierSwap_disjoint
#print axioms canonicalProjectivePrimalTreeCarrierSwap_list_prod_apply
#print axioms canonicalProjectivePrimalTreeSwapPerm_apply
#print axioms canonicalProjectivePrimalTreeModifiedVertexPerm_apply_faceSuccessor

end

end SystolicGrowth
