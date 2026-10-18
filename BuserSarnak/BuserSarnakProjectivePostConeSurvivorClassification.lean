module

public import BuserSarnak.BuserSarnakProjectivePostConeSurvivorEmbedding
public import BuserSarnak.BuserSarnakProjectivePrimalVertexPermutation

@[expose] public section

/-!
# Exact classification of retained physical polygon darts

The final contour keeps precisely the original darts outside the primal
Schreier tree and the selected dual face tree. Cone normalization chooses an
orientation of each remaining physical edge, and deletes no additional dart.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete
open scoped Classical

noncomputable local instance survivorClassificationRangeFintype
    (p : ℕ) [NeZero p] : Fintype (BuserSarnakProjectiveReductionRange p) :=
  Fintype.ofFinite _

/-- The actual image of the final signed endpoint alphabet in original darts. -/
def canonicalProjectivePostConeSurvivorSet
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    Set (CanonicalProjectivePolygonDart p) :=
  Set.range (canonicalProjectivePostConeSurvivingDart_embedding hp hp2)

/-- A physical occurrence removed by the selected dual face tree. -/
def IsCanonicalProjectivePostConeDualTreeCarrier
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d : CanonicalProjectivePolygonDart p) : Prop :=
  ∃ slot : CanonicalProjectivePostConeTreeSlot hp hp2,
    d = projectivePolygonPostConeEdgeSourceDart
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot) ∨
      d = projectivePolygonPostConeEdgeTargetDart
        (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)

/-- The final endpoint alphabet is exactly the subtype of retained original
physical darts, with the actual embedding as forward map. -/
def canonicalProjectivePostConeSurvivorPhysicalEquiv
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    CanonicalProjectivePostConeSurvivingDart hp hp2 ≃
      canonicalProjectivePostConeSurvivorSet hp hp2 :=
  Equiv.ofInjective (canonicalProjectivePostConeSurvivingDart_embedding hp hp2)
    (canonicalProjectivePostConeSurvivingDart_embedding_injective hp hp2)

@[simp] theorem canonicalProjectivePostConeSurvivorPhysicalEquiv_apply_val
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (x : CanonicalProjectivePostConeSurvivingDart hp hp2) :
    (canonicalProjectivePostConeSurvivorPhysicalEquiv hp hp2 x).val =
      canonicalProjectivePostConeSurvivingDart_embedding hp hp2 x := rfl

/-- A degenerate raw symbol contributes the identity at its polygon side. -/
theorem canonicalProjectiveConePostConeBoundaryTerm_eq_one_of_raw_degenerate
    {p : ℕ} [NeZero p] (d : CanonicalProjectivePolygonDart p)
    (hdeg : (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol d.1 d.2)) :
    canonicalProjectiveConePostConeBoundaryTerm p d.1 d.2 = 1 := by
  have hside : canonicalProjectiveConePostConeSideWord p d.1 d.2 = 1 := by
    unfold canonicalProjectiveConePostConeSideWord
    rw [(CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord_of_degenerate
      hdeg, map_one]
  rcases d with ⟨q, s⟩
  cases s <;> simp only [canonicalProjectiveConePostConeBoundaryTerm, hside, inv_one]

/-- Both physical occurrences of every primal edge disappear at the first
stage, including the cone target whose displayed raw symbol differs. -/
theorem canonicalProjectiveConePostConeBoundaryTerm_eq_one_of_primal_carrier
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p)
    (d : CanonicalProjectivePolygonDart p)
    (hd : IsCanonicalProjectivePolygonTreeCarrier z d) :
    canonicalProjectiveConePostConeBoundaryTerm p d.1 d.2 = 1 := by
  have hsource : canonicalProjectiveConePostConeBoundaryTerm p
      (canonicalProjectivePolygonTreeSourceDart z).1
      (canonicalProjectivePolygonTreeSourceDart z).2 = 1 := by
    apply canonicalProjectiveConePostConeBoundaryTerm_eq_one_of_raw_degenerate
    rw [canonicalProjectivePolygonTreeSourceDart_rawSymbol]
    exact z.2
  rcases hd with rfl | rfl
  · exact hsource
  · rw [canonicalProjectivePolygonTreeTargetDart_eq_partner,
      canonicalProjectiveConePostConeBoundaryTerm_partner_eq_inv hp hp2,
      hsource, inv_one]

/-- A physical retained edge occurrence always contributes a nontrivial
single signed letter. -/
theorem canonicalProjectiveConePostConeBoundaryTerm_ne_one_of_physical_carrier
    {p : ℕ} [NeZero p] (d : CanonicalProjectivePolygonDart p)
    (h : CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrier p d.1 d.2) :
    canonicalProjectiveConePostConeBoundaryTerm p d.1 d.2 ≠ 1 := by
  rcases h with ⟨z, hsource | htarget⟩
  · rw [hsource.2.2]
    exact FreeGroup.of_ne_one z
  · rw [htarget.2.2]
    exact inv_ne_one.mpr (FreeGroup.of_ne_one z)

private theorem nonconeBoundaryTerm_ne_one_of_raw_nondegenerate
    {p : ℕ} [NeZero p] (q : BuserSarnakProjectiveReductionRange p)
    (s : ProjectivePolygonSide) (hs : s.generator = .a ∨ s.generator = .c)
    (hraw : ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol q s)) :
    canonicalProjectiveConePostConeBoundaryTerm p q s ≠ 1 := by
  let z := canonicalProjectiveConeKeptPolygonNonconeSide q s hraw hs
  have hside : canonicalProjectiveConePostConeSideWord p q s = FreeGroup.of z := by
    unfold canonicalProjectiveConePostConeSideWord
    rw [(CanonicalProjectiveConeSchreierData p).cleanedSchreierSymbolWord_of_not_degenerate
      hraw]
    exact canonicalProjectiveConeFirstStageSubstitution_of_kept z
  cases s <;> simp [ProjectivePolygonSide.generator] at hs
  all_goals first
    | simpa only [canonicalProjectiveConePostConeBoundaryTerm, hside] using
        FreeGroup.of_ne_one z
    | simpa only [canonicalProjectiveConePostConeBoundaryTerm, hside] using
        inv_ne_one.mpr (FreeGroup.of_ne_one z)

private theorem coneBoundaryTerm_physicalCarrier_of_raw_pair_nondegenerate
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p) (e : ProjectiveOctagonConeGenerator)
    (hraw : ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol
        q e.lift.positivePolygonSide))
    (hpair : ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSideRawSymbol
        ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner
          q e.lift.positivePolygonSide).1
        ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner
          q e.lift.positivePolygonSide).2)) :
    CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrier p q
      e.lift.positivePolygonSide := by
  let S := canonicalBuserSarnakProjectiveQuotientSectionData p
  let side := e.lift.positivePolygonSide
  let r := S.polygonSideStart q side
  have hrawEq : S.polygonSideRawSymbol q side = (r, e.lift) := by
    cases e <;> rfl
  have hpairEq : S.polygonSideRawSymbol (S.polygonSidePartner q side).1
      (S.polygonSidePartner q side).2 =
      (buserSarnakProjectiveConePartner p e r, e.lift) := by
    rw [S.polygonSideRawSymbol_partner]
    cases e <;> rfl
  have hsource : ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      (r, e.lift) := by
    simpa only [← hrawEq] using hraw
  have htarget : ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      (buserSarnakProjectiveConePartner p e r, e.lift) := by
    simpa only [← hpairEq] using hpair
  have hbase : S.polygonSideBase r side = q := S.polygonSideBase_start q side
  have h := canonicalProjectiveConePostConeConeBaseBoundaryTerm_physicalCarrier
    hp hp2 e r hsource htarget
  change CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrier p
    (S.polygonSideBase r side) side at h
  rw [hbase] at h
  exact h

/-- Outside the primal tree, each original dart belongs to an actual retained
physical edge. In particular cone-pivot normalization is not an extra cut. -/
theorem canonicalProjectiveConePostConeBoundaryTerm_physicalCarrier_of_not_primal
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d : CanonicalProjectivePolygonDart p)
    (hnot : ¬ ∃ z : CanonicalBuserSarnakProjectiveDegenerateSymbol p,
      IsCanonicalProjectivePolygonTreeCarrier z d) :
    CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrier p d.1 d.2 := by
  let S := canonicalBuserSarnakProjectiveQuotientSectionData p
  have hraw : ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      (S.polygonSideRawSymbol d.1 d.2) := by
    intro hdeg
    let z : CanonicalBuserSarnakProjectiveDegenerateSymbol p :=
      ⟨S.polygonSideRawSymbol d.1 d.2, hdeg⟩
    exact hnot ⟨z, isCanonicalProjectivePolygonTreeCarrier_of_rawSymbol_eq d.1 d.2 z rfl⟩
  have hpair : ¬ (CanonicalProjectiveConeSchreierData p).IsDegenerateSchreierSymbol
      (S.polygonSideRawSymbol (S.polygonSidePartner d.1 d.2).1
        (S.polygonSidePartner d.1 d.2).2) := by
    intro hdeg
    let z : CanonicalBuserSarnakProjectiveDegenerateSymbol p :=
      ⟨S.polygonSideRawSymbol (S.polygonSidePartner d.1 d.2).1
        (S.polygonSidePartner d.1 d.2).2, hdeg⟩
    exact hnot ⟨z,
      isCanonicalProjectivePolygonTreeCarrier_of_partnerRawSymbol_eq d.1 d.2 z rfl⟩
  rcases d with ⟨q, s⟩
  cases s with
  | a | cInv | aInv | c =>
      have hne := nonconeBoundaryTerm_ne_one_of_raw_nondegenerate q _
        (by simp [ProjectivePolygonSide.generator]) hraw
      exact (canonicalProjectiveConePostConeBoundaryTerm_eq_one_or_physicalCarrier
        hp hp2 q _).resolve_left hne
  | e1 =>
      exact coneBoundaryTerm_physicalCarrier_of_raw_pair_nondegenerate
        hp hp2 q .e1 hraw hpair
  | e2 =>
      exact coneBoundaryTerm_physicalCarrier_of_raw_pair_nondegenerate
        hp hp2 q .e2 hraw hpair
  | e3 =>
      exact coneBoundaryTerm_physicalCarrier_of_raw_pair_nondegenerate
        hp hp2 q .e3 hraw hpair
  | e4 =>
      exact coneBoundaryTerm_physicalCarrier_of_raw_pair_nondegenerate
        hp hp2 q .e4 hraw hpair

/-- The trivial first-stage branch is exactly deletion of a primal-tree
edge; it is not a residual classification hypothesis. -/
theorem canonicalProjectiveConePostConeBoundaryTerm_eq_one_iff_primal_carrier
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d : CanonicalProjectivePolygonDart p) :
    canonicalProjectiveConePostConeBoundaryTerm p d.1 d.2 = 1 ↔
      ∃ z : CanonicalBuserSarnakProjectiveDegenerateSymbol p,
        IsCanonicalProjectivePolygonTreeCarrier z d := by
  constructor
  · intro hterm
    by_contra hnot
    exact canonicalProjectiveConePostConeBoundaryTerm_ne_one_of_physical_carrier d
      (canonicalProjectiveConePostConeBoundaryTerm_physicalCarrier_of_not_primal
        hp hp2 d hnot) hterm
  · rintro ⟨z, hz⟩
    exact canonicalProjectiveConePostConeBoundaryTerm_eq_one_of_primal_carrier hp hp2 z d hz

/-- Final signed endpoints are disjoint from every primal tree carrier. -/
theorem canonicalProjectivePostConeSurvivingDart_not_primal_carrier
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (x : CanonicalProjectivePostConeSurvivingDart hp hp2)
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p) :
    ¬ IsCanonicalProjectivePolygonTreeCarrier z
      (canonicalProjectivePostConeSurvivingDart_embedding hp hp2 x) := by
  intro h
  have hterm := canonicalProjectiveConePostConeBoundaryTerm_eq_one_of_primal_carrier
    hp hp2 z _ h
  cases x with
  | inl y =>
      change canonicalProjectiveConePostConeBoundaryTerm p
        (projectivePolygonPostConeEdgeSource y.1).state
        (projectivePolygonPostConeEdgeSide y.1) = 1 at hterm
      rw [canonicalProjectiveConePostConeBoundaryTerm_edgeSource_eq] at hterm
      exact FreeGroup.of_ne_one y.1 hterm
  | inr y =>
      change canonicalProjectiveConePostConeBoundaryTerm p
        (projectivePolygonPostConeEdgeTarget y.1).state
        (projectivePolygonPostConeEdgeTargetSide y.1) = 1 at hterm
      have hi := canonicalProjectiveConePostConeBoundaryTerm_edgeTarget_eq_inv hp hp2 y.1
      change canonicalProjectiveConePostConeBoundaryTerm p
        (projectivePolygonPostConeEdgeTarget y.1).state
        (projectivePolygonPostConeEdgeTargetSide y.1) = (FreeGroup.of y.1)⁻¹ at hi
      rw [hi] at hterm
      exact inv_ne_one.mpr (FreeGroup.of_ne_one y.1) hterm

private theorem physicalCarrierBy_iff_endpoint_darts
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d : CanonicalProjectivePolygonDart p) (z : CanonicalProjectiveConeKeptSymbol p) :
    CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrierBy p d.1 d.2 z ↔
      d = projectivePolygonPostConeEdgeSourceDart z ∨
        d = projectivePolygonPostConeEdgeTargetDart z := by
  constructor
  · rintro (h | h)
    · left
      exact Prod.ext (congrArg ProjectivePolygonPostConeFace.state h.1) h.2.1
    · right
      exact Prod.ext (congrArg ProjectivePolygonPostConeFace.state h.1) h.2.1
  · rintro (rfl | rfl)
    · exact Or.inl ⟨rfl, rfl, canonicalProjectiveConePostConeBoundaryTerm_edgeSource_eq z⟩
    · refine Or.inr ⟨rfl, rfl, ?_⟩
      change canonicalProjectiveConePostConeBoundaryTerm p
        (projectivePolygonPostConeEdgeTarget z).state
        (projectivePolygonPostConeEdgeTargetSide z) = (FreeGroup.of z)⁻¹
      exact canonicalProjectiveConePostConeBoundaryTerm_edgeTarget_eq_inv hp hp2 z

private theorem survivingDart_physicalCarrierBy
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (x : CanonicalProjectivePostConeSurvivingDart hp hp2) :
    ∃ z : CanonicalProjectivePostConeFinalGenerator hp hp2,
      CanonicalProjectiveConePostConeBoundaryTermPhysicalCarrierBy p
        (canonicalProjectivePostConeSurvivingDart_embedding hp hp2 x).1
        (canonicalProjectivePostConeSurvivingDart_embedding hp hp2 x).2 z.1 := by
  cases x with
  | inl z =>
      refine ⟨z, (physicalCarrierBy_iff_endpoint_darts hp hp2 _ z.1).mpr ?_⟩
      exact Or.inl rfl
  | inr z =>
      refine ⟨z, (physicalCarrierBy_iff_endpoint_darts hp hp2 _ z.1).mpr ?_⟩
      exact Or.inr rfl

/-- No retained physical dart belongs to a selected dual edge. -/
theorem canonicalProjectivePostConeSurvivingDart_not_dual_carrier
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (x : CanonicalProjectivePostConeSurvivingDart hp hp2) :
    ¬ IsCanonicalProjectivePostConeDualTreeCarrier hp hp2
      (canonicalProjectivePostConeSurvivingDart_embedding hp hp2 x) := by
  rintro ⟨slot, hslot⟩
  obtain ⟨z, hz⟩ := survivingDart_physicalCarrierBy hp hp2 x
  have hslotBy := (physicalCarrierBy_iff_endpoint_darts hp hp2 _
    (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)).mpr hslot
  have hlabel := canonicalProjectiveConePostConeBoundaryTermPhysicalCarrier_witness_unique
    hz hslotBy
  exact z.2 ⟨slot, hlabel.symm⟩

/-- Exact survivor classification: primal deletion, dual deletion, and
retention exhaust the original physical dart set. -/
theorem mem_canonicalProjectivePostConeSurvivorSet_iff
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d : CanonicalProjectivePolygonDart p) :
    d ∈ canonicalProjectivePostConeSurvivorSet hp hp2 ↔
      (¬ ∃ z : CanonicalBuserSarnakProjectiveDegenerateSymbol p,
        IsCanonicalProjectivePolygonTreeCarrier z d) ∧
      ¬ IsCanonicalProjectivePostConeDualTreeCarrier hp hp2 d := by
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨?_, canonicalProjectivePostConeSurvivingDart_not_dual_carrier hp hp2 x⟩
    rintro ⟨z, hz⟩
    exact canonicalProjectivePostConeSurvivingDart_not_primal_carrier hp hp2 x z hz
  · rintro ⟨hprimal, hdual⟩
    obtain ⟨z, hz⟩ :=
      canonicalProjectiveConePostConeBoundaryTerm_physicalCarrier_of_not_primal
        hp hp2 d hprimal
    have hendpoint := (physicalCarrierBy_iff_endpoint_darts hp hp2 d z).mp hz
    have hfinal : ¬ isCanonicalProjectivePostConeTreeEliminationSymbol hp hp2 z := by
      rintro ⟨slot, hslot⟩
      exact hdual ⟨slot, by simpa only [hslot] using hendpoint⟩
    let final : CanonicalProjectivePostConeFinalGenerator hp hp2 := ⟨z, hfinal⟩
    rcases hendpoint with hsource | htarget
    · exact ⟨Sum.inl final, hsource.symm⟩
    · exact ⟨Sum.inr final, htarget.symm⟩

/-- The omitted physical darts are exactly the carriers of either tree. -/
theorem not_mem_canonicalProjectivePostConeSurvivorSet_iff
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d : CanonicalProjectivePolygonDart p) :
    d ∉ canonicalProjectivePostConeSurvivorSet hp hp2 ↔
      (∃ z : CanonicalBuserSarnakProjectiveDegenerateSymbol p,
        IsCanonicalProjectivePolygonTreeCarrier z d) ∨
      IsCanonicalProjectivePostConeDualTreeCarrier hp hp2 d := by
  rw [mem_canonicalProjectivePostConeSurvivorSet_iff]
  simp only [not_and_or, not_not]

/-- The primal and selected dual tree deletions are disjoint. -/
theorem canonicalProjectivePostConeDualTreeCarrier_not_primal
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d : CanonicalProjectivePolygonDart p)
    (hdual : IsCanonicalProjectivePostConeDualTreeCarrier hp hp2 d) :
    ¬ ∃ z : CanonicalBuserSarnakProjectiveDegenerateSymbol p,
      IsCanonicalProjectivePolygonTreeCarrier z d := by
  rintro ⟨z, hz⟩
  obtain ⟨slot, hslot⟩ := hdual
  have hcarrier := (physicalCarrierBy_iff_endpoint_darts hp hp2 d
    (canonicalProjectivePostConeTreeSlotLabel hp hp2 slot)).mpr hslot
  exact canonicalProjectiveConePostConeBoundaryTerm_ne_one_of_physical_carrier d
    ⟨canonicalProjectivePostConeTreeSlotLabel hp hp2 slot, hcarrier⟩
    (canonicalProjectiveConePostConeBoundaryTerm_eq_one_of_primal_carrier hp hp2 z d hz)

/-- Actual physical side pairing preserves the final survivor set. -/
theorem canonicalProjectivePostConeSurvivorSet_partner_iff
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d : CanonicalProjectivePolygonDart p) :
    (canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner d.1 d.2 ∈
        canonicalProjectivePostConeSurvivorSet hp hp2 ↔
      d ∈ canonicalProjectivePostConeSurvivorSet hp hp2 := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨Sum.swap x, ?_⟩
    rw [canonicalProjectivePostConeSurvivingDart_embedding_swap, hx,
      BuserSarnakProjectiveQuotientSectionData.polygonSidePartner_involutive]
  · rintro ⟨x, rfl⟩
    exact ⟨Sum.swap x, canonicalProjectivePostConeSurvivingDart_embedding_swap hp hp2 x⟩

/-- The selected dual deletion, like primal deletion, consists of complete
physical paired edges. -/
theorem canonicalProjectivePostConeDualTreeCarrier_partner_iff
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d : CanonicalProjectivePolygonDart p) :
    IsCanonicalProjectivePostConeDualTreeCarrier hp hp2
        ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner d.1 d.2) ↔
      IsCanonicalProjectivePostConeDualTreeCarrier hp hp2 d := by
  have hforward : ∀ e : CanonicalProjectivePolygonDart p,
      IsCanonicalProjectivePostConeDualTreeCarrier hp hp2 e →
      IsCanonicalProjectivePostConeDualTreeCarrier hp hp2
        ((canonicalBuserSarnakProjectiveQuotientSectionData p).polygonSidePartner e.1 e.2) := by
    intro e he
    rcases he with ⟨slot, rfl | rfl⟩
    · refine ⟨slot, Or.inr ?_⟩
      exact (projectivePolygonPostConeEdgeTargetDart_eq_partner _).symm
    · refine ⟨slot, Or.inl ?_⟩
      rw [projectivePolygonPostConeEdgeTargetDart_eq_partner,
        BuserSarnakProjectiveQuotientSectionData.polygonSidePartner_involutive]
      rfl
  constructor
  · intro h
    simpa only [BuserSarnakProjectiveQuotientSectionData.polygonSidePartner_involutive]
      using hforward _ h
  · exact hforward d

/-- Before first return, the primal-tree swap acts trivially on every final
physical survivor. -/
theorem canonicalProjectivePrimalTreeSwapPerm_apply_of_survivor
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (d : canonicalProjectivePostConeSurvivorSet hp hp2) :
    canonicalProjectivePrimalTreeSwapPerm p d.val = d.val := by
  rw [canonicalProjectivePrimalTreeSwapPerm_apply]
  exact if_neg ((mem_canonicalProjectivePostConeSurvivorSet_iff hp hp2 d.val).mp d.property).1

#print axioms canonicalProjectiveConePostConeBoundaryTerm_eq_one_of_primal_carrier
#print axioms canonicalProjectiveConePostConeBoundaryTerm_eq_one_iff_primal_carrier
#print axioms canonicalProjectivePostConeSurvivingDart_not_primal_carrier
#print axioms mem_canonicalProjectivePostConeSurvivorSet_iff
#print axioms not_mem_canonicalProjectivePostConeSurvivorSet_iff
#print axioms canonicalProjectivePostConeDualTreeCarrier_not_primal
#print axioms canonicalProjectivePostConeSurvivorSet_partner_iff
#print axioms canonicalProjectivePostConeDualTreeCarrier_partner_iff
#print axioms canonicalProjectivePrimalTreeSwapPerm_apply_of_survivor

end

end SystolicGrowth
